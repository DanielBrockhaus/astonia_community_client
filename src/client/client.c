/*
 * Part of Astonia Client (c) Daniel Brockhaus. Please read license.txt.
 *
 * Client/Server Communication
 *
 * Parses server commands and sends back player input
 *
 */

#include "dll.h"
#include "astonia_net.h"
#include <SDL2/SDL_timer.h>
#include <time.h>
#include <zlib.h>
#include <SDL2/SDL.h>

#include "astonia.h"
#include "client/client.h"
#include "client/client_private.h"
#include "sdl/sdl.h"
#include "sdl/sdl_private.h"
#include "gui/gui.h"
#include "modder/modder.h"
#include "protocol.h"

int display_gfx = 0, display_time = 0;
static int rec_bytes = 0;
static int sent_bytes = 0;
static astonia_sock *sock = NULL;
int sockstate = 0;
static unsigned int socktime = 0;
int socktimeout = 0;
int change_area = 0;
int kicked_out = 0;
unsigned int unique = 0;
#ifdef STORE_UNIQUE
unsigned int usum = 0;
#endif
int target_port = 5556;
DLL_EXPORT char *target_server = NULL;
DLL_EXPORT char password[16];
static int zsinit;
static struct z_stream_s zs;

DLL_EXPORT char username[40];
DLL_EXPORT int tick;
DLL_EXPORT int mirror = 0;
DLL_EXPORT int realtime;
DLL_EXPORT int protocol_version = 0;

int newmirror = 0;
int lasttick; // ticks in inbuf
static int lastticksize; // size inbuf must reach to get the last tick complete in the queue

static struct queue queue[Q_SIZE];
int q_in, q_out, q_size;

int server_cycles;

static int ticksize;
static int inused;
static int indone;
int login_done;
static unsigned char inbuf[MAX_INBUF];

static int outused;
static unsigned char outbuf[MAX_OUTBUF];

DLL_EXPORT int act;
DLL_EXPORT int actx;
DLL_EXPORT int acty;

DLL_EXPORT unsigned int cflags; // current item flags
DLL_EXPORT unsigned int csprite; // and sprite

DLL_EXPORT int originx;
DLL_EXPORT int originy;
DLL_EXPORT struct map map[MAPDX * MAPDY];
DLL_EXPORT struct map map2[MAPDX * MAPDY];

DLL_EXPORT int value[2][V_MAX];
DLL_EXPORT int item[INVENTORYSIZE];
DLL_EXPORT int item_flags[INVENTORYSIZE];
DLL_EXPORT int hp;
DLL_EXPORT int mana;
DLL_EXPORT int rage;
DLL_EXPORT int endurance;
DLL_EXPORT int lifeshield;
DLL_EXPORT int experience;
DLL_EXPORT int experience_used;
DLL_EXPORT int mil_exp;
DLL_EXPORT int gold;

DLL_EXPORT struct player player[MAXCHARS];

DLL_EXPORT union ceffect ceffect[MAXEF];
DLL_EXPORT unsigned char ueffect[MAXEF];

DLL_EXPORT int con_type;
DLL_EXPORT char con_name[80];
DLL_EXPORT int con_cnt;
DLL_EXPORT int container[CONTAINERSIZE];
DLL_EXPORT int price[CONTAINERSIZE];
DLL_EXPORT int itemprice[CONTAINERSIZE];
DLL_EXPORT int cprice;

DLL_EXPORT int lookinv[12];
DLL_EXPORT int looksprite, lookc1, lookc2, lookc3;
DLL_EXPORT char look_name[80];
DLL_EXPORT char look_desc[1024];

DLL_EXPORT char pent_str[7][80];

DLL_EXPORT int pspeed = 0; // 0=normal   1=fast      2=stealth     - like the server

int may_teleport[64 + 32];

DLL_EXPORT int frames_per_second = TICKS;

// Unaligned load/store helpers
DLL_EXPORT void client_send(void *buf, int len)
{
	if (len > MAX_OUTBUF - outused) {
		return;
	}

	memcpy(outbuf + outused, buf, len);
	outused += len;
}

void bzero_client(int part)
{
	if (part == 0) {
		lasttick = 0;
		lastticksize = 0;

		bzero(queue, sizeof(queue));
		q_in = q_out = q_size = 0;

		server_cycles = 0;

		zsinit = 0;
		bzero(&zs, sizeof(zs));

		ticksize = 0;
		inused = 0;
		indone = 0;
		login_done = 0;
		bzero(inbuf, sizeof(inbuf));

		outused = 0;
		bzero(outbuf, sizeof(outbuf));
	}

	if (part == 1) {
		act = 0;
		actx = 0;
		acty = 0;

		cflags = 0;
		csprite = 0;

		originx = 0;
		originy = 0;
		bzero(map, sizeof(map));

		bzero(value, sizeof(value));
		bzero(item, sizeof(item));
		bzero(item_flags, sizeof(item_flags));
		hp = 0;
		mana = 0;
		endurance = 0;
		lifeshield = 0;
		experience = 0;
		experience_used = 0;
		mil_exp = 0;
		gold = 0;

		bzero(player, sizeof(player));

		bzero(ceffect, sizeof(ceffect));
		bzero(ueffect, sizeof(ueffect));

		con_cnt = 0;
		bzero(container, sizeof(container));
		bzero(price, sizeof(price));
		bzero(itemprice, sizeof(itemprice));
		cprice = 0;

		bzero(lookinv, sizeof(lookinv));
		show_look = 0;

		pspeed = 0;
		pent_str[0][0] = pent_str[1][0] = pent_str[2][0] = pent_str[3][0] = pent_str[4][0] = pent_str[5][0] =
		    pent_str[6][0] = 0;

		bzero(may_teleport, sizeof(may_teleport));

		amod_areachange();
		minimap_clear();
	}
}

int close_client(void)
{
	if (sock) {
		astonia_net_close(sock);
		sock = NULL;
	}
	if (zsinit) {
		inflateEnd(&zs);
		zsinit = 0;
	}

	sockstate = 0;
	socktime = 0;

	bzero_client(0);
	bzero_client(1);

	return 0;
}

#define MAXPASSWORD 16

void decrypt(const char *name, char *password)
{
	int i;
	static const char secret[4][MAXPASSWORD] = {"\000cgf\000de8etzdf\000dx", "jrfa\000v7d\000drt\000edm",
	    "t6zh\000dlr\000fu4dms\000", "jkdm\000u7z5g\000j77\000g"};

	for (i = 0; i < MAXPASSWORD; i++) {
		password[i] = password[i] ^ secret[name[1] % 4][i] ^ name[i % 3];
	}
}

void send_info(astonia_sock *s)
{
	char buf[12] = {0};
	uint32_t local_ip, peer_ip;
	astonia_net_local_ipv4(s, &local_ip);
	astonia_net_peer_ipv4(s, &peer_ip);
	store_u32(buf + 0, local_ip);
	store_u32(buf + 4, peer_ip);

#ifdef STORE_UNIQUE
	load_unique();
#endif

	store_u32(buf + 8, unique);
	(void)astonia_net_send(s, buf, 12);
}

int poll_network(void)
{
	int n;

	// something fatal failed (sockstate will somewhen tell you what)
	if (sockstate < 0) {
		return -1;
	}

	// create nonblocking socket
	if (sockstate == 0 && !kicked_out) {
		if (SDL_GetTicks() < socktime) {
			return 0;
		}

		// reset socket
		if (sock) {
			astonia_net_close(sock);
			sock = NULL;
		}
		if (zsinit) {
			inflateEnd(&zs);
			zsinit = 0;
		}

		change_area = 0;
		kicked_out = 0;

		// reset client
		bzero_client(0);

		if (!socktimeout) {
			socktimeout = time(NULL);
		}

		// connect to server (non-blocking); require hostname string
		if (target_server == NULL) {
			fail("Server URL not specified.");
			sockstate = -3; // fail - no retry
			return -1;
		}

		sock = astonia_net_connect(target_server, (unsigned short)target_port, 0);
		if (!sock) {
			fail("creating socket failed");
			sockstate = 0;
			socktime = SDL_GetTicks() + 5000;
			return -1;
		}

		// statechange
		sockstate = 1;
		// return 0;
	}

	// wait until connect is ok
	if (sockstate == 1) {
		if (SDL_GetTicks() < socktime) {
			return 0;
		}

		n = astonia_net_poll(sock, 2, 50);
		if (n == 0) { /* timeout -> try next frame */
			socktime = SDL_GetTicks() + 50;
			return 0;
		} else if (n < 0 || (n & 2) == 0) { /* error or not writable */
			note("connect failed");
			sockstate = 0;
			socktime = SDL_GetTicks() + 5000;
			return -1;
		}

#ifdef DEVELOPER
		{
			uint32_t be = 0;
			char ip[16] = "unknown";
			if (astonia_net_peer_ipv4(sock, &be) == 0 && be != 0) {
				ipv4_be_to_string(be, ip);
				note("Using login server at %s (%s):%u", target_server, ip, (unsigned)target_port);
			} else {
				// Could be IPv6 or not yet retrievable; still log the hostname.
				note("Using login server at %s:%u", target_server, (unsigned)target_port);
			}
		}
#endif

		// statechange
		sockstate = 2;
	}

	// connected - send password and initialize compression buffers
	if (sockstate == 2) {
		char tmp[256];

		// initialize compression
		if (inflateInit(&zs)) {
			note("zsinit failed");
			sockstate = -5; // fail - no retry
			return -1;
		}
		zsinit = 1;

		bzero(tmp, sizeof(tmp));
		strcpy(tmp, username);
		astonia_net_send(sock, tmp, 40);

		// send password
		bzero(tmp, sizeof(tmp));
		strcpy(tmp, password);
		decrypt(username, tmp);
		astonia_net_send(sock, tmp, 16);

		store_u32(tmp, 0x8fd46100 | 0x01); // magic code + version 1
		astonia_net_send(sock, tmp, 4);
		send_info(sock);

		// statechange
		sockstate = 3;
	}

	// here we go ...
	if (change_area) {
		sockstate = 0;
		socktimeout = time(NULL);
		return 0;
	}

	if (kicked_out) {
		sockstate = -6; // fail - no retry
		close_client();
		return -1;
	}

	// check if we have one tick, so we can reset the map and move to state 4 !!! note that this state has no return
	// statement, so we still read and write)
	if (sockstate == 3) {
		if (login_done) { // if (lasttick>1) {
			// statechange
			// note("go ahead (left at tick=%d)",tick);
			// bzero_client(1);
			sockstate = 4;
		}
	}

	// send
	if (outused && sockstate == 4 && sock) {
		n = (int)astonia_net_send(sock, outbuf, outused);
		if (n == 0) {
			addline("connection lost during write\n");
			sockstate = 0;
			socktimeout = time(NULL);
			return -1;
		} else if (n < 0) {
			// would-block -> no progress this frame
			n = 0;
		} else {
			memmove(outbuf, outbuf + n, outused - n);
			outused -= n;
			sent_bytes += n;
		}
	}

	// recv
	n = 0;
	if (sock && astonia_net_poll(sock, 1, 0) > 0) {
		n = (int)astonia_net_recv(sock, (char *)inbuf + inused, MAX_INBUF - inused);
		if (n < 0) {
			n = 0; /* would-block */
		} else if (n == 0) {
			addline("connection lost during read\n");
			sockstate = 0;
			socktimeout = time(NULL);
			return -1;
		}
	} else {
		return 0; /* no data this frame */
	}

	inused += n;
	rec_bytes += n;

	// count ticks
	while (1) {
		if (inused >= lastticksize + 1 && *(inbuf + lastticksize) & 0x40) {
			lastticksize += 1 + (*(inbuf + lastticksize) & 0x3F);
		} else if (inused >= lastticksize + 2) {
			lastticksize += 2 + (net_read16(inbuf + lastticksize) & 0x3FFF);
		} else {
			break;
		}

		lasttick++;
	}

	return 0;
}

void auto_tick(struct map *cmap)
{
	int x, y, mn;

	// automatically tick map
	for (y = 0; y < MAPDY; y++) {
		for (x = 0; x < MAPDX; x++) {
			mn = mapmn(x, y);
			if (!(cmap[mn].csprite)) {
				continue;
			}

			cmap[mn].step++;
			if (cmap[mn].step < cmap[mn].duration) {
				continue;
			}
			cmap[mn].step = 0;
		}
	}
}

int next_tick(void)
{
	int ticksize;
	int size, ret, attick;

	// no room for next tick, leave it in in-queue
	if (q_size == Q_SIZE) {
		return 0;
	}

	// do we have a new tick
	if (inused >= 1 && (*(inbuf) & 0x40)) {
		ticksize = 1 + (*(inbuf) & 0x3F);
		if (inused < ticksize) {
			return 0;
		}
		indone = 1;
	} else if (inused >= 2 && !(*(inbuf) & 0x40)) {
		ticksize = 2 + (net_read16(inbuf) & 0x3FFF);
		if (inused < ticksize) {
			return 0;
		}
		indone = 2;
	} else {
		return 0;
	}

	// decompress
	if (*inbuf & 0x80) {
		zs.next_in = inbuf + indone;
		zs.avail_in = ticksize - indone;

		zs.next_out = queue[q_in].buf;
		zs.avail_out = sizeof(queue[q_in].buf);

		ret = inflate(&zs, Z_SYNC_FLUSH);
		if (ret != Z_OK) {
			warn("Compression error %d\n", ret);
			quit = 1;
			return 0;
		}

		if (zs.avail_in) {
			warn("HELP (%d)\n", zs.avail_in);
			return 0;
		}

		size = sizeof(queue[q_in].buf) - zs.avail_out;
	} else {
		size = ticksize - indone;
		memcpy(queue[q_in].buf, inbuf + indone, size);
	}
	queue[q_in].size = size;

	auto_tick(map2);
	attick = prefetch(queue[q_in].buf, queue[q_in].size);

	q_in = (q_in + 1) % Q_SIZE;
	q_size++;

	// remove tick from inbuf
	if (inused - ticksize >= 0) {
		memmove(inbuf, inbuf + ticksize, inused - ticksize);
	} else {
		note("kuckuck!");
	}
	inused = inused - ticksize;

	// adjust some values
	lasttick--;
	lastticksize -= ticksize;

	return attick;
}

int do_tick(void)
{
	// process tick
	if (q_size > 0) {
		auto_tick(map);
		process(queue[q_out].buf, queue[q_out].size);
		q_out = (q_out + 1) % Q_SIZE;
		q_size--;
		hover_capture_tick();

		// increase tick
		tick++;
		if (tick % TICKS == 0) {
			realtime++;
		}

		return 1;
	}

	return 0;
}

void cl_ticker(void)
{
	char buf[256];

	buf[0] = CL_TICKER;
	store_u32(buf + 1, tick);
	client_send(buf, 5);
}

// X exp yield level Y
DLL_EXPORT int exp2level(int val)
{
	if (val < 1) {
		return 1;
	}

	return max(1, (int)(sqrt(sqrt(val))));
}

// to reach level X you need Y exp
DLL_EXPORT int level2exp(int level)
{
	return pow(level, 4);
}

DLL_EXPORT int mapmn(int x, int y)
{
	if (x < 0 || y < 0 || x >= MAPDX || y >= MAPDY) {
		return -1;
	}
	return (x + y * MAPDX);
}
