/*
 * Part of Astonia Client (c) Daniel Brockhaus. Please read license.txt.
 *
 * Startup And Command Line
 *
 * Contains the startup stuff and the parsing of the command line. Plus a
 * bunch of generic helper for memory allocation and error display.
 *
 */

#include <stdint.h>
#include <stdio.h>
#include <time.h>
#include <SDL2/SDL.h>
#ifdef _WIN32
#include <windows.h>
#endif

#include "astonia.h"
#include "game/game.h"
#include "game/game_private.h"
#include "sdl/sdl.h"
#include "gui/gui.h"
#include "client/client.h"
#include "modder/modder.h"

int quit = 0;

char *localdata;

static int panic_reached = 0;
static int xmemcheck_failed = 0;
char user_keys[10] = {'Q', 'W', 'E', 'A', 'S', 'D', 'Z', 'X', 'C', 'V'};

DLL_EXPORT uint64_t game_options = GO_NOTSET;

static char memcheck_failed_str[] = {"memcheck failed"};
static char panic_reached_str[] = {"panic failure"};

FILE *errorfp;

// note, warn, fail, paranoia, addline

DLL_EXPORT int note(const char *format, ...)
{
	va_list va;
	char buf[1024];


	va_start(va, format);
	vsprintf(buf, format, va);
	va_end(va);

	printf("NOTE: %s\n", buf);
	fflush(stdout);
#ifdef DEVELOPER
	addline("NOTE: %s\n", buf);
#endif

	return 0;
}

DLL_EXPORT int warn(const char *format, ...)
{
	va_list va;
	char buf[1024];


	va_start(va, format);
	vsprintf(buf, format, va);
	va_end(va);

	printf("WARN: %s\n", buf);
	fflush(stdout);
	addline("WARN: %s\n", buf);

	return 0;
}

DLL_EXPORT int fail(const char *format, ...)
{
	va_list va;
	char buf[1024];


	va_start(va, format);
	vsprintf(buf, format, va);
	va_end(va);

	fprintf(errorfp, "FAIL: %s\n", buf);
	fflush(errorfp);
	printf("FAIL: %s\n", buf);
	fflush(stdout);
	addline("FAIL: %s\n", buf);

	return -1;
}

DLL_EXPORT void paranoia(const char *format, ...)
{
	va_list va;

	fprintf(errorfp, "PARANOIA EXIT in ");

	va_start(va, format);
	vfprintf(errorfp, format, va);
	va_end(va);

	fprintf(errorfp, "\n");
	fflush(errorfp);

	exit(-1);
}

void xlog(FILE *logfp, char *format, ...)
{
	va_list args;
	char buf[1024];
	struct tm *tm;
	time_t time_now;
	time(&time_now);

	va_start(args, format);
	vsnprintf(buf, 1024, format, args);
	va_end(args);

	tm = localtime(&time_now);
	if (tm) {
		fprintf(logfp, "%02d.%02d.%02d %02d:%02d:%02d: %s\n", tm->tm_mday, tm->tm_mon + 1, tm->tm_year - 100,
		    tm->tm_hour, tm->tm_min, tm->tm_sec, buf);
	} else {
		fprintf(logfp, "%s\n", buf);
	}
	fflush(logfp);
}

static int _addlinesep = 0;

void addlinesep(void)
{
	_addlinesep = 1;
}

DLL_EXPORT void addline(const char *format, ...)
{
	va_list va;
	char buf[1024];

	if (_addlinesep) {
		_addlinesep = 0;
		addline("-------------");
	}

	va_start(va, format);
	vsnprintf(buf, sizeof(buf) - 1, format, va);
	buf[sizeof(buf) - 1] = 0;
	va_end(va);

	if (dd_text_init_done()) {
		dd_add_text(buf);
	}
}

// io

int rread(FILE *fp, void *ptr, int size)
{
	int n;

	while (size > 0) {
		n = fread(ptr, 1, size, fp);
		if (n < 0) {
			return -1;
		}
		if (n == 0) {
			return 1;
		}
		size -= n;
		ptr = ((unsigned char *)(ptr)) + n;
	}
	return 0;
}

char *load_ascii_file(char *filename, int ID)
{
	FILE *fp;
	int size;
	char *ptr;

	if (!(fp = fopen(filename, "rb"))) {
		return NULL;
	}
	if (fseek(fp, 0, SEEK_END) != 0) {
		fclose(fp);
		return NULL;
	}
	size = ftell(fp);
	if (fseek(fp, 0, SEEK_SET) != 0) {
		fclose(fp);
		return NULL;
	}
	ptr = xmalloc(size + 1, ID);
	if (rread(fp, ptr, size)) {
		xfree(ptr);
		fclose(fp);
		return NULL;
	}
	ptr[size] = 0;
	fclose(fp);

	return ptr;
}

// memory

int memused = 0;
int memptrused = 0;

int maxmemsize = 0;
int maxmemptrs = 0;
int memptrs[MAX_MEM];
int memsize[MAX_MEM];

struct memhead {
	int size;
	int ID;
};

// TODO: removed unused memory areas
static char *memname[MAX_MEM] = {"MEM_TOTA", // 0
    "MEM_GLOB", "MEM_TEMP", "MEM_ELSE", "MEM_DL",
    "MEM_IC", // 5
    "MEM_SC", "MEM_VC", "MEM_PC", "MEM_GUI",
    "MEM_GAME", // 10
    "MEM_TEMP11", "MEM_VPC", "MEM_VSC", "MEM_VLC", "MEM_SDL_BASE", "MEM_SDL_PIXEL", "MEM_SDL_PNG", "MEM_SDL_PIXEL2",
    "MEM_TEMP5", "MEM_TEMP6", "MEM_TEMP7", "MEM_TEMP8", "MEM_TEMP9", "MEM_TEMP10"};

unsigned long long get_total_system_memory(void);

void list_mem(void)
{
	int i, flag = 0;
	extern long long mem_tex;

	note("--mem----------------------");
	for (i = 1; i < MAX_MEM; i++) {
		if (memsize[i] || memptrs[i]) {
			flag = 1;
			note("%s %.2fMB in %d ptrs", memname[i], memsize[i] / (1024.0 * 1024.0), memptrs[i]);
		}
	}
	if (flag) {
		note("%s %.2fMB in %d ptrs", memname[0], memsize[0] / (1024.0 * 1024.0), memptrs[0]);
	}
	note("%s %.2fMB in %d ptrs", "MEM_MAX", maxmemsize / (1024.0 * 1024.0), maxmemptrs);
	note("---------------------------");
	note("Texture Cache: %.2fMB", mem_tex / (1024.0 * 1024.0));

	note("UsedMem=%.2fG of %.2fG", (memused + mem_tex) / 1024.0 / 1024.0 / 1024.0,
	    get_total_system_memory() / 1024.0 / 1024.0 / 1024.0);
}

static int memcheckset = 0;
static unsigned char memcheck[256];

int xmemcheck(void *ptr)
{
	struct memhead *mem;
	unsigned char *head, *tail, *rptr;

	if (!ptr) {
		return 0;
	}

	mem = (struct memhead *)(((unsigned char *)(ptr)) - 8 - sizeof(memcheck));

	// ID check
	if (mem->ID >= MAX_MEM) {
		note("xmemcheck: ill mem id (%d)", mem->ID);
		xmemcheck_failed = 1;
		return -1;
	}

	// border check
	head = ((unsigned char *)(mem)) + 8;
	rptr = ((unsigned char *)(mem)) + 8 + sizeof(memcheck);
	tail = ((unsigned char *)(mem)) + 8 + sizeof(memcheck) + mem->size;

	if (memcmp(head, memcheck, sizeof(memcheck))) {
		fail("xmemcheck: ill head in %s (ptr=%p)", memname[mem->ID], rptr);
		xmemcheck_failed = 1;
		return -1;
	}
	if (memcmp(tail, memcheck, sizeof(memcheck))) {
		fail("xmemcheck: ill tail in %s (ptr=%p)", memname[mem->ID], rptr);
		xmemcheck_failed = 1;
		return -1;
	}

	return 0;
}

void *xmalloc(int size, int ID)
{
	struct memhead *mem;
	unsigned char *head, *tail, *rptr;

	if (!memcheckset) {
		for (memcheckset = 0; memcheckset < sizeof(memcheck); memcheckset++) {
			memcheck[memcheckset] = rrand(256);
		}
		sprintf(memcheck, "!MEMCKECK MIGHT FAIL!");
	}

	if (!size) {
		return NULL;
	}

	memptrused++;

	mem = calloc(1, 8 + sizeof(memcheck) + size + sizeof(memcheck));
	if (!mem) {
		fail("OUT OF MEMORY !!!");
		return NULL;
	}

	memused += 8 + sizeof(memcheck) + size + sizeof(memcheck);

	if (ID >= MAX_MEM) {
		fail("xmalloc: ill mem id");
		return NULL;
	}

	mem->ID = ID;
	mem->size = size;
	memsize[mem->ID] += mem->size;
	memptrs[mem->ID] += 1;
	memsize[0] += mem->size;
	memptrs[0] += 1;

	if (memsize[0] > maxmemsize) {
		maxmemsize = memsize[0];
	}
	if (memptrs[0] > maxmemptrs) {
		maxmemptrs = memptrs[0];
	}

	head = ((unsigned char *)(mem)) + 8;
	rptr = ((unsigned char *)(mem)) + 8 + sizeof(memcheck);
	tail = ((unsigned char *)(mem)) + 8 + sizeof(memcheck) + mem->size;

	// set memcheck
	memcpy(head, memcheck, sizeof(memcheck));
	memcpy(tail, memcheck, sizeof(memcheck));

	xmemcheck(rptr);

	return rptr;
}

static void update_mem_stats_add(int ID, int size)
{
	memsize[ID] += size;
	memptrs[ID] += 1;
	memsize[0] += size;
	memptrs[0] += 1;

	if (memsize[0] > maxmemsize) {
		maxmemsize = memsize[0];
	}
	if (memptrs[0] > maxmemptrs) {
		maxmemptrs = memptrs[0];
	}

	memused += 8 + sizeof(memcheck) + size + sizeof(memcheck);
	memptrused++;
}

static void update_mem_stats_remove(int ID, int size)
{
	memsize[ID] -= size;
	memptrs[ID] -= 1;
	memsize[0] -= size;
	memptrs[0] -= 1;

	memused -= 8 + sizeof(memcheck) + size + sizeof(memcheck);
	memptrused--;
}

char *xstrdup(const char *src, int ID)
{
	int size;
	char *dst;

	size = strlen(src) + 1;

	dst = xmalloc(size, ID);
	if (!dst) {
		return NULL;
	}

	memcpy(dst, src, size);

	return dst;
}

void xfree(void *ptr)
{
	struct memhead *mem;

	if (!ptr) {
		return;
	}
	if (xmemcheck(ptr)) {
		return;
	}

	// get mem
	mem = (struct memhead *)(((unsigned char *)(ptr)) - 8 - sizeof(memcheck));

	update_mem_stats_remove(mem->ID, mem->size);

	// free
	free(mem);
}

void xinfo(void *ptr)
{
	struct memhead *mem;

	if (!ptr) {
		printf("NULL");
		return;
	}
	if (xmemcheck(ptr)) {
		printf("ILL");
		return;
	}

	// get mem
	mem = (struct memhead *)(((unsigned char *)(ptr)) - 8 - sizeof(memcheck));

	printf("%d bytes", mem->size);
}

void *xrealloc(void *ptr, int size, int ID)
{
	struct memhead *mem;
	unsigned char *head, *tail, *rptr;

	if (!ptr) {
		return xmalloc(size, ID);
	}
	if (!size) {
		xfree(ptr);
		return NULL;
	}
	if (xmemcheck(ptr)) {
		return NULL;
	}

	mem = (struct memhead *)(((unsigned char *)(ptr)) - 8 - sizeof(memcheck));

	int old_ID = mem->ID;
	int old_size = mem->size;
	update_mem_stats_remove(old_ID, old_size);

	// realloc
	struct memhead *new_mem = realloc(mem, 8 + sizeof(memcheck) + size + sizeof(memcheck));
	if (!new_mem) {
		// Restore counters since realloc failed
		update_mem_stats_add(old_ID, old_size);
		fail("xrealloc: OUT OF MEMORY !!!");
		return NULL;
	}
	mem = new_mem;

	update_mem_stats_add(ID, size);
	mem->ID = ID; // Update ID in case it changed
	mem->size = size;

	head = ((unsigned char *)(mem)) + 8;
	rptr = ((unsigned char *)(mem)) + 8 + sizeof(memcheck);
	tail = ((unsigned char *)(mem)) + 8 + sizeof(memcheck) + mem->size;

	// set memcheck
	memcpy(head, memcheck, sizeof(memcheck));
	memcpy(tail, memcheck, sizeof(memcheck));

	return rptr;
}

void *xrecalloc(void *ptr, int size, int ID)
{
	struct memhead *mem;
	unsigned char *head, *tail, *rptr;

	if (!ptr) {
		return xmalloc(size, ID);
	}
	if (!size) {
		xfree(ptr);
		return NULL;
	}
	if (xmemcheck(ptr)) {
		return NULL;
	}

	mem = (struct memhead *)(((unsigned char *)(ptr)) - 8 - sizeof(memcheck));

	int old_ID = mem->ID;
	int old_size = mem->size;
	update_mem_stats_remove(old_ID, old_size);

	// realloc
	struct memhead *new_mem = realloc(mem, 8 + sizeof(memcheck) + size + sizeof(memcheck));
	if (!new_mem) {
		// Restore counters since realloc failed
		update_mem_stats_add(old_ID, old_size);
		fail("xrecalloc: OUT OF MEMORY !!!");
		return NULL;
	}
	mem = new_mem;

	if (size - old_size > 0) {
		bzero(((unsigned char *)(mem)) + 8 + sizeof(memcheck) + old_size, size - old_size);
	}

	update_mem_stats_add(ID, size);
	mem->ID = ID; // Update ID in case it changed
	mem->size = size;

	head = ((unsigned char *)(mem)) + 8;
	rptr = ((unsigned char *)(mem)) + 8 + sizeof(memcheck);
	tail = ((unsigned char *)(mem)) + 8 + sizeof(memcheck) + mem->size;

	// set memcheck
	memcpy(head, memcheck, sizeof(memcheck));
	memcpy(tail, memcheck, sizeof(memcheck));

	return rptr;
}

// rrandom

void rrandomize(void)
{
	srand(time(NULL));
}

int rrand(int range)
{
	return rand() % range;
}

// parsing command line

void display_messagebox(char *title, char *text)
{
	SDL_ShowSimpleMessageBox(SDL_MESSAGEBOX_ERROR, title, text, NULL);
}

void display_usage(void)
{
	char *buf;
	int size = 4096;

	buf = xmalloc(size, MEM_TEMP);
	if (!buf) {
		return;
	}

	snprintf(buf, size,
	    "The Astonia Client can only be started from the command line or with a specially created shortcut.\n\n"
	    "Usage: moac -u playername -p password -d url\n ... [-w width] [-h height]\n"
	    " ... [-m threads] [-o options] [-c cachesize]\n ... [-k framespersecond]\n\n"
	    "url being, for example, \"server.astonia.com\" or \"192.168.77.132\" (without the quotes).\n\n"
	    "width and height are the desired window size. If this matches the desktop size the client "
	    "will start in windowed borderless pseudo-fullscreen mode.\n\n"
	    "threads is the number of background threads the game should use. Use 0 to disable. Default is 4.\n\n"
	    "options is a bitfield.\nBit 0 (value of 1) enables the Dark GUI by Tegra.\n"
	    "Bit 1 enables the context menu.\nBit 2 the new keybindings.\nBit 3 the smaller bottom GUI.\n"
	    "Bit 4 the sliding away of the top GUI.\nBit 5 enables the bigger health/mana bars.\n"
	    "Bit 6 enables sound.\nBit 7 the large font.\nBit 8 true full screen mode.\nBit 9 enables the "
	    "legacy mouse wheel logic.\n"
	    "Bit 10 enables out-of-order execution (read: faster) of inventory access and command feedback.\n"
	    "Bit 11 reduces the animation buffer for faster reactions and more stutter.\n"
	    "Bit 12 writes application files to %%appdata%% instead of the current folder.\n"
	    "Bit 13 enables the loading and saving of minimaps.\n"
	    "Bit 14 and 15 increase gamma.\n"
	    "Bit 16 makes the sliding top bar less sensitive.\n"
	    "Bit 17 reduces lighting effects (more performance, less pretty).\n"
	    "Bit 18 disables the minimap.\n"
	    "Default depends on screen height.\n\n"
	    "cachesize is the size of the texture cache. Default is 8000. Lower numbers might crash!\n\n"
	    "framespersecond will set the display rate in frames per second.\n\n");

	SDL_ShowSimpleMessageBox(SDL_MESSAGEBOX_INFORMATION, "Usage", buf, NULL);
	printf("%s", buf);

	xfree(buf);
}

DLL_EXPORT char server_url[256];
DLL_EXPORT int server_port = 0;
DLL_EXPORT int want_width = 0;
DLL_EXPORT int want_height = 0;

int parse_args(int argc, char *argv[])
{
	int i;
	char *end;

	for (i = 1; i < argc; i++) {
		char *arg = argv[i];

		if (arg[0] != '-') {
			continue;
		}

		char opt = tolower(arg[1]);
		char *val = NULL;

		if (arg[2] != '\0') {
			val = &arg[2];
		} else if (i + 1 < argc) {
			val = argv[i + 1];
			// We only consume the next arg if we use it.
			// However, in the loop, we need to be careful.
			// If we define that flags taking args MUST have them, we increment i.
		}

		switch (opt) {
		case 'u':
			if (!val && i + 1 < argc) {
				val = argv[++i];
			}
			if (val) {
				snprintf(username, sizeof(username), "%s", val);
			}
			break;
		case 'p':
			if (!val && i + 1 < argc) {
				val = argv[++i];
			}
			if (val) {
				snprintf(password, sizeof(password), "%s", val);
			}
			break;
		case 'd':
			if (!val && i + 1 < argc) {
				val = argv[++i];
			}
			if (val) {
				snprintf(server_url, sizeof(server_url), "%s", val);
			}
			break;
		case 'h':
			if (!val && i + 1 < argc) {
				val = argv[++i];
			}
			if (val) {
				want_height = strtol(val, &end, 10);
			}
			break;
		case 'w':
			if (!val && i + 1 < argc) {
				val = argv[++i];
			}
			if (val) {
				want_width = strtol(val, &end, 10);
			}
			break;
		case 'm':
			if (!val && i + 1 < argc) {
				val = argv[++i];
			}
			if (val) {
				sdl_multi = strtol(val, &end, 10);
			}
			break;
		case 'o':
			if (!val && i + 1 < argc) {
				val = argv[++i];
			}
			if (val) {
				game_options = strtoull(val, &end, 10);
			}
			break;
		case 'c':
			if (!val && i + 1 < argc) {
				val = argv[++i];
			}
			if (val) {
				sdl_cache_size = strtol(val, &end, 10);
			}
			break;
		case 'k':
			if (!val && i + 1 < argc) {
				val = argv[++i];
			}
			if (val) {
				frames_per_second = strtol(val, &end, 10);
			}
			break;
		case 't':
			if (!val && i + 1 < argc) {
				val = argv[++i];
			}
			if (val) {
				server_port = strtol(val, &end, 10);
			}
			break;
		default:
			// Unknown option, ignore or warn?
			break;
		}
	}
	return 0;
}

void save_options(void)
{
	FILE *fp;
	char filename[MAX_PATH];

	if (localdata) {
		sprintf(filename, "%s%s", localdata, "moac.dat");
	} else {
		sprintf(filename, "%s", "bin/data/moac.dat");
	}

	fp = fopen(filename, "wb");
	if (!fp) {
		return;
	}

	fwrite(&user_keys, sizeof(user_keys), 1, fp);
	fwrite(&action_row, sizeof(action_row), 1, fp);
	fwrite(&action_enabled, sizeof(action_enabled), 1, fp);
	fwrite(&gear_lock, sizeof(gear_lock), 1, fp);
	fclose(fp);
}

void load_options(void)
{
	FILE *fp;
	char filename[MAX_PATH];

	if (localdata) {
		sprintf(filename, "%s%s", localdata, "moac.dat");
	} else {
		sprintf(filename, "%s", "bin/data/moac.dat");
	}

	fp = fopen(filename, "rb");
	if (!fp) {
		return;
	}

	fread(&user_keys, sizeof(user_keys), 1, fp);
	fread(&action_row, sizeof(action_row), 1, fp);
	fread(&action_enabled, sizeof(action_enabled), 1, fp);
	fread(&gear_lock, sizeof(gear_lock), 1, fp);
	fclose(fp);

	actions_loaded();
}

void register_crash_handler(void);

void init_logging(void)
{
	char filename[MAX_PATH];

	if (game_options & GO_APPDATA) {
		localdata = SDL_GetPrefPath(ORG_NAME, APP_NAME);
		if (localdata) {
			snprintf(filename, sizeof(filename), "%s%s", localdata, "moac.log");
		} else {
			// Fallback if SDL_GetPrefPath fails
			snprintf(filename, sizeof(filename), "moac.log");
		}
	} else {
		snprintf(filename, sizeof(filename), "moac.log");
	}

	errorfp = fopen(filename, "a");
	if (!errorfp) {
		errorfp = stderr;
	}
}

void determine_resolution(void)
{
	if (!want_height) {
		if (want_width == 800) {
			want_height = 600;
		} else if (want_width == 1600) {
			want_height = 1200;
		} else if (want_width == 2400) {
			want_height = 1800;
		} else if (want_width == 3200) {
			want_height = 2400;
		} else if (want_width) {
			want_height = want_width * 9 / 16;
		}
	}
	if (!want_width) {
		if (want_height == 600) {
			want_width = 800;
		} else if (want_height == 1000) {
			want_width = 1600;
		} else if (want_height == 1200) {
			want_width = 1600;
		} else if (want_height == 1800) {
			want_width = 2400;
		} else if (want_height == 2000) {
			want_width = 3200;
		} else if (want_height == 2400) {
			want_width = 3200;
		} else if (want_height) {
			want_width = want_height * 16 / 9;
		}
	}
}

// main
int main(int argc, char *argv[])
{
	int ret;
	char buf[80];

	if ((ret = parse_args(argc, argv)) != 0) {
		return -1;
	}

	init_logging();

#ifdef ENABLE_CRASH_HANDLER
	register_crash_handler();
#endif

	amod_init();
#ifdef ENABLE_SHAREDMEM
	sharedmem_init();
#endif

	load_options();

	// set some stuff
	if (!*username || !*password || !*server_url) {
		display_usage();
		return 0;
	}

	xlog(errorfp, "Client started with -h%d -w%d -o%llu", want_height, want_width, game_options);

#ifdef _WIN32
	SetProcessDPIAware();
#endif

	target_server = server_url;

	if (server_port) {
		target_port = server_port;
	}

	// init random
	rrandomize();

	determine_resolution();

	sprintf(buf, "Astonia 3 v%d.%d.%d", (VERSION >> 16) & 255, (VERSION >> 8) & 255, (VERSION) & 255);
	if (!sdl_init(want_width, want_height, buf)) {
		dd_exit();
		return -1;
	}

	dd_init();
	init_sound();

	if (game_options & GO_LARGE) {
		namesize = 0;
		dd_set_textfont(1);
	}

	main_init();
	update_user_keys();

	main_loop();

#ifdef ENABLE_SHAREDMEM
	sharedmem_exit();
#endif
	amod_exit();
	main_exit();
	sound_exit();
	dd_exit();
	sdl_exit();

	list_mem();

	if (panic_reached) {
		SDL_ShowSimpleMessageBox(SDL_MESSAGEBOX_ERROR, "recursion panic", panic_reached_str, NULL);
	}
	if (xmemcheck_failed) {
		SDL_ShowSimpleMessageBox(SDL_MESSAGEBOX_ERROR, "memory panic", memcheck_failed_str, NULL);
	}

	if (localdata) {
		SDL_free(localdata);
	}

	xlog(errorfp, "Clean client shutdown. Thank you for playing!");
	if (errorfp != stderr) {
		fclose(errorfp);
	}
	return 0;
}
