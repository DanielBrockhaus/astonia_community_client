/*
 * Part of Astonia Client (c) Daniel Brockhaus. Please read license.txt.
 */

#ifndef __PROTOCOL_H__
#define __PROTOCOL_H__

#include <stdint.h>
#include <string.h>
#include <stdio.h>

static inline uint32_t load_ulong(const void *p)
{
	uint32_t v;
	memcpy(&v, p, sizeof v);
	return v;
}

static inline uint32_t load_u32(const void *p)
{
	uint32_t v;
	memcpy(&v, p, sizeof v);
	return v;
}

static inline uint16_t load_u16(const void *p)
{
	uint16_t v;
	memcpy(&v, p, sizeof v);
	return v;
}

static inline int16_t load_i16(const void *p)
{
	int16_t v;
	memcpy(&v, p, sizeof v);
	return v;
}

static inline void store_u16(void *p, uint16_t v)
{
	memcpy(p, &v, sizeof v);
}

static inline void store_u32(void *p, uint32_t v)
{
	memcpy(p, &v, sizeof v);
}

static inline unsigned short net_read16(const void *p)
{
	const unsigned char *b = (const unsigned char *)p;
	return (unsigned short)((b[0] << 8) | b[1]);
}

static inline void ipv4_be_to_string(uint32_t be, char out[16])
{
	unsigned char o0 = (unsigned char)((be >> 24) & 0xFF);
	unsigned char o1 = (unsigned char)((be >> 16) & 0xFF);
	unsigned char o2 = (unsigned char)((be >> 8) & 0xFF);
	unsigned char o3 = (unsigned char)((be) & 0xFF);
	/* out must be at least 16 bytes (xxx.xxx.xxx.xxx\0) */
	snprintf(out, 16, "%u.%u.%u.%u", (unsigned)o0, (unsigned)o1, (unsigned)o2, (unsigned)o3);
}

void process(unsigned char *buf, int size);
int prefetch(unsigned char *buf, int size);

void sv_protocol(unsigned char *buf);

void cmd_move(int x, int y);
void cmd_ping(void);
void cmd_swap(int with);
void cmd_fastsell(int with);
void cmd_use_inv(int with);
void cmd_take(int x, int y);
void cmd_look_map(int x, int y);
void cmd_look_item(int x, int y);
void cmd_look_inv(int pos);
void cmd_look_char(int cn);
void cmd_use(int x, int y);
void cmd_drop(int x, int y);
void cmd_speed(int mode);
void cmd_teleport(int nr);
void cmd_stop(void);
void cmd_kill(int cn);
void cmd_give(int cn);
void cmd_some_spell(int spell, int x, int y, int chr);
void cmd_raise(int vn);
void cmd_take_gold(int vn);
void cmd_drop_gold(void);
void cmd_junk_item(void);
void cmd_text(char *text);
void cmd_log(char *text);
void cmd_con(int pos);
void cmd_con_fast(int pos);
void cmd_look_con(int pos);
void cmd_getquestlog(void);
void cmd_reopen_quest(int nr);

#endif
