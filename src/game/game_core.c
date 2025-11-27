/*
 * Part of Astonia Client (c) Daniel Brockhaus. Please read license.txt.
 *
 * Display Game Map - Core Functions
 *
 * Display list management, initialization and cleanup functions.
 */

#include <stdint.h>
#include <stddef.h>
#include <SDL2/SDL.h>

#include "astonia.h"
#include "game/game.h"
#include "game/game_private.h"
#include "gui/gui.h"
#include "client/client.h"

// Sprite counters - shared with game_display.c
int fsprite_cnt = 0, f2sprite_cnt = 0, gsprite_cnt = 0, g2sprite_cnt = 0, isprite_cnt = 0, csprite_cnt = 0;
// Timing statistics - shared with game_display.c
static int qs_time = 0;
int dg_time = 0, ds_time = 0;
int stom_off_x = 0, stom_off_y = 0;

static DL *dllist = NULL;
static DL **dlsort = NULL;
static int dlused = 0, dlmax = 0;
static int stat_dlsortcalls, stat_dlused;
int namesize = DD_SMALL;

DL *dl_next(void)
{
	int d;
	ptrdiff_t diff;
	DL *rem;

	if (dlused == dlmax) {
		rem = dllist;
		dllist = xrealloc(dllist, (dlmax + DL_STEP) * sizeof(DL), MEM_DL);
		dlsort = xrealloc(dlsort, (dlmax + DL_STEP) * sizeof(DL *), MEM_DL);
		diff = (unsigned char *)dllist - (unsigned char *)rem;
		for (d = 0; d < dlmax; d++) {
			dlsort[d] = (DL *)(((unsigned char *)(dlsort[d])) + diff);
		}
		for (d = dlmax; d < dlmax + DL_STEP; d++) {
			dlsort[d] = &dllist[d];
		}
		dlmax += DL_STEP;
	} else if (dlused > dlmax) {
		fail("dlused normally shouldn't exceed dlmax - the error is somewhere else ;-)");
		return dlsort[dlused - 1];
	}

	dlused++;
	bzero(dlsort[dlused - 1], sizeof(DL));

	if (dlused % 16 == 0) {
		dlsort[dlused - 1]->call = DLC_DUMMY;
		return dl_next();
	}

	dlsort[dlused - 1]->ddfx.sink = 0;
	dlsort[dlused - 1]->ddfx.scale = 100;
	dlsort[dlused - 1]->ddfx.cr = dlsort[dlused - 1]->ddfx.cg = dlsort[dlused - 1]->ddfx.cb =
	    dlsort[dlused - 1]->ddfx.clight = dlsort[dlused - 1]->ddfx.sat = 0;
	dlsort[dlused - 1]->ddfx.c1 = 0;
	dlsort[dlused - 1]->ddfx.c2 = 0;
	dlsort[dlused - 1]->ddfx.c3 = 0;
	dlsort[dlused - 1]->ddfx.shine = 0;
	return dlsort[dlused - 1];
}

DL *dl_next_set(int layer, int sprite, int scrx, int scry, int light)
{
	DL *dl;
	DDFX *ddfx;

	if (sprite > MAXSPRITE || sprite < 0) {
		note("trying to add illegal sprite %d in dl_next_set", sprite);
		return NULL;
	}

	ddfx = &(dl = dl_next())->ddfx;

	dl->x = scrx;
	dl->y = scry;
	dl->layer = layer;

	ddfx->sprite = sprite;
	ddfx->ml = ddfx->ll = ddfx->rl = ddfx->ul = ddfx->dl = light;
	ddfx->sink = 0;
	ddfx->scale = 100;
	ddfx->cr = ddfx->cg = ddfx->cb = ddfx->clight = ddfx->sat = 0;
	ddfx->c1 = 0;
	ddfx->c2 = 0;
	ddfx->c3 = 0;
	ddfx->shine = 0;

	return dl;
}

int dl_qcmp(const void *ca, const void *cb)
{
	DL *a, *b;
	int diff;

	stat_dlsortcalls++;

	a = *(DL **)ca;
	b = *(DL **)cb;

	if (a->call == DLC_DUMMY && b->call == DLC_DUMMY) {
		return 0;
	}
	if (a->call == DLC_DUMMY) {
		return -1;
	}
	if (b->call == DLC_DUMMY) {
		return 1;
	}

	diff = a->layer - b->layer;
	if (diff) {
		return diff;
	}

	diff = a->y - b->y;
	if (diff) {
		return diff;
	}

	diff = a->x - b->x;
	if (diff) {
		return diff;
	}

	return a->ddfx.sprite - b->ddfx.sprite;
}

void draw_pixel(int x, int y, int color)
{
	dd_pixel(x, y, color);
}

void dl_play(void)
{
	int d, start;
	void helper_cmp_dl(int attick, DL **dl, int dlused);

	// helper_cmp_dl(tick,dlsort,dlused);

	start = SDL_GetTicks();
	stat_dlsortcalls = 0;
	stat_dlused = dlused;
	qsort(dlsort, dlused, sizeof(DL *), dl_qcmp);
	qs_time += SDL_GetTicks() - start;

	for (d = 0; d < dlused && !quit; d++) {
		if (dlsort[d]->call == 0) {
			dd_copysprite_fx(&dlsort[d]->ddfx, dlsort[d]->x, dlsort[d]->y - dlsort[d]->h);
		} else {
			switch (dlsort[d]->call) {
			case DLC_STRIKE:
				dd_display_strike(dlsort[d]->call_x1, dlsort[d]->call_y1, dlsort[d]->call_x2, dlsort[d]->call_y2);
				break;
			case DLC_NUMBER:
				dd_drawtext_fmt(dlsort[d]->call_x1, dlsort[d]->call_y1, 0xffff, DD_CENTER | DD_SMALL | DD_FRAME, "%d",
				    dlsort[d]->call_x2);
				break;
			case DLC_DUMMY:
				break;
			case DLC_PIXEL:
				draw_pixel(dlsort[d]->call_x1, dlsort[d]->call_y1, dlsort[d]->call_x2);
				break;
			case DLC_BLESS:
				dd_draw_bless(
				    dlsort[d]->call_x1, dlsort[d]->call_y1, dlsort[d]->call_x2, dlsort[d]->call_y2, dlsort[d]->call_x3);
				break;
			case DLC_POTION:
				dd_draw_potion(
				    dlsort[d]->call_x1, dlsort[d]->call_y1, dlsort[d]->call_x2, dlsort[d]->call_y2, dlsort[d]->call_x3);
				break;
			case DLC_RAIN:
				dd_draw_rain(
				    dlsort[d]->call_x1, dlsort[d]->call_y1, dlsort[d]->call_x2, dlsort[d]->call_y2, dlsort[d]->call_x3);
				break;
			case DLC_PULSE:
				dd_draw_curve(
				    dlsort[d]->call_x1, dlsort[d]->call_y1, dlsort[d]->call_x2, dlsort[d]->call_y2, dlsort[d]->call_x3);
				break;
			case DLC_PULSEBACK:
				dd_display_pulseback(dlsort[d]->call_x1, dlsort[d]->call_y1, dlsort[d]->call_x2, dlsort[d]->call_y2);
				break;
			}
		}
	}

	dlused = 0;
}

void sdl_pre_add(int attick, int sprite, signed char sink, unsigned char freeze, unsigned char scale, char cr, char cg,
    char cb, char light, char sat, int c1, int c2, int c3, int shine, char ml, char ll, char rl, char ul, char dl);

void dl_prefetch(int attick)
{
	void helper_add_dl(int attick, DL **dl, int dlused);
	int d;

	// helper_add_dl(attick,dlsort,dlused);

	for (d = 0; d < dlused && !quit; d++) {
		if (dlsort[d]->call == 0) {
			sdl_pre_add(attick, dlsort[d]->ddfx.sprite, dlsort[d]->ddfx.sink, dlsort[d]->ddfx.freeze,
			    dlsort[d]->ddfx.scale, dlsort[d]->ddfx.cr, dlsort[d]->ddfx.cg, dlsort[d]->ddfx.cb,
			    dlsort[d]->ddfx.clight, dlsort[d]->ddfx.sat, dlsort[d]->ddfx.c1, dlsort[d]->ddfx.c2, dlsort[d]->ddfx.c3,
			    dlsort[d]->ddfx.shine, dlsort[d]->ddfx.ml, dlsort[d]->ddfx.ll, dlsort[d]->ddfx.rl, dlsort[d]->ddfx.ul,
			    dlsort[d]->ddfx.dl);
		}
	}

	dlused = 0;
}

// analyse
QUICK *quick;
int maxquick;

#define RANDOM(a) (rand() % (a))
#define MAXBUB    100

struct bubble {
	int type;
	int origx, origy;
	int cx, cy;
	int state;
};

struct bubble bubble[MAXBUB];

void add_bubble(int x, int y, int h)
{
	int n;
	int offx, offy;

	mtos(originx, originy, &offx, &offy);
	offx -= mapaddx * 2;
	offy -= mapaddx * 2;

	for (n = 0; n < MAXBUB; n++) {
		if (!bubble[n].state) {
			bubble[n].state = 1;
			bubble[n].origx = x + offx;
			bubble[n].origy = y + offy;
			bubble[n].cx = x + offx;
			bubble[n].cy = y - h + offy;
			bubble[n].type = RANDOM(3);
			// addline("added bubble at %d,%d",offx,offy);
			return;
		}
	}
}

void show_bubbles(void)
{
	int n, spr, offx, offy;
	DL *dl;
	// static int oo=0;

	mtos(originx, originy, &offx, &offy);
	offx -= mapaddx * 2;
	offy -= mapaddy * 2;
	// if (oo!=mapaddx) addline("shown bubble at %d,%d %d,%d",offx,offy,oo=mapaddx,mapaddy);

	for (n = 0; n < MAXBUB; n++) {
		if (!bubble[n].state) {
			continue;
		}

		spr = (bubble[n].state - 1) % 6;
		if (spr > 3) {
			spr = 3 - (spr - 3);
		}
		spr += bubble[n].type * 3;

		dl = dl_next_set(GME_LAY, 1140 + spr, bubble[n].cx - offx, bubble[n].origy - offy, DDFX_NLIGHT);
		dl->h = bubble[n].origy - bubble[n].cy;
		bubble[n].state++;
		bubble[n].cx += 2 - RANDOM(5);
		bubble[n].cy -= 1 + RANDOM(3);
		if (bubble[n].cy < 1) {
			bubble[n].state = 0;
		}
		if (bubble[n].state > 50) {
			bubble[n].state = 0;
		}
	}
}

// make quick
int quick_qcmp(const void *va, const void *vb)
{
	const QUICK *a;
	const QUICK *b;

	a = (QUICK *)va;
	b = (QUICK *)vb;

	if (a->mapx + a->mapy < b->mapx + b->mapy) {
		return -1;
	} else if (a->mapx + a->mapy > b->mapx + b->mapy) {
		return 1;
	}

	return a->mapx - b->mapx;
}

void make_quick(int game, int mcx, int mcy)
{
	int cnt;
	int x, y, xs, xe, i, ii;
	int dist = DIST;

	if (game) {
		set_mapoff(mcx, mcy, MAPDX, MAPDY);
		set_mapadd(0, 0);
	}

	// calc maxquick
	for (i = y = 0; y <= dist * 2; y++) {
		if (y < dist) {
			xs = dist - y;
			xe = dist + y;
		} else {
			xs = y - dist;
			xe = dist * 3 - y;
		}
		for (x = xs; x <= xe; x++) {
			i++;
		}
	}
	maxquick = i;

	// set quick (and mn[4]) in server order
	quick = xrealloc(quick, (maxquick + 1) * sizeof(QUICK), MEM_GAME);
	for (i = y = 0; y <= dist * 2; y++) {
		if (y < dist) {
			xs = dist - y;
			xe = dist + y;
		} else {
			xs = y - dist;
			xe = dist * 3 - y;
		}
		for (x = xs; x <= xe; x++) {
			quick[i].mn[4] = x + y * (dist * 2 + 1);

			quick[i].mapx = x;
			quick[i].mapy = y;
			mtos(x, y, &quick[i].cx, &quick[i].cy);
			i++;
		}
	}

	// sort quick in client order
	qsort(quick, maxquick, sizeof(QUICK), quick_qcmp);

	// set quick neighbours
	cnt = 0;
	for (i = 0; i < maxquick; i++) {
		for (y = -1; y <= 1; y++) {
			for (x = -1; x <= 1; x++) {
				if (x == 1 || (x == 0 && y == 1)) {
					for (ii = i + 1; ii < maxquick; ii++) {
						if (quick[i].mapx + x == quick[ii].mapx && quick[i].mapy + y == quick[ii].mapy) {
							break;
						} else {
							cnt++;
						}
					}
				} else if (x == -1 || (x == 0 && y == -1)) {
					for (ii = i - 1; ii >= 0; ii--) {
						if (quick[i].mapx + x == quick[ii].mapx && quick[i].mapy + y == quick[ii].mapy) {
							break;
						} else {
							cnt++;
						}
					}
					if (ii == -1) {
						ii = maxquick;
					}
				} else {
					ii = i;
				}

				if (ii == maxquick) {
					quick[i].mn[(x + 1) + (y + 1) * 3] = 0;
					quick[i].qi[(x + 1) + (y + 1) * 3] = maxquick;
				} else {
					quick[i].mn[(x + 1) + (y + 1) * 3] = quick[ii].mn[4];
					quick[i].qi[(x + 1) + (y + 1) * 3] = ii;
				}
			}
		}
	}

	// set values for quick[maxquick]
	for (y = -1; y <= 1; y++) {
		for (x = -1; x <= 1; x++) {
			quick[maxquick].mn[(x + 1) + (y + 1) * 3] = 0;
			quick[maxquick].qi[(x + 1) + (y + 1) * 3] = maxquick;
		}
	}
}

// init, exit

void init_game(int mcx, int mcy)
{
	make_quick(1, mcx, mcy);
}

void exit_game(void)
{
	xfree(quick);
	quick = NULL;
	maxquick = 0;
	xfree(dllist);
	dllist = NULL;
	xfree(dlsort);
	dlsort = NULL;
	dlused = 0;
	dlmax = 0;
}
