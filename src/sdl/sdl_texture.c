/*
 * Part of Astonia Client (c) Daniel Brockhaus. Please read license.txt.
 *
 * SDL - Texture Cache Module
 *
 * Texture cache management, hash functions, allocation, and the main sdl_tx_load function.
 */

#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <SDL2/SDL.h>

#include "dll.h"
#include "astonia.h"
#include "sdl/sdl.h"
#include "sdl/sdl_private.h"

// Texture cache data
struct sdl_texture *sdlt = NULL;
int sdlt_best, sdlt_last;
int *sdlt_cache;

// Image cache
struct sdl_image *sdli = NULL;

// Statistics
int texc_used = 0;
long long mem_png = 0, mem_tex = 0;
long long texc_hit = 0, texc_miss = 0, texc_pre = 0;

// Timing
long long sdl_time_preload = 0;
long long sdl_time_make = 0;
long long sdl_time_make_main = 0;
long long sdl_time_load = 0;
long long sdl_time_alloc = 0;
long long sdl_time_tex = 0;
long long sdl_time_tex_main = 0;
long long sdl_time_text = 0;
long long sdl_time_blit = 0;
long long sdl_time_pre1 = 0;
long long sdl_time_pre2 = 0;
long long sdl_time_pre3 = 0;

int maxpanic = 0;

void sdl_tx_best(int stx)
{
	PARANOIA(if (stx == STX_NONE) paranoia("sdl_tx_best(): sidx=SIDX_NONE");)
	PARANOIA(if (stx >= MAX_TEXCACHE) paranoia("sdl_tx_best(): sidx>max_systemcache (%d>=%d)", stx, MAX_TEXCACHE);)

	if (sdlt[stx].prev == STX_NONE) {
		PARANOIA(if (stx != sdlt_best) paranoia("sdl_tx_best(): stx should be best");)

		return;
	} else if (sdlt[stx].next == STX_NONE) {
		PARANOIA(if (stx != sdlt_last) paranoia("sdl_tx_best(): sidx should be last");)

		sdlt_last = sdlt[stx].prev;
		sdlt[sdlt_last].next = STX_NONE;
		sdlt[sdlt_best].prev = stx;
		sdlt[stx].prev = STX_NONE;
		sdlt[stx].next = sdlt_best;
		sdlt_best = stx;

		return;
	} else {
		sdlt[sdlt[stx].prev].next = sdlt[stx].next;
		sdlt[sdlt[stx].next].prev = sdlt[stx].prev;
		sdlt[stx].prev = STX_NONE;
		sdlt[stx].next = sdlt_best;
		sdlt[sdlt_best].prev = stx;
		sdlt_best = stx;
		return;
	}
}

static inline unsigned int hashfunc(int sprite, int ml, int ll, int rl, int ul, int dl)
{
	unsigned int hash;

	hash = sprite ^ (ml << 2) ^ (ll << 4) ^ (rl << 6) ^ (ul << 8) ^ (dl << 10);

	return hash % MAX_TEXHASH;
}

static inline unsigned int hashfunc_text(const char *text, int color, int flags)
{
	unsigned int hash, t0, t1, t2, t3;

	t0 = text[0];
	if (text[0]) {
		t1 = text[1];
		if (text[1]) {
			t2 = text[2];
			if (text[2]) {
				t3 = text[3];
			} else {
				t3 = 0;
			}
		} else {
			t2 = t3 = 0;
		}
	} else {
		t1 = t2 = t3 = 0;
	}

	hash = (t0 << 0) ^ (t1 << 3) ^ (t2 << 6) ^ (t3 << 9) ^ ((uint32_t)color << 0) ^ ((uint32_t)flags << 5);

	return hash % MAX_TEXHASH;
}

SDL_Texture *sdl_maketext(const char *text, struct renderfont *font, uint32_t color, int flags);

static void not_busy_or_panic(struct sdl_texture *st)
{
	int panic = 0;

	if (sdl_multi) {
		while (42) {
			SDL_LockMutex(premutex);
			if (!(st->flags & (SF_BUSY))) {
				st->flags |= SF_BUSY;
				SDL_UnlockMutex(premutex);
				break;
			}
			SDL_UnlockMutex(premutex);
			SDL_Delay(1);
			if (panic++ > 100) {
				fail("texture cache too small (Delete: BUSY)");
				exit(42);
			}
		}
	} else {
		st->flags |= SF_BUSY;
	}
}

static void unbusy(struct sdl_texture *st)
{
	if (sdl_multi) {
		SDL_LockMutex(premutex);
	}
	st->flags &= ~SF_BUSY;
	if (sdl_multi) {
		SDL_UnlockMutex(premutex);
	}
}

int sdl_tx_load(int sprite, int sink, int freeze, int scale, int cr, int cg, int cb, int light, int sat, int c1, int c2,
    int c3, int shine, int ml, int ll, int rl, int ul, int dl, const char *text, int text_color, int text_flags,
    void *text_font, int checkonly, int preload, int fortick)
{
	int stx, ptx, ntx, panic = 0;
	int hash;

	if (!text) {
		hash = hashfunc(sprite, ml, ll, rl, ul, dl);
	} else {
		hash = hashfunc_text(text, text_color, text_flags);
	}

	if (sprite >= MAXSPRITE || sprite < 0) {
		note("illegal sprite %d wanted in sdl_tx_load", sprite);
		return STX_NONE;
	}

	for (stx = sdlt_cache[hash]; stx != STX_NONE; stx = sdlt[stx].hnext, panic++) {
		if (panic > 999) {
			warn("%04d: stx=%d, hprev=%d, hnext=%d sprite=%d (%d%d%d%d%d%d%d%d%d%d%d%d%d%d%d%d%d,%p) PANIC\n", panic,
			    stx, sdlt[stx].hprev, sdlt[stx].hnext, sprite, sdlt[stx].sink, sdlt[stx].freeze, sdlt[stx].scale,
			    sdlt[stx].cr, sdlt[stx].cg, sdlt[stx].cb, sdlt[stx].light, sdlt[stx].sat, sdlt[stx].c1, sdlt[stx].c2,
			    sdlt[stx].c3, sdlt[stx].shine, sdlt[stx].ml, sdlt[stx].ll, sdlt[stx].rl, sdlt[stx].ul, sdlt[stx].dl,
			    sdlt[stx].text);
			if (panic > 1099) {
#ifdef DEVELOPER
				sdl_dump_spritecache();
#endif
				exit(42);
			}
		}
		if (text) {
			if (!(sdlt[stx].flags & SF_TEXT)) {
				continue;
			}
			if (!(sdlt[stx].tex)) {
				continue; // text does not go through the preloader, so if the texture is empty maketext failed earlier.
			}
			if (!sdlt[stx].text || strcmp(sdlt[stx].text, text) != 0) {
				continue;
			}
			if (sdlt[stx].text_flags != text_flags) {
				continue;
			}
			if (sdlt[stx].text_color != text_color) {
				continue;
			}
			if (sdlt[stx].text_font != text_font) {
				continue;
			}
		} else {
			if (!(sdlt[stx].flags & SF_SPRITE)) {
				continue;
			}
			if (sdlt[stx].sprite != sprite) {
				continue;
			}
			if (sdlt[stx].sink != sink) {
				continue;
			}
			if (sdlt[stx].freeze != freeze) {
				continue;
			}
			if (sdlt[stx].scale != scale) {
				continue;
			}
			if (sdlt[stx].cr != cr) {
				continue;
			}
			if (sdlt[stx].cg != cg) {
				continue;
			}
			if (sdlt[stx].cb != cb) {
				continue;
			}
			if (sdlt[stx].light != light) {
				continue;
			}
			if (sdlt[stx].sat != sat) {
				continue;
			}
			if (sdlt[stx].c1 != c1) {
				continue;
			}
			if (sdlt[stx].c2 != c2) {
				continue;
			}
			if (sdlt[stx].c3 != c3) {
				continue;
			}
			if (sdlt[stx].shine != shine) {
				continue;
			}
			if (sdlt[stx].ml != ml) {
				continue;
			}
			if (sdlt[stx].ll != ll) {
				continue;
			}
			if (sdlt[stx].rl != rl) {
				continue;
			}
			if (sdlt[stx].ul != ul) {
				continue;
			}
			if (sdlt[stx].dl != dl) {
				continue;
			}
		}

		if (checkonly) {
			return 1;
		}
		if (preload == 1) {
			return -1;
		}

		if (panic > maxpanic) {
			maxpanic = panic;
		}

		if (!preload && (sdlt[stx].flags & SF_SPRITE)) {
			// load image and allocate memory if preload didn't do it yet
			if (!(sdlt[stx].flags & SF_DIDALLOC)) {
				// long long start=SDL_GetTicks64();
				// printf("main-making alloc and make for sprite %d (%d)\n",sprite,preload);
				sdl_ic_load(sprite);

				not_busy_or_panic(sdlt + stx);
				sdl_make(sdlt + stx, sdli + sprite, 1);
				sdl_make(sdlt + stx, sdli + sprite, 2);
				unbusy(sdlt + stx);
				// sdl_time_tex_main+=SDL_GetTicks64()-start; TODO
			}

			// Make make in main if not busy
			if (sdl_multi) {
				SDL_LockMutex(premutex);
			}

			if (!(sdlt[stx].flags & (SF_DIDMAKE | SF_BUSY))) {
				sdlt[stx].flags |= SF_BUSY;

				if (sdl_multi) {
					SDL_UnlockMutex(premutex);
				}

				sdl_make(sdlt + stx, sdli + sprite, 2);

				if (sdl_multi) {
					SDL_LockMutex(premutex);
				}

				sdlt[stx].flags &= ~SF_BUSY;
				sdlt[stx].flags |= SF_DIDMAKE;

				if (sdl_multi) {
					SDL_UnlockMutex(premutex);
				}
			} else {
				if (sdl_multi) {
					SDL_UnlockMutex(premutex);
				}
			}

			// wait for the background preloader if we have multiple threads
			panic = 0;
			while (sdl_multi) {
				if (sdlt[stx].flags & SF_DIDMAKE) {
					break;
				}

				// warn("waiting for graphics...");
				SDL_Delay(1);

				if (panic++ > 100) {
					fail("graphics not being made for sprite %d (flags=%s %s %s %s)", sdlt[stx].sprite,
					    (sdlt[stx].flags & SF_DIDALLOC) ? "didalloc" : "",
					    (sdlt[stx].flags & SF_DIDMAKE) ? "didmake" : "", (sdlt[stx].flags & SF_DIDTEX) ? "didtex" : "",
					    (sdlt[stx].flags & SF_BUSY) ? "busy" : "");
					exit(42);
				}
			}

			// if we are single threaded do it yourself
			if (!sdl_multi && !(sdlt[stx].flags & SF_DIDMAKE)) {
				// printf("main-making make for sprite %d\n",sprite);
				long long start = SDL_GetTicks64();
				sdl_make(sdlt + stx, sdli + sprite, 2);
				sdl_time_make_main += SDL_GetTicks64() - start;
			}

			// make texture now if preload didn't finish it
			if (!(sdlt[stx].flags & SF_DIDTEX)) {
				// printf("main-making texture for sprite %d\n",sprite);
				long long start = SDL_GetTicks64();
				sdl_make(sdlt + stx, sdli + sprite, 3);
				sdl_time_tex_main += SDL_GetTicks64() - start;
			}
		}

		sdl_tx_best(stx);

		// remove from old pos
		ntx = sdlt[stx].hnext;
		ptx = sdlt[stx].hprev;

		if (ptx == STX_NONE) {
			sdlt_cache[hash] = ntx;
		} else {
			sdlt[ptx].hnext = sdlt[stx].hnext;
		}

		if (ntx != STX_NONE) {
			sdlt[ntx].hprev = sdlt[stx].hprev;
		}

		// add to top pos
		ntx = sdlt_cache[hash];

		if (ntx != STX_NONE) {
			sdlt[ntx].hprev = stx;
		}

		sdlt[stx].hprev = STX_NONE;
		sdlt[stx].hnext = ntx;

		sdlt_cache[hash] = stx;

		// update statistics
		if (fortick) {
			sdlt[stx].fortick = fortick;
		}
		if (!preload) {
			texc_hit++;
		}

		return stx;
	}
	if (checkonly) {
		return 0;
	}

	stx = sdlt_last;

	// delete
	if (sdlt[stx].flags) {
		int hash2;

		if (sdlt[stx].flags & SF_SPRITE) {
			not_busy_or_panic(sdlt + stx);
		}

		if (sdlt[stx].flags & SF_SPRITE) {
			hash2 = hashfunc(sdlt[stx].sprite, sdlt[stx].ml, sdlt[stx].ll, sdlt[stx].rl, sdlt[stx].ul, sdlt[stx].dl);
		} else if (sdlt[stx].flags & SF_TEXT) {
			hash2 = hashfunc_text(sdlt[stx].text, sdlt[stx].text_color, sdlt[stx].text_flags);
		} else {
			hash2 = 0;
			warn("weird entry in texture cache!");
		}

		ntx = sdlt[stx].hnext;
		ptx = sdlt[stx].hprev;

		if (ptx == STX_NONE) {
			if (sdlt_cache[hash2] != stx) {
				fail("sdli[sprite].stx!=stx\n");
				exit(42);
			}
			sdlt_cache[hash2] = ntx;
		} else {
			sdlt[ptx].hnext = sdlt[stx].hnext;
		}

		if (ntx != STX_NONE) {
			sdlt[ntx].hprev = sdlt[stx].hprev;
		}

		if (sdlt[stx].flags & SF_DIDTEX) {
			mem_tex -= sdlt[stx].xres * sdlt[stx].yres * sizeof(uint32_t);
			if (sdlt[stx].tex) {
				SDL_DestroyTexture(sdlt[stx].tex);
			}
		} else if (sdlt[stx].flags & SF_DIDALLOC) {
			if (sdlt[stx].pixel) {
#ifdef SDL_FAST_MALLOC
				free(sdlt[stx].pixel);
#else
				xfree(sdlt[stx].pixel);
#endif
				sdlt[stx].pixel = NULL;
			}
		}
#ifdef SDL_FAST_MALLOC
		if (sdlt[stx].flags & SF_TEXT) {
			free(sdlt[stx].text);
			sdlt[stx].text = NULL;
		}
#else
		if (sdlt[stx].flags & SF_TEXT) {
			xfree(sdlt[stx].text);
			sdlt[stx].text = NULL;
		}
#endif

		sdlt[stx].flags = 0;
	} else {
		texc_used++;
	}

	// build
	if (text) {
		int w, h;
		sdlt[stx].tex = sdl_maketext(text, (struct renderfont *)text_font, text_color, text_flags);
		sdlt[stx].flags = SF_USED | SF_TEXT | SF_DIDALLOC | SF_DIDMAKE | SF_DIDTEX;
		sdlt[stx].text_color = text_color;
		sdlt[stx].text_flags = text_flags;
		sdlt[stx].text_font = text_font;
#ifdef SDL_FAST_MALLOC
		sdlt[stx].text = strdup(text);
#else
		sdlt[stx].text = xstrdup(text, MEM_TEMP7);
#endif
		if (sdlt[stx].tex) {
			SDL_QueryTexture(sdlt[stx].tex, NULL, NULL, &w, &h);
			sdlt[stx].xres = w;
			sdlt[stx].yres = h;
		} else {
			sdlt[stx].xres = sdlt[stx].yres = 0;
		}
	} else {
		if (preload != 1) {
			sdl_ic_load(sprite);
		}

		// init
		sdlt[stx].flags = SF_USED | SF_SPRITE | SF_BUSY;
		sdlt[stx].sprite = sprite;
		sdlt[stx].sink = sink;
		sdlt[stx].freeze = freeze;
		sdlt[stx].scale = scale;
		sdlt[stx].cr = cr;
		sdlt[stx].cg = cg;
		sdlt[stx].cb = cb;
		sdlt[stx].light = light;
		sdlt[stx].sat = sat;
		sdlt[stx].c1 = c1;
		sdlt[stx].c2 = c2;
		sdlt[stx].c3 = c3;
		sdlt[stx].shine = shine;
		sdlt[stx].ml = ml;
		sdlt[stx].ll = ll;
		sdlt[stx].rl = rl;
		sdlt[stx].ul = ul;
		sdlt[stx].dl = dl;

		if (preload != 1) {
			sdl_make(sdlt + stx, sdli + sprite, preload);
		}
		unbusy(sdlt + stx);
	}

	mem_tex += sdlt[stx].xres * sdlt[stx].yres * sizeof(uint32_t);

	ntx = sdlt_cache[hash];

	if (ntx != STX_NONE) {
		sdlt[ntx].hprev = stx;
	}

	sdlt[stx].hprev = STX_NONE;
	sdlt[stx].hnext = ntx;

	sdlt_cache[hash] = stx;

	sdl_tx_best(stx);

	// update statistics
	if (fortick) {
		sdlt[stx].fortick = fortick;
	}

	if (preload) {
		texc_pre++;
	} else if (sprite) { // Do not count missed text sprites. Those are expected.
		texc_miss++;
	}

	return stx;
}

#ifdef DEVELOPER
int *dumpidx;

int dump_cmp(const void *ca, const void *cb)
{
	int a, b, tmp;

	a = *(int *)ca;
	b = *(int *)cb;

	if (!sdlt[a].flags) {
		return 1;
	}
	if (!sdlt[b].flags) {
		return -1;
	}

	if (sdlt[a].flags & SF_TEXT) {
		return 1;
	}
	if (sdlt[b].flags & SF_TEXT) {
		return -1;
	}

	if (((tmp = sdlt[a].sprite - sdlt[b].sprite) != 0)) {
		return tmp;
	}

	if (((tmp = sdlt[a].ml - sdlt[b].ml) != 0)) {
		return tmp;
	}
	if (((tmp = sdlt[a].ll - sdlt[b].ll) != 0)) {
		return tmp;
	}
	if (((tmp = sdlt[a].rl - sdlt[b].rl) != 0)) {
		return tmp;
	}
	if (((tmp = sdlt[a].ul - sdlt[b].ul) != 0)) {
		return tmp;
	}

	return sdlt[a].dl - sdlt[b].dl;
}

void sdl_dump_spritecache(void)
{
	int i, n, cnt = 0, uni = 0, text = 0;
	long long size = 0;
	char filename[MAX_PATH];
	FILE *fp;

	dumpidx = xmalloc(sizeof(int) * MAX_TEXCACHE, MEM_TEMP);
	for (i = 0; i < MAX_TEXCACHE; i++) {
		dumpidx[i] = i;
	}

	qsort(dumpidx, MAX_TEXCACHE, sizeof(int), dump_cmp);

	if (localdata) {
		sprintf(filename, "%s%s", localdata, "sdlt.txt");
	} else {
		sprintf(filename, "%s", "sdlt.txt");
	}
	fp = fopen(filename, "w");
	if (fp == NULL) {
		xfree(dumpidx);
		return;
	}

	for (i = 0; i < MAX_TEXCACHE; i++) {
		n = dumpidx[i];
		if (!sdlt[n].flags) {
			break;
		}

		if (sdlt[n].flags & SF_TEXT) {
			text++;
		} else {
			if (i == 0 || sdlt[dumpidx[i]].sprite != sdlt[dumpidx[i - 1]].sprite) {
				uni++;
			}
			cnt++;
		}

		if (sdlt[n].flags & SF_SPRITE) {
			fprintf(fp, "Sprite: %6d (%7d) %s%s%s%s%s\n", sdlt[n].sprite, sdlt[n].fortick,
			    (sdlt[n].flags & SF_USED) ? "SF_USED " : "", (sdlt[n].flags & SF_DIDALLOC) ? "SF_DIDALLOC " : "",
			    (sdlt[n].flags & SF_DIDMAKE) ? "SF_DIDMAKE " : "", (sdlt[n].flags & SF_DIDTEX) ? "SF_DIDTEX " : "",
			    (sdlt[n].flags & SF_BUSY) ? "SF_BUSY " : "");
		}

		/*fprintf(fp,"Sprite: %6d, Lights: %2d,%2d,%2d,%2d,%2d, Light: %3d, Colors: %3d,%3d,%3d, Colors: %4X,%4X,%4X,
		   Sink: %2d, Freeze: %2d, Scale: %3d, Sat: %3d, Shine: %3d, %dx%d\n", sdlt[n].sprite, sdlt[n].ml, sdlt[n].ll,
		       sdlt[n].rl,
		       sdlt[n].ul,
		       sdlt[n].dl,
		       sdlt[n].light,
		       sdlt[n].cr,
		       sdlt[n].cg,
		       sdlt[n].cb,
		       sdlt[n].c1,
		       sdlt[n].c2,
		       sdlt[n].c3,
		       sdlt[n].sink,
		       sdlt[n].freeze,
		       sdlt[n].scale,
		       sdlt[n].sat,
		       sdlt[n].shine,
		       sdlt[n].xres,
		       sdlt[n].yres);*/
		if (sdlt[n].flags & SF_TEXT) {
			fprintf(fp, "Color: %08X, Flags: %04X, Font: %p, Text: %s (%dx%d)\n", sdlt[n].text_color,
			    sdlt[n].text_flags, sdlt[n].text_font, sdlt[n].text, sdlt[n].xres, sdlt[n].yres);
		}

		size += sdlt[n].xres * sdlt[n].yres * sizeof(uint32_t);
	}
	fprintf(fp, "\n%d unique sprites, %d sprites + %d texts of %d used. %.2fM texture memory.\n", uni, cnt, text,
	    MAX_TEXCACHE, size / (1024.0 * 1024.0));
	fclose(fp);
	xfree(dumpidx);
}
#endif

int sdlt_xoff(int stx)
{
	return sdlt[stx].xoff;
}

int sdlt_yoff(int stx)
{
	return sdlt[stx].yoff;
}

int sdlt_xres(int stx)
{
	return sdlt[stx].xres;
}

int sdlt_yres(int stx)
{
	return sdlt[stx].yres;
}

int sdl_tex_xres(int stx)
{
	return sdlt[stx].xres;
}

int sdl_tex_yres(int stx)
{
	return sdlt[stx].yres;
}

void sdl_tex_alpha(int stx, int alpha)
{
	if (sdlt[stx].tex) {
		SDL_SetTextureAlphaMod(sdlt[stx].tex, alpha);
	}
}
