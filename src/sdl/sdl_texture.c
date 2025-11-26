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
#ifdef DEVELOPER
extern int sockstate; // Declare early for use in wait logging
#endif

// Texture cache data
struct sdl_texture *sdlt = NULL;
int sdlt_best, sdlt_last;
int *sdlt_cache;

// Image cache
struct sdl_image *sdli = NULL;

// Statistics
int texc_used = 0;
long long mem_png = 0;
long long mem_tex = 0;
long long texc_hit = 0, texc_miss = 0, texc_pre = 0;

#ifdef DEVELOPER
uint64_t sdl_render_wait = 0;
uint64_t sdl_render_wait_count = 0;
#endif

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

// Forward declarations
extern int next_job_id(void); // in sdl_core.c
extern SDL_mutex *premutex;
extern int sdl_pre_worker(struct zip_handles *zips); // in sdl_core.c

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
#ifdef DEVELOPER
		// Detect and break self-loops to recover gracefully
		if (sdlt[stx].hnext == stx) {
			warn("Hash self-loop detected at stx=%d for sprite=%d - breaking chain", stx, sprite);
			sdlt[stx].hnext = STX_NONE; // break the loop to recover gracefully
			if (panic > maxpanic) {
				maxpanic = panic;
			}
			break;
		}
#endif
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
			if (!(flags_load(&sdlt[stx]) & SF_TEXT)) {
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
			if (!(flags_load(&sdlt[stx]) & SF_SPRITE)) {
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

		if (!preload && (flags_load(&sdlt[stx]) & SF_SPRITE)) {
			// Wait for background workers to complete processing
			panic = 0;
#ifdef DEVELOPER
			uint64_t wait_start = 0;
#endif
			while (!(flags_load(&sdlt[stx]) & SF_DIDMAKE)) {
#ifdef DEVELOPER
				if (wait_start == 0) {
					wait_start = SDL_GetTicks64();
					extern uint64_t sdl_render_wait_count;
					sdl_render_wait_count++;
				}
#endif

				// In single-threaded mode, process queue to make progress
				if (!sdl_multi) {
					sdl_pre_worker(NULL);
				}

				SDL_Delay(1);

				if (panic++ > 1000) {
					uint16_t flags = flags_load(&sdlt[stx]);
					// Worker is stuck or taking too long - give up this frame rather than corrupting memory
					warn("Render thread timeout waiting for sprite %d (stx=%d, flags=%s %s %s %s) - giving up this "
					     "frame",
					    sdlt[stx].sprite, stx, (flags & SF_CLAIMJOB) ? "claimed" : "",
					    (flags & SF_DIDALLOC) ? "didalloc" : "", (flags & SF_DIDMAKE) ? "didmake" : "",
					    (flags & SF_DIDTEX) ? "didtex" : "");
					// Return STX_NONE to skip this texture this frame - better than use-after-free
					return STX_NONE;
				}
			}
#ifdef DEVELOPER
			if (wait_start > 0) {
				uint64_t wait_time = SDL_GetTicks64() - wait_start;
				extern uint64_t sdl_render_wait;
				sdl_render_wait += wait_time;
#ifdef DEVELOPER_NOISY
				// Suppress warnings during boot - only show "real" stalls (>= 10ms)
				extern int sockstate;
				if (sockstate >= 4 && wait_time >= 10) {
					warn("Render thread waited %lu ms for sprite %d", (unsigned long)wait_time, sdlt[stx].sprite);
				}
#endif
			}
#endif

			// make texture now if preload didn't finish it
			if (!(flags_load(&sdlt[stx]) & SF_DIDTEX)) {
				// printf("main-making texture for sprite %d\n",sprite);
#ifdef DEVELOPER
				long long start = SDL_GetTicks64();
				sdl_make(sdlt + stx, sdli + sprite, 3);
				sdl_time_tex_main += SDL_GetTicks64() - start;
#else
				sdl_make(sdlt + stx, sdli + sprite, 3);
#endif
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

	// Try to evict an entry, potentially trying multiple LRU candidates if workers are stuck
	static int sdl_eviction_failures = 0;
	for (int eviction_attempts = 0; eviction_attempts < 10; eviction_attempts++) {
		// delete
		if (!flags_load(&sdlt[stx])) {
			// Empty slot, just use it
			break;
		}

		int hash2;
		int can_evict = 1;

		// Wait for any in-progress work to complete before deleting
		if (sdl_multi && (flags_load(&sdlt[stx]) & SF_SPRITE)) {
			int panic = 0;
			for (;;) {
				uint16_t f = flags_load(&sdlt[stx]);

				// No job queued/claimed -> nothing to wait for
				if (!(f & (SF_INQUEUE | SF_CLAIMJOB))) {
					break;
				}

				// Job started and CPU-side work finished -> safe to evict
				if ((f & SF_CLAIMJOB) && (f & SF_DIDMAKE)) {
					break;
				}

				SDL_Delay(1);

				// Timeout handling: After 100ms of waiting, we need to decide whether to evict or skip this entry.
				// The key distinction:
				//   - SF_CLAIMJOB set: A worker has claimed and is actively processing this job. We must NOT evict.
				//   - SF_INQUEUE set (but not SF_CLAIMJOB): Job is queued but unclaimed after 100ms. This is stale
				//     and can be neutralized/evicted. The worker will see STX_NONE when it eventually processes it.
				//   - Neither set: No job activity, safe to evict.
				if (panic++ > 100) {
					uint16_t *flags_ptr = (uint16_t *)&sdlt[stx].flags;
					uint16_t f2 = __atomic_load_n(flags_ptr, __ATOMIC_ACQUIRE);
					warn("Timeout waiting to evict stx=%d sprite=%d (flags=0x%04x)", stx, sdlt[stx].sprite, f2);

					// If a job is actually in progress (claimed by a worker), do NOT evict this entry
					if (f2 & SF_CLAIMJOB) {
						// Worker still owns this entry, try previous LRU candidate
						can_evict = 0;
						int candidate = sdlt[stx].prev;
						if (candidate == STX_NONE) {
							// No more candidates, give up
							return STX_NONE;
						}
						// Clear SF_INQUEUE and neutralize any stale queue entries before trying next candidate
						__atomic_fetch_and(flags_ptr, (uint16_t)~SF_INQUEUE, __ATOMIC_RELEASE);
						neutralize_stale_jobs(stx);
						stx = candidate;
						break;
					}

					// No worker is claiming this entry. If SF_INQUEUE was set, the job is stale (queued but
					// unclaimed for 100ms). Clear the flag and neutralize the queue entry, then proceed with eviction.
					__atomic_fetch_and(flags_ptr, (uint16_t)~SF_INQUEUE, __ATOMIC_RELEASE);
					neutralize_stale_jobs(stx);
					break;
				}
			}
		}

		// If we can't evict this entry, try the next candidate
		if (!can_evict) {
			continue;
		}

		uint16_t flags = flags_load(&sdlt[stx]);
		if (flags & SF_SPRITE) {
			hash2 = hashfunc(sdlt[stx].sprite, sdlt[stx].ml, sdlt[stx].ll, sdlt[stx].rl, sdlt[stx].ul, sdlt[stx].dl);
		} else if (flags & SF_TEXT) {
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

		flags = flags_load(&sdlt[stx]);
		if (flags & SF_DIDTEX) {
			__atomic_sub_fetch(&mem_tex, sdlt[stx].xres * sdlt[stx].yres * sizeof(uint32_t), __ATOMIC_RELAXED);
			if (sdlt[stx].tex) {
				SDL_DestroyTexture(sdlt[stx].tex);
			}
		} else if (flags & SF_DIDALLOC) {
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
		if (flags & SF_TEXT) {
			free(sdlt[stx].text);
			sdlt[stx].text = NULL;
		}
#else
		if (flags & SF_TEXT) {
			xfree(sdlt[stx].text);
			sdlt[stx].text = NULL;
		}
#endif

		uint16_t *flags_ptr = (uint16_t *)&sdlt[stx].flags;
		__atomic_store_n(flags_ptr, 0, __ATOMIC_RELEASE);
		break; // Successfully evicted, exit the retry loop
	}

	// *** SAFETY CHECK ***
	// If after all that the entry is still non-empty, we failed to get a usable slot.
	// Do NOT reuse it; that would corrupt the hash chains.
	if (flags_load(&sdlt[stx])) {
		sdl_eviction_failures++;
#ifdef DEVELOPER
		if (sdl_eviction_failures == 1 || (sdl_eviction_failures % 100) == 0) {
			warn("SDL: texture cache eviction failed %d times; workers may be wedged", sdl_eviction_failures);
		}
#endif
		// Could not free or find an empty entry in the limited attempts.
		// Safer to bail out than corrupt the cache.
		return STX_NONE;
	}

	// From here on, stx is guaranteed empty
	texc_used++;

	// build
	if (text) {
		int w, h;
		sdlt[stx].tex = sdl_maketext(text, (struct renderfont *)text_font, text_color, text_flags);
		uint16_t *flags_ptr = (uint16_t *)&sdlt[stx].flags;
		__atomic_store_n(flags_ptr, SF_USED | SF_TEXT | SF_DIDALLOC | SF_DIDMAKE | SF_DIDTEX, __ATOMIC_RELEASE);
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
			sdl_ic_load(sprite, NULL);
		}

		// Initialize all non-atomic fields first
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

		// Set flags with RELEASE to establish happens-before: workers reading flags with ACQUIRE
		// will see all the above fields as initialized
		uint16_t *flags_ptr = (uint16_t *)&sdlt[stx].flags;
		__atomic_store_n(flags_ptr, SF_USED | SF_SPRITE, __ATOMIC_RELEASE);

		if (preload != 1) {
			sdl_make(sdlt + stx, sdli + sprite, preload);
		}
	}

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

	if (!flags_load(&sdlt[a])) {
		return 1;
	}
	if (!flags_load(&sdlt[b])) {
		return -1;
	}

	if (flags_load(&sdlt[a]) & SF_TEXT) {
		return 1;
	}
	if (flags_load(&sdlt[b]) & SF_TEXT) {
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
		if (!flags_load(&sdlt[n])) {
			break;
		}

		uint16_t flags_n = flags_load(&sdlt[n]);
		if (flags_n & SF_TEXT) {
			text++;
		} else {
			if (i == 0 || sdlt[dumpidx[i]].sprite != sdlt[dumpidx[i - 1]].sprite) {
				uni++;
			}
			cnt++;
		}

		if (flags_n & SF_SPRITE) {
			fprintf(fp, "Sprite: %6d (%7d) %s%s%s%s\n", sdlt[n].sprite, sdlt[n].fortick,
			    (flags_n & SF_USED) ? "SF_USED " : "", (flags_n & SF_DIDALLOC) ? "SF_DIDALLOC " : "",
			    (flags_n & SF_DIDMAKE) ? "SF_DIDMAKE " : "", (flags_n & SF_DIDTEX) ? "SF_DIDTEX " : "");
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
		if (flags_n & SF_TEXT) {
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

long long sdl_get_mem_tex(void)
{
	return (long long)__atomic_load_n(&mem_tex, __ATOMIC_RELAXED);
}