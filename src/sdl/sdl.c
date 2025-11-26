/*
 * Part of Astonia Client (c) Daniel Brockhaus. Please read license.txt.
 *
 * SDL
 *
 * Translates called from dd.c into SDL2 library calls. Also has the software
 * shader and texture cache.
 *
 */

#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <SDL2/SDL.h>
#include <SDL2/SDL_mixer.h>
#include <png.h>
#include <zip.h>

#include "../../src/dll.h"
#include "../../src/astonia.h"
#include "../../src/sdl.h"
#include "../../src/sdl/_sdl.h"
#ifdef DEVELOPER
extern int sockstate; // Declare early for use in wait logging
#endif

// Lock-free flag read helpers (writes under mutex)
// Cast atomic type to regular pointer for __atomic_* functions
static inline uint16_t flags_load(struct sdl_texture *st)
{
	uint16_t *flags_ptr = (uint16_t *)&st->flags;
	return __atomic_load_n(flags_ptr, __ATOMIC_ACQUIRE);
}

// Atomically set flag if not already set (returns 1 if successfully set, 0 if already set)
static inline int flags_set_if_not_set(struct sdl_texture *st, uint16_t mask)
{
	uint16_t *flags_ptr = (uint16_t *)&st->flags;
	uint16_t old, new;
	do {
		old = __atomic_load_n(flags_ptr, __ATOMIC_ACQUIRE);
		if (old & mask) {
			return 0; // Already set
		}
		new = old | mask;
	} while (!__atomic_compare_exchange_n(flags_ptr, &old, new, 0, __ATOMIC_RELEASE, __ATOMIC_ACQUIRE));
	return 1; // Successfully set
}

// Atomically claim a job - returns true if already claimed (by another thread), false if we claimed it
static inline int job_claimed(struct sdl_texture *st)
{
	// Returns 1 if already claimed, 0 if we successfully claimed it
	return !flags_set_if_not_set(st, SF_CLAIMJOB);
}

static SDL_Window *sdlwnd;
static SDL_Renderer *sdlren;

static struct sdl_texture *sdlt = NULL;
static int sdlt_best, sdlt_last;
static int *sdlt_cache;

static SDL_Cursor *curs[20];

static struct sdl_image *sdli = NULL;

// Thread-safe image loading state machine
enum {
	IMG_UNLOADED = 0,
	IMG_LOADING = 1,
	IMG_READY = 2,
	IMG_FAILED = 3,
};

static int *sdli_state = NULL;

int texc_used = 0;
static long long mem_png = 0;
static long long mem_tex = 0;
long long texc_hit = 0, texc_miss = 0, texc_pre = 0;

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
#ifdef DEVELOPER
uint64_t sdl_render_wait = 0;
uint64_t sdl_render_wait_count = 0;
#endif

DLL_EXPORT int sdl_scale = 1;
DLL_EXPORT int sdl_frames = 0;
DLL_EXPORT int sdl_multi = 4;
DLL_EXPORT int sdl_cache_size = 8000;

static zip_t *sdl_zip1 = NULL;
static zip_t *sdl_zip2 = NULL;

static zip_t *sdl_zip1p = NULL;
static zip_t *sdl_zip2p = NULL;

static zip_t *sdl_zip1m = NULL;
static zip_t *sdl_zip2m = NULL;

struct zip_handles {
	zip_t *zip1;
	zip_t *zip2;
	zip_t *zip1p;
	zip_t *zip2p;
	zip_t *zip1m;
	zip_t *zip2m;
};

static SDL_mutex *premutex = NULL;
static SDL_atomic_t pre_quit;
static SDL_Thread **prethreads = NULL;
static struct zip_handles *worker_zips = NULL;

DLL_EXPORT int __yres = YRES0;

static int sdlm_sprite = 0;
static int sdlm_scale = 0;
static void *sdlm_pixel = NULL;

static int sdl_eviction_failures = 0;

void sdl_dump(FILE *fp)
{
	fprintf(fp, "SDL datadump:\n");

	fprintf(fp, "XRES: %d\n", XRES);
	fprintf(fp, "YRES: %d\n", YRES);

	fprintf(fp, "sdl_scale: %d\n", sdl_scale);
	fprintf(fp, "sdl_frames: %d\n", sdl_frames);
	fprintf(fp, "sdl_multi: %d\n", sdl_multi);
	fprintf(fp, "sdl_cache_size: %d\n", sdl_cache_size);

	fprintf(fp, "mem_png: %lld\n", (long long)__atomic_load_n(&mem_png, __ATOMIC_RELAXED));
	fprintf(fp, "mem_tex: %lld\n", (long long)__atomic_load_n(&mem_tex, __ATOMIC_RELAXED));
	fprintf(fp, "texc_hit: %lld\n", texc_hit);
	fprintf(fp, "texc_miss: %lld\n", texc_miss);
	fprintf(fp, "texc_pre: %lld\n", texc_pre);

	fprintf(fp, "sdlm_sprite: %d\n", sdlm_sprite);
	fprintf(fp, "sdlm_scale: %d\n", sdlm_scale);
	fprintf(fp, "sdlm_pixel: %p\n", sdlm_pixel);

	fprintf(fp, "\n");
}

#define GO_DEFAULTS (GO_CONTEXT | GO_ACTION | GO_BIGBAR | GO_PREDICT | GO_SHORT | GO_MAPSAVE)

// #define GO_DEFAULTS (GO_CONTEXT|GO_ACTION|GO_BIGBAR|GO_PREDICT|GO_SHORT|GO_MAPSAVE|GO_NOMAP)

int sdl_init(int width, int height, char *title)
{
	int len, i;
	SDL_DisplayMode DM;

	if (SDL_Init(SDL_INIT_VIDEO | ((game_options & GO_SOUND) ? SDL_INIT_AUDIO : 0)) != 0) {
		fail("SDL_Init Error: %s", SDL_GetError());
		return 0;
	}

	SDL_SetHint(SDL_HINT_MOUSE_FOCUS_CLICKTHROUGH, "1");
	SDL_SetHint(SDL_HINT_WINDOWS_NO_CLOSE_ON_ALT_F4, "1");

	SDL_GetCurrentDisplayMode(0, &DM);

	if (!width || !height) {
		width = DM.w;
		height = DM.h;
	}

	sdlwnd = SDL_CreateWindow(title, DM.w / 2 - width / 2, DM.h / 2 - height / 2, width, height, SDL_WINDOW_SHOWN);
	if (!sdlwnd) {
		fail("SDL_Init Error: %s", SDL_GetError());
		SDL_Quit();
		return 0;
	}

	if (game_options & GO_FULL) {
		SDL_SetWindowFullscreen(sdlwnd, SDL_WINDOW_FULLSCREEN); // true full screen
	} else if (DM.w == width && DM.h == height) {
		SDL_SetWindowFullscreen(sdlwnd, SDL_WINDOW_FULLSCREEN_DESKTOP); // borderless windowed
	}

	sdlren = SDL_CreateRenderer(sdlwnd, -1, SDL_RENDERER_ACCELERATED | SDL_RENDERER_PRESENTVSYNC);
	if (!sdlren) {
		SDL_DestroyWindow(sdlwnd);
		fail("SDL_Init Error: %s", SDL_GetError());
		SDL_Quit();
		return 0;
	}

	len = sizeof(struct sdl_image) * MAXSPRITE;
	sdli = xmalloc(len * 1, MEM_SDL_BASE);
	if (!sdli) {
		return fail("Out of memory in sdl_init");
	}

	// Initialize image loading state array
	sdli_state = xmalloc(MAXSPRITE * sizeof(int), MEM_SDL_BASE);
	if (!sdli_state) {
		return fail("Out of memory in sdl_init");
	}
	for (i = 0; i < MAXSPRITE; i++) {
		__atomic_store_n((int *)&sdli_state[i], IMG_UNLOADED, __ATOMIC_RELAXED);
	}

	sdlt_cache = xmalloc(MAX_TEXHASH * sizeof(int), MEM_SDL_BASE);
	if (!sdlt_cache) {
		return fail("Out of memory in sdl_init");
	}

	for (i = 0; i < MAX_TEXHASH; i++) {
		sdlt_cache[i] = STX_NONE;
	}

	sdlt = xmalloc(MAX_TEXCACHE * sizeof(struct sdl_texture), MEM_SDL_BASE);
	if (!sdlt) {
		return fail("Out of memory in sdl_init");
	}

	for (i = 0; i < MAX_TEXCACHE; i++) {
		uint16_t *flags_ptr = (uint16_t *)&sdlt[i].flags;
		__atomic_store_n(flags_ptr, 0, __ATOMIC_RELAXED);
		sdlt[i].prev = i - 1;
		sdlt[i].next = i + 1;
		sdlt[i].hnext = STX_NONE;
		sdlt[i].hprev = STX_NONE;
	}
	sdlt[0].prev = STX_NONE;
	sdlt[MAX_TEXCACHE - 1].next = STX_NONE;
	sdlt_best = 0;
	sdlt_last = MAX_TEXCACHE - 1;

	SDL_RaiseWindow(sdlwnd);

	// We want SDL to translate scan codes to ASCII / Unicode
	// but we don't really want the SDL line editing stuff.
	// I hope just keeping it enabled all the time doesn't break
	// anything.
	SDL_StartTextInput();

	// decide on screen format
	if (width != XRES || height != YRES) {
		int tmp_scale = 1, off = 0;

		if (width / XRES >= 4 && height / YRES0 >= 4) {
			sdl_scale = 4;
		} else if (width / XRES >= 3 && height / YRES0 >= 3) {
			sdl_scale = 3;
		} else if (width / XRES >= 2 && height / YRES0 >= 2) {
			sdl_scale = 2;
		}

		if (width / XRES >= 4 && height / YRES2 >= 4) {
			tmp_scale = 4;
		} else if (width / XRES >= 3 && height / YRES2 >= 3) {
			tmp_scale = 3;
		} else if (width / XRES >= 2 && height / YRES2 >= 2) {
			tmp_scale = 2;
		}

		if (tmp_scale > sdl_scale || height < YRES0) {
			sdl_scale = tmp_scale;
			YRES = height / sdl_scale;
		}

		YRES = height / sdl_scale;

		if (game_options & GO_SMALLTOP) {
			off += 40;
		}
		if (game_options & GO_SMALLBOT) {
			off += 40;
		}

		if (YRES > YRES1 - off) {
			YRES = YRES1 - off;
		}

		dd_set_offset((width / sdl_scale - XRES) / 2, (height / sdl_scale - YRES) / 2);
	}
	if (game_options & GO_NOTSET) {
		if (YRES >= 620) {
			game_options = GO_DEFAULTS;
		} else if (YRES >= 580) {
			game_options = GO_DEFAULTS | GO_SMALLBOT;
		} else {
			game_options = GO_DEFAULTS | GO_SMALLBOT | GO_SMALLTOP;
		}
	}
	note("SDL using %dx%d scale %d, options=%" PRIu64, XRES, YRES, sdl_scale, game_options);

	sdl_create_cursors();

	sdl_zip1 = zip_open("res/gx1.zip", ZIP_RDONLY, NULL);
	sdl_zip1p = zip_open("res/gx1_patch.zip", ZIP_RDONLY, NULL);
	sdl_zip1m = zip_open("res/gx1_mod.zip", ZIP_RDONLY, NULL);

	switch (sdl_scale) {
	case 2:
		sdl_zip2 = zip_open("res/gx2.zip", ZIP_RDONLY, NULL);
		sdl_zip2p = zip_open("res/gx2_patch.zip", ZIP_RDONLY, NULL);
		sdl_zip2m = zip_open("res/gx2_mod.zip", ZIP_RDONLY, NULL);
		break;
	case 3:
		sdl_zip2 = zip_open("res/gx3.zip", ZIP_RDONLY, NULL);
		sdl_zip2p = zip_open("res/gx3_patch.zip", ZIP_RDONLY, NULL);
		sdl_zip2m = zip_open("res/gx3_mod.zip", ZIP_RDONLY, NULL);
		break;
	case 4:
		sdl_zip2 = zip_open("res/gx4.zip", ZIP_RDONLY, NULL);
		sdl_zip2p = zip_open("res/gx4_patch.zip", ZIP_RDONLY, NULL);
		sdl_zip2m = zip_open("res/gx4_mod.zip", ZIP_RDONLY, NULL);
		break;
	default:
		break;
	}

	if ((game_options & GO_SOUND) && Mix_OpenAudio(44100, MIX_DEFAULT_FORMAT, 2, 2048) < 0) {
		warn("initializing audio failed");
		game_options &= ~GO_SOUND;
	}

	if (game_options & GO_SOUND) {
		int number_of_sound_channels = Mix_AllocateChannels(MAX_SOUND_CHANNELS);
		note("Allocated %d sound channels", number_of_sound_channels);
	}


	// Always create premutex for thread-safe allocation
	// Single threaded is extremely rare, and not worth splitting logic for.
	premutex = SDL_CreateMutex();
	if (!premutex) {
		warn("Failed to create premutex");
	}

	if (sdl_multi) {
		char buf[80];
		int n;
		int init_failed = 0;

		SDL_AtomicSet(&pre_quit, 0);
		prethreads = xmalloc(sdl_multi * sizeof(SDL_Thread *), MEM_SDL_BASE);
		worker_zips = xmalloc(sdl_multi * sizeof(struct zip_handles), MEM_SDL_BASE);

		// First pass: open all zip handles for all workers
		// Don't create threads yet - if any zip fails, we can safely cleanup without threads running
		for (n = 0; n < sdl_multi; n++) {
			worker_zips[n].zip1 = zip_open("res/gx1.zip", ZIP_RDONLY, NULL);
			worker_zips[n].zip1p = zip_open("res/gx1_patch.zip", ZIP_RDONLY, NULL);
			worker_zips[n].zip1m = zip_open("res/gx1_mod.zip", ZIP_RDONLY, NULL);

			switch (sdl_scale) {
			case 2:
				worker_zips[n].zip2 = zip_open("res/gx2.zip", ZIP_RDONLY, NULL);
				worker_zips[n].zip2p = zip_open("res/gx2_patch.zip", ZIP_RDONLY, NULL);
				worker_zips[n].zip2m = zip_open("res/gx2_mod.zip", ZIP_RDONLY, NULL);
				break;
			case 3:
				worker_zips[n].zip2 = zip_open("res/gx3.zip", ZIP_RDONLY, NULL);
				worker_zips[n].zip2p = zip_open("res/gx3_patch.zip", ZIP_RDONLY, NULL);
				worker_zips[n].zip2m = zip_open("res/gx3_mod.zip", ZIP_RDONLY, NULL);
				break;
			case 4:
				worker_zips[n].zip2 = zip_open("res/gx4.zip", ZIP_RDONLY, NULL);
				worker_zips[n].zip2p = zip_open("res/gx4_patch.zip", ZIP_RDONLY, NULL);
				worker_zips[n].zip2m = zip_open("res/gx4_mod.zip", ZIP_RDONLY, NULL);
				break;
			default:
				worker_zips[n].zip2 = NULL;
				worker_zips[n].zip2p = NULL;
				worker_zips[n].zip2m = NULL;
				break;
			}

			if (!worker_zips[n].zip1) {
				warn("Worker %d: Failed to open res/gx1.zip - aborting initialization", n);
				init_failed = 1;
				break;
			}
		}

		// If any zip failed, cleanup all zips and don't create threads
		if (init_failed) {
			for (int i = 0; i < n; i++) {
				if (worker_zips[i].zip1) {
					zip_close(worker_zips[i].zip1);
				}
				if (worker_zips[i].zip1p) {
					zip_close(worker_zips[i].zip1p);
				}
				if (worker_zips[i].zip1m) {
					zip_close(worker_zips[i].zip1m);
				}
				if (worker_zips[i].zip2) {
					zip_close(worker_zips[i].zip2);
				}
				if (worker_zips[i].zip2p) {
					zip_close(worker_zips[i].zip2p);
				}
				if (worker_zips[i].zip2m) {
					zip_close(worker_zips[i].zip2m);
				}
			}
			xfree(worker_zips);
			worker_zips = NULL;
			xfree(prethreads);
			prethreads = NULL;
			sdl_multi = 0;
		} else {
			// All zips opened successfully - now create all threads
			for (n = 0; n < sdl_multi; n++) {
				sprintf(buf, "moac background worker %d", n);
				prethreads[n] = SDL_CreateThread(sdl_pre_backgnd, buf, (void *)(long long)n);
			}
		}
	}

	return 1;
}

int maxpanic = 0;

int sdl_clear(void)
{
	// SDL_SetRenderDrawColor(sdlren,255,63,63,255);     // clear with bright red to spot broken sprites
	SDL_SetRenderDrawColor(sdlren, 0, 0, 0, 255);
	SDL_RenderClear(sdlren);
	// note("mem: %.2fM PNG, %.2fM Tex, Hit: %ld, Miss: %ld, Max:
	// %d\n",mem_png/(1024.0*1024.0),mem_tex/(1024.0*1024.0),texc_hit,texc_miss,maxpanic);
	maxpanic = 0;
	return 1;
}

int sdl_render(void)
{
	SDL_RenderPresent(sdlren);
	sdl_frames++;
	return 1;
}

uint32_t mix_argb(uint32_t c1, uint32_t c2, float w1, float w2)
{
	int r1, r2, g1, g2, b1, b2, a1, a2;
	int r, g, b, a;

	a1 = IGET_A(c1);
	a2 = IGET_A(c2);
	if (!a1 && !a2) {
		return 0; // save some work
	}

	r1 = IGET_R(c1);
	g1 = IGET_G(c1);
	b1 = IGET_B(c1);

	r2 = IGET_R(c2);
	g2 = IGET_G(c2);
	b2 = IGET_B(c2);

	a = (a1 * w1 + a2 * w2);
	r = (r1 * w1 + r2 * w2);
	g = (g1 * w1 + g2 * w2);
	b = (b1 * w1 + b2 * w2);

	a = min(255, a);
	r = min(255, r);
	g = min(255, g);
	b = min(255, b);

	return IRGBA(r, g, b, a);
}

void sdl_smoothify(uint32_t *pixel, int xres, int yres, int scale)
{
	int x, y;
	uint32_t c1, c2, c3, c4;

	switch (scale) {
	case 2:
		for (x = 0; x < xres - 2; x += 2) {
			for (y = 0; y < yres - 2; y += 2) {
				c1 = pixel[x + y * xres]; // top left
				c2 = pixel[x + y * xres + 2]; // top right
				c3 = pixel[x + y * xres + xres * 2]; // bottom left
				c4 = pixel[x + y * xres + 2 + xres * 2]; // bottom right

				pixel[x + y * xres + 1] = mix_argb(c1, c2, 0.5, 0.5);
				pixel[x + y * xres + xres] = mix_argb(c1, c3, 0.5, 0.5);
				pixel[x + y * xres + 1 + xres] =
				    mix_argb(mix_argb(c1, c2, 0.5, 0.5), mix_argb(c3, c4, 0.5, 0.5), 0.5, 0.5);
			}
		}
		break;
	case 3:
		for (x = 0; x < xres - 3; x += 3) {
			for (y = 0; y < yres - 3; y += 3) {
				c1 = pixel[x + y * xres]; // top left
				c2 = pixel[x + y * xres + 3]; // top right
				c3 = pixel[x + y * xres + xres * 3]; // bottom left
				c4 = pixel[x + y * xres + 3 + xres * 3]; // bottom right

				pixel[x + y * xres + 1] = mix_argb(c1, c2, 0.667, 0.333);
				pixel[x + y * xres + 2] = mix_argb(c1, c2, 0.333, 0.667);

				pixel[x + y * xres + xres * 1] = mix_argb(c1, c3, 0.667, 0.333);
				pixel[x + y * xres + xres * 2] = mix_argb(c1, c3, 0.333, 0.667);

				pixel[x + y * xres + 1 + xres * 1] =
				    mix_argb(mix_argb(c1, c2, 0.5, 0.5), mix_argb(c3, c4, 0.5, 0.5), 0.5, 0.5);
				pixel[x + y * xres + 2 + xres * 1] =
				    mix_argb(mix_argb(c1, c2, 0.333, 0.667), mix_argb(c3, c4, 0.333, 0.667), 0.667, 0.333);
				pixel[x + y * xres + 1 + xres * 2] =
				    mix_argb(mix_argb(c1, c2, 0.667, 0.333), mix_argb(c3, c4, 0.667, 0.333), 0.333, 0.667);
				pixel[x + y * xres + 2 + xres * 2] =
				    mix_argb(mix_argb(c1, c2, 0.333, 0.667), mix_argb(c3, c4, 0.333, 0.667), 0.333, 0.667);
			}
		}
		break;

	case 4:
		for (x = 0; x < xres - 4; x += 4) {
			for (y = 0; y < yres - 4; y += 4) {
				c1 = pixel[x + y * xres]; // top left
				c2 = pixel[x + y * xres + 4]; // top right
				c3 = pixel[x + y * xres + xres * 4]; // bottom left
				c4 = pixel[x + y * xres + 4 + xres * 4]; // bottom right

				pixel[x + y * xres + 1] = mix_argb(c1, c2, 0.75, 0.25);
				pixel[x + y * xres + 2] = mix_argb(c1, c2, 0.50, 0.50);
				pixel[x + y * xres + 3] = mix_argb(c1, c2, 0.25, 0.75);

				pixel[x + y * xres + xres * 1] = mix_argb(c1, c3, 0.75, 0.25);
				pixel[x + y * xres + xres * 2] = mix_argb(c1, c3, 0.50, 0.50);
				pixel[x + y * xres + xres * 3] = mix_argb(c1, c3, 0.25, 0.75);

				pixel[x + y * xres + 1 + xres * 1] =
				    mix_argb(mix_argb(c1, c2, 0.75, 0.25), mix_argb(c3, c4, 0.75, 0.25), 0.75, 0.25);
				pixel[x + y * xres + 1 + xres * 2] =
				    mix_argb(mix_argb(c1, c2, 0.75, 0.25), mix_argb(c3, c4, 0.75, 0.25), 0.50, 0.50);
				pixel[x + y * xres + 1 + xres * 3] =
				    mix_argb(mix_argb(c1, c2, 0.75, 0.75), mix_argb(c3, c4, 0.75, 0.25), 0.25, 0.75);

				pixel[x + y * xres + 2 + xres * 1] =
				    mix_argb(mix_argb(c1, c2, 0.50, 0.50), mix_argb(c3, c4, 0.50, 0.50), 0.75, 0.25);
				pixel[x + y * xres + 2 + xres * 2] =
				    mix_argb(mix_argb(c1, c2, 0.50, 0.50), mix_argb(c3, c4, 0.50, 0.50), 0.50, 0.50);
				pixel[x + y * xres + 2 + xres * 3] =
				    mix_argb(mix_argb(c1, c2, 0.50, 0.50), mix_argb(c3, c4, 0.50, 0.50), 0.25, 0.75);

				pixel[x + y * xres + 3 + xres * 1] =
				    mix_argb(mix_argb(c1, c2, 0.25, 0.75), mix_argb(c3, c4, 0.25, 0.75), 0.75, 0.25);
				pixel[x + y * xres + 3 + xres * 2] =
				    mix_argb(mix_argb(c1, c2, 0.25, 0.75), mix_argb(c3, c4, 0.25, 0.75), 0.50, 0.50);
				pixel[x + y * xres + 3 + xres * 3] =
				    mix_argb(mix_argb(c1, c2, 0.25, 0.75), mix_argb(c3, c4, 0.25, 0.75), 0.25, 0.75);
			}
		}
		break;
	default:
		warn("Unsupported scale %d in sdl_load_image_png()", sdl_scale);
		break;
	}
}

void sdl_premulti(uint32_t *pixel, int xres, int yres, int scale)
{
	int n, r, g, b, a;
	uint32_t c;

	for (n = 0; n < xres * yres; n++) {
		c = pixel[n];

		a = IGET_A(c);
		if (!a) {
			continue;
		}

		r = IGET_R(c);
		g = IGET_G(c);
		b = IGET_B(c);

		r = min(255, r * 255 / a);
		g = min(255, g * 255 / a);
		b = min(255, b * 255 / a);

		c = IRGBA(r, g, b, a);
		pixel[n] = c;
	}
}

struct png_helper {
	char *filename;
	zip_t *zip;
	unsigned char **row;
	int xres;
	int yres;
	int bpp;

	png_structp png_ptr;
	png_infop info_ptr;
};

void png_helper_read(png_structp ps, png_bytep buf, png_size_t len)
{
	zip_fread(png_get_io_ptr(ps), buf, len);
}

int png_load_helper(struct png_helper *p)
{
	FILE *fp = NULL;
	zip_file_t *zp = NULL;
	int tmp;

	if (p->zip) {
		zp = zip_fopen(p->zip, p->filename, 0);
		if (!zp) {
			return -1;
		}
	} else {
		fp = fopen(p->filename, "rb");
		if (!fp) {
			return -1;
		}
	}

	p->png_ptr = png_create_read_struct(PNG_LIBPNG_VER_STRING, NULL, NULL, NULL);
	if (!p->png_ptr) {
		if (zp) {
			zip_fclose(zp);
		}
		if (fp) {
			fclose(fp);
		}
		warn("create read\n");
		return -1;
	}

	p->info_ptr = png_create_info_struct(p->png_ptr);
	if (!p->info_ptr) {
		if (zp) {
			zip_fclose(zp);
		}
		if (fp) {
			fclose(fp);
		}
		png_destroy_read_struct(&p->png_ptr, (png_infopp)NULL, (png_infopp)NULL);
		warn("create info1\n");
		return -1;
	}

	if (p->zip) {
		png_set_read_fn(p->png_ptr, zp, png_helper_read);
	} else {
		png_init_io(p->png_ptr, fp);
	}
	png_set_strip_16(p->png_ptr);
	png_read_png(p->png_ptr, p->info_ptr, PNG_TRANSFORM_PACKING, NULL);

	p->row = png_get_rows(p->png_ptr, p->info_ptr);
	if (!p->row) {
		if (zp) {
			zip_fclose(zp);
		}
		if (fp) {
			fclose(fp);
		}
		png_destroy_read_struct(&p->png_ptr, &p->info_ptr, (png_infopp)NULL);
		warn("read row\n");
		return -1;
	}

	p->xres = png_get_image_width(p->png_ptr, p->info_ptr);
	p->yres = png_get_image_height(p->png_ptr, p->info_ptr);

	tmp = png_get_rowbytes(p->png_ptr, p->info_ptr);

	if (tmp == p->xres * 3) {
		p->bpp = 24;
	} else if (tmp == p->xres * 4) {
		p->bpp = 32;
	} else {
		if (zp) {
			zip_fclose(zp);
		}
		if (fp) {
			fclose(fp);
		}
		png_destroy_read_struct(&p->png_ptr, &p->info_ptr, (png_infopp)NULL);
		warn("rowbytes!=xres*4 (%d, %d, %s)", tmp, p->xres, p->filename);
		return -1;
	}

	if (png_get_bit_depth(p->png_ptr, p->info_ptr) != 8) {
		if (zp) {
			zip_fclose(zp);
		}
		if (fp) {
			fclose(fp);
		}
		png_destroy_read_struct(&p->png_ptr, &p->info_ptr, (png_infopp)NULL);
		warn("bit depth!=8\n");
		return -1;
	}
	if (png_get_channels(p->png_ptr, p->info_ptr) != p->bpp / 8) {
		if (zp) {
			zip_fclose(zp);
		}
		if (fp) {
			fclose(fp);
		}
		png_destroy_read_struct(&p->png_ptr, &p->info_ptr, (png_infopp)NULL);
		warn("channels!=format\n");
		return -1;
	}

	if (p->zip) {
		zip_fclose(zp);
	} else {
		fclose(fp);
	}

	return 0;
}

void png_load_helper_exit(struct png_helper *p)
{
	png_destroy_read_struct(&p->png_ptr, &p->info_ptr, (png_infopp)NULL);
}

// Load high res PNG
int sdl_load_image_png_(struct sdl_image *si, char *filename, zip_t *zip)
{
	int x, y, r, g, b, a, sx, sy, ex, ey;
	uint32_t c;
	struct png_helper p;

	p.zip = zip;
	p.filename = filename;
	if (png_load_helper(&p)) {
		return -1;
	}

	// prescan
	sx = p.xres;
	sy = p.yres;
	ex = 0;
	ey = 0;

	for (y = 0; y < p.yres; y++) {
		for (x = 0; x < p.xres; x++) {
			if (p.bpp == 32 && (p.row[y][x * 4 + 3] == 0 || (p.row[y][x * 4 + 0] == 255 && p.row[y][x * 4 + 1] == 0 &&
			                                                    p.row[y][x * 4 + 2] == 255))) {
				continue;
			}
			if (p.bpp == 24 && (p.row[y][x * 3 + 0] == 255 && p.row[y][x * 3 + 1] == 0 && p.row[y][x * 3 + 2] == 255)) {
				continue;
			}
			if (x < sx) {
				sx = x;
			}
			if (x > ex) {
				ex = x;
			}
			if (y < sy) {
				sy = y;
			}
			if (y > ey) {
				ey = y;
			}
		}
	}

	// Make sure the new found borders of the image are on multiples
	// of sd_scale. And never shrink the visible portion to do that.
	sx = (sx / sdl_scale) * sdl_scale;
	sy = (sy / sdl_scale) * sdl_scale;
	ex = ((ex + sdl_scale) / sdl_scale) * sdl_scale;
	ey = ((ey + sdl_scale) / sdl_scale) * sdl_scale;

	if (ex < sx) {
		ex = sx - 1;
	}
	if (ey < sy) {
		ey = sy - 1;
	}

	// write
	si->flags = 1;
	si->xres = ex - sx;
	si->yres = ey - sy;
	si->xoff = -(p.xres / 2) + sx;
	si->yoff = -(p.yres / 2) + sy;

#ifdef SDL_FAST_MALLOC
	si->pixel = malloc(si->xres * si->yres * sizeof(uint32_t));
#else
	si->pixel = xmalloc(si->xres * si->yres * sizeof(uint32_t), MEM_SDL_PNG);
#endif
	__atomic_add_fetch(&mem_png, si->xres * si->yres * sizeof(uint32_t), __ATOMIC_RELAXED);

	for (y = 0; y < si->yres; y++) {
		for (x = 0; x < si->xres; x++) {
			if (p.bpp == 32) {
				if (sx + x >= p.xres || sy + y >= p.yres) {
					r = g = b = a = 0;
				} else {
					r = p.row[(sy + y)][(sx + x) * 4 + 0];
					g = p.row[(sy + y)][(sx + x) * 4 + 1];
					b = p.row[(sy + y)][(sx + x) * 4 + 2];
					a = p.row[(sy + y)][(sx + x) * 4 + 3];
				}
			} else {
				if (sx + x >= p.xres || sy + y >= p.yres) {
					r = g = b = a = 0;
				} else {
					r = p.row[(sy + y)][(sx + x) * 3 + 0];
					g = p.row[(sy + y)][(sx + x) * 3 + 1];
					b = p.row[(sy + y)][(sx + x) * 3 + 2];
					if (r == 255 && g == 0 && b == 255) {
						a = 0;
					} else {
						a = 255;
					}
				}
			}

			if (r == 255 && g == 0 && b == 255) {
				a = 0;
			}

			if (a) { // pre-multiply rgb channel by alpha
				r = min(255, r * 255 / a);
				g = min(255, g * 255 / a);
				b = min(255, b * 255 / a);
			} else {
				r = g = b = 0;
			}

			c = IRGBA(r, g, b, a);

			si->pixel[x + y * si->xres] = c;
		}
	}

	png_load_helper_exit(&p);

	si->xres /= sdl_scale;
	si->yres /= sdl_scale;
	si->xoff /= sdl_scale;
	si->yoff /= sdl_scale;

	return 0;
}

// Load and up-scale low res PNG
// TODO: add support for using a 2X image as a base for 4X
// and possibly the other way around too
int sdl_load_image_png(struct sdl_image *si, char *filename, zip_t *zip, int smoothify)
{
	int x, y, r, g, b, a, sx, sy, ex, ey;
	uint32_t c;
	struct png_helper p;

	p.zip = zip;
	p.filename = filename;
	if (png_load_helper(&p)) {
		return -1;
	}

	// prescan
	sx = p.xres;
	sy = p.yres;
	ex = 0;
	ey = 0;

	for (y = 0; y < p.yres; y++) {
		for (x = 0; x < p.xres; x++) {
			if (p.bpp == 32 && (p.row[y][x * 4 + 3] == 0 || (p.row[y][x * 4 + 0] == 255 && p.row[y][x * 4 + 1] == 0 &&
			                                                    p.row[y][x * 4 + 2] == 255))) {
				continue;
			}
			if (p.bpp == 24 && (p.row[y][x * 3 + 0] == 255 && p.row[y][x * 3 + 1] == 0 && p.row[y][x * 3 + 2] == 255)) {
				continue;
			}
			if (x < sx) {
				sx = x;
			}
			if (x > ex) {
				ex = x;
			}
			if (y < sy) {
				sy = y;
			}
			if (y > ey) {
				ey = y;
			}
		}
	}

	if (ex < sx) {
		ex = sx - 1;
	}
	if (ey < sy) {
		ey = sy - 1;
	}

	// write
	si->flags = 1;
	si->xres = ex - sx + 1;
	si->yres = ey - sy + 1;
	si->xoff = -(p.xres / 2) + sx;
	si->yoff = -(p.yres / 2) + sy;

#ifdef SDL_FAST_MALLOC
	si->pixel = malloc(si->xres * si->yres * sizeof(uint32_t) * sdl_scale * sdl_scale);
#else
	si->pixel = xmalloc(si->xres * si->yres * sizeof(uint32_t) * sdl_scale * sdl_scale, MEM_SDL_PNG);
#endif
	__atomic_add_fetch(&mem_png, si->xres * si->yres * sizeof(uint32_t) * sdl_scale * sdl_scale, __ATOMIC_RELAXED);

	for (y = 0; y < si->yres; y++) {
		for (x = 0; x < si->xres; x++) {
			if (p.bpp == 32) {
				r = p.row[(sy + y)][(sx + x) * 4 + 0];
				g = p.row[(sy + y)][(sx + x) * 4 + 1];
				b = p.row[(sy + y)][(sx + x) * 4 + 2];
				a = p.row[(sy + y)][(sx + x) * 4 + 3];
			} else {
				r = p.row[(sy + y)][(sx + x) * 3 + 0];
				g = p.row[(sy + y)][(sx + x) * 3 + 1];
				b = p.row[(sy + y)][(sx + x) * 3 + 2];
				if (r == 255 && g == 0 && b == 255) {
					a = 0;
				} else {
					a = 255;
				}
			}

			if (r == 255 && g == 0 && b == 255) {
				a = 0;
			}

			if (!a) { // don't pre-multiply rgb channel by alpha because that needs to happen after scaling
				r = g = b = 0;
			}

			c = IRGBA(r, g, b, a);

			switch (sdl_scale) {
			case 1:
				si->pixel[x + y * si->xres] = c;
				break;
			case 2:
				si->pixel[x * 2 + y * si->xres * 4] = c;
				si->pixel[x * 2 + y * si->xres * 4 + 1] = c;
				si->pixel[x * 2 + y * si->xres * 4 + si->xres * 2] = c;
				si->pixel[x * 2 + y * si->xres * 4 + 1 + si->xres * 2] = c;
				break;
			case 3:
				si->pixel[x * 3 + y * si->xres * 9 + 0] = c;
				si->pixel[x * 3 + y * si->xres * 9 + 0 + si->xres * 3] = c;
				si->pixel[x * 3 + y * si->xres * 9 + 0 + si->xres * 6] = c;

				si->pixel[x * 3 + y * si->xres * 9 + 1] = c;
				si->pixel[x * 3 + y * si->xres * 9 + 1 + si->xres * 3] = c;
				si->pixel[x * 3 + y * si->xres * 9 + 1 + si->xres * 6] = c;

				si->pixel[x * 3 + y * si->xres * 9 + 2] = c;
				si->pixel[x * 3 + y * si->xres * 9 + 2 + si->xres * 3] = c;
				si->pixel[x * 3 + y * si->xres * 9 + 2 + si->xres * 6] = c;
				break;
			case 4:
				si->pixel[x * 4 + y * si->xres * 16 + 0] = c;
				si->pixel[x * 4 + y * si->xres * 16 + 0 + si->xres * 4] = c;
				si->pixel[x * 4 + y * si->xres * 16 + 0 + si->xres * 8] = c;
				si->pixel[x * 4 + y * si->xres * 16 + 0 + si->xres * 12] = c;

				si->pixel[x * 4 + y * si->xres * 16 + 1] = c;
				si->pixel[x * 4 + y * si->xres * 16 + 1 + si->xres * 4] = c;
				si->pixel[x * 4 + y * si->xres * 16 + 1 + si->xres * 8] = c;
				si->pixel[x * 4 + y * si->xres * 16 + 1 + si->xres * 12] = c;

				si->pixel[x * 4 + y * si->xres * 16 + 2] = c;
				si->pixel[x * 4 + y * si->xres * 16 + 2 + si->xres * 4] = c;
				si->pixel[x * 4 + y * si->xres * 16 + 2 + si->xres * 8] = c;
				si->pixel[x * 4 + y * si->xres * 16 + 2 + si->xres * 12] = c;

				si->pixel[x * 4 + y * si->xres * 16 + 3] = c;
				si->pixel[x * 4 + y * si->xres * 16 + 3 + si->xres * 4] = c;
				si->pixel[x * 4 + y * si->xres * 16 + 3 + si->xres * 8] = c;
				si->pixel[x * 4 + y * si->xres * 16 + 3 + si->xres * 12] = c;
				break;
			default:
				warn("Unsupported scale %d in sdl_load_image_png()", sdl_scale);
				break;
			}
		}
	}

	if (sdl_scale > 1 && smoothify) {
		sdl_smoothify(si->pixel, si->xres * sdl_scale, si->yres * sdl_scale, sdl_scale);
		sdl_premulti(si->pixel, si->xres * sdl_scale, si->yres * sdl_scale, sdl_scale);
	} else {
		sdl_premulti(si->pixel, si->xres * sdl_scale, si->yres * sdl_scale, sdl_scale);
	}

	png_load_helper_exit(&p);

	return 0;
}

int do_smoothify(int sprite)
{
	// TODO: add more to this list
	if (sprite >= 50 && sprite <= 56) {
		return 0;
	}
	if (sprite > 0 && sprite <= 1000) {
		return 1; // GUI
	}
	if (sprite >= 10000 && sprite < 11000) {
		return 1; // items
	}
	if (sprite >= 11000 && sprite < 12000) {
		return 1; // coffin, berries, farn, ...
	}
	if (sprite >= 13000 && sprite < 14000) {
		return 1; // bones and towers, ...
	}
	if (sprite >= 16000 && sprite < 17000) {
		return 1; // cameron doors, carts, ...
	}
	if (sprite >= 20025 && sprite < 20034) {
		return 1; // torches
	}
	if (sprite >= 20042 && sprite < 20082) {
		return 1; // torches
	}
	if (sprite >= 20086 && sprite < 20119) {
		return 1; // chests, chairs
	}

	if (sprite >= 100000) {
		return 1; // all character sprites
	}

	return 0;
}

int sdl_load_image(struct sdl_image *si, int sprite, struct zip_handles *zips)
{
	char filename[1024];
	zip_t *zip1, *zip1p, *zip1m, *zip2, *zip2p, *zip2m;

	if (zips) {
		zip1 = zips->zip1;
		zip1p = zips->zip1p;
		zip1m = zips->zip1m;
		zip2 = zips->zip2;
		zip2p = zips->zip2p;
		zip2m = zips->zip2m;
	} else {
		zip1 = sdl_zip1;
		zip1p = sdl_zip1p;
		zip1m = sdl_zip1m;
		zip2 = sdl_zip2;
		zip2p = sdl_zip2p;
		zip2m = sdl_zip2m;
	}

	if (sprite >= MAXSPRITE || sprite < 0) {
		note("sdl_load_image: illegal sprite %d wanted", sprite);
		return -1;
	}

#if 0
	// get patch png
	sprintf(filename,"../gfxp/x%d/%08d/%08d.png",sdl_scale,(sprite/1000)*1000,sprite);
	if (sdl_load_image_png_(si,filename,NULL)==0) return 0;
#endif

	// get high res from archive
	if (zip2 || zip2p || zip2m) {
		sprintf(filename, "%08d.png", sprite);
		if (zip2m && sdl_load_image_png_(si, filename, zip2m) == 0) {
			return 0; // check mod archive first
		}
		if (zip2p && sdl_load_image_png_(si, filename, zip2p) == 0) {
			return 0; // check patch archive second
		}
		if (zip2 && sdl_load_image_png_(si, filename, zip2) == 0) {
			return 0; // check base archive third
		}
	}

#if 0
	// get high res from base png folder
	sprintf(filename,"../gfx/x%d/%08d/%08d.png",sdl_scale,(sprite/1000)*1000,sprite);
	if (sdl_load_image_png_(si,filename,NULL)==0) return 0;
#endif

	// get standard from archive
	if (zip1 || zip1p || zip1m) {
		sprintf(filename, "%08d.png", sprite);
		if (zip1m && sdl_load_image_png(si, filename, zip1m, do_smoothify(sprite)) == 0) {
			return 0;
		}
		if (zip1p && sdl_load_image_png(si, filename, zip1p, do_smoothify(sprite)) == 0) {
			return 0;
		}
		if (zip1 && sdl_load_image_png(si, filename, zip1, do_smoothify(sprite)) == 0) {
			return 0;
		}
	}

#if 0
	// get standard from base png folder
	sprintf(filename,"../gfx/x1/%08d/%08d.png",(sprite/1000)*1000,sprite);
	if (sdl_load_image_png(si,filename,NULL,do_smoothify(sprite))==0) return 0;
	sprintf(filename,"../gfxp/x1/%08d/%08d.png",(sprite/1000)*1000,sprite);
	if (sdl_load_image_png(si,filename,NULL,do_smoothify(sprite))==0) return 0;
#endif

	sprintf(filename, "%08d.png", sprite);
	warn("%s not found", filename);

	// get unknown sprite image
	sprintf(filename, "%08d.png", 2);
	if (zip1 && sdl_load_image_png(si, filename, zip1, do_smoothify(sprite)) == 0) {
		return 0;
	}

	char *txt = "The client could not locate the graphics file gx1.zip. "
	            "Please make sure you start the client from the main folder, "
	            "not from within the bin-folder.\n\n"
	            "You can create a shortcut with the working directory set to the main folder.";
	display_messagebox("Graphics Not Found", txt);
	exit(105);
	return -1;
}

int sdl_ic_load(int sprite, struct zip_handles *zips)
{
#ifdef DEVELOPER
	uint64_t start = SDL_GetTicks64();
#endif

	if (sprite < 0 || sprite >= MAXSPRITE) {
		note("illegal sprite %d wanted in sdl_ic_load", sprite);
		return -1;
	}

	int state;
retry:
	state = __atomic_load_n((int *)&sdli_state[sprite], __ATOMIC_ACQUIRE);

	if (state == IMG_READY) {
#ifdef DEVELOPER
		sdl_time_load += SDL_GetTicks64() - start;
#endif
		return sprite;
	}

	if (state == IMG_FAILED) {
		return -1;
	}

	if (state == IMG_LOADING) {
		// Someone else is loading; wait for them
		SDL_Delay(1);
		goto retry;
	}

	// state == IMG_UNLOADED, try to become the loader
	int expected = IMG_UNLOADED;
	if (!__atomic_compare_exchange_n(
	        (int *)&sdli_state[sprite], &expected, IMG_LOADING, 0, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) {
		// Lost the race, someone else started loading; wait
		goto retry;
	}

	// We are the loader now
	if (sdl_load_image(sdli + sprite, sprite, zips) == 0) {
		__atomic_store_n((int *)&sdli_state[sprite], IMG_READY, __ATOMIC_RELEASE);
#ifdef DEVELOPER
		sdl_time_load += SDL_GetTicks64() - start;
#endif
		return sprite;
	} else {
		__atomic_store_n((int *)&sdli_state[sprite], IMG_FAILED, __ATOMIC_RELEASE);
		return -1;
	}
}

#define DDFX_MAX_FREEZE 8

static inline int light_calc(int val, int light)
{
	int v1, v2, m = 3, d = 4;

	if (game_options & (GO_LIGHTER | GO_LIGHTER2)) {
		v1 = val * light / 15;
		v2 = val * sqrt(light) / 3.87;
		if (game_options & GO_LIGHTER) {
			m--;
			d--;
		}
		if (game_options & GO_LIGHTER2) {
			m -= 2;
			d -= 2;
		}
		return (v1 * m + v2) / d;
	} else {
		return val * light / 15;
	}
}

static inline uint32_t sdl_light(int light, uint32_t irgb)
{
	int r, g, b, a;

	r = IGET_R(irgb);
	g = IGET_G(irgb);
	b = IGET_B(irgb);
	a = IGET_A(irgb);

	if (light == 0) {
		r = min(255, r * 2 + 4);
		g = min(255, g * 2 + 4);
		b = min(255, b * 2 + 4);
	} else {
		r = light_calc(r, light);
		g = light_calc(g, light);
		b = light_calc(b, light);
	}

	return IRGBA(r, g, b, a);
}

static inline uint32_t sdl_freeze(int freeze, uint32_t irgb)
{
	int r, g, b, a;

	r = IGET_R(irgb);
	g = IGET_G(irgb);
	b = IGET_B(irgb);
	a = IGET_A(irgb);

	r = min(255, r + 255 * freeze / (3 * DDFX_MAX_FREEZE - 1));
	g = min(255, g + 255 * freeze / (3 * DDFX_MAX_FREEZE - 1));
	b = min(255, b + 255 * 3 * freeze / (3 * DDFX_MAX_FREEZE - 1));

	return IRGBA(r, g, b, a);
}

#define REDCOL   (0.40)
#define GREENCOL (0.70)
#define BLUECOL  (0.70)

#define OGET_R(c) ((((unsigned short int)(c)) >> 10) & 0x1F)
#define OGET_G(c) ((((unsigned short int)(c)) >> 5) & 0x1F)
#define OGET_B(c) ((((unsigned short int)(c)) >> 0) & 0x1F)

static uint32_t sdl_shine_pix(uint32_t irgb, unsigned short shine)
{
	int a;
	double r, g, b;

	r = IGET_R(irgb) / 127.5;
	g = IGET_G(irgb) / 127.5;
	b = IGET_B(irgb) / 127.5;
	a = IGET_A(irgb);

	r = ((r * r * r * r) * shine + r * (100.0 - shine)) / 200.0;
	g = ((g * g * g * g) * shine + g * (100.0 - shine)) / 200.0;
	b = ((b * b * b * b) * shine + b * (100.0 - shine)) / 200.0;

	if (r > 1.0) {
		r = 1.0;
	}
	if (g > 1.0) {
		g = 1.0;
	}
	if (b > 1.0) {
		b = 1.0;
	}

	irgb = IRGBA((int)(r * 255.0), (int)(g * 255.0), (int)(b * 255.0), a);

	return irgb;
}

static uint32_t sdl_colorize_pix(uint32_t irgb, unsigned short c1v, unsigned short c2v, unsigned short c3v)
{
	double rf, gf, bf, m, rm, gm, bm;
	double c1 = 0, c2 = 0, c3 = 0;
	double shine = 0;
	int r, g, b, a;

	rf = IGET_R(irgb) / 255.0;
	gf = IGET_G(irgb) / 255.0;
	bf = IGET_B(irgb) / 255.0;

	m = max(max(rf, gf), bf) + 0.000001;
	rm = rf / m;
	gm = gf / m;
	bm = bf / m;

	// channel 1: green max
	if (c1v && gm > 0.99 && rm < GREENCOL && bm < GREENCOL) {
		c1 = gf - max(bf, rf);
		if (c1v & 0x8000) {
			shine += gm - max(rm, bm);
		}

		gf -= c1;
	}

	m = max(max(rf, gf), bf) + 0.000001;
	rm = rf / m;
	gm = gf / m;
	bm = bf / m;

	// channel 2: blue max
	if (c2v && bm > 0.99 && rm < BLUECOL && gm < BLUECOL) {
		c2 = bf - max(rf, gf);
		if (c2v & 0x8000) {
			shine += bm - max(rm, gm);
		}

		bf -= c2;
	}

	m = max(max(rf, gf), bf) + 0.000001;
	rm = rf / m;
	gm = gf / m;
	bm = bf / m;

	// channel 3: red max
	if (c3v && rm > 0.99 && gm < REDCOL && bm < REDCOL) {
		c3 = rf - max(gf, bf);
		if (c3v & 0x8000) {
			shine += rm - max(gm, bm);
		}

		rf -= c3;
	}

	// sanity
	rf = max(0, rf);
	gf = max(0, gf);
	bf = max(0, bf);

	// collect
	r = min(255, 8 * 2 * c1 * OGET_R(c1v) + 8 * 2 * c2 * OGET_R(c2v) + 8 * 2 * c3 * OGET_R(c3v) + 8 * rf * 31);
	g = min(255, 8 * 2 * c1 * OGET_G(c1v) + 8 * 2 * c2 * OGET_G(c2v) + 8 * 2 * c3 * OGET_G(c3v) + 8 * gf * 31);
	b = min(255, 8 * 2 * c1 * OGET_B(c1v) + 8 * 2 * c2 * OGET_B(c2v) + 8 * 2 * c3 * OGET_B(c3v) + 8 * bf * 31);

	a = IGET_A(irgb);

	irgb = IRGBA(r, g, b, a);

	if (shine > 0.1) {
		irgb = sdl_shine_pix(irgb, (int)(shine * 50));
	}

	return irgb;
}

static int would_colorize(int x, int y, int xres, int yres, uint32_t *pixel, int what)
{
	double rf, gf, bf, m, rm, gm, bm;
	uint32_t irgb;

	if (x < 0 || x >= xres * sdl_scale) {
		return 0;
	}
	if (y < 0 || y >= yres * sdl_scale) {
		return 0;
	}

	irgb = pixel[x + y * xres * sdl_scale];

	rf = IGET_R(irgb) / 255.0;
	gf = IGET_G(irgb) / 255.0;
	bf = IGET_B(irgb) / 255.0;

	m = max(max(rf, gf), bf) + 0.000001;
	rm = rf / m;
	gm = gf / m;
	bm = bf / m;

	if (what == 0 && gm > 0.99 && rm < GREENCOL && bm < GREENCOL) {
		return 1;
	}
	if (what == 1 && bm > 0.99 && rm < BLUECOL && gm < BLUECOL) {
		return 1;
	}
	if (what == 2 && rm > 0.99 && gm < REDCOL && bm < REDCOL) {
		return 1;
	}

	return 0;
}

static int would_colorize_neigh(int x, int y, int xres, int yres, uint32_t *pixel, int what)
{
	int v = 0;
	v = would_colorize(x + 1, y + 0, xres, yres, pixel, what) + would_colorize(x - 1, y + 0, xres, yres, pixel, what) +
	    would_colorize(x + 0, y + 1, xres, yres, pixel, what) + would_colorize(x + 0, y - 1, xres, yres, pixel, what);
	if (sdl_scale > 2) {
		v += would_colorize(x + 2, y + 0, xres, yres, pixel, what) +
		     would_colorize(x - 2, y + 0, xres, yres, pixel, what) +
		     would_colorize(x + 0, y + 2, xres, yres, pixel, what) +
		     would_colorize(x + 0, y - 2, xres, yres, pixel, what);
	}
	return v;
}

static uint32_t sdl_colorize_pix2(uint32_t irgb, unsigned short c1v, unsigned short c2v, unsigned short c3v, int x,
    int y, int xres, int yres, uint32_t *pixel, int sprite)
{
	double rf, gf, bf, m, rm, gm, bm;
	int r, g, b, a;

	// use old algorithm for old sprites
	if (sprite < 220000) {
		return sdl_colorize_pix(irgb, c1v, c2v, c3v);
	}

	rf = IGET_R(irgb) / 255.0;
	gf = IGET_G(irgb) / 255.0;
	bf = IGET_B(irgb) / 255.0;

	m = max(max(rf, gf), bf) + 0.000001;
	rm = rf / m;
	gm = gf / m;
	bm = bf / m;

	// channel 1: green
	if ((c1v && gm > 0.99 && rm < GREENCOL && bm < GREENCOL) ||
	    (c1v && gm > 0.67 && would_colorize_neigh(x, y, xres, yres, pixel, 0))) {
		r = 8.0 * (OGET_R(c1v) * gf + (1.0 - gf) * rf);
		g = 8.0 * OGET_G(c1v) * gf;
		b = 8.0 * (OGET_B(c1v) * gf + (1.0 - gf) * bf);
		a = IGET_A(irgb);
		return IRGBA(r, g, b, a);
	}

	// channel 2: blue
	if ((c2v && bm > 0.99 && rm < BLUECOL && gm < BLUECOL) ||
	    (c2v && bm > 0.67 && would_colorize_neigh(x, y, xres, yres, pixel, 1))) {
		r = 8.0 * (OGET_R(c2v) * bf + (1.0 - bf) * rf);
		g = 8.0 * (OGET_G(c2v) * bf + (1.0 - bf) * gf);
		b = 8.0 * OGET_B(c2v) * bf;
		a = IGET_A(irgb);
		return IRGBA(r, g, b, a);
	}

	// channel 3: red
	if ((c3v && rm > 0.99 && gm < REDCOL && bm < REDCOL) ||
	    (c3v && gm > 0.67 && would_colorize_neigh(x, y, xres, yres, pixel, 2))) {
		r = 8.0 * OGET_R(c3v) * rf;
		g = 8.0 * (OGET_G(c3v) * rf + (1.0 - rf) * gf);
		b = 8.0 * (OGET_B(c3v) * rf + (1.0 - rf) * bf);
		a = IGET_A(irgb);
		return IRGBA(r, g, b, a);
	}

	return irgb;
}

static uint32_t sdl_colorbalance(uint32_t irgb, char cr, char cg, char cb, char light, char sat)
{
	int r, g, b, a, grey;

	r = IGET_R(irgb);
	g = IGET_G(irgb);
	b = IGET_B(irgb);
	a = IGET_A(irgb);

	// lightness
	if (light) {
		r += light;
		g += light;
		b += light;
	}

	// saturation
	if (sat) {
		grey = (r + g + b) / 3;
		r = ((r * (20 - sat)) + (grey * sat)) / 20;
		g = ((g * (20 - sat)) + (grey * sat)) / 20;
		b = ((b * (20 - sat)) + (grey * sat)) / 20;
	}

	// color balancing
	cr *= 0.75;
	cg *= 0.75;
	cg *= 0.75;

	r += cr;
	g -= cr / 2;
	b -= cr / 2;
	r -= cg / 2;
	g += cg;
	b -= cg / 2;
	r -= cb / 2;
	g -= cb / 2;
	b += cb;

	if (r < 0) {
		r = 0;
	}
	if (g < 0) {
		g = 0;
	}
	if (b < 0) {
		b = 0;
	}

	if (r > 255) {
		g += (r - 255) / 2;
		b += (r - 255) / 2;
		r = 255;
	}
	if (g > 255) {
		r += (g - 255) / 2;
		b += (g - 255) / 2;
		g = 255;
	}
	if (b > 255) {
		r += (b - 255) / 2;
		g += (b - 255) / 2;
		b = 255;
	}

	if (r > 255) {
		r = 255;
	}
	if (g > 255) {
		g = 255;
	}
	if (b > 255) {
		b = 255;
	}

	irgb = IRGBA(r, g, b, a);

	return irgb;
}

static void sdl_make(struct sdl_texture *st, struct sdl_image *si, int preload)
{
	SDL_Texture *texture;
	int x, y, scale, sink;
	double ix, iy, low_x, low_y, high_x, high_y, dbr, dbg, dbb, dba;
	uint32_t irgb;
#ifdef DEVELOPER
	long long start = SDL_GetTicks64();
#endif

	if (si->xres == 0 || si->yres == 0) {
		scale = 100; // !!! needs better handling !!!
	} else {
		scale = st->scale;
	}

	// hack to adjust the size of mages to old client levels
	// this was originally done during loading from PAKs.
	if (st->sprite >= 160000 && st->sprite < 170000) {
		scale *= 0.88;
	}

	if (scale != 100) {
		st->xres = ceil((double)(si->xres - 1) * scale / 100.0);
		st->yres = ceil((double)(si->yres - 1) * scale / 100.0);

		st->xoff = floor(si->xoff * scale / 100.0 + 0.5);
		st->yoff = floor(si->yoff * scale / 100.0 + 0.5);
	} else {
		st->xres = si->xres;
		st->yres = si->yres;
		st->xoff = si->xoff;
		st->yoff = si->yoff;
	}

	if (st->sink) {
		sink = min(st->sink, max(0, st->yres - 4));
	} else {
		sink = 0;
	}

	if (!preload || preload == 1) {
		if (!(flags_load(st) & SF_DIDALLOC)) {
			// Only allocate if not already allocated (may be set by caller with mutex protection in multi-threaded
			// mode)
#ifdef SDL_FAST_MALLOC
			st->pixel = malloc(st->xres * st->yres * sizeof(uint32_t) * sdl_scale * sdl_scale);
#else
			st->pixel = xmalloc(st->xres * st->yres * sizeof(uint32_t) * sdl_scale * sdl_scale, MEM_SDL_PIXEL);
#endif
			uint16_t *flags_ptr = (uint16_t *)&st->flags;
			__atomic_fetch_or(flags_ptr, SF_DIDALLOC, __ATOMIC_RELEASE);
		}
		// If already allocated, skip allocation but continue to set sdlm_* variables below
	}

	sdlm_sprite = st->sprite;
	sdlm_scale = scale;
	sdlm_pixel = si->pixel;

	if (!preload || preload == 2) {
		if (!(flags_load(st) & SF_DIDALLOC)) {
			fail("cannot make without alloc for sprite %d (%p)", st->sprite, st);
			note("... sprite=%d (%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d)", st->sprite, st->sink, st->freeze,
			    st->scale, st->cr, st->cg, st->cb, st->light, st->sat, st->c1, st->c2, st->c3, st->shine, st->ml,
			    st->ll, st->rl, st->ul, st->dl);
			return;
		}
		if (!(st->pixel)) {
			fail("cannot make: pixel=NULL for sprite %d (%p)", st->sprite, st);
			note("... sprite=%d (%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d)", st->sprite, st->sink, st->freeze,
			    st->scale, st->cr, st->cg, st->cb, st->light, st->sat, st->c1, st->c2, st->c3, st->shine, st->ml,
			    st->ll, st->rl, st->ul, st->dl);
			return;
		}
		if (flags_load(st) & SF_DIDMAKE) {
			fail("double make for sprite %d (%d)", st->sprite, preload);
			note("... sprite=%d (%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d)", st->sprite, st->sink, st->freeze,
			    st->scale, st->cr, st->cg, st->cb, st->light, st->sat, st->c1, st->c2, st->c3, st->shine, st->ml,
			    st->ll, st->rl, st->ul, st->dl);
			return;
		}

#ifdef DEVELOPER
		start = SDL_GetTicks64();
#endif

		for (y = 0; y < st->yres * sdl_scale; y++) {
			for (x = 0; x < st->xres * sdl_scale; x++) {
				if (scale != 100) {
					ix = x * 100.0 / scale;
					iy = y * 100.0 / scale;

					if (ceil(ix) >= si->xres * sdl_scale) {
						ix = si->xres * sdl_scale - 1.001;
					}

					if (ceil(iy) >= si->yres * sdl_scale) {
						iy = si->yres * sdl_scale - 1.001;
					}

					high_x = ix - floor(ix);
					high_y = iy - floor(iy);
					low_x = 1 - high_x;
					low_y = 1 - high_y;

					irgb = si->pixel[(int)(floor(ix) + floor(iy) * si->xres * sdl_scale)];

					if (st->c1 || st->c2 || st->c3) {
						irgb = sdl_colorize_pix2(irgb, st->c1, st->c2, st->c3, floor(ix), floor(iy), si->xres, si->yres,
						    si->pixel, st->sprite);
					}
					dba = IGET_A(irgb) * low_x * low_y;
					dbr = IGET_R(irgb) * low_x * low_y;
					dbg = IGET_G(irgb) * low_x * low_y;
					dbb = IGET_B(irgb) * low_x * low_y;

					irgb = si->pixel[(int)(ceil(ix) + floor(iy) * si->xres * sdl_scale)];

					if (st->c1 || st->c2 || st->c3) {
						irgb = sdl_colorize_pix2(irgb, st->c1, st->c2, st->c3, ceil(ix), floor(iy), si->xres, si->yres,
						    si->pixel, st->sprite);
					}
					dba += IGET_A(irgb) * high_x * low_y;
					dbr += IGET_R(irgb) * high_x * low_y;
					dbg += IGET_G(irgb) * high_x * low_y;
					dbb += IGET_B(irgb) * high_x * low_y;

					irgb = si->pixel[(int)(floor(ix) + ceil(iy) * si->xres * sdl_scale)];

					if (st->c1 || st->c2 || st->c3) {
						irgb = sdl_colorize_pix2(irgb, st->c1, st->c2, st->c3, floor(ix), ceil(iy), si->xres, si->yres,
						    si->pixel, st->sprite);
					}
					dba += IGET_A(irgb) * low_x * high_y;
					dbr += IGET_R(irgb) * low_x * high_y;
					dbg += IGET_G(irgb) * low_x * high_y;
					dbb += IGET_B(irgb) * low_x * high_y;

					irgb = si->pixel[(int)(ceil(ix) + ceil(iy) * si->xres * sdl_scale)];

					if (st->c1 || st->c2 || st->c3) {
						irgb = sdl_colorize_pix2(irgb, st->c1, st->c2, st->c3, ceil(ix), ceil(iy), si->xres, si->yres,
						    si->pixel, st->sprite);
					}
					dba += IGET_A(irgb) * high_x * high_y;
					dbr += IGET_R(irgb) * high_x * high_y;
					dbg += IGET_G(irgb) * high_x * high_y;
					dbb += IGET_B(irgb) * high_x * high_y;

					irgb = IRGBA((int)dbr, (int)dbg, (int)dbb, (int)dba);

				} else {
					irgb = si->pixel[x + y * si->xres * sdl_scale];
					if (st->c1 || st->c2 || st->c3) {
						irgb = sdl_colorize_pix2(
						    irgb, st->c1, st->c2, st->c3, x, y, si->xres, si->yres, si->pixel, st->sprite);
					}
				}

				if (st->cr || st->cg || st->cb || st->light || st->sat) {
					irgb = sdl_colorbalance(irgb, st->cr, st->cg, st->cb, st->light, st->sat);
				}
				if (st->shine) {
					irgb = sdl_shine_pix(irgb, st->shine);
				}

				if (st->ll != st->ml || st->rl != st->ml || st->ul != st->ml || st->dl != st->ml) {
					int r, g, b, a;
					int r1 = 0, r2 = 0, r3 = 0, r4 = 0, r5 = 0;
					int g1 = 0, g2 = 0, g3 = 0, g4 = 0, g5 = 0;
					int b1 = 0, b2 = 0, b3 = 0, b4 = 0, b5 = 0;
					int v1, v2, v3, v4, v5 = 0;
					int div;


					if (y < 10 * sdl_scale + (20 * sdl_scale - abs(20 * sdl_scale - x)) / 2) {
						// This part calculates a floor tile, or the top of a wall tile
						if (x / 2 < 20 * sdl_scale - y) {
							v2 = -(x / 2 - (20 * sdl_scale - y));
							r2 = IGET_R(sdl_light(st->ll, irgb));
							g2 = IGET_G(sdl_light(st->ll, irgb));
							b2 = IGET_B(sdl_light(st->ll, irgb));
						} else {
							v2 = 0;
						}
						if (x / 2 > 20 * sdl_scale - y) {
							v3 = (x / 2 - (20 * sdl_scale - y));
							r3 = IGET_R(sdl_light(st->rl, irgb));
							g3 = IGET_G(sdl_light(st->rl, irgb));
							b3 = IGET_B(sdl_light(st->rl, irgb));
						} else {
							v3 = 0;
						}
						if (x / 2 > y) {
							v4 = (x / 2 - y);
							r4 = IGET_R(sdl_light(st->ul, irgb));
							g4 = IGET_G(sdl_light(st->ul, irgb));
							b4 = IGET_B(sdl_light(st->ul, irgb));
						} else {
							v4 = 0;
						}
						if (x / 2 < y) {
							v5 = -(x / 2 - y);
							r5 = IGET_R(sdl_light(st->dl, irgb));
							g5 = IGET_G(sdl_light(st->dl, irgb));
							b5 = IGET_B(sdl_light(st->dl, irgb));
						} else {
							v5 = 0;
						}

						v1 = 20 * sdl_scale - (v2 + v3 + v4 + v5);
						r1 = IGET_R(sdl_light(st->ml, irgb));
						g1 = IGET_G(sdl_light(st->ml, irgb));
						b1 = IGET_B(sdl_light(st->ml, irgb));
					} else {
						// This is for the lower part (left side and front as seen on the screen)
						if (x < 10 * sdl_scale) {
							v2 = (10 * sdl_scale - x) * 2 - 2;
							r2 = IGET_R(sdl_light(st->ll, irgb));
							g2 = IGET_G(sdl_light(st->ll, irgb));
							b2 = IGET_B(sdl_light(st->ll, irgb));
						} else {
							v2 = 0;
						}
						if (x > 10 * sdl_scale && x < 20 * sdl_scale) {
							v3 = (x - 10 * sdl_scale) * 2 - 2;
							r3 = IGET_R(sdl_light(st->rl, irgb));
							g3 = IGET_G(sdl_light(st->rl, irgb));
							b3 = IGET_B(sdl_light(st->rl, irgb));
						} else {
							v3 = 0;
						}
						if (x > 20 * sdl_scale && x < 30 * sdl_scale) {
							v5 = (10 * sdl_scale - (x - 20 * sdl_scale)) * 2 - 2;
							r5 = IGET_R(sdl_light(st->dl, irgb));
							g5 = IGET_G(sdl_light(st->dl, irgb));
							b5 = IGET_B(sdl_light(st->dl, irgb));
						} else {
							v5 = 0;
						}
						if (x > 30 * sdl_scale) {
							if (x < 40 * sdl_scale) {
								v4 = (x - 30 * sdl_scale) * 2 - 2;
							} else {
								v4 = 0;
							}
							r4 = IGET_R(sdl_light(st->ul, irgb));
							g4 = IGET_G(sdl_light(st->ul, irgb));
							b4 = IGET_B(sdl_light(st->ul, irgb));
						} else {
							v4 = 0;
						}

						v1 = 20 * sdl_scale - (v2 + v3 + v4 + v5) / 2;
						r1 = IGET_R(sdl_light(st->ml, irgb));
						g1 = IGET_G(sdl_light(st->ml, irgb));
						b1 = IGET_B(sdl_light(st->ml, irgb));
					}

					div = v1 + v2 + v3 + v4 + v5;

					if (div == 0) {
						a = 0;
						r = g = b = 0;
					} else {
						a = IGET_A(irgb);
						r = (r1 * v1 + r2 * v2 + r3 * v3 + r4 * v4 + r5 * v5) / div;
						g = (g1 * v1 + g2 * v2 + g3 * v3 + g4 * v4 + g5 * v5) / div;
						b = (b1 * v1 + b2 * v2 + b3 * v3 + b4 * v4 + b5 * v5) / div;
					}

					irgb = IRGBA(r, g, b, a);

				} else {
					irgb = sdl_light(st->ml, irgb);
				}

				if (sink) {
					if (st->yres * sdl_scale - sink * sdl_scale < y) {
						irgb &= 0xffffff; // zero alpha to make it transparent
					}
				}

				if (st->freeze) {
					irgb = sdl_freeze(st->freeze, irgb);
				}

				st->pixel[x + y * st->xres * sdl_scale] = irgb;
			}
		}
		uint16_t *flags_ptr = (uint16_t *)&st->flags;
		__atomic_fetch_or(flags_ptr, SF_DIDMAKE, __ATOMIC_RELEASE);

#ifdef DEVELOPER
		if (preload) {
			sdl_time_preload += SDL_GetTicks64() - start;
		} else {
			sdl_time_make += SDL_GetTicks64() - start;
		}
#endif
	}

	if (!preload || preload == 3) {
		if (!(flags_load(st) & SF_DIDMAKE)) {
			fail("cannot texture without make for sprite %d (%d)", st->sprite, preload);
			// note("... sprite=%d
			// (%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d)",st->sprite,st->sink,st->freeze,st->scale,st->cr,st->cg,st->cb,st->light,st->sat,st->c1,st->c2,st->c3,st->shine,st->ml,st->ll,st->rl,st->ul,st->dl);
			return;
		}
		if (flags_load(st) & SF_DIDTEX) {
			fail("double texture for sprite %d (%d)", st->sprite, preload);
			// note("... sprite=%d
			// (%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d)",st->sprite,st->sink,st->freeze,st->scale,st->cr,st->cg,st->cb,st->light,st->sat,st->c1,st->c2,st->c3,st->shine,st->ml,st->ll,st->rl,st->ul,st->dl);
			return;
		}

#ifdef DEVELOPER
		start = SDL_GetTicks64();
#endif

		if (st->xres > 0 && st->yres > 0) {
			texture = SDL_CreateTexture(
			    sdlren, SDL_PIXELFORMAT_ARGB8888, SDL_TEXTUREACCESS_STATIC, st->xres * sdl_scale, st->yres * sdl_scale);
			if (!texture) {
				warn("SDL_texture Error: %s in sprite %d (%s, %d,%d) preload=%d", SDL_GetError(), st->sprite, st->text,
				    st->xres, st->yres, preload);
				return;
			}
			SDL_UpdateTexture(texture, NULL, st->pixel, st->xres * sizeof(uint32_t) * sdl_scale);
			SDL_SetTextureBlendMode(texture, SDL_BLENDMODE_BLEND);
			// Update memory accounting when texture is actually created
			__atomic_add_fetch(&mem_tex, st->xres * st->yres * sizeof(uint32_t), __ATOMIC_RELAXED);
		} else {
			texture = NULL;
		}
#ifdef SDL_FAST_MALLOC
		free(st->pixel);
#else
		xfree(st->pixel);
#endif
		st->pixel = NULL;
		st->tex = texture;

		uint16_t *flags_ptr = (uint16_t *)&st->flags;
		__atomic_fetch_or(flags_ptr, SF_DIDTEX, __ATOMIC_RELEASE);

#ifdef DEVELOPER
		sdl_time_tex += SDL_GetTicks64() - start;
#endif
	}
}

static void sdl_tx_best(int stx)
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

SDL_Texture *sdl_maketext(const char *text, struct ddfont *font, uint32_t color, int flags);

static int sdl_pre_worker(struct zip_handles *zips);
static void neutralize_stale_jobs(int stx);

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
		return STX_NONE; // Return before locking
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
					sdl_render_wait_count++;
				}
#endif

				// In single-threaded mode, process queue to make progress
				if (!sdl_multi) {
					sdl_pre_worker(NULL);
				}

				SDL_Delay(1);

				if (panic++ > 100) {
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
				sdl_render_wait += wait_time;
#ifdef DEVELOPER_NOISY
				// Suppress warnings during boot - only show "real" stalls (>= 10ms)
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

				if (panic++ > 100) {
					uint16_t *flags_ptr = (uint16_t *)&sdlt[stx].flags;
					uint16_t f2 = __atomic_load_n(flags_ptr, __ATOMIC_ACQUIRE);
					warn("Timeout waiting to evict stx=%d sprite=%d (flags=0x%04x)", stx, sdlt[stx].sprite, f2);

					// If a job is actually in progress, do NOT evict this entry
					if (f2 & SF_CLAIMJOB) {
						// Worker still owns this entry, try previous LRU
						can_evict = 0;
						int candidate = sdlt[stx].prev;
						if (candidate == STX_NONE) {
							// No more candidates, give up
							return STX_NONE;
						}
						// Only neutralize queue entries if nothing is actually claiming it
						__atomic_fetch_and(flags_ptr, (uint16_t)~SF_INQUEUE, __ATOMIC_RELEASE);
						neutralize_stale_jobs(stx);
						stx = candidate;
						break;
					}

					// Only neutralize queue entries if nothing is actually claiming it
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
		sdlt[stx].tex = sdl_maketext(text, (struct ddfont *)text_font, text_color, text_flags);
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

static void sdl_blit_tex(
    SDL_Texture *tex, int sx, int sy, int clipsx, int clipsy, int clipex, int clipey, int x_offset, int y_offset)
{
	int addx = 0, addy = 0, dx, dy;
	SDL_Rect dr, sr;
#ifdef DEVELOPER
	long long start = SDL_GetTicks64();
#endif

	SDL_QueryTexture(tex, NULL, NULL, &dx, &dy);

	dx /= sdl_scale;
	dy /= sdl_scale;
	if (sx < clipsx) {
		addx = clipsx - sx;
		dx -= addx;
		sx = clipsx;
	}
	if (sy < clipsy) {
		addy = clipsy - sy;
		dy -= addy;
		sy = clipsy;
	}
	if (sx + dx >= clipex) {
		dx = clipex - sx;
	}
	if (sy + dy >= clipey) {
		dy = clipey - sy;
	}
	dx *= sdl_scale;
	dy *= sdl_scale;

	dr.x = (sx + x_offset) * sdl_scale;
	dr.w = dx;
	dr.y = (sy + y_offset) * sdl_scale;
	dr.h = dy;

	sr.x = addx * sdl_scale;
	sr.w = dx;
	sr.y = addy * sdl_scale;
	sr.h = dy;

	SDL_RenderCopy(sdlren, tex, &sr, &dr);

#ifdef DEVELOPER
	sdl_time_blit += SDL_GetTicks64() - start;
#endif
}

void sdl_blit(int stx, int sx, int sy, int clipsx, int clipsy, int clipex, int clipey, int x_offset, int y_offset)
{
	if (sdlt[stx].tex) {
		sdl_blit_tex(sdlt[stx].tex, sx, sy, clipsx, clipsy, clipex, clipey, x_offset, y_offset);
	}
}

#define DD_LEFT    0
#define DD_CENTER  1
#define DD_RIGHT   2
#define DD_SHADE   4
#define DD_LARGE   0
#define DD_SMALL   8
#define DD_FRAME   16
#define DD_BIG     32
#define DD_NOCACHE 64

#define DD__SHADEFONT 128
#define DD__FRAMEFONT 256

#define R16TO32(color) (int)(((((color) >> 10) & 31) / 31.0f) * 255.0f)
#define G16TO32(color) (int)(((((color) >> 5) & 31) / 31.0f) * 255.0f)
#define B16TO32(color) (int)((((color) & 31) / 31.0f) * 255.0f)

#define MAXFONTHEIGHT 64

SDL_Texture *sdl_maketext(const char *text, struct ddfont *font, uint32_t color, int flags)
{
	uint32_t *pixel, *dst;
	unsigned char *rawrun;
	int x, y = 0, sizex, sizey = 0, sx = 0;
	const char *c, *otext = text;
#ifdef DEVELOPER
	long long start = SDL_GetTicks64();
#endif

	for (sizex = 0, c = text; *c; c++) {
		sizex += font[*c].dim * sdl_scale;
	}

	if (flags & (DD__FRAMEFONT | DD__SHADEFONT)) {
		sizex += sdl_scale * 2;
	}

#ifdef SDL_FAST_MALLOC
	pixel = calloc(sizex * MAXFONTHEIGHT, sizeof(uint32_t));
#else
	pixel = xmalloc(sizex * MAXFONTHEIGHT * sizeof(uint32_t), MEM_SDL_PIXEL2);
#endif
	if (pixel == NULL) {
		return NULL;
	}

	while (*text && *text != DDT) {
		if (*text < 0) {
			note("PANIC: char over limit");
			text++;
			continue;
		}

		rawrun = font[*text].raw;

		x = sx;
		y = 0;

		dst = pixel + x + y * sizex;

		while (*rawrun != 255) {
			if (*rawrun == 254) {
				y++;
				x = sx;
				rawrun++;
				dst = pixel + x + y * sizex;
				if (y > sizey) {
					sizey = y;
				}
				continue;
			}

			dst += *rawrun;
			x += *rawrun;

			rawrun++;
			*dst = color;
		}
		sx += font[*text++].dim * sdl_scale;
	}

	if (sizex < 1) {
		sizex = 1;
	}
	if (sizey < 1) {
		sizey = 1;
	}

	sizey++;
#ifdef DEVELOPER
	sdl_time_text += SDL_GetTicks64() - start;
	start = SDL_GetTicks64();
#endif
	SDL_Texture *texture = SDL_CreateTexture(sdlren, SDL_PIXELFORMAT_ARGB8888, SDL_TEXTUREACCESS_STATIC, sizex, sizey);
	if (texture) {
		SDL_UpdateTexture(texture, NULL, pixel, sizex * sizeof(uint32_t));
		SDL_SetTextureBlendMode(texture, SDL_BLENDMODE_BLEND);
	} else {
		warn("SDL_texture Error: %s maketext (%s)", SDL_GetError(), otext);
	}
#ifdef SDL_FAST_MALLOC
	free(pixel);
#else
	xfree(pixel);
#endif
#ifdef DEVELOPER
	sdl_time_tex += SDL_GetTicks64() - start;
#endif

	return texture;
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

void sdl_exit(void)
{
	int n;

	if (sdl_multi && prethreads) {
		SDL_AtomicSet(&pre_quit, 1);
		for (n = 0; n < sdl_multi; n++) {
			SDL_WaitThread(prethreads[n], NULL);
		}
		if (worker_zips) {
			for (n = 0; n < sdl_multi; n++) {
				if (worker_zips[n].zip1) {
					zip_close(worker_zips[n].zip1);
				}
				if (worker_zips[n].zip1p) {
					zip_close(worker_zips[n].zip1p);
				}
				if (worker_zips[n].zip1m) {
					zip_close(worker_zips[n].zip1m);
				}
				if (worker_zips[n].zip2) {
					zip_close(worker_zips[n].zip2);
				}
				if (worker_zips[n].zip2p) {
					zip_close(worker_zips[n].zip2p);
				}
				if (worker_zips[n].zip2m) {
					zip_close(worker_zips[n].zip2m);
				}
			}
			xfree(worker_zips);
			worker_zips = NULL;
		}
		xfree(prethreads);
		prethreads = NULL;
	}

	if (premutex) {
		SDL_DestroyMutex(premutex);
		premutex = NULL;
	}
	if (sdli_state) {
		xfree(sdli_state);
		sdli_state = NULL;
	}
	if (sdl_zip1) {
		zip_close(sdl_zip1);
	}
	if (sdl_zip1m) {
		zip_close(sdl_zip1m);
	}
	if (sdl_zip1p) {
		zip_close(sdl_zip1p);
	}
	if (sdl_zip2) {
		zip_close(sdl_zip2);
	}
	if (sdl_zip2m) {
		zip_close(sdl_zip2m);
	}
	if (sdl_zip2p) {
		zip_close(sdl_zip2p);
	}

	if (game_options & GO_SOUND) {
		Mix_Quit();
	}
#ifdef DEVELOPER
	sdl_dump_spritecache();
#endif
}

long long sdl_get_mem_tex(void)
{
	return (long long)__atomic_load_n(&mem_tex, __ATOMIC_RELAXED);
}

int sdl_drawtext(int sx, int sy, unsigned short int color, int flags, const char *text, struct ddfont *font, int clipsx,
    int clipsy, int clipex, int clipey, int x_offset, int y_offset)
{
	int dx, stx;
	SDL_Texture *tex;
	int r, g, b, a;
	const char *c;

	if (!*text) {
		return sx;
	}

	r = R16TO32(color);
	g = G16TO32(color);
	b = B16TO32(color);
	a = 255;

	if (flags & DD_NOCACHE) {
		tex = sdl_maketext(text, font, IRGBA(r, g, b, a), flags);
	} else {
		stx = sdl_tx_load(
		    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, text, IRGBA(r, g, b, a), flags, font, 0, 0, 0);
		tex = sdlt[stx].tex;
	}

	for (dx = 0, c = text; *c; c++) {
		dx += font[*c].dim;
	}

	if (tex) {
		if (flags & DD_CENTER) {
			sx -= dx / 2;
		} else if (flags & DD_RIGHT) {
			sx -= dx;
		}

		sdl_blit_tex(tex, sx, sy, clipsx, clipsy, clipex, clipey, x_offset, y_offset);

		if (flags & DD_NOCACHE) {
			SDL_DestroyTexture(tex);
		}
	}

	return sx + dx;
}

void sdl_rect(int sx, int sy, int ex, int ey, unsigned short int color, int clipsx, int clipsy, int clipex, int clipey,
    int x_offset, int y_offset)
{
	int r, g, b, a;
	SDL_Rect rc;

	r = R16TO32(color);
	g = G16TO32(color);
	b = B16TO32(color);
	a = 255;

	if (sx < clipsx) {
		sx = clipsx;
	}
	if (sy < clipsy) {
		sy = clipsy;
	}
	if (ex > clipex) {
		ex = clipex;
	}
	if (ey > clipey) {
		ey = clipey;
	}

	if (sx > ex || sy > ey) {
		return;
	}

	rc.x = (sx + x_offset) * sdl_scale;
	rc.w = (ex - sx) * sdl_scale;
	rc.y = (sy + y_offset) * sdl_scale;
	rc.h = (ey - sy) * sdl_scale;

	SDL_SetRenderDrawColor(sdlren, r, g, b, a);
	SDL_RenderFillRect(sdlren, &rc);
}

void sdl_shaded_rect(int sx, int sy, int ex, int ey, unsigned short int color, unsigned short alpha, int clipsx,
    int clipsy, int clipex, int clipey, int x_offset, int y_offset)
{
	int r, g, b, a;
	SDL_Rect rc;

	r = R16TO32(color);
	g = G16TO32(color);
	b = B16TO32(color);
	a = alpha;

	if (sx < clipsx) {
		sx = clipsx;
	}
	if (sy < clipsy) {
		sy = clipsy;
	}
	if (ex > clipex) {
		ex = clipex;
	}
	if (ey > clipey) {
		ey = clipey;
	}

	if (sx > ex || sy > ey) {
		return;
	}

	rc.x = (sx + x_offset) * sdl_scale;
	rc.w = (ex - sx) * sdl_scale;
	rc.y = (sy + y_offset) * sdl_scale;
	rc.h = (ey - sy) * sdl_scale;

	SDL_SetRenderDrawColor(sdlren, r, g, b, a);
	SDL_SetRenderDrawBlendMode(sdlren, SDL_BLENDMODE_BLEND);
	SDL_RenderFillRect(sdlren, &rc);
}

void sdl_pixel(int x, int y, unsigned short color, int x_offset, int y_offset)
{
	int r, g, b, a, i;
	SDL_Point pt[16];

	r = R16TO32(color);
	g = G16TO32(color);
	b = B16TO32(color);
	a = 255;

	SDL_SetRenderDrawColor(sdlren, r, g, b, a);
	switch (sdl_scale) {
	case 1:
		SDL_RenderDrawPoint(sdlren, x + x_offset, y + y_offset);
		return;
	case 2:
		pt[0].x = (x + x_offset) * sdl_scale;
		pt[0].y = (y + y_offset) * sdl_scale;
		pt[1].x = pt[0].x + 1;
		pt[1].y = pt[0].y;
		pt[2].x = pt[0].x;
		pt[2].y = pt[0].y + 1;
		pt[3].x = pt[0].x + 1;
		pt[3].y = pt[0].y + 1;
		i = 4;
		break;
	case 3:
		pt[0].x = (x + x_offset) * sdl_scale;
		pt[0].y = (y + y_offset) * sdl_scale;
		pt[1].x = pt[0].x + 1;
		pt[1].y = pt[0].y;
		pt[2].x = pt[0].x;
		pt[2].y = pt[0].y + 1;
		pt[3].x = pt[0].x + 1;
		pt[3].y = pt[0].y + 1;
		pt[4].x = pt[0].x + 2;
		pt[4].y = pt[0].y;
		pt[5].x = pt[0].x;
		pt[5].y = pt[0].y + 2;
		pt[6].x = pt[0].x + 2;
		pt[6].y = pt[0].y + 2;
		pt[7].x = pt[0].x + 2;
		pt[7].y = pt[0].y + 1;
		pt[8].x = pt[0].x + 1;
		pt[8].y = pt[0].y + 2;
		i = 9;
		break;
	case 4:
		pt[0].x = (x + x_offset) * sdl_scale;
		pt[0].y = (y + y_offset) * sdl_scale;
		pt[1].x = pt[0].x + 1;
		pt[1].y = pt[0].y;
		pt[2].x = pt[0].x;
		pt[2].y = pt[0].y + 1;
		pt[3].x = pt[0].x + 1;
		pt[3].y = pt[0].y + 1;
		pt[4].x = pt[0].x + 2;
		pt[4].y = pt[0].y;
		pt[5].x = pt[0].x;
		pt[5].y = pt[0].y + 2;
		pt[6].x = pt[0].x + 2;
		pt[6].y = pt[0].y + 2;
		pt[7].x = pt[0].x + 2;
		pt[7].y = pt[0].y + 1;
		pt[8].x = pt[0].x + 1;
		pt[8].y = pt[0].y + 2;
		pt[9].x = pt[0].x + 3;
		pt[9].y = pt[0].y;
		pt[10].x = pt[0].x + 3;
		pt[10].y = pt[0].y + 1;
		pt[11].x = pt[0].x + 3;
		pt[11].y = pt[0].y + 2;
		pt[12].x = pt[0].x + 3;
		pt[12].y = pt[0].y + 3;
		pt[13].x = pt[0].x;
		pt[13].y = pt[0].y + 3;
		pt[14].x = pt[0].x + 1;
		pt[14].y = pt[0].y + 3;
		pt[15].x = pt[0].x + 2;
		pt[15].y = pt[0].y + 3;
		i = 16;
		break;
	default:
		warn("unsupported scale %d in sdl_pixel()", sdl_scale);
		return;
	}
	SDL_RenderDrawPoints(sdlren, pt, i);
}

void sdl_line(int fx, int fy, int tx, int ty, unsigned short color, int clipsx, int clipsy, int clipex, int clipey,
    int x_offset, int y_offset)
{
	int r, g, b, a;

	r = R16TO32(color);
	g = G16TO32(color);
	b = B16TO32(color);
	a = 255;

	if (fx < clipsx) {
		fx = clipsx;
	}
	if (fy < clipsy) {
		fy = clipsy;
	}
	if (fx >= clipex) {
		fx = clipex - 1;
	}
	if (fy >= clipey) {
		fy = clipey - 1;
	}

	if (tx < clipsx) {
		tx = clipsx;
	}
	if (ty < clipsy) {
		ty = clipsy;
	}
	if (tx >= clipex) {
		tx = clipex - 1;
	}
	if (ty >= clipey) {
		ty = clipey - 1;
	}

	fx += x_offset;
	tx += x_offset;
	fy += y_offset;
	ty += y_offset;

	SDL_SetRenderDrawColor(sdlren, r, g, b, a);
	// TODO: This is a thinner line when scaled up. It looks surprisingly good. Maybe keep it this way?
	SDL_RenderDrawLine(sdlren, fx * sdl_scale, fy * sdl_scale, tx * sdl_scale, ty * sdl_scale);
}

void gui_sdl_keyproc(int wparam);
void gui_sdl_mouseproc(int x, int y, int but, int clicks);
void gui_sdl_draghack(void);
void cmd_proc(int key);
void context_keyup(int key);

void sdl_loop(void)
{
	SDL_Event event;

	while (SDL_PollEvent(&event)) {
		switch (event.type) {
		case SDL_QUIT:
			quit = 1;
			break;
		case SDL_KEYDOWN:
			gui_sdl_keyproc(event.key.keysym.sym);
			break;
		case SDL_KEYUP:
			context_keyup(event.key.keysym.sym);
			break;
		case SDL_TEXTINPUT:
			cmd_proc(event.text.text[0]);
			break;
		case SDL_MOUSEMOTION:
			gui_sdl_mouseproc(event.motion.x, event.motion.y, SDL_MOUM_NONE, 0);
			break;
		case SDL_MOUSEBUTTONDOWN:
			if (event.button.button == SDL_BUTTON_LEFT) {
				gui_sdl_mouseproc(event.motion.x, event.motion.y, SDL_MOUM_LDOWN, event.button.clicks);
			}
			if (event.button.button == SDL_BUTTON_MIDDLE) {
				gui_sdl_mouseproc(event.motion.x, event.motion.y, SDL_MOUM_MDOWN, event.button.clicks);
			}
			if (event.button.button == SDL_BUTTON_RIGHT) {
				gui_sdl_mouseproc(event.motion.x, event.motion.y, SDL_MOUM_RDOWN, event.button.clicks);
			}
			break;
		case SDL_MOUSEBUTTONUP:
			if (event.button.button == SDL_BUTTON_LEFT) {
				gui_sdl_mouseproc(event.motion.x, event.motion.y, SDL_MOUM_LUP, event.button.clicks);
			}
			if (event.button.button == SDL_BUTTON_MIDDLE) {
				gui_sdl_mouseproc(event.motion.x, event.motion.y, SDL_MOUM_MUP, event.button.clicks);
			}
			if (event.button.button == SDL_BUTTON_RIGHT) {
				gui_sdl_mouseproc(event.motion.x, event.motion.y, SDL_MOUM_RUP, event.button.clicks);
			}
			break;
		case SDL_MOUSEWHEEL:
			gui_sdl_mouseproc(event.wheel.x, event.wheel.y, SDL_MOUM_WHEEL, 0);
			break;
		case SDL_WINDOWEVENT:
#ifdef ENABLE_DRAGHACK
			if (event.window.event == SDL_WINDOWEVENT_FOCUS_GAINED) {
				int x, y;
				Uint32 mouseState = SDL_GetMouseState(&x, &y);
				if (mouseState & SDL_BUTTON(SDL_BUTTON_LEFT)) {
					gui_sdl_draghack();
				}
			}
#endif
			break;
		default:
			break;
		}
	}
}

void sdl_set_cursor_pos(int x, int y)
{
	SDL_WarpMouseInWindow(sdlwnd, x, y);
}

void sdl_show_cursor(int flag)
{
	SDL_ShowCursor(flag ? SDL_ENABLE : SDL_DISABLE);
}

void sdl_capture_mouse(int flag)
{
	SDL_CaptureMouse(flag);
}

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

DLL_EXPORT uint32_t *sdl_load_png(char *filename, int *dx, int *dy)
{
	int x, y, xres, yres, tmp, r, g, b, a;
	int format;
	unsigned char **row;
	uint32_t *pixel;
	FILE *fp;
	png_structp png_ptr;
	png_infop info_ptr;

	fp = fopen(filename, "rb");
	if (!fp) {
		return NULL;
	}

	png_ptr = png_create_read_struct(PNG_LIBPNG_VER_STRING, NULL, NULL, NULL);
	if (!png_ptr) {
		fclose(fp);
		warn("create read\n");
		return NULL;
	}

	info_ptr = png_create_info_struct(png_ptr);
	if (!info_ptr) {
		fclose(fp);
		png_destroy_read_struct(&png_ptr, (png_infopp)NULL, (png_infopp)NULL);
		warn("create info1\n");
		return NULL;
	}

	png_init_io(png_ptr, fp);
	png_set_strip_16(png_ptr);
	png_read_png(png_ptr, info_ptr, PNG_TRANSFORM_PACKING, NULL);

	row = png_get_rows(png_ptr, info_ptr);
	if (!row) {
		fclose(fp);
		png_destroy_read_struct(&png_ptr, &info_ptr, (png_infopp)NULL);
		warn("read row\n");
		return NULL;
	}

	xres = png_get_image_width(png_ptr, info_ptr);
	yres = png_get_image_height(png_ptr, info_ptr);

	tmp = png_get_rowbytes(png_ptr, info_ptr);

	if (tmp == xres * 3) {
		format = 3;
	} else if (tmp == xres * 4) {
		format = 4;
	} else {
		fclose(fp);
		png_destroy_read_struct(&png_ptr, &info_ptr, (png_infopp)NULL);
		warn("rowbytes!=xres*4 (%d)", tmp);
		return NULL;
	}

	if (png_get_bit_depth(png_ptr, info_ptr) != 8) {
		fclose(fp);
		png_destroy_read_struct(&png_ptr, &info_ptr, (png_infopp)NULL);
		warn("bit depth!=8\n");
		return NULL;
	}
	if (png_get_channels(png_ptr, info_ptr) != format) {
		fclose(fp);
		png_destroy_read_struct(&png_ptr, &info_ptr, (png_infopp)NULL);
		warn("channels!=format\n");
		return NULL;
	}

	// prescan
	if (dx) {
		*dx = xres;
	}
	if (dy) {
		*dy = yres;
	}

#ifdef SDL_FAST_MALLOC
	pixel = malloc(xres * yres * sizeof(uint32_t));
#else
	pixel = xmalloc(xres * yres * sizeof(uint32_t), MEM_TEMP8);
#endif

	if (!pixel) {
		fclose(fp);
		png_destroy_read_struct(&png_ptr, &info_ptr, (png_infopp)NULL);
		warn("failed to allocate memory for pixel buffer\n");
		return NULL;
	}

	if (format == 4) {
		for (y = 0; y < yres; y++) {
			for (x = 0; x < xres; x++) {
				r = row[y][x * 4 + 0];
				g = row[y][x * 4 + 1];
				b = row[y][x * 4 + 2];
				a = row[y][x * 4 + 3];

				if (a) {
					r = min(255, r * 255 / a);
					g = min(255, g * 255 / a);
					b = min(255, b * 255 / a);
				} else {
					r = g = b = 0;
				}

				pixel[x + y * xres] = IRGBA(r, g, b, a);
			}
		}
	} else {
		for (y = 0; y < yres; y++) {
			for (x = 0; x < xres; x++) {
				r = row[y][x * 3 + 0];
				g = row[y][x * 3 + 1];
				b = row[y][x * 3 + 2];
				a = 255;

				pixel[x + y * xres] = IRGBA(r, g, b, a);
			}
		}
	}

	png_destroy_read_struct(&png_ptr, &info_ptr, (png_infopp)NULL);
	fclose(fp);

	return pixel;
}

/* This function is a hack. It can only load one specific type of
   Windows cursor file: 32x32 pixels with 1 bit depth. */

SDL_Cursor *sdl_create_cursor(char *filename)
{
	FILE *fp;
	unsigned char mask[128], data[128], buf[326];
	unsigned char mask2[128 * 16] = {0}, data2[128 * 16] = {0};

	fp = fopen(filename, "rb");
	if (!fp) {
		warn("SDL Error: Could not open cursor file %s.\n", filename);
		return NULL;
	}

	if (fread(buf, 1, 326, fp) != 326) {
		warn("SDL Error: Read cursor file failed.\n");
		fclose(fp);
		return NULL;
	}
	fclose(fp);

	// translate .cur
	for (int i = 0; i < 32; i++) {
		for (int j = 0; j < 4; j++) {
			data[i * 4 + j] = (~buf[322 - i * 4 + j]) & (~buf[194 - i * 4 + j]);
			mask[i * 4 + j] = buf[194 - i * 4 + j];
		}
	}

	// scale up if needed and add frame to cross
	static char cross[11][11] = {{0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0}, {0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0},
	    {0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0}, {0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0}, {1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1},
	    {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1}, {1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1}, {0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0},
	    {0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0}, {0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0}, {0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0}};
	int dst, src, i1, b1, i2, b2, y1, y2;

	for (y2 = 0; y2 < 32 * sdl_scale; y2++) {
		y1 = y2 / sdl_scale;

		for (dst = 0; dst < 32 * sdl_scale; dst++) {
			src = dst / sdl_scale;

			i1 = src / 8 + y1 * 4;
			b1 = 128 >> (src & 7);

			i2 = dst / 8 + y2 * 4 * sdl_scale;
			b2 = 128 >> (dst & 7);

			if (src < 11 && y1 < 11 && cross[y1][src]) {
				data2[i2] |= b2;
				mask2[i2] |= b2;
			} else {
				if (data[i1] & b1) {
					data2[i2] |= b2;
				} else {
					data2[i2] &= ~b2;
				}
				if (mask[i1] & b1) {
					mask2[i2] |= b2;
				} else {
					mask2[i2] &= ~b2;
				}
			}
		}
	}
	return SDL_CreateCursor(data2, mask2, 32 * sdl_scale, 32 * sdl_scale, 6 * sdl_scale, 6 * sdl_scale);
}

int sdl_create_cursors(void)
{
	curs[SDL_CUR_c_only] = sdl_create_cursor("res/cursor/c_only.cur");
	curs[SDL_CUR_c_take] = sdl_create_cursor("res/cursor/c_take.cur");
	curs[SDL_CUR_c_drop] = sdl_create_cursor("res/cursor/c_drop.cur");
	curs[SDL_CUR_c_attack] = sdl_create_cursor("res/cursor/c_atta.cur");
	curs[SDL_CUR_c_raise] = sdl_create_cursor("res/cursor/c_rais.cur");
	curs[SDL_CUR_c_give] = sdl_create_cursor("res/cursor/c_give.cur");
	curs[SDL_CUR_c_use] = sdl_create_cursor("res/cursor/c_use.cur");
	curs[SDL_CUR_c_usewith] = sdl_create_cursor("res/cursor/c_usew.cur");
	curs[SDL_CUR_c_swap] = sdl_create_cursor("res/cursor/c_swap.cur");
	curs[SDL_CUR_c_sell] = sdl_create_cursor("res/cursor/c_sell.cur");
	curs[SDL_CUR_c_buy] = sdl_create_cursor("res/cursor/c_buy.cur");
	curs[SDL_CUR_c_look] = sdl_create_cursor("res/cursor/c_look.cur");
	curs[SDL_CUR_c_set] = sdl_create_cursor("res/cursor/c_set.cur");
	curs[SDL_CUR_c_spell] = sdl_create_cursor("res/cursor/c_spell.cur");
	curs[SDL_CUR_c_pix] = sdl_create_cursor("res/cursor/c_pix.cur");
	curs[SDL_CUR_c_say] = sdl_create_cursor("res/cursor/c_say.cur");
	curs[SDL_CUR_c_junk] = sdl_create_cursor("res/cursor/c_junk.cur");
	curs[SDL_CUR_c_get] = sdl_create_cursor("res/cursor/c_get.cur");

	return 1;
}

void sdl_set_cursor(int cursor)
{
	if (cursor < SDL_CUR_c_only || cursor > SDL_CUR_c_get) {
		return;
	}
	SDL_SetCursor(curs[cursor]);
}

// pre[] ring is main-thread only:
//   - sdl_pre_add() appends at pre_in
//   - sdl_pre_ready() advances pre_ready when stages 1+2 are complete (SF_DIDMAKE)
//   - sdl_pre_done() advances pre_done when stage 3 is complete (SF_DIDTEX)
// job_queue[] is the hand-off to workers:
//   - main thread pushes pre indices under premutex
//   - workers pop under premutex and advance jq_head via next_job_id()
//   - job queue provides mutual exclusion
//
// Flag operations:
//   - Reads: Lock-free using flags_load() with atomic operations
//   - Writes: Atomic operations (__atomic_fetch_or, __atomic_store_n) with appropriate memory ordering
//   - Job claiming: SF_CLAIMJOB flag used atomically via job_claimed() helper
//   - Workers only lock premutex when popping from job_queue via next_job_id()

struct prefetch {
	int attick;

	int stx;
};

#define MAXPRE (16384)
static struct prefetch pre[MAXPRE];
int pre_in = 0, pre_ready = 0, pre_done = 0;

static int job_queue[MAXPRE];
static int jq_head = 0, jq_tail = 0;

// Neutralize any stale queue entries referencing a given stx (called during eviction timeout)
static void neutralize_stale_jobs(int stx)
{
	if (!premutex) {
		return;
	}
	SDL_LockMutex(premutex);
	int qpos = jq_head;
	while (qpos != jq_tail) {
		int idx = job_queue[qpos];
		if (idx >= 0 && idx < MAXPRE && pre[idx].stx == stx) {
			// Neutralize this stale entry
			pre[idx].stx = STX_NONE;
		}
		qpos = (qpos + 1) % MAXPRE;
	}
	SDL_UnlockMutex(premutex);
}

// Get next job from queue, returns pre[] index or -1 if queue is empty
// Handles mutex locking internally
static int next_job_id(void)
{
	if (!premutex) {
		// This should never happen - premutex is created in sdl_init() before any workers start
		// If we hit this, it means sdl_pre_worker() was called before initialization completed
		fail("next_job_id: premutex is NULL - fatal initialization error");
		abort();
	}
	SDL_LockMutex(premutex);
	if (jq_head == jq_tail) {
		SDL_UnlockMutex(premutex);
		return -1; // Queue is empty
	}
	int idx = job_queue[jq_head];

	// Validate index before using it - this should never be invalid if queue is properly maintained
	if (idx < 0 || idx >= MAXPRE) {
		// Invalid index in queue - indicates corruption or race condition
		warn("next_job_id: Invalid index %d in job queue (jq_head=%d, jq_tail=%d, pre_in=%d)", idx, jq_head, jq_tail,
		    pre_in);
		// Don't advance jq_head, leave corrupted entry for debugging
		SDL_UnlockMutex(premutex);
		return -1;
	}

	jq_head = (jq_head + 1) % MAXPRE;
	SDL_UnlockMutex(premutex);
	return idx;
}

void sdl_pre_add(int attick, int sprite, signed char sink, unsigned char freeze, unsigned char scale, char cr, char cg,
    char cb, char light, char sat, int c1, int c2, int c3, int shine, char ml, char ll, char rl, char ul, char dl)
{
	int n;
#ifdef DEVELOPER
	long long start = SDL_GetTicks64();
#endif

	if ((pre_in + 1) % MAXPRE == pre_done) { // buffer is full
		return;
	}

	if (sprite >= MAXSPRITE || sprite < 0) {
		note("illegal sprite %d wanted in pre_add", sprite);
		return;
	}

	// Don't pre-load images here - let workers do it using their own zip handles
	// Find in texture cache
	// Will allocate a new entry if not found, or return -1 if already in cache
	n = sdl_tx_load(sprite, sink, freeze, scale, cr, cg, cb, light, sat, c1, c2, c3, shine, ml, ll, rl, ul, dl, NULL, 0,
	    0, NULL, 0, 1, attick);
#ifdef DEVELOPER
	sdl_time_alloc += SDL_GetTicks64() - start;
#endif
	if (n == -1) {
		return;
	}

	if (sdl_multi) {
		SDL_LockMutex(premutex);

		// Check if queue is full
		if ((jq_tail + 1) % MAXPRE == jq_head) {
			SDL_UnlockMutex(premutex);
			return;
		}

		// Check if this texture is already queued or being processed (inside lock to prevent race)
		// SF_CLAIMJOB is cumulative - if set, work has started (or was started)
		// SF_INQUEUE indicates job is queued but not yet claimed
		uint16_t flags = flags_load(&sdlt[n]);
		if (flags & (SF_CLAIMJOB | SF_INQUEUE)) {
			// Work has started (or was started) or already queued, no need to queue again
			SDL_UnlockMutex(premutex);
			return;
		}

		// Mark as queued before adding to queue (protects from eviction)
		uint16_t *flags_ptr = (uint16_t *)&sdlt[n].flags;
		__atomic_fetch_or(flags_ptr, SF_INQUEUE, __ATOMIC_RELEASE);

		pre[pre_in].stx = n;
		pre[pre_in].attick = attick;
		job_queue[jq_tail] = pre_in;
		jq_tail = (jq_tail + 1) % MAXPRE;
		pre_in = (pre_in + 1) % MAXPRE;
		SDL_UnlockMutex(premutex);
	} else {
		// Single-threaded mode: add to queue and process immediately
		pre[pre_in].stx = n;
		pre[pre_in].attick = attick;
		job_queue[jq_tail] = pre_in;
		jq_tail = (jq_tail + 1) % MAXPRE;
		pre_in = (pre_in + 1) % MAXPRE;
		// Process one item from queue (main thread acts as worker)
		sdl_pre_worker(NULL);
	}
}

long long sdl_time_mutex = 0;

#ifdef DEVELOPER
extern uint64_t sdl_backgnd_wait, sdl_backgnd_work;
extern uint64_t sdl_backgnd_jobs;
extern uint64_t sdl_main_jobs;
extern uint64_t sdl_render_wait;
extern uint64_t sdl_render_wait_count;

static uint64_t sdl_perf_last_report = 0;
static uint64_t sdl_perf_last_preload = 0;
static uint64_t sdl_perf_last_make = 0;
static uint64_t sdl_perf_last_make_main = 0;
static uint64_t sdl_perf_last_tex = 0;
static uint64_t sdl_perf_last_tex_main = 0;
static uint64_t sdl_perf_last_mutex = 0;
static uint64_t sdl_perf_last_backgnd_wait = 0;
static uint64_t sdl_perf_last_backgnd_work = 0;
static uint64_t sdl_perf_last_backgnd_jobs = 0;
static uint64_t sdl_perf_last_main_jobs = 0;
static uint64_t sdl_perf_last_render_wait = 0;
static uint64_t sdl_perf_last_render_wait_count = 0;

static void sdl_perf_report(void)
{
	uint64_t now = SDL_GetTicks64();
	if (sdl_perf_last_report == 0) {
		sdl_perf_last_report = now;
		sdl_perf_last_preload = sdl_time_preload;
		sdl_perf_last_make = sdl_time_make;
		sdl_perf_last_make_main = sdl_time_make_main;
		sdl_perf_last_tex = sdl_time_tex;
		sdl_perf_last_tex_main = sdl_time_tex_main;
		sdl_perf_last_mutex = sdl_time_mutex;
		sdl_perf_last_backgnd_wait = sdl_backgnd_wait;
		sdl_perf_last_backgnd_work = sdl_backgnd_work;
		sdl_perf_last_backgnd_jobs = sdl_backgnd_jobs;
		sdl_perf_last_main_jobs = sdl_main_jobs;
		sdl_perf_last_render_wait = sdl_render_wait;
		sdl_perf_last_render_wait_count = sdl_render_wait_count;
		return;
	}

	uint64_t elapsed = now - sdl_perf_last_report;
	if (elapsed < 1000) {
		return;
	}

	uint64_t make_main_delta = sdl_time_make_main - sdl_perf_last_make_main;
	uint64_t tex_main_delta = sdl_time_tex_main - sdl_perf_last_tex_main;
	// sdl_time_mutex is long long (signed), so handle signed arithmetic to avoid underflow
	int64_t mutex_delta_signed = (int64_t)sdl_time_mutex - (int64_t)sdl_perf_last_mutex;
	uint64_t mutex_delta = (mutex_delta_signed < 0) ? 0 : (uint64_t)mutex_delta_signed;
	uint64_t backgnd_wait_delta = sdl_backgnd_wait - sdl_perf_last_backgnd_wait;
	uint64_t backgnd_work_delta = sdl_backgnd_work - sdl_perf_last_backgnd_work;
#ifdef DEVELOPER_NOISY
	uint64_t backgnd_jobs_delta = sdl_backgnd_jobs - sdl_perf_last_backgnd_jobs;
	uint64_t main_jobs_delta = sdl_main_jobs - sdl_perf_last_main_jobs;
	uint64_t render_wait_delta = sdl_render_wait - sdl_perf_last_render_wait;
	uint64_t render_wait_count_delta = sdl_render_wait_count - sdl_perf_last_render_wait_count;
#endif

	double elapsed_sec = elapsed / 1000.0;
	double make_main_ms_per_sec = make_main_delta / elapsed_sec;
	double tex_main_ms_per_sec = tex_main_delta / elapsed_sec;
	double mutex_ms_per_sec = mutex_delta / elapsed_sec;
	double backgnd_wait_ms_per_sec = backgnd_wait_delta / elapsed_sec;
	double backgnd_work_ms_per_sec = backgnd_work_delta / elapsed_sec;
#ifdef DEVELOPER_NOISY
	double render_wait_ms_per_sec = render_wait_delta / elapsed_sec;
#endif

	if (sdl_multi) {
		double backgnd_total = backgnd_wait_ms_per_sec + backgnd_work_ms_per_sec;
		double main_total = make_main_ms_per_sec + tex_main_ms_per_sec;

		if (backgnd_total > 0 && main_total > 0) {
			double ratio = backgnd_total / main_total;
			if (ratio < 0.8) {
				warn("SDL perf: Background workers lagging (%.1f%% of main thread load)", ratio * 100.0);
			}
		}

#ifdef DEVELOPER_NOISY
		// Report job distribution to verify workers are helping
		uint64_t total_jobs = backgnd_jobs_delta + main_jobs_delta;
		if (total_jobs > 0) {
			double backgnd_job_pct = (backgnd_jobs_delta * 100.0) / total_jobs;
			double main_job_pct = (main_jobs_delta * 100.0) / total_jobs;
			if (backgnd_jobs_delta > 0 || main_jobs_delta > 0) {
				warn("SDL perf: Jobs processed: %.1f%% background workers (%lu), %.1f%% main thread (%lu)",
				    backgnd_job_pct, (unsigned long)backgnd_jobs_delta, main_job_pct, (unsigned long)main_jobs_delta);
			}
		}
#endif

		if (mutex_ms_per_sec > 5.0) {
			warn("SDL perf: High mutex contention (%.1f ms/sec)", mutex_ms_per_sec);
		}

#ifdef DEVELOPER_NOISY
		// Report render thread wait statistics
		if (render_wait_count_delta > 0 || render_wait_ms_per_sec > 0.1) {
			warn("SDL perf: Render thread waited %lu times, %.1f ms/sec total (%.2f ms avg per wait)",
			    (unsigned long)render_wait_count_delta, render_wait_ms_per_sec,
			    render_wait_count_delta > 0 ? render_wait_ms_per_sec / render_wait_count_delta : 0.0);
		}
#endif
	}

	sdl_perf_last_report = now;
	sdl_perf_last_preload = sdl_time_preload;
	sdl_perf_last_make = sdl_time_make;
	sdl_perf_last_make_main = sdl_time_make_main;
	sdl_perf_last_tex = sdl_time_tex;
	sdl_perf_last_tex_main = sdl_time_tex_main;
	sdl_perf_last_mutex = sdl_time_mutex;
	sdl_perf_last_backgnd_wait = sdl_backgnd_wait;
	sdl_perf_last_backgnd_work = sdl_backgnd_work;
	sdl_perf_last_backgnd_jobs = sdl_backgnd_jobs;
	sdl_perf_last_main_jobs = sdl_main_jobs;
	sdl_perf_last_render_wait = sdl_render_wait;
	sdl_perf_last_render_wait_count = sdl_render_wait_count;
}
#endif

#ifdef DEVELOPER
static void __attribute__((used)) sdl_lock_impl(SDL_mutex *mutex)
{
	long long start = SDL_GetTicks64();
	SDL_LockMutex(mutex);
	sdl_time_mutex += SDL_GetTicks64() - start;
}

#define SDL_LockMutex(a) sdl_lock_impl(a)
#endif

int sdl_pre_ready(void)
{
	if (pre_in == pre_ready) {
		return 0; // prefetch buffer is empty
	}

	int has_work = 0;

	int stx = pre[pre_ready].stx;
	if (stx == STX_NONE) {
		// Slot is dead (neutralized or already processed); skip it
		pre_ready = (pre_ready + 1) % MAXPRE;
		return 1;
	}

	// Advance pre_ready when stages 1+2 are complete (SF_DIDMAKE)
	// pre_ready is main-thread only, and flags are atomic, so no mutex needed
	uint16_t flags = flags_load(&sdlt[stx]);
	if (flags & SF_DIDMAKE) {
		// Work is complete, advance
		pre_ready = (pre_ready + 1) % MAXPRE;
		has_work = 1;
	} else {
		// Work is pending, signal workers (or will be processed by main thread in single-threaded mode)
		has_work = 1;
	}

	return has_work ? 1 : 0;
}

int sdl_pre_worker(struct zip_handles *zips)
{
	int idx, work = 0;
	int stx;

	// Get one job from the queue
	idx = next_job_id();
	if (idx == -1) {
		return 0; // Queue is empty
	}

	stx = pre[idx].stx;

	if (stx == STX_NONE) {
		// Slot was cleared, no work
		return 0;
	}

	// Validate stx before accessing sdlt[] array
	if (stx < 0 || stx >= MAX_TEXCACHE) {
		return 0; // Invalid entry, no work
	}

	// Check if job is already done or claimed - silently skip if so
	uint16_t flags = flags_load(&sdlt[stx]);
	if (flags & SF_DIDMAKE) {
		// Already done, skip
		return 0;
	}

	// Atomically claim the work FIRST - only one thread will succeed
	// This prevents multiple workers from processing the same job
	// If already claimed, job_claimed() returns true and we skip it
	if (job_claimed(&sdlt[stx])) {
		// Already claimed by another worker, skip
		return 0;
	}

	// We successfully claimed it - clear SF_INQUEUE since we're now processing it
	// SF_CLAIMJOB is set by job_claimed(), so we just need to clear SF_INQUEUE
	uint16_t *flags_ptr = (uint16_t *)&sdlt[stx].flags;
	__atomic_fetch_and(flags_ptr, (uint16_t)~SF_INQUEUE, __ATOMIC_RELEASE);

	// Ensure image is loaded via this worker's zip handles (thread-safe via state machine)
	int sprite = sdlt[stx].sprite;
	if (sdl_ic_load(sprite, zips) < 0) {
		// Loading failed; mark as done (so we don't spin forever) but with no texture
		__atomic_fetch_or(flags_ptr, SF_DIDALLOC | SF_DIDMAKE, __ATOMIC_RELEASE);
		return 0;
	}

	// Now image is in sdli[sprite]; do stages 1+2
	// Do Stage 1 work: allocate pixel buffer
	sdl_make(sdlt + stx, sdli + sprite, 1);

	// Verify pixel was allocated
	if (!sdlt[stx].pixel) {
		__atomic_fetch_or(flags_ptr, SF_DIDALLOC | SF_DIDMAKE, __ATOMIC_RELEASE);
		// Keep SF_CLAIMJOB set - it's cumulative and indicates work was started
		return 0; // Failed, no work
	}

	work = 1;

	// Stage 2: Process pixel buffer (we just did Stage 1, so Stage 2 definitely isn't done)
	sdl_make(sdlt + stx, sdli + sprite, 2);
	__atomic_fetch_or(flags_ptr, SF_DIDMAKE, __ATOMIC_RELEASE);
	// Keep SF_CLAIMJOB set - it's cumulative and indicates work was started

	return work; // Successfully processed a job
}

int sdl_pre_done(void)
{
	if (pre_ready == pre_done) {
		return 0; // prefetch buffer is empty
	}

	int stx = pre[pre_done].stx;

	if (stx == STX_NONE) {
		pre_done = (pre_done + 1) % MAXPRE;
		return 1;
	}

	uint16_t flags_done = flags_load(&sdlt[stx]);
	if (!(flags_done & SF_DIDTEX) && (flags_done & SF_DIDMAKE)) {
		sdl_make(sdlt + stx, sdli + sdlt[stx].sprite, 3);
	}
	pre[pre_done].stx = STX_NONE; // Clear slot after processing
	pre_done = (pre_done + 1) % MAXPRE;

	return 1;
}

int sdl_pre_do(int curtick)
{
#ifdef DEVELOPER
	long long start;
#endif
	int size;
	int work1, work3;

	// Quick check: if buffer is completely empty, skip all timing overhead
	// This avoids expensive SDL_GetTicks64() calls on Windows when idle
	if (pre_in == pre_ready && pre_ready == pre_done) {
		return 0;
	}

	// Only time when there's actual work to avoid Windows overhead
	work1 = (pre_in != pre_ready);
	if (work1) {
#ifdef DEVELOPER
		start = SDL_GetTicks64();
		sdl_pre_ready();
		sdl_time_pre1 += SDL_GetTicks64() - start;
#else
		sdl_pre_ready();
#endif
	}

	// Process queue in single-threaded mode (main thread acts as worker)
	if (!sdl_multi) {
		int processed = 0;
		while (processed < 10) { // Limit per frame to avoid blocking
			int work = sdl_pre_worker(NULL);
			if (!work) {
				break;
			}
			processed++;
#ifdef DEVELOPER
			sdl_main_jobs++;
#endif
		}
	}

	work3 = (pre_ready != pre_done);
	if (work3) {
#ifdef DEVELOPER
		start = SDL_GetTicks64();
		sdl_pre_done();
		sdl_time_pre3 += SDL_GetTicks64() - start;
#else
		sdl_pre_done();
#endif
	}

#ifdef DEVELOPER
	sdl_perf_report();
#endif

	if (pre_in >= pre_ready) {
		size = pre_in - pre_ready;
	} else {
		size = MAXPRE + pre_in - pre_ready;
	}

	if (pre_ready >= pre_done) {
		size += pre_ready - pre_done;
	} else {
		size += MAXPRE + pre_ready - pre_done;
	}

	return size;
}

uint64_t sdl_backgnd_wait = 0, sdl_backgnd_work = 0;
uint64_t sdl_backgnd_jobs = 0; // Jobs processed by background workers
uint64_t sdl_main_jobs = 0; // Jobs processed by main thread (when acting as worker)

int sdl_pre_backgnd(void *ptr)
{
	int worker_id = (int)(long long)ptr;
	struct zip_handles *zips = worker_zips ? &worker_zips[worker_id] : NULL;
#ifdef DEVELOPER
	uint64_t t1;
#endif
	int found_work;

	SDL_SetThreadPriority(SDL_THREAD_PRIORITY_LOW); // This should never block render.

	for (;;) {
		if (SDL_AtomicGet(&pre_quit)) {
			break;
		}

#ifdef DEVELOPER
		t1 = SDL_GetTicks64();
#endif
		found_work = sdl_pre_worker(zips);

		if (!found_work) {
			// No work available, small delay to avoid 100% CPU usage
			SDL_Delay(1);
#ifdef DEVELOPER
			uint64_t t2 = SDL_GetTicks64();
			sdl_backgnd_wait += t2 - t1; // Track actual idle time in milliseconds
		} else {
			uint64_t t2 = SDL_GetTicks64();
			uint64_t work_time = t2 - t1;
			// We successfully processed a job - always count it as work time
			// Even if it's fast (< 2ms), it's still real work being done
			sdl_backgnd_work += work_time;
			sdl_backgnd_jobs++;
#endif
		}
		// If work was found, loop immediately to check for more work
	}

	return 0;
}

void sdl_bargraph_add(int dx, unsigned char *data, int val)
{
	memmove(data + 1, data, dx - 1);
	data[0] = val;
}

void sdl_bargraph(int sx, int sy, int dx, unsigned char *data, int x_offset, int y_offset)
{
	int n;

	for (n = 0; n < dx; n++) {
		if (data[n] > 40) {
			SDL_SetRenderDrawColor(sdlren, 255, 80, 80, 127);
		} else {
			SDL_SetRenderDrawColor(sdlren, 80, 255, 80, 127);
		}

		SDL_RenderDrawLine(sdlren, (sx + n + x_offset) * sdl_scale, (sy + y_offset) * sdl_scale,
		    (sx + n + x_offset) * sdl_scale, (sy - data[n] + y_offset) * sdl_scale);
	}
}

int sdl_is_shown(void)
{
	uint32_t flags;

	flags = SDL_GetWindowFlags(sdlwnd);

	if (flags & SDL_WINDOW_HIDDEN) {
		return 0;
	}
	if (flags & SDL_WINDOW_MINIMIZED) {
		return 0;
	}

	return 1;
}

int sdl_has_focus(void)
{
	uint32_t flags;

	flags = SDL_GetWindowFlags(sdlwnd);

	if (flags & SDL_WINDOW_MOUSE_FOCUS) {
		return 1;
	}

	return 0;
}

void sdl_set_title(char *title)
{
	SDL_SetWindowTitle(sdlwnd, title);
}

void *sdl_create_texture(int width, int height)
{
	return SDL_CreateTexture(sdlren, SDL_PIXELFORMAT_ARGB8888, SDL_TEXTUREACCESS_STATIC, width, height);
}

void sdl_render_copy(void *tex, void *sr, void *dr)
{
	SDL_RenderCopy(sdlren, tex, sr, dr);
}

void sdl_render_copy_ex(void *tex, void *sr, void *dr, double angle)
{
	SDL_RenderCopyEx(sdlren, tex, sr, dr, angle, 0, SDL_FLIP_NONE);
}

int sdl_tex_xres(int stx)
{
	return sdlt[stx].xres;
}

int sdl_tex_yres(int stx)
{
	return sdlt[stx].yres;
}

void sdl_render_circle(int32_t centreX, int32_t centreY, int32_t radius, uint32_t color)
{
	SDL_Point pts[((radius * 8 * 35 / 49) + (8 - 1)) & -8];
	int32_t dC = 0;

	const int32_t diameter = (radius * 2);
	int32_t x = (radius - 1);
	int32_t y = 0;
	int32_t tx = 1;
	int32_t ty = 1;
	int32_t error = (tx - diameter);

	while (x >= y) {
		pts[dC].x = centreX + x;
		pts[dC].y = centreY - y;
		dC++;
		pts[dC].x = centreX + x;
		pts[dC].y = centreY + y;
		dC++;
		pts[dC].x = centreX - x;
		pts[dC].y = centreY - y;
		dC++;
		pts[dC].x = centreX - x;
		pts[dC].y = centreY + y;
		dC++;
		pts[dC].x = centreX + y;
		pts[dC].y = centreY - x;
		dC++;
		pts[dC].x = centreX + y;
		pts[dC].y = centreY + x;
		dC++;
		pts[dC].x = centreX - y;
		pts[dC].y = centreY - x;
		dC++;
		pts[dC].x = centreX - y;
		pts[dC].y = centreY + x;
		dC++;

		if (error <= 0) {
			++y;
			error += ty;
			ty += 2;
		}

		if (error > 0) {
			--x;
			tx += 2;
			error += (tx - diameter);
		}
	}

	SDL_SetRenderDrawColor(sdlren, IGET_R(color), IGET_G(color), IGET_B(color), IGET_A(color));
	SDL_RenderDrawPoints(sdlren, pts, dC);
}

void sdl_flush_textinput(void)
{
	SDL_FlushEvent(SDL_TEXTINPUT);
}

void sdl_tex_alpha(int stx, int alpha)
{
	if (sdlt[stx].tex) {
		SDL_SetTextureAlphaMod(sdlt[stx].tex, alpha);
	}
}

int sdl_check_mouse(void)
{
	int x, y, x2, y2, x3, y3, top;
	SDL_GetGlobalMouseState(&x, &y);

	SDL_GetWindowPosition(sdlwnd, &x2, &y2);
	SDL_GetWindowSize(sdlwnd, &x3, &y3);
	SDL_GetWindowBordersSize(sdlwnd, &top, NULL, NULL, NULL);

	if (x < x2 || x > x2 + x3 || y > y2 + y3) {
		return 1;
	}

	if (game_options & GO_TINYTOP) {
		if (y2 - y > top) {
			return 1;
		}
	} else {
		if (y2 - y > 100 * sdl_scale) {
			return 1;
		}
	}

	if (y < y2) {
		return -1;
	}

	return 0;
}

/*

for /r "." %a in (0*) do magick mogrify -resize 200% png32:"%~a"
magick mogrify -resize 50% png32:*.png

-transparent rgb(255,0,255)
- specify output format (32 bits RGBA)


zip -0 gx1.zip -r -j -q x1
zip -0 gx2.zip -r -j -q x2
zip -0 gx3.zip -r -j -q x3
zip -0 gx4.zip -r -j -q x4

zip -0 gx1_patch.zip -r -j -q x1
zip -0 gx2_patch.zip -r -j -q x2
zip -0 gx3_patch.zip -r -j -q x3
zip -0 gx4_patch.zip -r -j -q x4

mogrify +profile "*" *.png

*/
