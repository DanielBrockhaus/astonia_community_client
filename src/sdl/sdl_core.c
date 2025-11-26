/*
 * Part of Astonia Client (c) Daniel Brockhaus. Please read license.txt.
 *
 * SDL - Core Module
 *
 * Initialization, lifecycle management, window management, cursor handling,
 * event loop, and background prefetching system.
 */

#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <SDL2/SDL.h>
#include <SDL2/SDL_mixer.h>
#include <zip.h>

#include "dll.h"
#include "astonia.h"
#include "sdl/sdl.h"
#include "sdl/sdl_private.h"

// SDL window and renderer
SDL_Window *sdlwnd = NULL;
SDL_Renderer *sdlren = NULL;

// Cursors
static SDL_Cursor *curs[20];

// Zip archives for graphics
zip_t *sdl_zip1 = NULL;
zip_t *sdl_zip2 = NULL;
zip_t *sdl_zip1p = NULL;
zip_t *sdl_zip2p = NULL;
zip_t *sdl_zip1m = NULL;
zip_t *sdl_zip2m = NULL;

// Prefetch threading (shared with sdl_texture.c)
SDL_mutex *premutex = NULL;

// Scale and resolution settings
DLL_EXPORT int sdl_scale = 1;
DLL_EXPORT int sdl_frames = 0;
DLL_EXPORT int sdl_multi = 4;
DLL_EXPORT int sdl_cache_size = 8000;
DLL_EXPORT int __yres = YRES0;

// Prefetch buffer
#define MAXPRE (16384)

struct prefetch {
	int attick;
	int stx;
};
static struct prefetch pre[MAXPRE];
int pre_in = 0, pre_ready = 0, pre_done = 0;

// Job queue for background workers
static int job_queue[MAXPRE];
static int jq_head = 0, jq_tail = 0;

// Worker thread management
struct zip_handles;
static struct zip_handles *worker_zips = NULL;
static SDL_atomic_t pre_quit;
static SDL_Thread **prethreads = NULL;

// Image loading state machine (shared with sdl_image.c)
int *sdli_state = NULL;

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

	// sdlm_sprite, sdlm_scale, sdlm_pixel are static in sdl_image.c
	// fprintf(fp, "sdlm_sprite: %d\n", sdlm_sprite);
	// fprintf(fp, "sdlm_scale: %d\n", sdlm_scale);
	// fprintf(fp, "sdlm_pixel: %p\n", sdlm_pixel);

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

	// Initialize sdli_state array for image loading state machine
	sdli_state = xmalloc(MAXSPRITE * sizeof(int), MEM_SDL_BASE);
	if (!sdli_state) {
		return fail("Out of memory in sdl_init");
	}
	for (i = 0; i < MAXSPRITE; i++) {
		sdli_state[i] = 0; // IMG_UNLOADED
	}

	for (i = 0; i < MAX_TEXCACHE; i++) {
		// Initialize flags atomically
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

		render_set_offset((width / sdl_scale - XRES) / 2, (height / sdl_scale - YRES) / 2);
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

	// Initialize mutex unconditionally (needed for job queue even in single-threaded mode)
	premutex = SDL_CreateMutex();
	if (!premutex) {
		fail("Failed to create premutex");
		return 0;
	}

	SDL_AtomicSet(&pre_quit, 0);

	if (sdl_multi) {
		char buf[80];
		int n;

		// Allocate worker zip handles
		worker_zips = xmalloc(sdl_multi * sizeof(struct zip_handles), MEM_SDL_BASE);
		if (!worker_zips) {
			fail("Out of memory for worker zip handles");
			sdl_multi = 0;
		} else {
			// Open zip handles for each worker
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
					break;
				}

				if (!worker_zips[n].zip1) {
					warn("Worker %d: Failed to open res/gx1.zip - aborting initialization", n);
					// Clean up already opened zips
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
					sdl_multi = 0;
					break;
				}
			}

			// Only create threads if all zip handles succeeded
			if (sdl_multi > 0) {
				prethreads = xmalloc(sdl_multi * sizeof(SDL_Thread *), MEM_SDL_BASE);
				if (!prethreads) {
					fail("Out of memory for thread handles");
					// Clean up zip handles
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
					sdl_multi = 0;
				} else {
					// Create all threads
					for (n = 0; n < sdl_multi; n++) {
						sprintf(buf, "moac background worker %d", n);
						prethreads[n] = SDL_CreateThread(sdl_pre_backgnd, buf, (void *)(long long)n);
						if (!prethreads[n]) {
							warn("Failed to create worker thread %d", n);
							// Signal quit and join already created threads
							SDL_AtomicSet(&pre_quit, 1);
							for (int i = 0; i < n; i++) {
								if (prethreads[i]) {
									SDL_WaitThread(prethreads[i], NULL);
								}
							}
							// Clean up
							xfree(prethreads);
							prethreads = NULL;
							for (int i = 0; i < sdl_multi; i++) {
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
							sdl_multi = 0;
							break;
						}
					}
				}
			}
		}
	}

	return 1;
}

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

void sdl_exit(void)
{
	// Signal workers to quit and join them
	if (sdl_multi && prethreads) {
		SDL_AtomicSet(&pre_quit, 1);
		for (int n = 0; n < sdl_multi; n++) {
			if (prethreads[n]) {
				SDL_WaitThread(prethreads[n], NULL);
			}
		}
		xfree(prethreads);
		prethreads = NULL;
	}

	// Close worker zip handles
	if (worker_zips) {
		for (int n = 0; n < sdl_multi; n++) {
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

	if (premutex) {
		SDL_DestroyMutex(premutex);
		premutex = NULL;
	}

	if (sdli_state) {
		xfree(sdli_state);
		sdli_state = NULL;
	}

	if (game_options & GO_SOUND) {
		Mix_Quit();
	}
#ifdef DEVELOPER
	sdl_dump_spritecache();
#endif
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
	int error = 0;

	curs[SDL_CUR_c_only] = sdl_create_cursor("res/cursor/c_only.cur");
	if (!curs[SDL_CUR_c_only]) {
		error = 1;
	}

	curs[SDL_CUR_c_take] = sdl_create_cursor("res/cursor/c_take.cur");
	if (!curs[SDL_CUR_c_take]) {
		error = 1;
	}

	curs[SDL_CUR_c_drop] = sdl_create_cursor("res/cursor/c_drop.cur");
	if (!curs[SDL_CUR_c_drop]) {
		error = 1;
	}

	curs[SDL_CUR_c_attack] = sdl_create_cursor("res/cursor/c_atta.cur");
	if (!curs[SDL_CUR_c_attack]) {
		error = 1;
	}

	curs[SDL_CUR_c_raise] = sdl_create_cursor("res/cursor/c_rais.cur");
	if (!curs[SDL_CUR_c_raise]) {
		error = 1;
	}

	curs[SDL_CUR_c_give] = sdl_create_cursor("res/cursor/c_give.cur");
	if (!curs[SDL_CUR_c_give]) {
		error = 1;
	}

	curs[SDL_CUR_c_use] = sdl_create_cursor("res/cursor/c_use.cur");
	if (!curs[SDL_CUR_c_use]) {
		error = 1;
	}

	curs[SDL_CUR_c_usewith] = sdl_create_cursor("res/cursor/c_usew.cur");
	if (!curs[SDL_CUR_c_usewith]) {
		error = 1;
	}

	curs[SDL_CUR_c_swap] = sdl_create_cursor("res/cursor/c_swap.cur");
	if (!curs[SDL_CUR_c_swap]) {
		error = 1;
	}

	curs[SDL_CUR_c_sell] = sdl_create_cursor("res/cursor/c_sell.cur");
	if (!curs[SDL_CUR_c_sell]) {
		error = 1;
	}

	curs[SDL_CUR_c_buy] = sdl_create_cursor("res/cursor/c_buy.cur");
	if (!curs[SDL_CUR_c_buy]) {
		error = 1;
	}

	curs[SDL_CUR_c_look] = sdl_create_cursor("res/cursor/c_look.cur");
	if (!curs[SDL_CUR_c_look]) {
		error = 1;
	}

	curs[SDL_CUR_c_set] = sdl_create_cursor("res/cursor/c_set.cur");
	if (!curs[SDL_CUR_c_set]) {
		error = 1;
	}

	curs[SDL_CUR_c_spell] = sdl_create_cursor("res/cursor/c_spell.cur");
	if (!curs[SDL_CUR_c_spell]) {
		error = 1;
	}

	curs[SDL_CUR_c_pix] = sdl_create_cursor("res/cursor/c_pix.cur");
	if (!curs[SDL_CUR_c_pix]) {
		error = 1;
	}

	curs[SDL_CUR_c_say] = sdl_create_cursor("res/cursor/c_say.cur");
	if (!curs[SDL_CUR_c_say]) {
		error = 1;
	}

	curs[SDL_CUR_c_junk] = sdl_create_cursor("res/cursor/c_junk.cur");
	if (!curs[SDL_CUR_c_junk]) {
		error = 1;
	}

	curs[SDL_CUR_c_get] = sdl_create_cursor("res/cursor/c_get.cur");
	if (!curs[SDL_CUR_c_get]) {
		error = 1;
	}

	if (error) {
		fail("Failed to load one or more cursor files");
		return 0;
	}

	return 1;
}

void sdl_set_cursor(int cursor)
{
	if (cursor < SDL_CUR_c_only || cursor > SDL_CUR_c_get) {
		return;
	}
	if (!curs[cursor]) {
		return;
	}
	SDL_SetCursor(curs[cursor]);
}

// Helper function to get next job from queue (returns -1 if queue is empty)
int next_job_id(void)
{
	int idx = -1;
	if (!premutex) {
		fail("premutex is NULL in next_job_id");
		abort();
	}
	SDL_LockMutex(premutex);
	if (jq_head != jq_tail) {
		idx = job_queue[jq_head];
		jq_head = (jq_head + 1) % MAXPRE;
	}
	SDL_UnlockMutex(premutex);
	return idx;
}

// Neutralize stale jobs in the queue for a given stx
void neutralize_stale_jobs(int stx)
{
	if (!premutex) {
		return;
	}

	SDL_LockMutex(premutex);
	int qpos = jq_head;
	while (qpos != jq_tail) {
		int idx = job_queue[qpos];
		if (idx >= 0 && idx < MAXPRE && pre[idx].stx == stx) {
			pre[idx].stx = STX_NONE; // kill job
		}
		qpos = (qpos + 1) % MAXPRE;
	}
	SDL_UnlockMutex(premutex);
}

// Worker function to process jobs from the queue
// Returns 1 if work was found and processed, 0 if queue was empty
int sdl_pre_worker(struct zip_handles *zips)
{
	extern struct sdl_texture *sdlt;
	extern struct sdl_image *sdli;
	extern int sdl_ic_load(int sprite, struct zip_handles *zips);
	extern void sdl_make(struct sdl_texture * st, struct sdl_image * si, int preload);

	int idx = next_job_id();
	if (idx == -1) {
		return 0; // Queue empty
	}

	int stx = pre[idx].stx;
	if (stx == STX_NONE) {
		// Job was neutralized
		return 0;
	}

	if (stx < 0 || stx >= MAX_TEXCACHE) {
		// Invalid stx
		return 0;
	}

	// Check if already processed
	uint16_t flags = flags_load(&sdlt[stx]);
	if (flags & SF_DIDMAKE) {
		// Already processed
		return 0;
	}

	// Try to claim the job atomically
	if (job_claimed(&sdlt[stx])) {
		// Already claimed by another worker
		return 0;
	}

	// Clear SF_INQUEUE now that we've claimed the job
	uint16_t *flags_ptr = (uint16_t *)&sdlt[stx].flags;
	__atomic_fetch_and(flags_ptr, (uint16_t)~SF_INQUEUE, __ATOMIC_RELEASE);

	int sprite = sdlt[stx].sprite;

	// Load image using worker's zip handles
	if (sdl_ic_load(sprite, zips) < 0) {
		// Loading failed; mark as done but with no texture
		__atomic_fetch_or(flags_ptr, SF_DIDMAKE, __ATOMIC_RELEASE);
		return 0;
	}

	// Stage 1: Allocate pixel buffer
	sdl_make(sdlt + stx, sdli + sprite, 1);
	if (!sdlt[stx].pixel) {
		// Allocation failed
		__atomic_fetch_or(flags_ptr, SF_DIDALLOC | SF_DIDMAKE, __ATOMIC_RELEASE);
		return 0;
	}

	// Stage 2: Process pixels
	sdl_make(sdlt + stx, sdli + sprite, 2);
	__atomic_fetch_or(flags_ptr, SF_DIDMAKE, __ATOMIC_RELEASE);

	return 1;
}

void sdl_pre_add(int attick, int sprite, signed char sink, unsigned char freeze, unsigned char scale, char cr, char cg,
    char cb, char light, char sat, int c1, int c2, int c3, int shine, char ml, char ll, char rl, char ul, char dl)
{
	int n;
	long long start;

	if (sprite >= MAXSPRITE || sprite < 0) {
		note("illegal sprite %d wanted in pre_add", sprite);
		return;
	}

	// Find in texture cache (expensive operation done outside lock)
	// Will allocate a new entry if not found, or return -1 if already in cache
	start = SDL_GetTicks64();
	n = sdl_tx_load(sprite, sink, freeze, scale, cr, cg, cb, light, sat, c1, c2, c3, shine, ml, ll, rl, ul, dl, NULL, 0,
	    0, NULL, 0, 1, attick);
	extern long long sdl_time_alloc;
	sdl_time_alloc += SDL_GetTicks64() - start;

	if (n == -1) {
		// Already in cache or failed
		return;
	}

	// Check if job is already queued or claimed
	extern struct sdl_texture *sdlt;
	uint16_t flags = flags_load(&sdlt[n]);
	if (flags & (SF_CLAIMJOB | SF_INQUEUE)) {
		// Already queued or being processed
		return;
	}

	// Lock mutex to add to queue
	SDL_LockMutex(premutex);

	// Double-check after acquiring lock
	flags = flags_load(&sdlt[n]);
	if (flags & (SF_CLAIMJOB | SF_INQUEUE)) {
		SDL_UnlockMutex(premutex);
		return;
	}

	// Check if buffer is full
	if ((pre_in + 1) % MAXPRE == pre_done) {
		SDL_UnlockMutex(premutex);
		return;
	}

	// Set SF_INQUEUE before adding to queue
	uint16_t *flags_ptr = (uint16_t *)&sdlt[n].flags;
	__atomic_fetch_or(flags_ptr, SF_INQUEUE, __ATOMIC_RELEASE);

	// Add to prefetch buffer
	int idx = pre_in;
	pre[idx].stx = n;
	pre[idx].attick = attick;
	pre_in = (pre_in + 1) % MAXPRE;

	// Add to job queue
	job_queue[jq_tail] = idx;
	jq_tail = (jq_tail + 1) % MAXPRE;

	SDL_UnlockMutex(premutex);
}

long long sdl_time_mutex = 0;

void sdl_lock(void *a)
{
	long long start = SDL_GetTicks64();
	SDL_LockMutex(a);
	sdl_time_mutex += SDL_GetTicks64() - start;
}

#define SDL_LockMutex(a) sdl_lock(a)

int sdl_pre_ready(void)
{
	extern struct sdl_texture *sdlt;
	extern struct sdl_image *sdli;

	if (pre_in == pre_ready) {
		return 0; // prefetch buffer is empty
	}

	int stx = pre[pre_ready].stx;
	if (stx == STX_NONE) {
		// Slot is dead; skip it
		pre_ready = (pre_ready + 1) % MAXPRE;
		return 1;
	}

	uint16_t flags = flags_load(&sdlt[stx]);

	if (flags & SF_DIDMAKE) {
		pre_ready = (pre_ready + 1) % MAXPRE;
		return 1;
	}

	return 1; // work still pending
}

int sdl_pre_done(void)
{
	extern struct sdl_texture *sdlt;
	extern struct sdl_image *sdli;

	if (pre_ready == pre_done) {
		return 0; // prefetch buffer is empty
	}

	int stx = pre[pre_done].stx;
	if (stx == STX_NONE) {
		pre_done = (pre_done + 1) % MAXPRE;
		return 1;
	}

	uint16_t flags = flags_load(&sdlt[stx]);
	if (!(flags & SF_DIDTEX) && (flags & SF_DIDMAKE)) {
		sdl_make(sdlt + stx, sdli + sdlt[stx].sprite, 3);
	}

	pre[pre_done].stx = STX_NONE; // Clear slot after processing
	pre_done = (pre_done + 1) % MAXPRE;

	return 1;
}

int sdl_pre_do(int curtick)
{
	long long start;
	int size;

	start = SDL_GetTicks64();
	sdl_pre_ready();
	extern long long sdl_time_pre1;
	sdl_time_pre1 += SDL_GetTicks64() - start;

	start = SDL_GetTicks64();
	if (!sdl_multi) {
		// In single-threaded mode, process jobs on main thread
		sdl_pre_worker(NULL);
	}
	extern long long sdl_time_pre2;
	sdl_time_pre2 += SDL_GetTicks64() - start;

	start = SDL_GetTicks64();
	sdl_pre_done();
	extern long long sdl_time_pre3;
	sdl_time_pre3 += SDL_GetTicks64() - start;

	// Calculate queue size
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

uint64_t sdl_backgnd_wait = 0, sdl_backgnd_work = 0, sdl_backgnd_jobs = 0;

int sdl_pre_backgnd(void *ptr)
{
	int worker_id = (int)(long long)ptr;
	struct zip_handles *zips = worker_zips ? &worker_zips[worker_id] : NULL;
	uint64_t start, t1, t2;
	int found_work;

	// Validate mutex
	if (!premutex) {
		SDL_Log("sdl_pre_backgnd: premutex is NULL, exiting thread");
		return -1;
	}

	while (!quit && !SDL_AtomicGet(&pre_quit)) {
		start = SDL_GetTicks64();
		t1 = start;

		// Poll job queue with 1ms delay when idle
		found_work = sdl_pre_worker(zips);

		t2 = SDL_GetTicks64();

		if (!found_work) {
			SDL_Delay(1);
			sdl_backgnd_wait += t2 - t1;
		} else {
			uint64_t work_time = t2 - t1;
			sdl_backgnd_work += work_time;
			sdl_backgnd_jobs++;
		}
	}

	return 0;
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

void sdl_flush_textinput(void)
{
	SDL_FlushEvent(SDL_TEXTINPUT);
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
