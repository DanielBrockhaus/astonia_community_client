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
SDL_sem *prework = NULL;
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
int pre_in = 0, pre_1 = 0, pre_2 = 0, pre_3 = 0;

void sdl_dump(FILE *fp)
{
	fprintf(fp, "SDL datadump:\n");

	fprintf(fp, "XRES: %d\n", XRES);
	fprintf(fp, "YRES: %d\n", YRES);

	fprintf(fp, "sdl_scale: %d\n", sdl_scale);
	fprintf(fp, "sdl_frames: %d\n", sdl_frames);
	fprintf(fp, "sdl_multi: %d\n", sdl_multi);
	fprintf(fp, "sdl_cache_size: %d\n", sdl_cache_size);

	fprintf(fp, "mem_png: %lld\n", mem_png);
	fprintf(fp, "mem_tex: %lld\n", mem_tex);
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

	for (i = 0; i < MAX_TEXCACHE; i++) {
		sdlt[i].flags = 0;
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

	if (sdl_multi) {
		char buf[80];
		int n;

		prework = SDL_CreateSemaphore(0);
		premutex = SDL_CreateMutex();

		for (n = 0; n < sdl_multi; n++) {
			sprintf(buf, "moac background worker %d", n);
			SDL_CreateThread(sdl_pre_backgnd, buf, (void *)(long long)n);
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

void sdl_pre_add(int attick, int sprite, signed char sink, unsigned char freeze, unsigned char scale, char cr, char cg,
    char cb, char light, char sat, int c1, int c2, int c3, int shine, char ml, char ll, char rl, char ul, char dl)
{
	int n;
	long long start;
	int reserved_idx;

	if (sprite > MAXSPRITE || sprite < 0) {
		note("illegal sprite %d wanted in pre_add", sprite);
		return;
	}

	// Lock mutex to check buffer and reserve slot
	if (sdl_multi) {
		SDL_LockMutex(premutex);
	}

	if ((pre_in + 1) % MAXPRE == pre_3) { // buffer is full
		if (sdl_multi) {
			SDL_SemPost(prework); // nudge background tasks
			SDL_UnlockMutex(premutex);
		}
		return;
	}

	// Reserve a slot
	reserved_idx = pre_in;
	pre_in = (pre_in + 1) % MAXPRE;

	if (sdl_multi) {
		SDL_UnlockMutex(premutex);
	}

	// Find in texture cache (expensive operation done outside lock)
	// Will allocate a new entry if not found, or return -1 if already in cache
	start = SDL_GetTicks64();
	n = sdl_tx_load(sprite, sink, freeze, scale, cr, cg, cb, light, sat, c1, c2, c3, shine, ml, ll, rl, ul, dl, NULL, 0,
	    0, NULL, 0, 1, attick);
	sdl_time_alloc += SDL_GetTicks64() - start;

	// Re-acquire lock to update the reserved slot or roll back
	if (sdl_multi) {
		SDL_LockMutex(premutex);
	}

	if (n == -1) {
		// Roll back the slot reservation
		pre_in = (pre_in - 1 + MAXPRE) % MAXPRE;
		if (sdl_multi) {
			SDL_UnlockMutex(premutex);
		}
		return;
	}

	// Write to the reserved slot
	pre[reserved_idx].stx = n;
	pre[reserved_idx].attick = attick;

	if (sdl_multi) {
		SDL_UnlockMutex(premutex);
	}
}

long long sdl_time_mutex = 0;

void sdl_lock(void *a)
{
	long long start = SDL_GetTicks64();
	SDL_LockMutex(a);
	sdl_time_mutex += SDL_GetTicks64() - start;
}

#define SDL_LockMutex(a) sdl_lock(a)

int sdl_pre_1(void)
{
	if (pre_in == pre_1) {
		return 0; // prefetch buffer is empty
	}

	if (!(sdlt[pre[pre_1].stx].flags & SF_DIDALLOC)) {
		sdl_ic_load(sdlt[pre[pre_1].stx].sprite);

		sdl_make(sdlt + pre[pre_1].stx, sdli + sdlt[pre[pre_1].stx].sprite, 1);

		if (sdl_multi) {
			SDL_SemPost(prework);
		}
	}
	pre_1 = (pre_1 + 1) % MAXPRE;

	return 1;
}

int sdl_pre_2(void)
{
	int i, work = 0;

	if (pre_1 == pre_2) {
		return 0; // prefetch buffer is empty
	}

	for (i = pre_2; i != pre_1; i = (i + 1) % MAXPRE) {
		if (sdl_multi) {
			SDL_LockMutex(premutex);
		}

		// printf("Preload2: Slot %d, STX %d, flags %X\n",i,pre[i].stx,pre[i].stx!=-1 ? sdlt[pre[i].stx].flags : 0);
		if (pre[i].stx != STX_NONE && !(sdlt[pre[i].stx].flags & (SF_DIDMAKE | SF_BUSY)) &&
		    (sdlt[pre[i].stx].flags & SF_DIDALLOC)) {
			// printf("Preload2: Slot %d, sprite %d (%d, %d, %d, %d)\n",i,pre[i].sprite,pre_in,pre_1,pre_2,pre_3);
			// fflush(stdout);

			sdlt[pre[i].stx].flags |= SF_BUSY;
			if (sdl_multi) {
				SDL_UnlockMutex(premutex);
			}

			sdl_make(sdlt + pre[i].stx, sdli + sdlt[pre[i].stx].sprite, 2);

			if (sdl_multi) {
				SDL_LockMutex(premutex);
			}
			sdlt[pre[i].stx].flags &= ~SF_BUSY;
			sdlt[pre[i].stx].flags |= SF_DIDMAKE;
			if (sdl_multi) {
				SDL_UnlockMutex(premutex);
			}
			work = 1;
			break;

		} else {
			if (sdl_multi) {
				SDL_UnlockMutex(premutex);
			}
		}
	}

	if (sdl_multi) {
		SDL_LockMutex(premutex);
	}
	while ((pre[pre_2].stx == STX_NONE || (sdlt[pre[pre_2].stx].flags & SF_DIDMAKE)) && pre_1 != pre_2) {
		work = 1;
		pre_2 = (pre_2 + 1) % MAXPRE;
	}
	if (sdl_multi) {
		SDL_UnlockMutex(premutex);
	}

	return work;
}

int sdl_pre_3(void)
{
	if (pre_2 == pre_3) {
		return 0; // prefetch buffer is empty
	}

	if (!(sdlt[pre[pre_3].stx].flags & SF_DIDTEX) && (sdlt[pre[pre_3].stx].flags & SF_DIDMAKE)) {
		sdl_make(sdlt + pre[pre_3].stx, sdli + sdlt[pre[pre_3].stx].sprite, 3);
	}
	pre_3 = (pre_3 + 1) % MAXPRE;

	return 1;
}

int sdl_pre_do(int curtick)
{
	long long start;
	int size;

	start = SDL_GetTicks64();
	sdl_pre_1();
	sdl_time_pre1 += SDL_GetTicks64() - start;

	start = SDL_GetTicks64();
	if (!sdl_multi) {
		sdl_pre_2();
	}
	sdl_time_pre2 += SDL_GetTicks64() - start;

	start = SDL_GetTicks64();
	sdl_pre_3();
	sdl_time_pre3 += SDL_GetTicks64() - start;

	if (pre_in >= pre_1) {
		size = pre_in - pre_1;
	} else {
		size = MAXPRE + pre_in - pre_1;
	}

	if (pre_1 >= pre_2) {
		size += pre_1 - pre_2;
	} else {
		size += MAXPRE + pre_1 - pre_2;
	}

	if (pre_2 >= pre_3) {
		size += pre_2 - pre_3;
	} else {
		size += MAXPRE + pre_2 - pre_3;
	}

	return size;
}

uint64_t sdl_backgnd_wait = 0, sdl_backgnd_work = 0;

int sdl_pre_backgnd(void *ptr)
{
	uint64_t start;
	int sem_result;

	// Validate semaphore before entering loop
	if (!prework) {
		SDL_Log("sdl_pre_backgnd: prework semaphore is NULL, exiting thread");
		return -1;
	}

	// Validate mutex if multithreading is enabled
	if (sdl_multi && !premutex) {
		SDL_Log("sdl_pre_backgnd: premutex is NULL but sdl_multi is enabled, exiting thread");
		return -1;
	}

	while (!quit) {
		start = SDL_GetTicks64();
		sem_result = SDL_SemWait(prework);

		// Check for semaphore wait errors
		if (sem_result != 0) {
			SDL_Log("sdl_pre_backgnd: SDL_SemWait failed: %s", SDL_GetError());
			// On fatal error, sleep briefly to avoid tight loop, then continue
			SDL_Delay(100);
			continue;
		}

		sdl_backgnd_wait += SDL_GetTicks64() - start;

		// Double-check mutex validity before calling sdl_pre_2()
		if (sdl_multi && !premutex) {
			SDL_Log("sdl_pre_backgnd: premutex became NULL during execution");
			return -1;
		}

		start = SDL_GetTicks64();
		sdl_pre_2();
		sdl_backgnd_work += SDL_GetTicks64() - start;
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
