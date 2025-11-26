/*
 * Part of Astonia Client (c) Daniel Brockhaus. Please read license.txt.
 */

#ifndef SDL_PRIVATE_H
#define SDL_PRIVATE_H

#include <stdint.h>
#include <zip.h>
#include <png.h>
#include <SDL2/SDL.h>

#define MAX_TEXCACHE (sdl_cache_size)
#define MAX_TEXHASH                                                                                                    \
	(sdl_cache_size) // Note: MAX_TEXCACHE and MAX_TEXHASH do not have to be the same value. It just turned out to work
	                 // well if they are.

#define STX_NONE (-1)

#define IGET_A(c)         ((((uint32_t)(c)) >> 24) & 0xFF)
#define IGET_R(c)         ((((uint32_t)(c)) >> 16) & 0xFF)
#define IGET_G(c)         ((((uint32_t)(c)) >> 8) & 0xFF)
#define IGET_B(c)         ((((uint32_t)(c)) >> 0) & 0xFF)
#define IRGB(r, g, b)     (((uint32_t)(r) << 16) | ((uint32_t)(g) << 8) | ((uint32_t)(b) << 0))
#define IRGBA(r, g, b, a) (((uint32_t)(a) << 24) | ((uint32_t)(r) << 16) | ((uint32_t)(g) << 8) | ((uint32_t)(b) << 0))

#define SF_USED     (1 << 0)
#define SF_SPRITE   (1 << 1)
#define SF_TEXT     (1 << 2)
#define SF_DIDALLOC (1 << 3)
#define SF_DIDMAKE  (1 << 4)
#define SF_DIDTEX   (1 << 5)
#define SF_CLAIMJOB (1 << 6)
#define SF_INQUEUE  (1 << 7)

struct sdl_texture {
	SDL_Texture *tex;
	uint32_t *pixel;

	int prev, next;
	int hprev, hnext;

	_Atomic(uint16_t) flags; // Atomic for lock-free reads, writes under mutex

	int fortick; // pre-cached for tick X

	// ---------- sprites ------------
	// fx
	int32_t sprite;
	int8_t sink;
	uint8_t scale;
	int16_t cr, cg, cb, light, sat;
	uint16_t c1, c2, c3, shine;

	uint8_t freeze;

	// light
	int8_t ml, ll, rl, ul, dl; // light in middle, left, right, up, down

	// primary
	uint16_t xres; // x resolution in pixels
	uint16_t yres; // y resolution in pixels
	int16_t xoff; // offset to blit position
	int16_t yoff; // offset to blit position

	// ---------- text --------------
	uint16_t text_flags;
	uint32_t text_color;
	char *text;
	void *text_font;
};

struct sdl_image {
	uint32_t *pixel;

	uint16_t flags;
	int16_t xres, yres;
	int16_t xoff, yoff;
};

// Lock-free flag operation helpers
// These provide consistent atomic ordering across all SDL modules
// Must be defined after struct sdl_texture is complete
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

#ifndef HAVE_DDFONT
#define HAVE_DDFONT

struct renderfont {
	int dim;
	unsigned char *raw;
};
#endif

#define RENDER_TEXT_TERMINATOR '\xB0' // draw text terminator - (zero stays one, too)

struct zip_handles {
	zip_t *zip1;
	zip_t *zip2;
	zip_t *zip1p;
	zip_t *zip2p;
	zip_t *zip1m;
	zip_t *zip2m;
};

int sdl_ic_load(int sprite, struct zip_handles *zips);
int sdl_pre_backgnd(void *ptr);
int sdl_create_cursors(void);

#define MAX_SOUND_CHANNELS 32
#define MAXSOUND           100

struct png_helper;
int png_load_helper(struct png_helper *p);
void png_load_helper_exit(struct png_helper *p);

// ============================================================================
// Shared variables from sdl_core.c
// ============================================================================
extern SDL_Window *sdlwnd;
extern SDL_Renderer *sdlren;
extern zip_t *sdl_zip1;
extern zip_t *sdl_zip2;
extern zip_t *sdl_zip1p;
extern zip_t *sdl_zip2p;
extern zip_t *sdl_zip1m;
extern zip_t *sdl_zip2m;
extern SDL_mutex *premutex;
extern int pre_in, pre_ready, pre_done;
extern int *sdli_state; // Image loading state machine

// ============================================================================
// Shared variables from sdl_texture.c
// ============================================================================
extern struct sdl_texture *sdlt;
extern int sdlt_best, sdlt_last;
extern int *sdlt_cache;
extern struct sdl_image *sdli;

extern int texc_used;
extern long long mem_png, mem_tex;
extern long long texc_hit, texc_miss, texc_pre;

extern long long sdl_time_preload;
extern long long sdl_time_make;
extern long long sdl_time_make_main;
extern long long sdl_time_load;
extern long long sdl_time_alloc;
extern long long sdl_time_tex;
extern long long sdl_time_tex_main;
extern long long sdl_time_text;
extern long long sdl_time_blit;
extern long long sdl_time_pre1;
extern long long sdl_time_pre2;
extern long long sdl_time_pre3;

extern int maxpanic;

// ============================================================================
// Internal functions from sdl_texture.c
// ============================================================================
void sdl_tx_best(int stx);
int sdl_tx_load(int sprite, int sink, int freeze, int scale, int cr, int cg, int cb, int light, int sat, int c1, int c2,
    int c3, int shine, int ml, int ll, int rl, int ul, int dl, const char *text, int text_color, int text_flags,
    void *text_font, int checkonly, int preload, int fortick);

#ifdef DEVELOPER
void sdl_dump_spritecache(void);
#endif

// ============================================================================
// Internal functions from sdl_image.c
// ============================================================================
uint32_t mix_argb(uint32_t c1, uint32_t c2, float w1, float w2);
void sdl_smoothify(uint32_t *pixel, int xres, int yres, int scale);
void sdl_premulti(uint32_t *pixel, int xres, int yres, int scale);
void png_helper_read(png_structp ps, png_bytep buf, png_size_t len);
int sdl_load_image_png_(struct sdl_image *si, char *filename, zip_t *zip);
int sdl_load_image_png(struct sdl_image *si, char *filename, zip_t *zip, int smoothify);
int do_smoothify(int sprite);
int sdl_load_image(struct sdl_image *si, int sprite, struct zip_handles *zips);
int sdl_ic_load(int sprite, struct zip_handles *zips);
void sdl_make(struct sdl_texture *st, struct sdl_image *si, int preload);

// ============================================================================
// Internal functions from sdl_effects.c
// ============================================================================
uint32_t sdl_light(int light, uint32_t irgb);
uint32_t sdl_freeze(int freeze, uint32_t irgb);
uint32_t sdl_shine_pix(uint32_t irgb, unsigned short shine);
uint32_t sdl_colorize_pix(uint32_t irgb, unsigned short c1v, unsigned short c2v, unsigned short c3v);
uint32_t sdl_colorize_pix2(uint32_t irgb, unsigned short c1v, unsigned short c2v, unsigned short c3v, int x, int y,
    int xres, int yres, uint32_t *pixel, int sprite);
uint32_t sdl_colorbalance(uint32_t irgb, char cr, char cg, char cb, char light, char sat);

// ============================================================================
// Internal functions from sdl_draw.c
// ============================================================================
SDL_Texture *sdl_maketext(const char *text, struct renderfont *font, uint32_t color, int flags);

// ============================================================================
// Internal functions from sdl_core.c
// ============================================================================
void neutralize_stale_jobs(int stx);
int sdl_pre_worker(struct zip_handles *zips);
int next_job_id(void);

#endif // SDL_PRIVATE_H
