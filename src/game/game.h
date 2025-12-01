/*
 * Part of Astonia Client (c) Daniel Brockhaus. Please read license.txt.
 */

#include "dll.h"

// Sprite alignment constants
#define RENDER_ALIGN_OFFSET 0 // Use sprite's built-in offset (must be zero for bzero default)
#define RENDER_ALIGN_CENTER 1 // Center sprite at position (also used in text rendering)
#define RENDER_ALIGN_NORMAL 2 // Normal positioning without offset

// Text alignment constants
#define RENDER_TEXT_LEFT   0 // Left-aligned text
#define RENDER_TEXT_CENTER 1 // Centered text
#define RENDER_TEXT_RIGHT  2 // Right-aligned text

// Text style flags (can be combined with bitwise OR)
#define RENDER_TEXT_SHADED  4 // Draw text with shadow
#define RENDER_TEXT_LARGE   0 // Large font size (default)
#define RENDER_TEXT_SMALL   8 // Small font size
#define RENDER_TEXT_FRAMED  16 // Draw text with black outline
#define RENDER_TEXT_BIG     32 // Big font size
#define RENDER_TEXT_NOCACHE 64 // Don't cache text rendering
#define RENDER_TEXT_WFRAME  (RENDER_TEXT_FRAMED | 512) // White frame variant

#define SPR_WALK 11

#define SPR_FFIELD 10
#define SPR_FIELD  12

#define SPR_ITPAD 13
#define SPR_ITSEL 14

#define SPR_SCRUP  27 // 20 // 17
#define SPR_SCRLT  28 // 21 // 19
#define SPR_SCRDW  29 // 23 // 18
#define SPR_SCRRT  30 // 22 // 19
#define SPR_SCRBAR 26

#define SPR_RAISE 19
#define SPR_CLOSE 36
#define SPR_TEXTF 35

#define SPR_GOLD_BEG 100
#define SPR_GOLD_END 109

// Lighting effect constants
#define RENDERFX_NORMAL_LIGHT 15 // Normal lighting level
#define RENDERFX_BRIGHT       0 // Maximum brightness

#define MMF_SIGHTBLOCK (1 << 1) // indicates sight block (set_map_lights)
#define MMF_DOOR       (1 << 2) // a door - helpful when cutting sprites - (set_map_sprites)
#define MMF_CUT        (1 << 3) // indicates cut (set_map_cut)

#define MMF_STRAIGHT_T (1 << 5) // (set_map_straight)
#define MMF_STRAIGHT_B (1 << 6) // (set_map_straight)
#define MMF_STRAIGHT_L (1 << 7) // (set_map_straight)
#define MMF_STRAIGHT_R (1 << 8) // (set_map_straight)


#define IGET_R(c)     ((((unsigned short int)(c)) >> 10) & 0x1F)
#define IGET_G(c)     ((((unsigned short int)(c)) >> 5) & 0x1F)
#define IGET_B(c)     ((((unsigned short int)(c)) >> 0) & 0x1F)
#define IRGB(r, g, b) (((r) << 10) | ((g) << 5) | ((b) << 0))

/**
 * Rendering effects structure for sprite rendering.
 * Contains all parameters needed to render a sprite with various effects including
 * lighting, scaling, color manipulation, and alpha blending.
 */
struct renderfx {
	int sprite; // Primary sprite number (must be first for dl_qcmp sorting)

	signed char sink; // Vertical sink amount for sprite positioning
	unsigned char scale; // Scale percentage (100 = normal size)
	char cr, cg, cb; // Color balance adjustments (red, green, blue)
	char clight, sat; // Lightness and saturation adjustments
	unsigned short c1, c2, c3, shine; // Color replacement values

	char light; // Lighting level: 0=bright (RENDERFX_BRIGHT), 15=normal (RENDERFX_NORMAL_LIGHT)
	char freeze; // Animation freeze frame: 0 to RENDERFX_MAX_FREEZE-1

	char ml, ll, rl, ul, dl; // Multi-directional lighting (main, left, right, up, down)

	char align; // Alignment mode: RENDER_ALIGN_OFFSET, RENDER_ALIGN_CENTER, RENDER_ALIGN_NORMAL
	short int clipsx, clipex; // Additional X clipping bounds around the offset
	short int clipsy, clipey; // Additional Y clipping bounds around the offset

	unsigned char alpha; // Alpha transparency value (0-255)
};

typedef struct renderfx RenderFX;

extern float mouse_scale; // mouse input needs to be scaled by this factor because the display window is stretched
extern char user_keys[10];
extern int namesize;
extern int stom_off_x, stom_off_y;
extern int __textdisplay_sy;
extern int x_offset, y_offset;

// Text rendering functions
DLL_EXPORT int render_text_length(int flags, const char *text);
int render_text_len(int flags, const char *text, int n);
DLL_EXPORT int render_text(int sx, int sy, unsigned short int color, int flags, const char *text);
DLL_EXPORT int render_text_fmt(int sx, int sy, unsigned short int color, int flags, const char *format, ...)
    __attribute__((format(printf, 5, 6)));
DLL_EXPORT int render_text_break_fmt(int sx, int sy, int breakx, unsigned short int color, int flags,
    const char *format, ...) __attribute__((format(printf, 6, 7)));
DLL_EXPORT int render_text_nl(int x, int y, int unsigned short color, int flags, const char *ptr);
DLL_EXPORT int render_text_break(int x, int y, int breakx, unsigned short color, int flags, const char *ptr);
DLL_EXPORT int render_text_break_length(int x, int y, int breakx, unsigned short color, int flags, const char *ptr);
int render_text_char(int sx, int sy, int c, unsigned short int color);
int render_char_len(char c);

// Sprite rendering functions
DLL_EXPORT int render_sprite_fx(RenderFX *fx, int scrx, int scry);
DLL_EXPORT void render_sprite(int sprite, int scrx, int scry, int light, int align);
void render_sprite_callfx(int sprite, int scrx, int scry, int light, int mli, int align);

// Primitive drawing functions
DLL_EXPORT void render_rect(int sx, int sy, int ex, int ey, unsigned short int color);
void render_shaded_rect(int sx, int sy, int ex, int ey, unsigned short color, unsigned short alpha);
DLL_EXPORT void render_line(int fx, int fy, int tx, int ty, unsigned short col);
DLL_EXPORT void render_pixel(int x, int y, unsigned short col);

// Clipping functions
DLL_EXPORT void render_push_clip(void);
DLL_EXPORT void render_pop_clip(void);
DLL_EXPORT void render_more_clip(int sx, int sy, int ex, int ey);
void render_set_clip(int sx, int sy, int ex, int ey);

// Chat window text functions
void render_display_text(void);
void render_text_pageup(void);
void render_text_pagedown(void);
void render_text_lineup(void);
void render_text_linedown(void);
int render_scantext(int x, int y, char *hit);
void render_list_text(void);

// Offset functions
int render_offset_x(void);
int render_offset_y(void);
extern int (*trans_asprite)(int mn, int sprite, int attick, unsigned char *pscale, unsigned char *pcr,
    unsigned char *pcg, unsigned char *pcb, unsigned char *plight, unsigned char *psat, unsigned short *pc1,
    unsigned short *pc2, unsigned short *pc3, unsigned short *pshine);
DLL_EXPORT int _trans_asprite(int mn, int sprite, int attick, unsigned char *pscale, unsigned char *pcr,
    unsigned char *pcg, unsigned char *pcb, unsigned char *plight, unsigned char *psat, unsigned short *pc1,
    unsigned short *pc2, unsigned short *pc3, unsigned short *pshine);
extern int (*trans_charno)(int csprite, int *pscale, int *pcr, int *pcg, int *pcb, int *plight, int *psat, int *pc1,
    int *pc2, int *pc3, int *pshine, int attick);
DLL_EXPORT int _trans_charno(int csprite, int *pscale, int *pcr, int *pcg, int *pcb, int *plight, int *psat, int *pc1,
    int *pc2, int *pc3, int *pshine, int attick);
extern int (*additional_sprite)(int sprite, int attick);
DLL_EXPORT int _additional_sprite(int sprite, int attick);
extern int (*get_player_sprite)(int nr, int zdir, int action, int step, int duration, int attick);
DLL_EXPORT int _get_player_sprite(int nr, int zdir, int action, int step, int duration, int attick);
void save_options(void);
extern int (*opt_sprite)(int sprite);
DLL_EXPORT int _opt_sprite(int sprite);
extern int (*no_lighting_sprite)(int sprite);
DLL_EXPORT int _no_lighting_sprite(int sprite);

struct map;
int get_sink(int mn, struct map *cmap);

void list_mem(void);

void display_game(void);

void set_map_values(struct map *cmap, int attick);
void quest_select(int nr);
void init_game(int mcx, int mcy);
void exit_game(void);
