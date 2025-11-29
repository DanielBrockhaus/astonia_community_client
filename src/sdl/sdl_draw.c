/*
 * Part of Astonia Client (c) Daniel Brockhaus. Please read license.txt.
 *
 * SDL - Drawing Module
 *
 * Drawing functions: blit, text rendering, rectangles, lines, pixels, circles, bargraphs.
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

#define RENDER_TEXT_LEFT    0
#define RENDER_ALIGN_CENTER 1
#define RENDER_TEXT_RIGHT   2
#define RENDER_TEXT_SHADED  4
#define RENDER_TEXT_LARGE   0
#define RENDER_TEXT_SMALL   8
#define RENDER_TEXT_FRAMED  16
#define RENDER_TEXT_BIG     32
#define RENDER_TEXT_NOCACHE 64

#define RENDER__SHADED_FONT 128
#define RENDER__FRAMED_FONT 256

#define R16TO32(color) (int)(((((color) >> 10) & 31) / 31.0f) * 255.0f)
#define G16TO32(color) (int)(((((color) >> 5) & 31) / 31.0f) * 255.0f)
#define B16TO32(color) (int)((((color) & 31) / 31.0f) * 255.0f)

#define MAXFONTHEIGHT 64

static void sdl_blit_tex(
    SDL_Texture *tex, int sx, int sy, int clipsx, int clipsy, int clipex, int clipey, int x_offset, int y_offset)
{
	int addx = 0, addy = 0, dx, dy;
	SDL_Rect dr, sr;
	long long start = SDL_GetTicks64();

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

	sdl_time_blit += SDL_GetTicks64() - start;
}

void sdl_blit(int stx, int sx, int sy, int clipsx, int clipsy, int clipex, int clipey, int x_offset, int y_offset)
{
	if (sdlt[stx].tex) {
		sdl_blit_tex(sdlt[stx].tex, sx, sy, clipsx, clipsy, clipex, clipey, x_offset, y_offset);
	}
}

SDL_Texture *sdl_maketext(const char *text, struct renderfont *font, uint32_t color, int flags)
{
	uint32_t *pixel, *dst;
	unsigned char *rawrun;
	int x, y = 0, sizex, sizey = 0, sx = 0;
	const char *c, *otext = text;
	long long start = SDL_GetTicks64();

	for (sizex = 0, c = text; *c; c++) {
		sizex += font[*c].dim * sdl_scale;
	}

	if (flags & (RENDER__FRAMED_FONT | RENDER__SHADED_FONT)) {
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

	while (*text && *text != RENDER_TEXT_TERMINATOR) {
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
	sdl_time_text += SDL_GetTicks64() - start;

	start = SDL_GetTicks64();
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
	sdl_time_tex += SDL_GetTicks64() - start;

	return texture;
}

int sdl_drawtext(int sx, int sy, unsigned short int color, int flags, const char *text, struct renderfont *font,
    int clipsx, int clipsy, int clipex, int clipey, int x_offset, int y_offset)
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

	if (flags & RENDER_TEXT_NOCACHE) {
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
		if (flags & RENDER_ALIGN_CENTER) {
			sx -= dx / 2;
		} else if (flags & RENDER_TEXT_RIGHT) {
			sx -= dx;
		}

		sdl_blit_tex(tex, sx, sy, clipsx, clipsy, clipex, clipey, x_offset, y_offset);

		if (flags & RENDER_TEXT_NOCACHE) {
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
