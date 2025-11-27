/*
 * Part of Astonia Client (c) Daniel Brockhaus. Please read license.txt.
 *
 * SDL - Effects Module
 *
 * Pixel effects: lighting, freezing, colorization, color balance, shine.
 */

#include <stdint.h>
#include <stdio.h>
#include <math.h>
#include <SDL2/SDL.h>

#include "astonia.h"
#include "sdl/sdl.h"
#include "sdl/sdl_private.h"

#define DDFX_MAX_FREEZE 8

#define REDCOL   (0.40)
#define GREENCOL (0.70)
#define BLUECOL  (0.70)

#define OGET_R(c) ((((unsigned short int)(c)) >> 10) & 0x1F)
#define OGET_G(c) ((((unsigned short int)(c)) >> 5) & 0x1F)
#define OGET_B(c) ((((unsigned short int)(c)) >> 0) & 0x1F)

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

uint32_t sdl_light(int light, uint32_t irgb)
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

uint32_t sdl_freeze(int freeze, uint32_t irgb)
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

uint32_t sdl_shine_pix(uint32_t irgb, unsigned short shine)
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

uint32_t sdl_colorize_pix(uint32_t irgb, unsigned short c1v, unsigned short c2v, unsigned short c3v)
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

uint32_t sdl_colorize_pix2(uint32_t irgb, unsigned short c1v, unsigned short c2v, unsigned short c3v, int x, int y,
    int xres, int yres, uint32_t *pixel, int sprite)
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
	    (c3v && rm > 0.67 && would_colorize_neigh(x, y, xres, yres, pixel, 2))) {
		r = 8.0 * OGET_R(c3v) * rf;
		g = 8.0 * (OGET_G(c3v) * rf + (1.0 - rf) * gf);
		b = 8.0 * (OGET_B(c3v) * rf + (1.0 - rf) * bf);
		a = IGET_A(irgb);
		return IRGBA(r, g, b, a);
	}

	return irgb;
}

uint32_t sdl_colorbalance(uint32_t irgb, char cr, char cg, char cb, char light, char sat)
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
	cb *= 0.75;

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
