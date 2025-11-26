/*
 * Part of Astonia Client (c) Daniel Brockhaus. Please read license.txt.
 *
 * SDL - Image Module
 *
 * PNG loading, image processing, smoothing, premultiplication, and the sdl_make function
 * that transforms sprite data into textures with applied effects.
 */

#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <math.h>
#include <SDL2/SDL.h>
#include <png.h>
#include <zip.h>

#include "dll.h"
#include "astonia.h"
#include "sdl/sdl.h"
#include "sdl/sdl_private.h"

// Module-local variables
static int sdlm_sprite = 0;
static int sdlm_scale = 0;
static void *sdlm_pixel = NULL;

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
	extern long long mem_png;
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
	extern long long mem_png;
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
		extern zip_t *sdl_zip1, *sdl_zip2, *sdl_zip1p, *sdl_zip2p, *sdl_zip1m, *sdl_zip2m;
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

	// sdli_state is in sdl_core.c, we need to access it
	// For now, we'll use a helper function or make it extern
	extern int *sdli_state; // declared in sdl_core.c

	enum {
		IMG_UNLOADED = 0,
		IMG_LOADING = 1,
		IMG_READY = 2,
		IMG_FAILED = 3,
	};

	int state;
retry:
	state = __atomic_load_n((int *)&sdli_state[sprite], __ATOMIC_ACQUIRE);

	if (state == IMG_READY) {
#ifdef DEVELOPER
		extern long long sdl_time_load;
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
	extern struct sdl_image *sdli;
	if (sdl_load_image(sdli + sprite, sprite, zips) == 0) {
		__atomic_store_n((int *)&sdli_state[sprite], IMG_READY, __ATOMIC_RELEASE);
#ifdef DEVELOPER
		extern long long sdl_time_load;
		sdl_time_load += SDL_GetTicks64() - start;
#endif
		return sprite;
	} else {
		__atomic_store_n((int *)&sdli_state[sprite], IMG_FAILED, __ATOMIC_RELEASE);
		return -1;
	}
}

void sdl_make(struct sdl_texture *st, struct sdl_image *si, int preload)
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
			extern long long sdl_time_preload;
			sdl_time_preload += SDL_GetTicks64() - start;
		} else {
			extern long long sdl_time_make;
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
			extern long long mem_tex;
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
		extern long long sdl_time_tex;
		sdl_time_tex += SDL_GetTicks64() - start;
#endif
	}
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
