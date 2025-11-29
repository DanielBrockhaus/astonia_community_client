/*
 * Part of Astonia Client (c) Daniel Brockhaus. Please read license.txt.
 *
 * Display Game Map - Main Rendering Functions
 *
 * Main game map rendering, spell display, character names, and UI overlays.
 */

#include <stdint.h>
#include <stddef.h>
#include <SDL2/SDL.h>

#include "astonia.h"
#include "game/game.h"
#include "game/game_private.h"
#include "gui/gui.h"
#include "client/client.h"

static int trans_x(int frx, int fry, int tox, int toy, int step, int start)
{
	int x, y, dx, dy, abs_dx, abs_dy;

	dx = (tox - frx);
	dy = (toy - fry);

	abs_dx = abs(dx);
	abs_dy = abs(dy);

	if (abs_dx > abs_dy) {
		if (abs_dx > 0) {
			dy = dy * step / abs_dx;
			dx = dx * step / abs_dx;
		}
	} else {
		if (abs_dy > 0) {
			dx = dx * step / abs_dy;
			dy = dy * step / abs_dy;
		}
	}

	x = frx * 1024 + 512;
	y = fry * 1024 + 512;

	x += dx * (tick - start);
	y += dy * (tick - start);

	x -= (originx - DIST) * 1024;
	y -= (originy - DIST) * 1024;

	return (x - y) * 20 / 1024 + mapoffx + mapaddx;
}

static int trans_y(int frx, int fry, int tox, int toy, int step, int start)
{
	int x, y, dx, dy, abs_dx, abs_dy;

	dx = (tox - frx);
	dy = (toy - fry);

	abs_dx = abs(dx);
	abs_dy = abs(dy);

	if (abs_dx > abs_dy) {
		if (abs_dx > 0) {
			dy = dy * step / abs_dx;
			dx = dx * step / abs_dx;
		}
	} else {
		if (abs_dy > 0) {
			dx = dx * step / abs_dy;
			dy = dy * step / abs_dy;
		}
	}

	x = frx * 1024 + 512;
	y = fry * 1024 + 512;

	x += dx * (tick - start);
	y += dy * (tick - start);

	x -= (originx - DIST) * 1024;
	y -= (originy - DIST) * 1024;

	return (x + y) * 10 / 1024 + mapoffy + mapaddy /*MR*/ - FDY / 2;
}

static void display_game_spells(void)
{
	int i, x, y, dx, sprite, start;
	int nr, fn, e;
	int mapx, mapy, mna, x1, y1, x2, y2, h1, h2, size, n;
	DL *dl;
	float alpha;

	start = SDL_GetTicks();

	for (i = 0; i < maxquick; i++) {
		int mn = quick[i].mn[4];
		int scrx = mapaddx + quick[i].cx;
		int scry = mapaddy + quick[i].cy;
		int light = map[mn].rlight;

		if (!light) {
			continue;
		}

		map[mn].sink = 0;

		if (map[mn].gsprite >= 59405 && map[mn].gsprite <= 59413) {
			map[mn].sink = 8;
		}
		if (map[mn].gsprite >= 59414 && map[mn].gsprite <= 59422) {
			map[mn].sink = 16;
		}
		if (map[mn].gsprite >= 59423 && map[mn].gsprite <= 59431) {
			map[mn].sink = 24;
		}
		if (map[mn].gsprite >= 20815 && map[mn].gsprite <= 20823) {
			map[mn].sink = 36;
		}

		for (e = 0; e < 68; e++) {
			if (e < 4) {
				if ((fn = map[mn].ef[e]) != 0) {
					nr = find_ceffect(fn);
				} else {
					continue;
				}
			} else if (map[mn].cn) {
				for (nr = e - 4; nr < MAXEF; nr++) {
					if (ueffect[nr] && is_char_ceffect(ceffect[nr].generic.type) &&
					    (unsigned)ceffect[nr].flash.cn == map[mn].cn) {
						break;
					}
				}
				if (nr == MAXEF) {
					break;
				} else {
					e = nr + 4;
				}
			} else {
				break;
			};

			if (nr != -1) {
				// addline("%d %d %d %d %d",fn,e,nr,ceffect[nr].generic.type,map[mn].cn);
				// if (e>3) addline("%d: effect %d at %d",tick,ceffect[nr].generic.type,nr);
				switch (ceffect[nr].generic.type) {
				case 1: // shield
					if (tick - ceffect[nr].shield.start < 3) {
						dl = dl_next_set(GME_LAY, 1002 + tick - ceffect[nr].shield.start, scrx + map[mn].xadd,
						    scry + map[mn].yadd + 1, RENDERFX_NORMAL_LIGHT);
						if (!dl) {
							note("error in shield #1");
							break;
						}
					}
					break;

				case 5: // flash
					x = scrx + map[mn].xadd + cos(2 * M_PI * (now % 1000) / 1000.0) * 16;
					y = scry + map[mn].yadd + sin(2 * M_PI * (now % 1000) / 1000.0) * 8;
					dl = dl_next_set(GME_LAY, 1006, x, y, RENDERFX_NORMAL_LIGHT); // shade
					if (!dl) {
						note("error in flash #1");
						break;
					}
					dl = dl_next_set(GME_LAY, 1005, x, y, RENDERFX_NORMAL_LIGHT); // small lightningball
					if (!dl) {
						note("error in flash #2");
						break;
					}
					dl->h = 50;
					break;

				case 3: // strike
				        // set source coords - mna is source
					mapx = ceffect[nr].strike.x - originx + DIST;
					mapy = ceffect[nr].strike.y - originy + DIST;
					mna = mapmn(mapx, mapy);
					mtos(mapx, mapy, &x1, &y1);

					if (map[mna].cn == 0) { // no char, so source should be a lightning ball
						h1 = 20;
					} else { // so i guess we spell from a char (use the flying ball as source)
						x1 = x1 + map[mna].xadd + cos(2 * M_PI * (now % 1000) / 1000.0) * 16;
						y1 = y1 + map[mna].yadd + sin(2 * M_PI * (now % 1000) / 1000.0) * 8;
						h1 = 50;
					}

					// set target coords - mn is target
					x2 = scrx + map[mn].xadd;
					y2 = scry + map[mn].yadd;
					h2 = 25;

					// sanity check
					if (abs(x1 - x2) + abs(y1 - y2) > 200) {
						break;
					}

					// mn is target
					dl_call_strike(GME_LAY, x1, y1, h1, x2, y2, h2);
					// addline("strike %d,%d to %d,%d",x1,y1,x2,y2);
					break;

				case 7: // explosion
					if (tick - ceffect[nr].explode.start < 8) {
						x = scrx;
						y = scry;

						if (ceffect[nr].explode.base >= 50450 && ceffect[nr].explode.base <= 50454) {
							dx = 15;
							sprite = 50450;
						} else {
							dx = 15;
							sprite = ceffect[nr].explode.base;
						}

						dl = dl_next_set(GME_LAY2, min(sprite + tick - ceffect[nr].explode.start, sprite + 7), x,
						    y - dx, RENDERFX_NORMAL_LIGHT);

						if (!dl) {
							note("error in explosion #1");
							break;
						}
						dl->h = dx;
						if (ceffect[nr].explode.base < 50450 || ceffect[nr].explode.base > 50454) {
							if (map[mn].flags & CMF_UNDERWATER) {
								dl->renderfx.cb = min(120, dl->renderfx.cb + 80);
								dl->renderfx.sat = min(20, dl->renderfx.sat + 10);
							}
							break;
						}
						if (ceffect[nr].explode.base == 50451) {
							dl->renderfx.c1 = IRGB(16, 12, 0);
						}

						dl = dl_next_set(GME_LAY2, min(sprite + 8 + tick - ceffect[nr].explode.start, sprite + 15), x,
						    y + dx, RENDERFX_NORMAL_LIGHT);
						if (!dl) {
							note("error in explosion #2");
							break;
						}
						dl->h = dx;
						if (ceffect[nr].explode.base == 50451) {
							dl->renderfx.c1 = IRGB(16, 12, 0);
						}
					}

					break;

				case 8: // warcry
					alpha = -2 * M_PI * (now % 1000) / 1000.0;

					for (x1 = 0; x1 < 4; x1++) {
						x = scrx + map[mn].xadd + cos(alpha + x1 * M_PI / 2) * 15;
						y = scry + map[mn].yadd + sin(alpha + x1 * M_PI / 2) * 15 / 2;
						dl = dl_next_set(GME_LAY, 1020 + (tick / 4 + x1) % 4, x, y, RENDERFX_NORMAL_LIGHT);
						if (!dl) {
							note("error in warcry #1");
							break;
						}
						dl->h = 40;
					}


					break;
				case 9: // bless
					dl_call_bless(GME_LAY, scrx + map[mn].xadd, scry + map[mn].yadd, ceffect[nr].bless.stop - tick,
					    ceffect[nr].bless.strength, 1);
					dl_call_bless(GME_LAY, scrx + map[mn].xadd, scry + map[mn].yadd, ceffect[nr].bless.stop - tick,
					    ceffect[nr].bless.strength, 0);
					break;

				case 10: // heal
					dl = dl_next_set(
					    GME_LAY, 50114, scrx + map[mn].xadd, scry + map[mn].yadd + 1, RENDERFX_NORMAL_LIGHT);
					if (!dl) {
						note("error in heal #1");
						break;
					}
					break;

				case 12: // burn //
					x = scrx + map[mn].xadd;
					y = scry + map[mn].yadd - 3;
					dl = dl_next_set(GME_LAY, 1024 + ((tick) % 10), x, y, RENDERFX_NORMAL_LIGHT); // burn behind
					if (!dl) {
						note("error in bun #1");
						break;
					}
					if (map[mn].flags & CMF_UNDERWATER) {
						dl->renderfx.cb = min(120, dl->renderfx.cb + 80);
						dl->renderfx.sat = min(20, dl->renderfx.sat + 10);
					}

					x = scrx + map[mn].xadd;
					y = scry + map[mn].yadd + 3;
					dl = dl_next_set(
					    GME_LAY, 1024 + ((5 + tick) % 10), x, y, RENDERFX_NORMAL_LIGHT); // small lightningball
					if (!dl) {
						note("error in burn #2");
						break;
					}
					if (map[mn].flags & CMF_UNDERWATER) {
						dl->renderfx.cb = min(120, dl->renderfx.cb + 80);
						dl->renderfx.sat = min(20, dl->renderfx.sat + 10);
					}

					break;
				case 13: // mist
					if (tick - ceffect[nr].mist.start < 24) {
						x = scrx;
						y = scry;
						dl = dl_next_set(
						    GME_LAY + 1, 1034 + (tick - ceffect[nr].mist.start), x, y, RENDERFX_NORMAL_LIGHT);
						if (!dl) {
							note("error in mist #1");
							break;
						}
					}
					break;

				case 14: // potion
					dl_call_potion(GME_LAY, scrx + map[mn].xadd, scry + map[mn].yadd, ceffect[nr].potion.stop - tick,
					    ceffect[nr].potion.strength, 1);
					dl_call_potion(GME_LAY, scrx + map[mn].xadd, scry + map[mn].yadd, ceffect[nr].potion.stop - tick,
					    ceffect[nr].potion.strength, 0);
					break;

				case 15: // earth-rain
					dl_call_rain2(GME_LAY, scrx, scry, tick, ceffect[nr].earthrain.strength, 1);
					dl_call_rain2(GME_LAY, scrx, scry, tick, ceffect[nr].earthrain.strength, 0);
					break;
				case 16: // earth-mud
					mapx = mn % MAPDX + originx - MAPDX / 2;
					mapy = mn / MAPDX + originy - MAPDY / 2;
					dl = dl_next_set(GME_LAY - 1, 50254 + (mapx % 3) + ((mapy / 3) % 3), scrx, scry, light);
					if (!dl) {
						note("error in mud #1");
						break;
					}
					map[mn].sink = 12;
					break;
				case 21: // pulse
					size = ((tick - ceffect[nr].pulse.start) % 6) * 4 + 10;
					for (n = 0; n < 4; n++) {
						dl_call_pulse(GME_LAY, scrx, scry - 3, n, size + 1, IRGB(0, 12, 0));
						dl_call_pulse(GME_LAY, scrx, scry - 2, n, size - 2, IRGB(0, 16, 0));
						dl_call_pulse(GME_LAY, scrx, scry - 1, n, size - 1, IRGB(0, 20, 0));
						dl_call_pulse(GME_LAY, scrx, scry, n, size, IRGB(16, 31, 16));
					}
					break;
				case 22: // pulseback
				         // set source coords - mna is source
					mapx = ceffect[nr].pulseback.x - originx + DIST;
					mapy = ceffect[nr].pulseback.y - originy + DIST;
					mna = mapmn(mapx, mapy);
					mtos(mapx, mapy, &x1, &y1);

					if (map[mna].cn == 0) { // no char, so source should be a lightning ball
						h1 = 20;
					} else { // so i guess we spell from a char (use the flying ball as source)
						h1 = 50;
					}

					// set target coords - mn is target
					x2 = scrx + map[mn].xadd;
					y2 = scry + map[mn].yadd;
					h2 = 25;

					// sanity check
					if (abs(x1 - x2) + abs(y1 - y2) > 200) {
						break;
					}

					// mn is target
					dl_call_pulseback(GME_LAY, x1, y1, h1, x2, y2, h2);
					// addline("strike %d,%d to %d,%d",x1,y1,x2,y2);
					break;
				case 23: // fire ringlet
					if (tick - ceffect[nr].firering.start < 7) {
						dl = dl_next_set(GME_LAY, 51601 + (tick - ceffect[nr].firering.start) * 2, scrx, scry + 20,
						    RENDERFX_NORMAL_LIGHT);
						dl->h = 40;
						if (map[mn].flags & CMF_UNDERWATER) {
							dl->renderfx.cb = min(120, dl->renderfx.cb + 80);
							dl->renderfx.sat = min(20, dl->renderfx.sat + 10);
						}
						dl = dl_next_set(GME_LAY, 51600 + (tick - ceffect[nr].firering.start) * 2, scrx, scry,
						    RENDERFX_NORMAL_LIGHT);
						dl->h = 20;
						if (map[mn].flags & CMF_UNDERWATER) {
							dl->renderfx.cb = min(120, dl->renderfx.cb + 80);
							dl->renderfx.sat = min(20, dl->renderfx.sat + 10);
						}
					}
					break;
				case 24: // forever blowing bubbles...
					if (ceffect[nr].bubble.yoff) {
						add_bubble(scrx + map[mn].xadd, scry + map[mn].yadd, ceffect[nr].bubble.yoff);
					} else {
						add_bubble(scrx, scry, ceffect[nr].bubble.yoff);
					}
					break;
				}
			}
		}
	}

	ds_time = SDL_GetTicks() - start;
}

static void display_game_spells2(void)
{
	int x, y, nr, mapx, mapy, mn;
	DL *dl;

	for (nr = 0; nr < MAXEF; nr++) {
		if (!ueffect[nr]) {
			continue;
		}

		switch (ceffect[nr].generic.type) {
		case 2: // ball
			x = trans_x(ceffect[nr].ball.frx, ceffect[nr].ball.fry, ceffect[nr].ball.tox, ceffect[nr].ball.toy, 128,
			    ceffect[nr].ball.start);
			y = trans_y(ceffect[nr].ball.frx, ceffect[nr].ball.fry, ceffect[nr].ball.tox, ceffect[nr].ball.toy, 128,
			    ceffect[nr].ball.start);

			stom(x, y, &mapx, &mapy);
			mn = mapmn(mapx, mapy);
			if (!map[mn].rlight) {
				break;
			}

			dl = dl_next_set(GME_LAY, 1008, x, y, RENDERFX_NORMAL_LIGHT); // shade
			if (!dl) {
				note("error in ball #1");
				break;
			}
			dl = dl_next_set(GME_LAY, 1000, x, y, RENDERFX_NORMAL_LIGHT); // lightningball
			if (!dl) {
				note("error in ball #2");
				break;
			}
			dl->h = 20;
			break;
		case 4: // fireball
			x = trans_x(ceffect[nr].fireball.frx, ceffect[nr].fireball.fry, ceffect[nr].fireball.tox,
			    ceffect[nr].fireball.toy, 1024, ceffect[nr].fireball.start);
			y = trans_y(ceffect[nr].fireball.frx, ceffect[nr].fireball.fry, ceffect[nr].fireball.tox,
			    ceffect[nr].fireball.toy, 1024, ceffect[nr].fireball.start);

			stom(x, y, &mapx, &mapy);
			mn = mapmn(mapx, mapy);
			if (!map[mn].rlight) {
				break;
			}

			dl = dl_next_set(GME_LAY, 1007, x, y, RENDERFX_NORMAL_LIGHT); // shade
			if (!dl) {
				note("error in fireball #1");
				break;
			}
			if (map[mn].flags & CMF_UNDERWATER) {
				dl->renderfx.cb = min(120, dl->renderfx.cb + 80);
				dl->renderfx.sat = min(20, dl->renderfx.sat + 10);
			}
			dl = dl_next_set(GME_LAY, 1001, x, y, RENDERFX_NORMAL_LIGHT); // fireball
			if (!dl) {
				note("error in fireball #2");
				break;
			}
			if (map[mn].flags & CMF_UNDERWATER) {
				dl->renderfx.cb = min(120, dl->renderfx.cb + 80);
				dl->renderfx.sat = min(20, dl->renderfx.sat + 10);
			}
			dl->h = 20;
			break;
		case 17: // edemonball
			x = trans_x(ceffect[nr].edemonball.frx, ceffect[nr].edemonball.fry, ceffect[nr].edemonball.tox,
			    ceffect[nr].edemonball.toy, 256, ceffect[nr].edemonball.start);
			y = trans_y(ceffect[nr].edemonball.frx, ceffect[nr].edemonball.fry, ceffect[nr].edemonball.tox,
			    ceffect[nr].edemonball.toy, 256, ceffect[nr].edemonball.start);

			stom(x, y, &mapx, &mapy);
			mn = mapmn(mapx, mapy);
			if (!map[mn].rlight) {
				break;
			}

			dl = dl_next_set(GME_LAY, 50281, x, y, RENDERFX_NORMAL_LIGHT); // shade
			if (!dl) {
				note("error in edemonball #1");
				break;
			}
			dl = dl_next_set(GME_LAY, 50264, x, y, RENDERFX_NORMAL_LIGHT); // edemonball
			if (!dl) {
				note("error in edemonball #2");
				break;
			}
			dl->h = 10;

			if (ceffect[nr].edemonball.base == 1) {
				dl->renderfx.c1 = IRGB(16, 12, 0);
			}
			// else if (ceffect[nr].edemonball.base==2) dl->renderfx.tint=EDEMONBALL_TINT3;
			// else if (ceffect[nr].edemonball.base==3) dl->renderfx.tint=EDEMONBALL_TINT4;

			break;
		}
	}
}

static char *roman(int nr)
{
	int h, t, o;
	static char buf[80];
	char *ptr = buf;

	if (nr > 399) {
		return "???";
	}

	h = nr / 100;
	nr -= h * 100;
	t = nr / 10;
	nr -= t * 10;
	o = nr;

	while (h) {
		*ptr++ = 'C';
		h--;
	}

	if (t == 9) {
		*ptr++ = 'X';
		*ptr++ = 'C';
		t = 0;
	}
	if (t > 4) {
		*ptr++ = 'L';
		t -= 5;
	}
	if (t == 4) {
		*ptr++ = 'X';
		*ptr++ = 'L';
		t = 0;
	}
	while (t) {
		*ptr++ = 'X';
		t--;
	}

	if (o == 9) {
		*ptr++ = 'I';
		*ptr++ = 'X';
		o = 0;
	}
	if (o > 4) {
		*ptr++ = 'V';
		o -= 5;
	}
	if (o == 4) {
		*ptr++ = 'I';
		*ptr++ = 'V';
		o = 0;
	}
	while (o) {
		*ptr++ = 'I';
		o--;
	}

	*ptr = 0;

	return buf;
}

static void display_game_names(void)
{
	int i, x, y, col, frame;
	char *sign;
	unsigned short clancolor[33];

	clancolor[1] = IRGB(31, 0, 0);
	clancolor[2] = IRGB(0, 31, 0);
	clancolor[3] = IRGB(0, 0, 31);
	clancolor[4] = IRGB(31, 31, 0);
	clancolor[5] = IRGB(31, 0, 31);
	clancolor[6] = IRGB(0, 31, 31);
	clancolor[7] = IRGB(31, 16, 16);
	clancolor[8] = IRGB(16, 16, 31);

	clancolor[9] = IRGB(24, 8, 8);
	clancolor[10] = IRGB(8, 24, 8);
	clancolor[11] = IRGB(8, 8, 24);
	clancolor[12] = IRGB(24, 24, 8);
	clancolor[13] = IRGB(24, 8, 24);
	clancolor[14] = IRGB(8, 24, 24);
	clancolor[15] = IRGB(24, 24, 24);
	clancolor[16] = IRGB(16, 16, 16);

	clancolor[17] = IRGB(31, 24, 24);
	clancolor[18] = IRGB(24, 31, 24);
	clancolor[19] = IRGB(24, 24, 31);
	clancolor[20] = IRGB(31, 31, 24);
	clancolor[21] = IRGB(31, 24, 31);
	clancolor[22] = IRGB(24, 31, 31);
	clancolor[23] = IRGB(31, 8, 8);
	clancolor[24] = IRGB(8, 8, 31);

	clancolor[25] = IRGB(16, 8, 8);
	clancolor[26] = IRGB(8, 16, 8);
	clancolor[27] = IRGB(8, 8, 16);
	clancolor[28] = IRGB(16, 16, 8);
	clancolor[29] = IRGB(16, 8, 16);
	clancolor[30] = IRGB(8, 16, 16);
	clancolor[31] = IRGB(8, 31, 8);
	clancolor[32] = IRGB(31, 8, 31);

	for (i = 0; i < maxquick; i++) {
		int mn = quick[i].mn[4];
		int scrx = mapaddx + quick[i].cx;
		int scry = mapaddy + quick[i].cy;

		if (!map[mn].rlight) {
			continue;
		}
		if (!map[mn].csprite) {
			continue;
		}
		if (map[mn].gsprite == 51066) {
			continue;
		}
		if (map[mn].gsprite == 51067) {
			continue;
		}

		x = scrx + map[mn].xadd;
		y = scry + 4 + map[mn].yadd + get_chr_height(map[mn].csprite) - 25 + get_sink(mn, map);

		col = whitecolor;
		frame = RENDER_TEXT_FRAMED;

		if (player[map[mn].cn].clan) {
			col = clancolor[player[map[mn].cn].clan];
			if (player[map[mn].cn].clan == 3) {
				frame = RENDER_TEXT_WFRAME;
			}
		}

		sign = "";
		if (player[map[mn].cn].pk_status == 5) {
			sign = " **";
		} else if (player[map[mn].cn].pk_status == 4) {
			sign = " *";
		} else if (player[map[mn].cn].pk_status == 3) {
			sign = " ++";
		} else if (player[map[mn].cn].pk_status == 2) {
			sign = " +";
		} else if (player[map[mn].cn].pk_status == 1) {
			sign = " -";
		}

		if (namesize != RENDER_TEXT_SMALL) {
			y -= 3;
		}
		render_text_fmt(x, y, col, RENDER_ALIGN_CENTER | namesize | frame, "%s%s", player[map[mn].cn].name, sign);


		if (namesize != RENDER_TEXT_SMALL) {
			y += 3;
		}
		y += 12;
		render_text(x, y, whitecolor, RENDER_ALIGN_CENTER | RENDER_TEXT_SMALL | RENDER_TEXT_FRAMED,
		    roman(player[map[mn].cn].level));


		x -= 12;
		y -= 6;
		if (map[mn].health > 1) {
			render_rect(x, y, x + 25, y + 1, blackcolor);
			render_rect(x, y, x + map[mn].health / 4, y + 1, healthcolor);
			y++;
		}
		if (map[mn].shield > 1) {
			render_rect(x, y, x + 25, y + 1, blackcolor);
			render_rect(x, y, x + map[mn].shield / 4, y + 1, shieldcolor);
			y++;
		}
		if (map[mn].mana > 1) {
			render_rect(x, y, x + 25, y + 1, blackcolor);
			render_rect(x, y, x + map[mn].mana / 4, y + 1, manacolor);
		}
	}
}

static void display_game_act(void)
{
	int acttyp;

	// act
	const char *actstr = NULL;

	switch (act) {
	case PAC_MOVE:
		acttyp = 0;
		actstr = "";
		break;

	case PAC_FIREBALL:
		acttyp = 1;
		actstr = "fireball";
		break;
	case PAC_BALL:
		acttyp = 1;
		actstr = "ball";
		break;
	case PAC_LOOK_MAP:
		acttyp = 1;
		actstr = "look";
		break;
	case PAC_DROP:
		acttyp = 1;
		actstr = "drop";
		break;

	case PAC_TAKE:
		acttyp = 2;
		actstr = "take";
		break;
	case PAC_USE:
		acttyp = 2;
		actstr = "use";
		break;

	case PAC_KILL:
		acttyp = 3;
		actstr = "attack";
		break;
	case PAC_HEAL:
		acttyp = 3;
		actstr = "heal";
		break;
	case PAC_BLESS:
		acttyp = 3;
		actstr = "bless";
		break;
	case PAC_FREEZE:
		acttyp = 3;
		actstr = "freeze";
		break;
	case PAC_GIVE:
		acttyp = 3;
		actstr = "give";
		break;

	case PAC_IDLE:
		acttyp = -1;
		break;
	case PAC_MAGICSHIELD:
		acttyp = -1;
		break;
	case PAC_FLASH:
		acttyp = -1;
		break;
	case PAC_WARCRY:
		acttyp = -1;
		break;
	case PAC_BERSERK:
		acttyp = -1;
		break;
	default:
		acttyp = -1;
		break;
	}

	if (acttyp != -1 && actstr) {
		int mn = mapmn(actx - originx + MAPDX / 2, acty - originy + MAPDY / 2);
		int mapx = mn % MAPDX;
		int mapy = mn / MAPDX;
		int scrx, scry;
		mtos(mapx, mapy, &scrx, &scry);
		if (acttyp == 0) {
			dl_next_set(GNDSEL_LAY, 5, scrx, scry, RENDERFX_NORMAL_LIGHT);
		} else {
			render_text(scrx, scry, textcolor, RENDER_ALIGN_CENTER | RENDER_TEXT_SMALL | RENDER_TEXT_FRAMED, actstr);
		}
	}
}

int get_sink(int mn, struct map *cmap)
{
	int x, y, mn2 = -1, xp, yp, tot;

	x = cmap[mn].xadd;
	y = cmap[mn].yadd;

	xp = mn % MAPDX;
	yp = mn / MAPDX;

	if (x == 0 && y == 0) {
		return cmap[mn].sink;
	}

	if (x > 0 && y == 0 && xp < MAPDX - 1) {
		tot = 40;
		mn2 = mn - MAPDX + 1;
	}
	if (x < 0 && y == 0 && xp > 0) {
		tot = 40;
		mn2 = mn + MAPDX - 1;
	}
	if (x == 0 && y > 0 && yp < MAPDY - 1) {
		tot = 20;
		mn2 = mn + MAPDX + 1;
	}
	if (x == 0 && y < 0 && yp > 0) {
		tot = 20;
		mn2 = mn - MAPDX - 1;
	}

	if (x > 0 && y > 0 && xp < MAPDX - 1 && yp < MAPDY - 1) {
		tot = 30;
		mn2 = mn + 1;
	}
	if (x > 0 && y < 0 && xp < MAPDY - 1 && yp > 0) {
		tot = 30;
		mn2 = mn - MAPDX;
	}
	if (x < 0 && y > 0 && xp > 0 && yp < MAPDY - 1) {
		tot = 30;
		mn2 = mn + MAPDX;
	}
	if (x < 0 && y < 0 && xp > 0 && yp > 0) {
		tot = 30;
		mn2 = mn - 1;
	}

	if (mn2 == -1) {
		return cmap[mn].sink;
	}

	x = abs(x);
	y = abs(y);

	return (cmap[mn].sink * (tot - x - y) + cmap[mn2].sink * (x + y)) / tot;
}

void display_game_map(struct map *cmap)
{
	int i, nr, mapx, mapy, mn, scrx, scry, light, mna, sprite, sink, xoff, yoff, start;
	DL *dl;
	int heightadd;

	start = SDL_GetTicks();

	for (i = 0; i < maxquick; i++) {
		mn = quick[i].mn[4];
		scrx = mapaddx + quick[i].cx;
		scry = mapaddy + quick[i].cy;
		light = cmap[mn].rlight;

		// field is invisible - draw a black square and ignore everything else
		if (!light) {
			dl_next_set(GNDSTR_LAY, 0, scrx, scry, RENDERFX_NORMAL_LIGHT);
			continue;
		}

		// blit the grounds and straighten it, if neccassary ...
		if (cmap[mn].rg.sprite) {
			dl = dl_next_set(get_lay_sprite(cmap[mn].gsprite, GND_LAY), cmap[mn].rg.sprite, scrx, scry - 10, light);
			if (!dl) {
				note("error in game #1");
				continue;
			}

			if ((mna = quick[i].mn[3]) != 0 && (cmap[mna].rlight)) {
				dl->renderfx.ll = cmap[mna].rlight;
			} else {
				dl->renderfx.ll = light;
			}
			if ((mna = quick[i].mn[5]) != 0 && (cmap[mna].rlight)) {
				dl->renderfx.rl = cmap[mna].rlight;
			} else {
				dl->renderfx.rl = light;
			}
			if ((mna = quick[i].mn[1]) != 0 && (cmap[mna].rlight)) {
				dl->renderfx.ul = cmap[mna].rlight;
			} else {
				dl->renderfx.ul = light;
			}
			if ((mna = quick[i].mn[7]) != 0 && (cmap[mna].rlight)) {
				dl->renderfx.dl = cmap[mna].rlight;
			} else {
				dl->renderfx.dl = light;
			}

			dl->renderfx.scale = cmap[mn].rg.scale;
			dl->renderfx.cr = cmap[mn].rg.cr;
			dl->renderfx.cg = cmap[mn].rg.cg;
			dl->renderfx.cb = cmap[mn].rg.cb;
			dl->renderfx.clight = cmap[mn].rg.light;
			dl->renderfx.sat = cmap[mn].rg.sat;
			dl->renderfx.c1 = cmap[mn].rg.c1;
			dl->renderfx.c2 = cmap[mn].rg.c2;
			dl->renderfx.c3 = cmap[mn].rg.c3;
			dl->renderfx.shine = cmap[mn].rg.shine;
			dl->h = -10;

			if (cmap[mn].flags & CMF_INFRA) {
				dl->renderfx.cr = min(120, dl->renderfx.cr + 80);
				dl->renderfx.sat = min(20, dl->renderfx.sat + 15);
			}
			if (cmap[mn].flags & CMF_UNDERWATER) {
				dl->renderfx.cb = min(120, dl->renderfx.cb + 80);
				dl->renderfx.sat = min(20, dl->renderfx.sat + 10);
			}

			gsprite_cnt++;
		}

		// ... 2nd (gsprite2)
		if (cmap[mn].rg2.sprite) {
			dl = dl_next_set(get_lay_sprite(cmap[mn].gsprite2, GND2_LAY), cmap[mn].rg2.sprite, scrx, scry, light);
			if (!dl) {
				note("error in game #2");
				continue;
			}

			if ((mna = quick[i].mn[3]) != 0 && (cmap[mna].rlight)) {
				dl->renderfx.ll = cmap[mna].rlight;
			} else {
				dl->renderfx.ll = light;
			}
			if ((mna = quick[i].mn[5]) != 0 && (cmap[mna].rlight)) {
				dl->renderfx.rl = cmap[mna].rlight;
			} else {
				dl->renderfx.rl = light;
			}
			if ((mna = quick[i].mn[1]) != 0 && (cmap[mna].rlight)) {
				dl->renderfx.ul = cmap[mna].rlight;
			} else {
				dl->renderfx.ul = light;
			}
			if ((mna = quick[i].mn[7]) != 0 && (cmap[mna].rlight)) {
				dl->renderfx.dl = cmap[mna].rlight;
			} else {
				dl->renderfx.dl = light;
			}

			dl->renderfx.scale = cmap[mn].rg2.scale;
			dl->renderfx.cr = cmap[mn].rg2.cr;
			dl->renderfx.cg = cmap[mn].rg2.cg;
			dl->renderfx.cb = cmap[mn].rg2.cb;
			dl->renderfx.clight = cmap[mn].rg2.light;
			dl->renderfx.sat = cmap[mn].rg2.sat;
			dl->renderfx.c1 = cmap[mn].rg2.c1;
			dl->renderfx.c2 = cmap[mn].rg2.c2;
			dl->renderfx.c3 = cmap[mn].rg2.c3;
			dl->renderfx.shine = cmap[mn].rg2.shine;

			if (cmap[mn].flags & CMF_INFRA) {
				dl->renderfx.cr = min(120, dl->renderfx.cr + 80);
				dl->renderfx.sat = min(20, dl->renderfx.sat + 15);
			}
			if (cmap[mn].flags & CMF_UNDERWATER) {
				dl->renderfx.cb = min(120, dl->renderfx.cb + 80);
				dl->renderfx.sat = min(20, dl->renderfx.sat + 10);
			}

			g2sprite_cnt++;
		}

		if (cmap[mn].mmf & MMF_STRAIGHT_T) {
			dl_next_set(GNDSTR_LAY, 50, scrx, scry, RENDERFX_NORMAL_LIGHT);
		}
		if (cmap[mn].mmf & MMF_STRAIGHT_B) {
			dl_next_set(GNDSTR_LAY, 51, scrx, scry, RENDERFX_NORMAL_LIGHT);
		}
		if (cmap[mn].mmf & MMF_STRAIGHT_L) {
			dl_next_set(GNDSTR_LAY, 52, scrx, scry, RENDERFX_NORMAL_LIGHT);
		}
		if (cmap[mn].mmf & MMF_STRAIGHT_R) {
			dl_next_set(GNDSTR_LAY, 53, scrx, scry, RENDERFX_NORMAL_LIGHT);
		}

		// blit fsprites
		if (cmap[mn].rf.sprite) {
			dl = dl_next_set(get_lay_sprite(cmap[mn].fsprite, GME_LAY), cmap[mn].rf.sprite, scrx, scry - 9, light);
			if (!dl) {
				note("error in game #3");
				continue;
			}
			dl->h = -9;
			if ((mna = quick[i].mn[3]) != 0 && (cmap[mna].rlight)) {
				dl->renderfx.ll = cmap[mna].rlight;
			} else {
				dl->renderfx.ll = light;
			}
			if ((mna = quick[i].mn[5]) != 0 && (cmap[mna].rlight)) {
				dl->renderfx.rl = cmap[mna].rlight;
			} else {
				dl->renderfx.rl = light;
			}
			if ((mna = quick[i].mn[1]) != 0 && (cmap[mna].rlight)) {
				dl->renderfx.ul = cmap[mna].rlight;
			} else {
				dl->renderfx.ul = light;
			}
			if ((mna = quick[i].mn[7]) != 0 && (cmap[mna].rlight)) {
				dl->renderfx.dl = cmap[mna].rlight;
			} else {
				dl->renderfx.dl = light;
			}

			if (no_lighting_sprite(cmap[mn].fsprite)) {
				dl->renderfx.ll = dl->renderfx.rl = dl->renderfx.ul = dl->renderfx.dl = dl->renderfx.ml;
			}

			// fsprite can increase the height of items and fsprite2
			heightadd = is_yadd_sprite(cmap[mn].rf.sprite);

			dl->renderfx.scale = cmap[mn].rf.scale;
			dl->renderfx.cr = cmap[mn].rf.cr;
			dl->renderfx.cg = cmap[mn].rf.cg;
			dl->renderfx.cb = cmap[mn].rf.cb;
			dl->renderfx.clight = cmap[mn].rf.light;
			dl->renderfx.sat = cmap[mn].rf.sat;
			dl->renderfx.c1 = cmap[mn].rf.c1;
			dl->renderfx.c2 = cmap[mn].rf.c2;
			dl->renderfx.c3 = cmap[mn].rf.c3;
			dl->renderfx.shine = cmap[mn].rf.shine;

			if (cmap[mn].flags & CMF_INFRA) {
				dl->renderfx.cr = min(120, dl->renderfx.cr + 80);
				dl->renderfx.sat = min(20, dl->renderfx.sat + 15);
			}
			if (cmap[mn].flags & CMF_UNDERWATER) {
				dl->renderfx.cb = min(120, dl->renderfx.cb + 80);
				dl->renderfx.sat = min(20, dl->renderfx.sat + 10);
			}

			if (get_offset_sprite(cmap[mn].fsprite, &xoff, &yoff)) {
				dl->x += xoff;
				dl->y += yoff;
			}

			fsprite_cnt++;
		} else {
			heightadd = 0;
		}

		// ... 2nd (fsprite2)
		if (cmap[mn].rf2.sprite) {
			dl = dl_next_set(get_lay_sprite(cmap[mn].fsprite2, GME_LAY), cmap[mn].rf2.sprite, scrx, scry + 1, light);
			if (!dl) {
				note("error in game #5");
				continue;
			}
			dl->h = 1;
			if ((mna = quick[i].mn[3]) != 0 && (cmap[mna].rlight)) {
				dl->renderfx.ll = cmap[mna].rlight;
			} else {
				dl->renderfx.ll = light;
			}
			if ((mna = quick[i].mn[5]) != 0 && (cmap[mna].rlight)) {
				dl->renderfx.rl = cmap[mna].rlight;
			} else {
				dl->renderfx.rl = light;
			}
			if ((mna = quick[i].mn[1]) != 0 && (cmap[mna].rlight)) {
				dl->renderfx.ul = cmap[mna].rlight;
			} else {
				dl->renderfx.ul = light;
			}
			if ((mna = quick[i].mn[7]) != 0 && (cmap[mna].rlight)) {
				dl->renderfx.dl = cmap[mna].rlight;
			} else {
				dl->renderfx.dl = light;
			}

			if (no_lighting_sprite(cmap[mn].fsprite2)) {
				dl->renderfx.ll = dl->renderfx.rl = dl->renderfx.ul = dl->renderfx.dl = dl->renderfx.ml;
			}

			dl->y += 1;
			dl->h += 1;
			dl->h += heightadd;
			dl->renderfx.scale = cmap[mn].rf2.scale;
			dl->renderfx.cr = cmap[mn].rf2.cr;
			dl->renderfx.cg = cmap[mn].rf2.cg;
			dl->renderfx.cb = cmap[mn].rf2.cb;
			dl->renderfx.clight = cmap[mn].rf2.light;
			dl->renderfx.sat = cmap[mn].rf2.sat;
			dl->renderfx.c1 = cmap[mn].rf2.c1;
			dl->renderfx.c2 = cmap[mn].rf2.c2;
			dl->renderfx.c3 = cmap[mn].rf2.c3;
			dl->renderfx.shine = cmap[mn].rf2.shine;

			if (cmap[mn].flags & CMF_INFRA) {
				dl->renderfx.cr = min(120, dl->renderfx.cr + 80);
				dl->renderfx.sat = min(20, dl->renderfx.sat + 15);
			}
			if (cmap[mn].flags & CMF_UNDERWATER) {
				dl->renderfx.cb = min(120, dl->renderfx.cb + 80);
				dl->renderfx.sat = min(20, dl->renderfx.sat + 10);
			}

			if (get_offset_sprite(cmap[mn].fsprite2, &xoff, &yoff)) {
				dl->x += xoff;
				dl->y += yoff;
			}

			f2sprite_cnt++;
		}

		// blit items
		if (cmap[mn].isprite) {
			dl = dl_next_set(get_lay_sprite(cmap[mn].isprite, GME_LAY), cmap[mn].ri.sprite, scrx, scry - 8,
			    itmsel == mn ? RENDERFX_BRIGHT : light);
			if (!dl) {
				note("error in game #8 (%d,%d)", cmap[mn].ri.sprite, cmap[mn].isprite);
				continue;
			}


#if 0
	        // Disabled shaded lighting for items. It is often wrong and needs re-doing
	        if ((mna=quick[i].mn[3])!=0 && (cmap[mna].rlight)) dl->renderfx.ll=cmap[mna].rlight;
	        else dl->renderfx.ll=light;
	        if ((mna=quick[i].mn[5])!=0 && (cmap[mna].rlight)) dl->renderfx.rl=cmap[mna].rlight;
	        else dl->renderfx.rl=light;
	        if ((mna=quick[i].mn[1])!=0 && (cmap[mna].rlight)) dl->renderfx.ul=cmap[mna].rlight;
	        else dl->renderfx.ul=light;
	        if ((mna=quick[i].mn[7])!=0 && (cmap[mna].rlight)) dl->renderfx.dl=cmap[mna].rlight;
	        else dl->renderfx.dl=light;
#else
			dl->renderfx.ll = dl->renderfx.rl = dl->renderfx.ul = dl->renderfx.dl = dl->renderfx.ml;
#endif

			dl->h += heightadd - 8;
			dl->renderfx.scale = cmap[mn].ri.scale;
			dl->renderfx.cr = cmap[mn].ri.cr;
			dl->renderfx.cg = cmap[mn].ri.cg;
			dl->renderfx.cb = cmap[mn].ri.cb;
			dl->renderfx.clight = cmap[mn].ri.light;
			dl->renderfx.sat = cmap[mn].ri.sat;
			dl->renderfx.c1 = cmap[mn].ri.c1;
			dl->renderfx.c2 = cmap[mn].ri.c2;
			dl->renderfx.c3 = cmap[mn].ri.c3;
			dl->renderfx.shine = cmap[mn].ri.shine;

			if (cmap[mn].flags & CMF_INFRA) {
				dl->renderfx.cr = min(120, dl->renderfx.cr + 80);
				dl->renderfx.sat = min(20, dl->renderfx.sat + 15);
			}
			if (cmap[mn].flags & CMF_UNDERWATER) {
				dl->renderfx.cb = min(120, dl->renderfx.cb + 80);
				dl->renderfx.sat = min(20, dl->renderfx.sat + 10);
			}

			if (cmap[mn].flags & CMF_TAKE) {
				dl->renderfx.sink = min(12, cmap[mn].sink);
				dl->y += min(6, cmap[mn].sink / 2);
				dl->h += -min(6, cmap[mn].sink / 2);
			} else if (cmap[mn].flags & CMF_USE) {
				dl->renderfx.sink = min(20, cmap[mn].sink);
				dl->y += min(10, cmap[mn].sink / 2);
				dl->h += -min(10, cmap[mn].sink / 2);
			}

			if (get_offset_sprite(cmap[mn].isprite, &xoff, &yoff)) {
				dl->x += xoff;
				dl->y += yoff;
			}

			isprite_cnt++;
		}

		// blit chars
		if (cmap[mn].csprite) {
			dl = dl_next_set(GME_LAY, cmap[mn].rc.sprite, scrx + cmap[mn].xadd, scry + cmap[mn].yadd,
			    chrsel == mn ? RENDERFX_BRIGHT : light);
			if (!dl) {
				note("error in game #9");
				continue;
			}
			sink = get_sink(mn, cmap);
			dl->renderfx.sink = sink;
			dl->y += sink / 2;
			dl->h = -sink / 2;
			dl->renderfx.scale = cmap[mn].rc.scale;
			// addline("sprite=%d, scale=%d",cmap[mn].rc.sprite,cmap[mn].rc.scale);
			dl->renderfx.cr = cmap[mn].rc.cr;
			dl->renderfx.cg = cmap[mn].rc.cg;
			dl->renderfx.cb = cmap[mn].rc.cb;
			dl->renderfx.clight = cmap[mn].rc.light;
			dl->renderfx.sat = cmap[mn].rc.sat;
			dl->renderfx.c1 = cmap[mn].rc.c1;
			dl->renderfx.c2 = cmap[mn].rc.c2;
			dl->renderfx.c3 = cmap[mn].rc.c3;
			dl->renderfx.shine = cmap[mn].rc.shine;

			// check for spells on char
			for (nr = 0; nr < MAXEF; nr++) {
				if (!ueffect[nr]) {
					continue;
				}
				if ((unsigned int)ceffect[nr].freeze.cn == map[mn].cn && ceffect[nr].generic.type == 11) { // freeze
					int diff;

					if ((diff = tick - ceffect[nr].freeze.start) < RENDERFX_MAX_FREEZE * 4) { // starting
						dl->renderfx.freeze = diff / 4;
					} else if (ceffect[nr].freeze.stop < tick) { // already finished
						continue;
					} else if ((diff = ceffect[nr].freeze.stop - tick) < RENDERFX_MAX_FREEZE * 4) { // ending
						dl->renderfx.freeze = diff / 4;
					} else {
						dl->renderfx.freeze = RENDERFX_MAX_FREEZE - 1; // running
					}
				}
				if ((unsigned int)ceffect[nr].curse.cn == map[mn].cn && ceffect[nr].generic.type == 18) { // curse

					dl->renderfx.sat = min(20, dl->renderfx.sat + (ceffect[nr].curse.strength / 4) + 5);
					dl->renderfx.clight = min(120, dl->renderfx.clight + ceffect[nr].curse.strength * 2 + 40);
					dl->renderfx.cb = min(80, dl->renderfx.cb + ceffect[nr].curse.strength / 2 + 10);
				}
				if ((unsigned int)ceffect[nr].cap.cn == map[mn].cn && ceffect[nr].generic.type == 19) { // palace cap

					dl->renderfx.sat = min(20, dl->renderfx.sat + 20);
					dl->renderfx.clight = min(120, dl->renderfx.clight + 80);
					dl->renderfx.cb = min(80, dl->renderfx.cb + 80);
				}
				if ((unsigned int)ceffect[nr].lag.cn == map[mn].cn && ceffect[nr].generic.type == 20) { // lag

					dl->renderfx.sat = min(20, dl->renderfx.sat + 20);
					dl->renderfx.clight = max(-120, dl->renderfx.clight - 80);
				}
			}
			if (cmap[mn].gsprite == 51066) {
				dl->renderfx.sat = 20;
				dl->renderfx.cr = 80;
				dl->renderfx.clight = -80;
				dl->renderfx.shine = 50;
				dl->renderfx.ml = dl->renderfx.ll = dl->renderfx.rl = dl->renderfx.ul = dl->renderfx.dl =
				    chrsel == mn ? RENDERFX_BRIGHT : RENDERFX_NORMAL_LIGHT;
			} else if (cmap[mn].gsprite == 51067) {
				dl->renderfx.sat = 20;
				dl->renderfx.cb = 80;
				dl->renderfx.clight = -80;
				dl->renderfx.shine = 50;
				dl->renderfx.ml = dl->renderfx.ll = dl->renderfx.rl = dl->renderfx.ul = dl->renderfx.dl =
				    chrsel == mn ? RENDERFX_BRIGHT : RENDERFX_NORMAL_LIGHT;
			} else {
				if (cmap[mn].flags & CMF_INFRA) {
					dl->renderfx.cr = min(120, dl->renderfx.cr + 80);
					dl->renderfx.sat = min(20, dl->renderfx.sat + 15);
				}
				if (cmap[mn].flags & CMF_UNDERWATER) {
					dl->renderfx.cb = min(120, dl->renderfx.cb + 80);
					dl->renderfx.sat = min(20, dl->renderfx.sat + 10);
				}
			}

			csprite_cnt++;
		}
	}
	show_bubbles();
	dg_time += SDL_GetTicks() - start;

	if (cmap == map) { // avoid acting on prefetch
		// selection on ground
		if (mapsel != -1 || context_getnm() != -1) {
			if (context_getnm() != -1) {
				mn = context_getnm();
			} else {
				mn = mapsel;
			}
			mapx = mn % MAPDX;
			mapy = mn / MAPDX;
			mtos(mapx, mapy, &scrx, &scry);
			if (cmap[mn].rlight == 0 || (cmap[mn].mmf & MMF_SIGHTBLOCK)) {
				sprite = SPR_FFIELD;
			} else {
				sprite = SPR_FIELD;
			}
			dl = dl_next_set(GNDSEL_LAY, sprite, scrx, scry, RENDERFX_NORMAL_LIGHT);
			if (!dl) {
				note("error in game #10");
			}
		}
		// act (field) quick and dirty
		if (act == PAC_MOVE) {
			display_game_act();
		}

		dl_play();

		// act (text)  quick and dirty
		if (act != PAC_MOVE) {
			display_game_act();
		}
	}
}

void display_pents(void)
{
	int n, col, yoff;

	for (n = 0; n < 7; n++) {
		switch (pent_str[n][0]) {
		case '0':
			col = graycolor;
			break;
		case '1':
			col = redcolor;
			break;
		case '2':
			col = greencolor;
			break;
		case '3':
			col = bluecolor;
			break;

		default:
			continue;
		}
		if (context_action_enabled()) {
			yoff = 30;
		} else {
			yoff = 0;
		}
		render_text(dotx(DOT_BOT) + 550, doty(DOT_BOT) - 80 + n * 10 - yoff, col,
		    RENDER_TEXT_SMALL | RENDER_TEXT_FRAMED, pent_str[n] + 1);
	}
}

void display_game(void)
{
	display_game_spells();
	display_game_spells2();
	display_game_map(map);
	display_game_names();
	display_pents();
}

void prefetch_game(int attick)
{
	set_map_values(map2, attick);
	set_mapadd(-map2[mapmn(MAPDX / 2, MAPDY / 2)].xadd, -map2[mapmn(MAPDX / 2, MAPDY / 2)].yadd);
	display_game_map(map2);
	dl_prefetch(attick);

#ifdef TICKPRINT
	printf("Prefetch %d\n", attick);
#endif
}
