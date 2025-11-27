/*
 * Part of Astonia Client (c) Daniel Brockhaus. Please read license.txt.
 *
 * Display Game Map - Lighting and Color
 *
 * Functions for calculating lighting, color balance, sprite cutting, and straightening.
 */

#include <stdint.h>
#include <stddef.h>
#include <SDL2/SDL.h>

#include "astonia.h"
#include "game/game.h"
#include "game/game_private.h"
#include "gui/gui.h"
#include "client/client.h"

void set_map_lights(struct map *cmap)
{
	int i, mn;

	for (i = 0; i < maxquick; i++) {
		mn = quick[i].mn[4];

		if (!(cmap[mn].flags & CMF_VISIBLE)) {
			cmap[mn].rlight = 0;
			continue;
		}

		cmap[mn].value = 0;
		cmap[mn].rlight = (cmap[mn].flags & CMF_LIGHT);

		if (cmap[mn].rlight != 15) {
			cmap[mn].rlight = max(0, cmap[mn].rlight);
			cmap[mn].rlight = min(14, cmap[mn].rlight);
		}
		cmap[mn].mmf = 0;

		if (cmap[mn].rlight == 15) {
			if (cmap[quick[i].mn[1]].flags & CMF_VISIBLE) {
				cmap[mn].rlight = min((unsigned)cmap[mn].rlight, cmap[quick[i].mn[1]].flags & CMF_LIGHT);
			}
			if (cmap[quick[i].mn[3]].flags & CMF_VISIBLE) {
				cmap[mn].rlight = min((unsigned)cmap[mn].rlight, cmap[quick[i].mn[3]].flags & CMF_LIGHT);
			}
			if (cmap[quick[i].mn[5]].flags & CMF_VISIBLE) {
				cmap[mn].rlight = min((unsigned)cmap[mn].rlight, cmap[quick[i].mn[5]].flags & CMF_LIGHT);
			}
			if (cmap[quick[i].mn[7]].flags & CMF_VISIBLE) {
				cmap[mn].rlight = min((unsigned)cmap[mn].rlight, cmap[quick[i].mn[7]].flags & CMF_LIGHT);
			}

			if (cmap[mn].rlight == 15) {
				if (cmap[quick[i].mn[0]].flags & CMF_VISIBLE) {
					cmap[mn].rlight = min((unsigned)cmap[mn].rlight, cmap[quick[i].mn[0]].flags & CMF_LIGHT);
				}
				if (cmap[quick[i].mn[2]].flags & CMF_VISIBLE) {
					cmap[mn].rlight = min((unsigned)cmap[mn].rlight, cmap[quick[i].mn[2]].flags & CMF_LIGHT);
				}
				if (cmap[quick[i].mn[6]].flags & CMF_VISIBLE) {
					cmap[mn].rlight = min((unsigned)cmap[mn].rlight, cmap[quick[i].mn[6]].flags & CMF_LIGHT);
				}
				if (cmap[quick[i].mn[8]].flags & CMF_VISIBLE) {
					cmap[mn].rlight = min((unsigned)cmap[mn].rlight, cmap[quick[i].mn[8]].flags & CMF_LIGHT);
				}

				if (cmap[mn].rlight == 15) {
					cmap[mn].rlight = 0;
					continue;
				}
			}

			cmap[mn].mmf |= MMF_SIGHTBLOCK;
		}

		cmap[mn].rlight = 15 - cmap[mn].rlight;

		if (game_options & GO_LOWLIGHT) {
			switch (cmap[mn].rlight) {
			case 2:
				cmap[mn].rlight = 1;
				break;
			case 3:
			case 4:
				cmap[mn].rlight = 5;
				break;
			case 6:
			case 7:
			case 8:
				cmap[mn].rlight = 9;
				break;
			case 10:
			case 11:
				cmap[mn].rlight = 12;
				break;
			case 13:
				cmap[mn].rlight = 14;
				break;
			}
		}
	}
}

void sprites_colorbalance(struct map *cmap, int mn, int r, int g, int b)
{
	cmap[mn].rf.cr = min(120, cmap[mn].rf.cr + r);
	cmap[mn].rf.cg = min(120, cmap[mn].rf.cg + g);
	cmap[mn].rf.cb = min(120, cmap[mn].rf.cb + b);

	cmap[mn].rf2.cr = min(120, cmap[mn].rf2.cr + r);
	cmap[mn].rf2.cg = min(120, cmap[mn].rf2.cg + g);
	cmap[mn].rf2.cb = min(120, cmap[mn].rf2.cb + b);

	cmap[mn].rg.cr = min(120, cmap[mn].rg.cr + r);
	cmap[mn].rg.cg = min(120, cmap[mn].rg.cg + g);
	cmap[mn].rg.cb = min(120, cmap[mn].rg.cb + b);

	cmap[mn].rg2.cr = min(120, cmap[mn].rg2.cr + r);
	cmap[mn].rg2.cg = min(120, cmap[mn].rg2.cg + g);
	cmap[mn].rg2.cb = min(120, cmap[mn].rg2.cb + b);

	cmap[mn].ri.cr = min(120, cmap[mn].ri.cr + r);
	cmap[mn].ri.cg = min(120, cmap[mn].ri.cg + g);
	cmap[mn].ri.cb = min(120, cmap[mn].ri.cb + b);

	cmap[mn].rc.cr = min(120, cmap[mn].rc.cr + r);
	cmap[mn].rc.cg = min(120, cmap[mn].rc.cg + g);
	cmap[mn].rc.cb = min(120, cmap[mn].rc.cb + b);
}

static void set_map_sprites(struct map *cmap, int attick)
{
	int i, mn;

	for (i = 0; i < maxquick; i++) {
		mn = quick[i].mn[4];

		if (!cmap[mn].rlight) {
			continue;
		}

		if (cmap[mn].gsprite) {
			cmap[mn].rg.sprite = trans_asprite(mn, cmap[mn].gsprite, attick, &cmap[mn].rg.scale, &cmap[mn].rg.cr,
			    &cmap[mn].rg.cg, &cmap[mn].rg.cb, &cmap[mn].rg.light, &cmap[mn].rg.sat, &cmap[mn].rg.c1,
			    &cmap[mn].rg.c2, &cmap[mn].rg.c3, &cmap[mn].rg.shine);
		} else {
			cmap[mn].rg.sprite = 0;
		}
		if (cmap[mn].fsprite) {
			cmap[mn].rf.sprite = trans_asprite(mn, cmap[mn].fsprite, attick, &cmap[mn].rf.scale, &cmap[mn].rf.cr,
			    &cmap[mn].rf.cg, &cmap[mn].rf.cb, &cmap[mn].rf.light, &cmap[mn].rf.sat, &cmap[mn].rf.c1,
			    &cmap[mn].rf.c2, &cmap[mn].rf.c3, &cmap[mn].rf.shine);
		} else {
			cmap[mn].rf.sprite = 0;
		}
		if (cmap[mn].gsprite2) {
			cmap[mn].rg2.sprite = trans_asprite(mn, cmap[mn].gsprite2, attick, &cmap[mn].rg2.scale, &cmap[mn].rg2.cr,
			    &cmap[mn].rg2.cg, &cmap[mn].rg2.cb, &cmap[mn].rg2.light, &cmap[mn].rg2.sat, &cmap[mn].rg2.c1,
			    &cmap[mn].rg2.c2, &cmap[mn].rg2.c3, &cmap[mn].rg2.shine);
		} else {
			cmap[mn].rg2.sprite = 0;
		}
		if (cmap[mn].fsprite2) {
			cmap[mn].rf2.sprite = trans_asprite(mn, cmap[mn].fsprite2, attick, &cmap[mn].rf2.scale, &cmap[mn].rf2.cr,
			    &cmap[mn].rf2.cg, &cmap[mn].rf2.cb, &cmap[mn].rf2.light, &cmap[mn].rf2.sat, &cmap[mn].rf2.c1,
			    &cmap[mn].rf2.c2, &cmap[mn].rf2.c3, &cmap[mn].rf2.shine);
		} else {
			cmap[mn].rf2.sprite = 0;
		}

		if (cmap[mn].isprite) {
			cmap[mn].ri.sprite = trans_asprite(mn, cmap[mn].isprite, attick, &cmap[mn].ri.scale, &cmap[mn].ri.cr,
			    &cmap[mn].ri.cg, &cmap[mn].ri.cb, &cmap[mn].ri.light, &cmap[mn].ri.sat, &cmap[mn].ri.c1,
			    &cmap[mn].ri.c2, &cmap[mn].ri.c3, &cmap[mn].ri.shine);
			if (cmap[mn].ic1 || cmap[mn].ic2 || cmap[mn].ic3) {
				cmap[mn].ri.c1 = cmap[mn].ic1;
				cmap[mn].ri.c2 = cmap[mn].ic2;
				cmap[mn].ri.c3 = cmap[mn].ic3;
			}

			if (is_door_sprite(cmap[mn].ri.sprite)) {
				cmap[mn].mmf |= MMF_DOOR;
			}
		} else {
			cmap[mn].ri.sprite = 0;
		}
		if (cmap[mn].csprite) {
			trans_csprite(mn, cmap, attick);
		}
	}
}

static void set_map_cut(struct map *cmap)
{
	int i, mn, mn2, i2;
	unsigned int tmp;

	if (nocut) {
		return;
	}

	// change sprites
	for (i = 0; i < maxquick; i++) {
		mn = quick[i].mn[0];
		i2 = quick[i].qi[0];
		if (mn) {
			mn2 = quick[i2].mn[0];
		} else {
			mn2 = 0;
		}

		if ((!mn || !cmap[mn].rlight ||
		        ((unsigned)abs(is_cut_sprite(cmap[mn].rf.sprite)) != cmap[mn].rf.sprite &&
		            is_cut_sprite(cmap[mn].rf.sprite) > 0) ||
		        ((unsigned)abs(is_cut_sprite(cmap[mn].rf2.sprite)) != cmap[mn].rf2.sprite &&
		            is_cut_sprite(cmap[mn].rf2.sprite) > 0) ||
		        ((unsigned)abs(is_cut_sprite(cmap[mn].ri.sprite)) != cmap[mn].ri.sprite &&
		            is_cut_sprite(cmap[mn].ri.sprite) > 0)) &&
		    (!mn2 || !cmap[mn2].rlight ||
		        ((unsigned)abs(is_cut_sprite(cmap[mn2].rf.sprite)) != cmap[mn2].rf.sprite &&
		            is_cut_sprite(cmap[mn2].rf.sprite) > 0) ||
		        ((unsigned)abs(is_cut_sprite(cmap[mn2].rf2.sprite)) != cmap[mn2].rf2.sprite &&
		            is_cut_sprite(cmap[mn2].rf2.sprite) > 0) ||
		        ((unsigned)abs(is_cut_sprite(cmap[mn2].ri.sprite)) != cmap[mn2].ri.sprite &&
		            is_cut_sprite(cmap[mn2].ri.sprite) > 0))) {
			continue;
		}


		cmap[quick[i].mn[4]].mmf |= MMF_CUT;
	}
	for (i = 0; i < maxquick; i++) {
		if (!(cmap[quick[i].mn[4]].mmf & MMF_CUT)) {
			continue;
		}

		if (is_cut_sprite(cmap[quick[i].mn[4]].rf.sprite) < 0 &&
		    ((!(cmap[quick[i].mn[1]].mmf & MMF_CUT) && is_cut_sprite(cmap[quick[i].mn[1]].rf.sprite)) ||
		        (!(cmap[quick[i].mn[3]].mmf & MMF_CUT) && is_cut_sprite(cmap[quick[i].mn[3]].rf.sprite)))) {
			continue;
		}

		tmp = abs(is_cut_sprite(cmap[quick[i].mn[4]].rf.sprite));
		if (tmp != cmap[quick[i].mn[4]].rf.sprite) {
			cmap[quick[i].mn[4]].rf.sprite = tmp;
		}

		tmp = abs(is_cut_sprite(cmap[quick[i].mn[4]].rf2.sprite));
		if (tmp != cmap[quick[i].mn[4]].rf2.sprite) {
			cmap[quick[i].mn[4]].rf2.sprite = tmp;
		}

		tmp = abs(is_cut_sprite(cmap[quick[i].mn[4]].ri.sprite));
		if (tmp != cmap[quick[i].mn[4]].ri.sprite) {
			cmap[quick[i].mn[4]].ri.sprite = tmp;
		}
	}
}

void set_map_straight(struct map *cmap)
{
	int i, mna, vl, vr, vt, vb, wl, wr, wt, wb;

	for (i = 0; i < maxquick; i++) {
		int mn = quick[i].mn[4];

		if (!cmap[mn].rlight) {
			continue;
		}

		if ((mna = quick[i].mn[3]) != 0) {
			vl = cmap[mna].rlight;
			wl = cmap[mna].mmf & MMF_SIGHTBLOCK;
		} else {
			vl = wl = 0;
		}
		if ((mna = quick[i].mn[5]) != 0) {
			vr = cmap[mna].rlight;
			wr = cmap[mna].mmf & MMF_SIGHTBLOCK;
		} else {
			vr = wr = 0;
		}
		if ((mna = quick[i].mn[1]) != 0) {
			vt = cmap[mna].rlight;
			wt = cmap[mna].mmf & MMF_SIGHTBLOCK;
		} else {
			vt = wt = 0;
		}
		if ((mna = quick[i].mn[7]) != 0) {
			vb = cmap[mna].rlight;
			wb = cmap[mna].mmf & MMF_SIGHTBLOCK;
		} else {
			vb = wb = 0;
		}

		if (!(cmap[mn].mmf & MMF_SIGHTBLOCK)) {
			if ((!vl || wl) && (!vb || wb) && vt && vr && (!wl || !wb)) {
				cmap[mn].mmf |= MMF_STRAIGHT_L;
			}
			if (vl && vb && (!vt || wt) && (!vr || wr) && (!wt || !wr)) {
				cmap[mn].mmf |= MMF_STRAIGHT_R;
			}
			if ((!vl || wl) && vb && (!vt || wt) && vr && (!wl || !wt)) {
				cmap[mn].mmf |= MMF_STRAIGHT_T;
			}
			if (vl && (!vb || wb) && vt && (!vr || wr) && (!wb || !wr)) {
				cmap[mn].mmf |= MMF_STRAIGHT_B;
			}
		} else {
			if (!vt && !vr && !(wl && wb)) {
				cmap[mn].mmf |= MMF_STRAIGHT_R;
			}
			if (!vb && !vl && !(wr && wt)) {
				cmap[mn].mmf |= MMF_STRAIGHT_L;
			}
		}
	}
}

void set_map_values(struct map *cmap, int attick)
{
	set_map_lights(cmap);
	set_map_sprites(cmap, attick);
	set_map_cut(cmap);
	set_map_straight(cmap);
}
