/*
 * Part of Astonia Client (c) Daniel Brockhaus. Please read license.txt.
 *
 * Graphical User Interface - Inventory and container management
 *
 */

#include <inttypes.h>
#include <time.h>
#include <SDL2/SDL.h>

#include "astonia.h"
#include "gui/gui.h"
#include "gui/gui_private.h"
#include "client/client.h"
#include "game/game.h"
#include "sdl/sdl.h"
#include "modder/modder.h"

void set_invoff(int bymouse, int ny)
{
	if (bymouse) {
		invoff += mousedy / LINEHEIGHT;
		mousedy = mousedy % LINEHEIGHT;
	} else {
		invoff = ny;
	}

	if (invoff < 0) {
		invoff = 0;
	}
	if (invoff > max_invoff) {
		invoff = max_invoff;
	}

	but[BUT_SCR_TR].y =
	    but[BUT_SCR_UP].y + 10 + (but[BUT_SCR_DW].y - but[BUT_SCR_UP].y - 20) * invoff / max(1, max_invoff);
}

void set_skloff(int bymouse, int ny)
{
	if (bymouse) {
		skloff += mousedy / LINEHEIGHT;
		mousedy = mousedy % LINEHEIGHT;
	} else {
		skloff = ny;
	}

	if (skloff < 0) {
		skloff = 0;
	}
	if (skloff > max_skloff) {
		skloff = max_skloff;
	}

	if (!con_cnt) {
		but[BUT_SCL_TR].y =
		    but[BUT_SCL_UP].y + 10 + (but[BUT_SCL_DW].y - but[BUT_SCL_UP].y - 20) * skloff / max(1, max_skloff);
	}
}

void set_conoff(int bymouse, int ny)
{
	if (bymouse) {
		conoff += mousedy / LINEHEIGHT;
		mousedy = mousedy % LINEHEIGHT;
	} else {
		conoff = ny;
	}

	if (conoff < 0) {
		conoff = 0;
	}
	if (conoff > max_conoff) {
		conoff = max_conoff;
	}

	if (con_cnt) {
		but[BUT_SCL_TR].y =
		    but[BUT_SCL_UP].y + 10 + (but[BUT_SCL_DW].y - but[BUT_SCL_UP].y - 20) * conoff / max(1, max_conoff);
	}
}

DLL_EXPORT int _get_skltab_index(int n)
{
	static int itab[V_MAX + 1] = {
	    -1, 0, 1, 2, // powers
	    3, 4, 5, 6, // bases
	    7, 8, 9, 10, 38, 41, // armor etc
	    12, 13, 14, 15, 16, 40, // fight skills
	    17, 18, 19, 20, 21, 22, 23, 24, // 2ndary fight skills
	    28, 29, 30, 31, 32, 33, 34, 11, 39, // spells
	    25, 26, 27, 35, 36, 37, // misc skills
	    42, // profession
	    43, 44, 45, 46, 47, 48, 49, 50, 51, 52, // professions 1-10
	    53, 54, 55, 56, 57, 58, 59, 60, 61, 62, // professions 11-20
	    -2 // end marker
	};

	return itab[n];
}

DLL_EXPORT int _get_skltab_sep(int i)
{
	return (i == 0 || i == 3 || i == 7 || i == 12 || i == 17 || i == 25 || i == 28 || i == 42 || i == 43);
}

DLL_EXPORT int _get_skltab_show(int i)
{
	return (i == V_WEAPON || i == V_ARMOR || i == V_SPEED || i == V_LIGHT);
}

void set_skltab(void)
{
	int i, use, flag, n;
	int experience_left, raisecost;


	experience_left = experience - experience_used;

	for (flag = use = 0, n = 0; n <= V_MAX; n++) {
		i = get_skltab_index(n);
		if (i == -2) {
			break;
		}

		if (flag && get_skltab_sep(i)) {
			if (use == skltab_max) {
				skltab = xrealloc(skltab, (skltab_max += 8) * sizeof(SKLTAB), MEM_GUI);
			}

			bzero(&skltab[use], sizeof(SKLTAB));
			skltab[use].v = STV_EMPTYLINE;

			use++;
			flag = 0;
		}

		if (i == -1) {
			// negative exp

			if (experience_left >= 0) {
				continue;
			}

			if (use == skltab_max) {
				skltab = xrealloc(skltab, (skltab_max += 8) * sizeof(SKLTAB), MEM_GUI);
			}

			strcpy(skltab[use].name, "Negative experience");
			skltab[use].v = STV_JUSTAVALUE;
			skltab[use].curr = (int)(-1000.0 * experience_left / max(1, experience_used));
			skltab[use].button = 0;

			use++;
			flag = 1;

		} else if (value[0][i] || value[1][i] || get_skltab_show(i)) {
			if (use == skltab_max) {
				skltab = xrealloc(skltab, (skltab_max += 8) * sizeof(SKLTAB), MEM_GUI);
			}

			if (value[1][i] && i != V_DEMON && i != V_COLD && i < V_PROFBASE) {
				skltab[use].button = 1;
			} else {
				skltab[use].button = 0;
			}

			skltab[use].v = i;

			strcpy(skltab[use].name, game_skill[i].name);
			skltab[use].base = value[1][i];
			skltab[use].curr = value[0][i];
			skltab[use].raisecost = raisecost = raise_cost(i, value[1][i]);

			if (experience_left >= 0) {
				if (raisecost > 0 && experience_left >= raisecost) {
					skltab[use].barsize = max(1, raisecost * (SKLWIDTH - 10) / experience_left);
				} else if (experience_left >= 0 && raisecost > 0) {
					skltab[use].barsize = -experience_left * (SKLWIDTH - 10) / raisecost;
				} else {
					skltab[use].barsize = 0;
				}
			} else {
				skltab[use].barsize = 0;
			}

			use++;
			flag = 1;
		}
	}

	skltab_cnt = use;
	max_skloff = max(0, skltab_cnt - SKLDY);

	set_skloff(0, skloff);
}

void set_cmd_invsel(void)
{
	if (context_key_enabled() && con_type == 2 && con_cnt && csprite && invsel != -1) {
		if (item[invsel]) {
			lcmd = CMD_INV_SWAP;
		} else {
			lcmd = CMD_INV_DROP;
		}
	} else if (context_key_enabled() && !con_cnt) {
		if (invsel == -1) {
			return;
		}
		if (item[invsel]) {
			if (csprite) {
				lcmd = CMD_INV_SWAP;
			} else {
				lcmd = CMD_INV_TAKE;
			}
		} else {
			if (csprite) {
				lcmd = CMD_INV_DROP;
			} else {
				lcmd = CMD_INV_TAKE; // show anyway for people who want to click faster than the server responds
			}
		}
	} else {
		if (invsel != -1 && !vk_item && !vk_char && !csprite && item[invsel] && (!con_type || !con_cnt)) {
			lcmd = CMD_INV_USE;
		}
		if (invsel != -1 && !vk_item && !vk_char && !csprite && !item[invsel] && (!con_type || !con_cnt)) {
			lcmd = CMD_INV_USE; // fake
		}
		if (invsel != -1 && !vk_item && !vk_char && csprite && item[invsel] && (!con_type || !con_cnt)) {
			lcmd = CMD_INV_USE_WITH;
		}

		if (invsel != -1 && !vk_item && !vk_char && !csprite && item[invsel] && con_type == 2 && con_cnt) {
			lcmd = CMD_CON_FASTSELL;
		}
		if (invsel != -1 && !vk_item && !vk_char && !csprite && !item[invsel] && con_type == 2 && con_cnt) {
			lcmd = CMD_CON_FASTSELL; // fake
		}
		if (invsel != -1 && !vk_item && !vk_char && csprite && item[invsel] && con_type == 2 && con_cnt) {
			lcmd = CMD_CON_FASTSELL;
		}

		if (invsel != -1 && !vk_item && !vk_char && !csprite && item[invsel] && con_type == 1 && con_cnt) {
			lcmd = CMD_CON_FASTDROP;
		}
		if (invsel != -1 && !vk_item && !vk_char && !csprite && !item[invsel] && con_type == 1 && con_cnt) {
			lcmd = CMD_CON_FASTDROP; // fake
		}
		if (invsel != -1 && !vk_item && !vk_char && csprite && item[invsel] && con_type == 1 && con_cnt) {
			lcmd = CMD_CON_FASTDROP;
		}

		if (invsel != -1 && !vk_item && !vk_char && csprite && !item[invsel]) {
			lcmd = CMD_INV_USE_WITH; // fake
		}
		if (invsel != -1 && vk_item && !vk_char && !csprite && item[invsel]) {
			lcmd = CMD_INV_TAKE;
		}
		if (invsel != -1 && vk_item && !vk_char && !csprite && !item[invsel]) {
			lcmd = CMD_INV_TAKE; // fake - slot is empty so i can't take
		}
		if (invsel != -1 && vk_item && !vk_char && csprite && item[invsel]) {
			lcmd = CMD_INV_SWAP;
		}
		if (invsel != -1 && vk_item && !vk_char && csprite && !item[invsel]) {
			lcmd = CMD_INV_DROP;
		}
	}
}

void set_cmd_weasel(void)
{
	if (context_key_enabled()) {
		if (weasel == -1) {
			return;
		}
		if (item[weatab[weasel]]) {
			if (csprite) {
				lcmd = CMD_WEA_SWAP;
			} else {
				lcmd = CMD_WEA_TAKE;
			}
		} else {
			if (csprite) {
				lcmd = CMD_WEA_DROP;
			} else {
				lcmd = CMD_WEA_TAKE; // show anyway for people who want to click faster than the server responds
			}
		}
	} else {
		if (weasel != -1 && !vk_item && !vk_char && !csprite && item[weatab[weasel]]) {
			lcmd = CMD_WEA_USE;
		}
		if (weasel != -1 && !vk_item && !vk_char && !csprite && !item[weatab[weasel]]) {
			lcmd = CMD_WEA_USE; // fake
		}
		if (weasel != -1 && !vk_item && !vk_char && csprite && item[weatab[weasel]]) {
			lcmd = CMD_WEA_USE_WITH;
		}
		if (weasel != -1 && !vk_item && !vk_char && csprite && !item[weatab[weasel]]) {
			lcmd = CMD_WEA_USE_WITH; // fake
		}
		if (weasel != -1 && vk_item && !vk_char && !csprite && item[weatab[weasel]]) {
			lcmd = CMD_WEA_TAKE;
		}
		if (weasel != -1 && vk_item && !vk_char && !csprite && !item[weatab[weasel]]) {
			lcmd = CMD_WEA_TAKE; // fake - slot is empty so i can't take
		}
		if (weasel != -1 && vk_item && !vk_char && csprite && item[weatab[weasel]]) {
			lcmd = CMD_WEA_SWAP;
		}
		if (weasel != -1 && vk_item && !vk_char && csprite && !item[weatab[weasel]]) {
			lcmd = CMD_WEA_DROP;
		}
	}
}

void set_cmd_consel(void)
{
	if (context_key_enabled()) {
		if (consel == -1 || !con_cnt) {
			return;
		}
		if (con_type == 1) { // grave
			if (!csprite) {
				lcmd = CMD_CON_FASTTAKE;
			} else {
				if (container[consel]) {
					lcmd = CMD_CON_SWAP;
				} else {
					lcmd = CMD_CON_DROP;
				}
			}
		} else { // shop
			if (!csprite) {
				lcmd = CMD_CON_FASTBUY;
			} else {
				lcmd = CMD_CON_SELL;
			}
		}
	} else {
		if (consel != -1 && vk_item && !vk_char && !csprite && con_type == 1 && con_cnt && container[consel]) {
			lcmd = CMD_CON_TAKE;
		}
		if (consel != -1 && vk_item && !vk_char && !csprite && con_type == 1 && con_cnt && !container[consel]) {
			lcmd = CMD_CON_TAKE; // fake - slot is empty so i can't take (buy is also not possible)
		}

		if (consel != -1 && !vk_item && !vk_char && !csprite && con_type == 1 && con_cnt && container[consel]) {
			lcmd = CMD_CON_FASTTAKE;
		}
		if (consel != -1 && !vk_item && !vk_char && !csprite && con_type == 1 && con_cnt && !container[consel]) {
			lcmd = CMD_CON_FASTTAKE; // fake
		}

		if (consel != -1 && vk_item && !vk_char && !csprite && con_type == 2 && con_cnt) {
			lcmd = CMD_CON_BUY;
		}
		if (consel != -1 && !vk_item && !vk_char && !csprite && con_type == 2 && con_cnt) {
			lcmd = CMD_CON_FASTBUY;
		}

		if (consel != -1 && vk_item && !vk_char && csprite && con_type == 1 && con_cnt && container[consel]) {
			lcmd = CMD_CON_SWAP;
		}
		if (consel != -1 && vk_item && !vk_char && csprite && con_type == 1 && con_cnt && !container[consel]) {
			lcmd = CMD_CON_DROP;
		}
		if (consel != -1 && vk_item && !vk_char && csprite && con_type == 2 && con_cnt) {
			lcmd = CMD_CON_SELL;
		}
	}
}

int is_fkey_use_item(int i)
{
	switch (item[i]) {
	case 10290:
	case 10294:
	case 10298:
	case 10302:
	case 10000:
	case 50204:
	case 50205:
	case 50206:
	case 50207:
	case 50208:
	case 50209:
	case 50211:
	case 50212:
		return 0;
	default:
		return item_flags[i] & IF_USE;
	}
}
