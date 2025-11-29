/*
 * Part of Astonia Client (c) Daniel Brockhaus. Please read license.txt.
 *
 * Graphical User Interface - Button and cursor logic
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

#define MAXHELP   24
#define MAXQUEST2 10

// Forward declarations for functions used by exec_cmd
void cmd_add_text(const char *buf, int typ);
void cmd_look_skill(int nr);
void help_drag(void);
void cmd_action(void);

int get_near_button(int x, int y)
{
	int b;
	int n = -1, ndist = 1000000, dist;

	if (x < 0 || y < 0 || x >= XRES || y >= YRES) {
		return -1;
	}

	for (b = 0; b < MAX_BUT; b++) {
		if (but[b].flags & BUTF_NOHIT) {
			continue;
		}

		dist = (butx(b) - x) * (butx(b) - x) + (buty(b) - y) * (buty(b) - y);
		if (dist > but[b].sqhitrad) {
			continue;
		}

		if (dist > ndist) {
			continue;
		}

		ndist = dist;
		n = b;
	}

	return n;
}

void set_button_flags(void)
{
	int b, i;

	if (con_cnt) {
		for (b = BUT_CON_BEG; b <= BUT_CON_END; b++) {
			but[b].flags &= ~BUTF_NOHIT;
		}
		for (b = BUT_SKL_BEG; b <= BUT_SKL_END; b++) {
			but[b].flags |= BUTF_NOHIT;
		}
	} else {
		for (b = BUT_CON_BEG; b <= BUT_CON_END; b++) {
			but[b].flags |= BUTF_NOHIT;
		}
		for (b = BUT_SKL_BEG; b <= BUT_SKL_END; b++) {
			i = skloff + b - BUT_SKL_BEG;
			if (i >= skltab_cnt || !skltab[i].button || skltab[i].barsize <= 0) {
				but[b].flags |= BUTF_NOHIT;
			} else {
				but[b].flags &= ~BUTF_NOHIT;
			}
		}
	}
}

static void set_cmd_cursor(int cmd)
{
	int cursor;

	// cursor
	switch (cmd) {
	case CMD_MAP_MOVE:
		cursor = SDL_CUR_c_only;
		break;
	case CMD_MAP_DROP:
		cursor = SDL_CUR_c_drop;
		break;

	case CMD_ITM_TAKE:
		cursor = SDL_CUR_c_take;
		break;
	case CMD_ITM_USE:
		cursor = SDL_CUR_c_use;
		break;
	case CMD_ITM_USE_WITH:
		cursor = SDL_CUR_c_usewith;
		break;

	case CMD_CHR_ATTACK:
		cursor = SDL_CUR_c_attack;
		break;
	case CMD_CHR_GIVE:
		cursor = SDL_CUR_c_give;
		break;

	case CMD_INV_USE:
		cursor = SDL_CUR_c_use;
		break;
	case CMD_INV_USE_WITH:
		cursor = SDL_CUR_c_usewith;
		break;
	case CMD_INV_TAKE:
		cursor = SDL_CUR_c_take;
		break;
	case CMD_INV_SWAP:
		cursor = SDL_CUR_c_swap;
		break;
	case CMD_INV_DROP:
		cursor = SDL_CUR_c_drop;
		break;

	case CMD_WEA_USE:
		cursor = SDL_CUR_c_use;
		break;
	case CMD_WEA_USE_WITH:
		cursor = SDL_CUR_c_usewith;
		break;
	case CMD_WEA_TAKE:
		cursor = SDL_CUR_c_take;
		break;
	case CMD_WEA_SWAP:
		cursor = SDL_CUR_c_swap;
		break;
	case CMD_WEA_DROP:
		cursor = SDL_CUR_c_drop;
		break;

	case CMD_CON_TAKE:
		cursor = SDL_CUR_c_take;
		break;
	case CMD_CON_FASTTAKE:
		cursor = SDL_CUR_c_take;
		break; // needs different cursor!!!

	case CMD_CON_BUY:
		cursor = SDL_CUR_c_buy;
		break;
	case CMD_CON_FASTBUY:
		cursor = SDL_CUR_c_buy;
		break; // needs different cursor!!!

	case CMD_CON_SWAP:
		cursor = SDL_CUR_c_swap;
		break;
	case CMD_CON_DROP:
		cursor = SDL_CUR_c_drop;
		break;
	case CMD_CON_SELL:
		cursor = SDL_CUR_c_sell;
		break;
	case CMD_CON_FASTSELL:
		cursor = SDL_CUR_c_sell;
		break; // needs different cursor!!!
	case CMD_CON_FASTDROP:
		cursor = SDL_CUR_c_drop;
		break; // needs different cursor!!!

	case CMD_MAP_LOOK:
		cursor = SDL_CUR_c_look;
		break;
	case CMD_ITM_LOOK:
		cursor = SDL_CUR_c_look;
		break;
	case CMD_CHR_LOOK:
		cursor = SDL_CUR_c_look;
		break;
	case CMD_INV_LOOK:
		cursor = SDL_CUR_c_look;
		break;
	case CMD_WEA_LOOK:
		cursor = SDL_CUR_c_look;
		break;
	case CMD_CON_LOOK:
		cursor = SDL_CUR_c_look;
		break;

	case CMD_MAP_CAST_L:
		cursor = SDL_CUR_c_spell;
		break;
	case CMD_ITM_CAST_L:
		cursor = SDL_CUR_c_spell;
		break;
	case CMD_CHR_CAST_L:
		cursor = SDL_CUR_c_spell;
		break;
	case CMD_MAP_CAST_R:
		cursor = SDL_CUR_c_spell;
		break;
	case CMD_ITM_CAST_R:
		cursor = SDL_CUR_c_spell;
		break;
	case CMD_CHR_CAST_R:
		cursor = SDL_CUR_c_spell;
		break;

	case CMD_SKL_RAISE:
		cursor = SDL_CUR_c_raise;
		break;

	case CMD_SAY_HITSEL:
		cursor = SDL_CUR_c_say;
		break;

	case CMD_DROP_GOLD:
		cursor = SDL_CUR_c_drop;
		break;
	case CMD_TAKE_GOLD:
		cursor = SDL_CUR_c_take;
		break;

	case CMD_JUNK_ITEM:
		cursor = SDL_CUR_c_junk;
		break;


	case CMD_SPEED0:
	case CMD_SPEED1:
	case CMD_SPEED2:
		cursor = SDL_CUR_c_set;
		break;

	case CMD_TELEPORT:
		cursor = SDL_CUR_c_take;
		break;

	case CMD_HELP_NEXT:
	case CMD_HELP_PREV:
	case CMD_HELP_CLOSE:
		cursor = SDL_CUR_c_use;
		break;

	case CMD_HELP_MISC:
		if (helpsel != -1) {
			cursor = SDL_CUR_c_use;
		} else if (questsel != -1) {
			cursor = SDL_CUR_c_use;
		} else {
			cursor = SDL_CUR_c_only;
		}
		break;

	case CMD_HELP:
		cursor = SDL_CUR_c_use;
		break;
	case CMD_QUEST:
		cursor = SDL_CUR_c_use;
		break;
	case CMD_EXIT:
		cursor = SDL_CUR_c_use;
		break;
	case CMD_NOLOOK:
		cursor = SDL_CUR_c_use;
		break;

	case CMD_COLOR:
		cursor = SDL_CUR_c_use;
		break;

	case CMD_ACTION:
		cursor = SDL_CUR_c_use;
		break;

	default:
		cursor = SDL_CUR_c_only;
		break;
	}

	if (cur_cursor != cursor) {
		sdl_set_cursor(cursor);
		cur_cursor = cursor;
	}
}

static int handle_captured_button(void)
{
	if (capbut != -1) {
		if (capbut == BUT_GLD) {
			takegold += (mousedy / 2) * (mousedy / 2) * (mousedy <= 0 ? 1 : -1);

			if (takegold < 0) {
				takegold = 0;
			}
			if (takegold > gold) {
				takegold = gold;
			}

			mousedy = 0;
		}
		return 1;
	}
	return 0;
}

static void detect_hover_target(void)
{
	int i, x, y;

	butsel = mapsel = itmsel = chrsel = invsel = weasel = consel = sklsel = sklsel2 = telsel = helpsel = colsel =
	    skl_look_sel = questsel = actsel = -1;

	if ((display_help || display_quest) && mousex >= dotx(DOT_HLP) && mousex <= dotx(DOT_HL2) - 40 &&
	    mousey >= doty(DOT_HLP) && mousey <= doty(DOT_HLP) + 12) {
		butsel = BUT_HELP_DRAG;
	}

	if ((display_help || display_quest) && butsel == -1) {
		if (mousex >= dotx(DOT_HLP) && mousex <= dotx(DOT_HL2) && mousey >= doty(DOT_HLP) && mousey <= doty(DOT_HL2)) {
			butsel = BUT_HELP_MISC;

			if (display_help == 1 && mousex >= dotx(DOT_HLP) + 7 && mousex <= dotx(DOT_HLP) + 136 &&
			    mousey >= 198 + doty(DOT_HLP) && mousey <= 198 + doty(DOT_HLP) + 12 * 10) {
				helpsel = (mousey - (198 + doty(DOT_HLP))) / 10 + 2;
				if (mousex > dotx(DOT_HLP) + 110) {
					helpsel += 12;
				}

				if (helpsel < 2 || helpsel > MAXHELP) {
					helpsel = -1;
				}
			}

			if (display_quest && mousex >= dotx(DOT_HLP) + 165 && mousex <= dotx(DOT_HLP) + 199) {
				int tmp, qy;

				tmp = (mousey - (doty(DOT_HLP) + 16)) / 40;
				qy = tmp * 40 + doty(DOT_HLP) + 16;
				if (tmp >= 0 && tmp <= 8 && mousey >= qy && mousey <= qy + 10) {
					int qos = questonscreen[tmp];
					if ((qos != -1) && (game_questlog[qos].flags & QLF_REPEATABLE) && (quest[qos].flags & QF_DONE) &&
					    quest[qos].done < 10) {
						questsel = tmp;
					}
				}
			}
		}
		if (mousex >= dotx(DOT_HLP) + 177 && mousex <= dotx(DOT_HLP) + 196 && mousey >= doty(DOT_HL2) - 20 &&
		    mousey <= doty(DOT_HL2) - 10) {
			butsel = BUT_HELP_PREV;
		}
		if (mousex >= dotx(DOT_HLP) + 200 && mousex <= dotx(DOT_HLP) + 219 && mousey >= doty(DOT_HL2) - 20 &&
		    mousey <= doty(DOT_HL2) - 10) {
			butsel = BUT_HELP_NEXT;
		}
		if (mousex >= dotx(DOT_HLP) + 211 && mousex <= dotx(DOT_HLP) + 224 && mousey >= doty(DOT_HLP) + 2 &&
		    mousey <= doty(DOT_HLP) + 12) {
			butsel = BUT_HELP_CLOSE;
		}
	}

	if (mousex >= dotx(DOT_TOP) + 704 && mousex <= dotx(DOT_TOP) + 739 && mousey >= doty(DOT_TOP) + 22 &&
	    mousey <= doty(DOT_TOP) + 30) {
		butsel = BUT_HELP;
	}
	if (mousex >= dotx(DOT_TOP) + 741 && mousex <= dotx(DOT_TOP) + 775 && mousey >= doty(DOT_TOP) + 22 &&
	    mousey <= doty(DOT_TOP) + 30) {
		butsel = BUT_QUEST;
	}
	if (mousex >= dotx(DOT_TOP) + 704 && mousex <= dotx(DOT_TOP) + 723 && mousey >= doty(DOT_TOP) + 7 &&
	    mousey <= doty(DOT_TOP) + 18) {
		butsel = BUT_EXIT;
	}

	// hit teleport?
	telsel = get_teleport(mousex, mousey);
	if (telsel != -1) {
		butsel = BUT_TEL;
	}

	colsel = get_color(mousex, mousey);
	if (colsel != -1) {
		butsel = BUT_COLOR;
	}

	if (teleporter && butsel == -1) {
		if (mousex >= dotx(DOT_TEL) && mousex <= dotx(DOT_TEL) + 520 && mousey >= doty(DOT_TEL) &&
		    mousey <= doty(DOT_TEL) + 320) {
			butsel = BUT_TEL_MISC;
		}
	}

	if (show_look && mousex >= dotx(DOT_LOK) + 493 && mousex <= dotx(DOT_LOK) + 500 && mousey >= doty(DOT_LOK) + 3 &&
	    mousey <= doty(DOT_LOK) + 10) {
		butsel = BUT_NOLOOK;
	}

	if (butsel == -1 && context_key_enabled()) {
		butsel = get_near_button(mousex, mousey);
		if (context_action_enabled()) {
			if (butsel >= BUT_ACT_BEG && butsel <= BUT_ACT_END && has_action_skill(butsel - BUT_ACT_BEG)) {
				actsel = butsel - BUT_ACT_BEG;
			}
			if (butsel == BUT_ACT_LCK || butsel == BUT_ACT_OPN)
				;
			else {
				butsel = -1;
			}
		} else {
			if (butsel == BUT_ACT_OPN && mousey > buty(BUT_ACT_OPN))
				;
			else {
				butsel = -1;
			}
		}
	}

	// hit map
	if (!hitsel[0] && butsel == -1 && mousex >= dotx(DOT_MTL) && mousey >= doty(DOT_MTL) && doty(DOT_MBR) &&
	    mousey < doty(DOT_MBR)) {
		if (action_ovr == 13) {
			itmsel = get_near_item(mousex, mousey, CMF_USE | CMF_TAKE, 3);
			if (itmsel == -1) {
				chrsel = get_near_char(mousex, mousey, 3);
			}
			if (itmsel == -1 && chrsel == -1) {
				mapsel = get_near_ground(mousex, mousey);
			}
		} else {
			if (vk_char || (action_ovr != -1 && (action_ovr != 11 || csprite) && action_ovr != 2)) {
				chrsel = get_near_char(mousex, mousey, vk_char ? MAPDX : 3);
			}
			if (chrsel == -1 && (vk_item || action_ovr == 11)) {
				itmsel = get_near_item(mousex, mousey, CMF_USE | CMF_TAKE, csprite ? 0 : MAPDX);
			}
			if (chrsel == -1 && itmsel == -1 && !vk_char && (!vk_item || csprite)) {
				mapsel = get_near_ground(mousex, mousey);
			}

			if (mapsel != -1 || itmsel != -1 || chrsel != -1) {
				butsel = BUT_MAP;
			}
		}
	}

	// skill text lines for hover text
	if (!hitsel[0] && butsel == -1 && !con_cnt) {
		for (i = 0; i <= BUT_SKL_END - BUT_SKL_BEG; i++) {
			x = butx(i + BUT_SKL_BEG);
			y = buty(i + BUT_SKL_BEG);
			if (mousex > x + 10 && mousex < x + SKLWIDTH && mousey > y - 5 && mousey < y + 5) {
				sklsel2 = i;
				break;
			}
		}
	}

	// buttons
	if (!hitsel[0] && butsel == -1) {
		butsel = get_near_button(mousex, mousey);

		// translate button
		if (butsel >= BUT_INV_BEG && butsel <= BUT_INV_END) {
			invsel = 30 + invoff * INVDX + butsel - BUT_INV_BEG;
		} else if (butsel >= BUT_WEA_BEG && butsel <= BUT_WEA_END) {
			weasel = butsel - BUT_WEA_BEG;
		} else if (butsel >= BUT_CON_BEG && butsel <= BUT_CON_END) {
			consel = conoff * CONDX + butsel - BUT_CON_BEG;
		} else if (butsel >= BUT_SKL_BEG && butsel <= BUT_SKL_END) {
			sklsel = skloff + butsel - BUT_SKL_BEG;
		}
	}
}

void exec_cmd(int cmd, int a)
{
	action_ovr = -1;
	context_key_reset();

	switch (cmd) {
	case CMD_NONE:
		return;

	case CMD_MAP_MOVE:
		cmd_move(originx - MAPDX / 2 + mapsel % MAPDX, originy - MAPDY / 2 + mapsel / MAPDX);
		return;
	case CMD_MAP_DROP:
		cmd_drop(originx - MAPDX / 2 + mapsel % MAPDX, originy - MAPDY / 2 + mapsel / MAPDX);
		return;

	case CMD_ITM_TAKE:
		cmd_take(originx - MAPDX / 2 + itmsel % MAPDX, originy - MAPDY / 2 + itmsel / MAPDX);
		return;
	case CMD_ITM_USE:
		cmd_use(originx - MAPDX / 2 + itmsel % MAPDX, originy - MAPDY / 2 + itmsel / MAPDX);
		return;
	case CMD_ITM_USE_WITH:
		cmd_use(originx - MAPDX / 2 + itmsel % MAPDX, originy - MAPDY / 2 + itmsel / MAPDX);
		return;

	case CMD_CHR_ATTACK:
		cmd_kill(map[chrsel].cn);
		return;
	case CMD_CHR_GIVE:
		cmd_give(map[chrsel].cn);
		return;

	case CMD_INV_USE:
		cmd_use_inv(invsel);
		return;
	case CMD_INV_USE_WITH:
		cmd_use_inv(invsel);
		return;
	case CMD_INV_TAKE:
		cmd_swap(invsel);
		return;
	case CMD_INV_SWAP:
		cmd_swap(invsel);
		return;
	case CMD_INV_DROP:
		cmd_swap(invsel);
		return;

	case CMD_CON_FASTDROP:
		cmd_fastsell(invsel);
		return;
	case CMD_CON_FASTSELL:
		cmd_fastsell(invsel);
		return;

	case CMD_WEA_USE:
		cmd_use_inv(weatab[weasel]);
		return;
	case CMD_WEA_USE_WITH:
		cmd_use_inv(weatab[weasel]);
		return;
	case CMD_WEA_TAKE:
		cmd_swap(weatab[weasel]);
		return;
	case CMD_WEA_SWAP:
		cmd_swap(weatab[weasel]);
		return;
	case CMD_WEA_DROP:
		cmd_swap(weatab[weasel]);
		return;

	case CMD_CON_TAKE: // return;
	case CMD_CON_BUY: // return;
	case CMD_CON_SWAP: // return;
	case CMD_CON_DROP: // return;
	case CMD_CON_SELL:
		cmd_con(consel);
		return;
	case CMD_CON_FASTTAKE:
	case CMD_CON_FASTBUY:
		cmd_con_fast(consel);
		return;

	case CMD_MAP_LOOK:
		cmd_look_map(originx - MAPDX / 2 + mapsel % MAPDX, originy - MAPDY / 2 + mapsel / MAPDX);
		return;
	case CMD_ITM_LOOK:
		cmd_look_item(originx - MAPDX / 2 + itmsel % MAPDX, originy - MAPDY / 2 + itmsel / MAPDX);
		return;
	case CMD_CHR_LOOK:
		cmd_look_char(map[chrsel].cn);
		return;
	case CMD_INV_LOOK:
		cmd_look_inv(invsel);
		last_right_click_invsel = invsel;
		return;
	case CMD_WEA_LOOK:
		cmd_look_inv(weatab[weasel]);
		last_right_click_invsel = weatab[weasel];
		return;
	case CMD_CON_LOOK:
		cmd_look_con(consel);
		last_right_click_invsel = INVENTORYSIZE + consel;
		return;

	case CMD_MAP_CAST_L:
		cmd_some_spell(CL_FIREBALL, originx - MAPDX / 2 + mapsel % MAPDX, originy - MAPDY / 2 + mapsel / MAPDX, 0);
		break;
	case CMD_ITM_CAST_L:
		cmd_some_spell(CL_FIREBALL, originx - MAPDX / 2 + itmsel % MAPDX, originy - MAPDY / 2 + itmsel / MAPDX, 0);
		break;
	case CMD_CHR_CAST_L:
		cmd_some_spell(CL_FIREBALL, 0, 0, map[chrsel].cn);
		break;
	case CMD_MAP_CAST_R:
		cmd_some_spell(CL_BALL, originx - MAPDX / 2 + mapsel % MAPDX, originy - MAPDY / 2 + mapsel / MAPDX, 0);
		break;
	case CMD_ITM_CAST_R:
		cmd_some_spell(CL_BALL, originx - MAPDX / 2 + itmsel % MAPDX, originy - MAPDY / 2 + itmsel / MAPDX, 0);
		break;
	case CMD_CHR_CAST_R:
		cmd_some_spell(CL_BALL, 0, 0, map[chrsel].cn);
		break;

	case CMD_SLF_CAST_K:
		cmd_some_spell(a, 0, 0, map[plrmn].cn);
		break;
	case CMD_MAP_CAST_K:
		cmd_some_spell(a, originx - MAPDX / 2 + mapsel % MAPDX, originy - MAPDY / 2 + mapsel / MAPDX, 0);
		break;
	case CMD_CHR_CAST_K:
		cmd_some_spell(a, 0, 0, map[chrsel].cn);
		break;

	case CMD_SKL_RAISE:
		cmd_raise(skltab[sklsel].v);
		break;

	case CMD_INV_OFF_UP:
		set_invoff(0, invoff - 1);
		break;
	case CMD_INV_OFF_DW:
		set_invoff(0, invoff + 1);
		break;
	case CMD_INV_OFF_TR:
		set_invoff(1, 0 /*mousey*/);
		break;

	case CMD_SKL_OFF_UP:
		set_skloff(0, skloff - 1);
		break;
	case CMD_SKL_OFF_DW:
		set_skloff(0, skloff + 1);
		break;
	case CMD_SKL_OFF_TR:
		set_skloff(1, 0 /*mousey*/);
		break;

	case CMD_CON_OFF_UP:
		set_conoff(0, conoff - 1);
		break;
	case CMD_CON_OFF_DW:
		set_conoff(0, conoff + 1);
		break;
	case CMD_CON_OFF_TR:
		set_conoff(1, 0 /*mousey*/);
		break;

	case CMD_SAY_HITSEL:
		cmd_add_text(hitsel, hittype);
		break;

	case CMD_USE_FKEYITEM:
		cmd_use_inv(fkeyitem[a]);
		return;

	case CMD_DROP_GOLD:
		cmd_drop_gold();
		return;
	case CMD_TAKE_GOLD:
		cmd_take_gold(takegold);
		return;

	case CMD_JUNK_ITEM:
		cmd_junk_item();
		return;

	case CMD_SPEED0:
		if (pspeed != 0) {
			cmd_speed(0);
		}
		return;
	case CMD_SPEED1:
		if (pspeed != 1) {
			cmd_speed(1);
		}
		return;
	case CMD_SPEED2:
		if (pspeed != 2) {
			cmd_speed(2);
		}
		return;

	case CMD_TELEPORT:
		if (telsel == 1042) {
			clan_offset = 16 - clan_offset;
		} else {
			if (telsel >= 64 && telsel <= 100) {
				cmd_teleport(telsel + clan_offset);
			} else {
				cmd_teleport(telsel);
			}
		}
		return;
	case CMD_COLOR:
		cmd_color(colsel);
		return;
	case CMD_SKL_LOOK:
		cmd_look_skill(skl_look_sel);
		return;

	case CMD_HELP_NEXT:
		if (display_help) {
			display_help++;
			if (display_help > MAXHELP) {
				display_help = 1;
			}
		}
		if (display_quest) {
			display_quest++;
			if (display_quest > MAXQUEST2) {
				display_quest = 1;
			}
		}
		return;
	case CMD_HELP_PREV:
		if (display_help) {
			display_help--;
			if (display_help < 1) {
				display_help = MAXHELP;
			}
		}
		if (display_quest) {
			display_quest--;
			if (display_quest < 1) {
				display_quest = MAXQUEST2;
			}
		}
		return;
	case CMD_HELP_CLOSE:
		display_help = 0;
		display_quest = 0;
		return;
	case CMD_HELP_MISC:
		if (helpsel > 0 && helpsel <= MAXHELP && display_help) {
			display_help = helpsel;
		}
		if (questsel != -1) {
			quest_select(questsel);
		}
		return;
	case CMD_HELP_DRAG:
		help_drag();
		return;
	case CMD_HELP:
		if (display_help) {
			display_help = 0;
		} else {
			display_help = 1;
			display_quest = 0;
		}
		return;
	case CMD_QUEST:
		if (display_quest) {
			display_quest = 0;
		} else {
			display_quest = 1;
			display_help = 0;
		}
		return;

	case CMD_EXIT:
		quit = 1;
		return;
	case CMD_NOLOOK:
		show_look = 0;
		return;

	case CMD_ACTION:
		cmd_action();
		return;
	case CMD_ACTION_CANCEL:
		return; // action gets cancelled on top
	case CMD_ACTION_LOCK:
		display_action_lock();
		return;
	case CMD_ACTION_OPEN:
		display_action_open();
		return;
	case CMD_WEAR_LOCK:
		display_wear_lock();
		return;
	}
	return;
}

void cmd_look_skill(int nr)
{
	if (nr >= 0 && nr < (*game_v_max)) {
		addline("%s: %s", game_skill[nr].name, game_skilldesc[nr]);
	} else {
		addline("Unknown.");
	}
}

void help_drag(void)
{
	int x, y;

	x = dot[DOT_HLP].x + mousedx;
	y = dot[DOT_HLP].y + mousedy;

	if (x < dotx(DOT_TL)) {
		mousedx += dotx(DOT_TL) - x;
	}
	if (y < doty(DOT_TL)) {
		mousedy += doty(DOT_TL) - y;
	}

	if (x > dotx(DOT_BR) + dotx(DOT_HLP) - dotx(DOT_HL2)) {
		mousedx += dotx(DOT_BR) + dotx(DOT_HLP) - dotx(DOT_HL2) - x;
	}
	if (y > doty(DOT_BR) - 20) {
		mousedy += doty(DOT_BR) - 20 - y;
	}

	dot[DOT_HLP].x += mousedx;
	dot[DOT_HLP].y += mousedy;
	dot[DOT_HL2].x += mousedx;
	dot[DOT_HL2].y += mousedy;
	but[BUT_HELP_DRAG].x += mousedx;
	but[BUT_HELP_DRAG].y += mousedy;

	mousedx = mousedy = 0;
}

void cmd_action(void)
{
	// nag the player to click the lock again
	if (!act_lck) {
		addline("Please disable key-binding mode (the padlock to the left)!");
	}

	switch (actsel) {
	case 0:
	case 1:
	case 2:
	case 11:
	case 13:
		action_ovr = actsel;
		break;

	case 3:
		cmd_some_spell(CL_FLASH, 0, 0, map[plrmn].cn);
		break;
	case 4:
		cmd_some_spell(CL_FREEZE, 0, 0, map[plrmn].cn);
		break;
	case 5:
		cmd_some_spell(CL_MAGICSHIELD, 0, 0, map[plrmn].cn);
		break;
	case 6:
		cmd_some_spell(CL_BLESS, 0, 0, map[plrmn].cn);
		break;
	case 7:
		cmd_some_spell(CL_HEAL, 0, 0, map[plrmn].cn);
		break;
	case 8:
		cmd_some_spell(CL_WARCRY, 0, 0, map[plrmn].cn);
		break;
	case 9:
		cmd_some_spell(CL_PULSE, 0, 0, map[plrmn].cn);
		break;
	case 10:
		cmd_some_spell(CL_FIREBALL, 0, 0, map[plrmn].cn);
		break;
	case 12:
		minimap_toggle();
		break;
	}
}

// Helper functions for set_cmd_states
static void set_cmd_key_states(void)
{
	int km;

	km = gui_keymode();

	vk_shift = (km & SDL_KEYM_SHIFT) || shift_override;
	vk_control = (km & SDL_KEYM_CTRL) || control_override;
	vk_alt = (km & SDL_KEYM_ALT) != 0;

	vk_char = vk_control;
	vk_item = vk_shift;
	vk_spell = vk_alt;
}

static void update_window_title(void)
{
	static char title[256];
	char buf[256];

	plrmn = mapmn(MAPDX / 2, MAPDY / 2);

	sprintf(buf, "%s - Astonia 3 v%d.%d.%d - (%s:%u)",
	    (map[plrmn].cn && player[map[plrmn].cn].name[0]) ? player[map[plrmn].cn].name : "Someone",
	    (VERSION >> 16) & 255, (VERSION >> 8) & 255, (VERSION) & 255, target_server, (unsigned int)target_port);
	if (strcmp(title, buf)) {
		strcpy(title, buf);
		sdl_set_title(title);
	}
}

static void update_fkeyitems(void)
{
	int i, c;
	fkeyitem[0] = fkeyitem[1] = fkeyitem[2] = fkeyitem[3] = 0;
	for (i = 30; i < INVENTORYSIZE; i++) {
		c = (i - 2) % 4;
		if (fkeyitem[c] == 0 && (is_fkey_use_item(i))) {
			fkeyitem[c] = i;
		}
	}
}

static int get_skl_look(int x, int y)
{
	int b, i;
	for (b = BUT_SKL_BEG; b <= BUT_SKL_END; b++) {
		i = skloff + b - BUT_SKL_BEG;
		if (i >= skltab_cnt) {
			continue;
		}
		if (x > but[b].x - 5 && x < but[b].x + 70 && y > but[b].y - 5 && y < but[b].y + 5) {
			return skltab[i].v;
		}
	}
	return -1;
}

void calculate_lcmd_logic(void)
{
	lcmd = CMD_NONE;

	if (context_key_set_cmd()) {
		return;
	}

	if (action_ovr != -1) {
		if (action_ovr == 0 && chrsel != -1) {
			lcmd = CMD_CHR_ATTACK;
		} else if (action_ovr == 1 && chrsel != -1) {
			lcmd = CMD_CHR_CAST_L;
		} else if (action_ovr == 2) {
			lcmd = CMD_MAP_CAST_R;
		} else if (action_ovr == 11) {
			if (itmsel != -1) {
				if (map[itmsel].flags & CMF_TAKE) { // take needs to come first as dropped items can be usable
					lcmd = CMD_ITM_TAKE;
				} else if (map[itmsel].flags & CMF_USE) {
					if (csprite) {
						lcmd = CMD_ITM_USE_WITH;
					} else {
						lcmd = CMD_ITM_USE;
					}
				}
			} else if (chrsel != -1 && csprite) {
				lcmd = CMD_CHR_GIVE;
			} else if (mapsel != -1 && csprite) {
				lcmd = CMD_MAP_DROP;
			}
		} else if (action_ovr == 13) {
			if (itmsel != -1) {
				lcmd = CMD_ITM_LOOK;
			} else if (chrsel != -1) {
				lcmd = CMD_CHR_LOOK;
			} else if (mapsel != -1) {
				lcmd = CMD_MAP_LOOK;
			}
		}
	} else {
		if (mapsel != -1 && !vk_item && !vk_char) {
			lcmd = CMD_MAP_MOVE;
		}
		if (mapsel != -1 && vk_item && !vk_char && csprite) {
			lcmd = CMD_MAP_DROP;
		}

		if (itmsel != -1 && vk_item && !vk_char && !csprite && map[itmsel].flags & CMF_USE) {
			lcmd = CMD_ITM_USE;
		}
		if (itmsel != -1 && vk_item && !vk_char && !csprite && map[itmsel].flags & CMF_TAKE) {
			lcmd = CMD_ITM_TAKE;
		}
		if (itmsel != -1 && vk_item && !vk_char && csprite && map[itmsel].flags & CMF_USE) {
			lcmd = CMD_ITM_USE_WITH;
		}

		if (chrsel != -1 && !vk_item && vk_char && !csprite) {
			lcmd = CMD_CHR_ATTACK;
		}
		if (chrsel != -1 && !vk_item && vk_char && csprite) {
			lcmd = CMD_CHR_GIVE;
		}
	}
}

void handle_special_buttons_logic(void)
{
	if (lcmd == CMD_NONE) {
		if (butsel == BUT_SCR_UP) {
			lcmd = CMD_INV_OFF_UP;
		}
		if (butsel == BUT_SCR_DW) {
			lcmd = CMD_INV_OFF_DW;
		}
		if (butsel == BUT_SCR_TR && !vk_lbut) {
			lcmd = CMD_INV_OFF_TR;
		}

		if (butsel == BUT_SCL_UP && !con_cnt) {
			lcmd = CMD_SKL_OFF_UP;
		}
		if (butsel == BUT_SCL_DW && !con_cnt) {
			lcmd = CMD_SKL_OFF_DW;
		}
		if (butsel == BUT_SCL_TR && !con_cnt && !vk_lbut) {
			lcmd = CMD_SKL_OFF_TR;
		}

		if (butsel == BUT_SCL_UP && con_cnt) {
			lcmd = CMD_CON_OFF_UP;
		}
		if (butsel == BUT_SCL_DW && con_cnt) {
			lcmd = CMD_CON_OFF_DW;
		}
		if (butsel == BUT_SCL_TR && con_cnt && !vk_lbut) {
			lcmd = CMD_CON_OFF_TR;
		}

		if (sklsel != -1) {
			lcmd = CMD_SKL_RAISE;
		}

		if (hitsel[0]) {
			lcmd = CMD_SAY_HITSEL;
		}

		if (vk_item && butsel == BUT_GLD && csprite >= SPR_GOLD_BEG && csprite <= SPR_GOLD_END) {
			lcmd = CMD_DROP_GOLD;
		}
		if (!vk_item && butsel == BUT_GLD && csprite >= SPR_GOLD_BEG && csprite <= SPR_GOLD_END) {
			takegold = cprice;
			lcmd = CMD_TAKE_GOLD;
		}
		if (!vk_item && butsel == BUT_GLD && !csprite) {
			takegold = 0;
			lcmd = CMD_TAKE_GOLD;
		}
		if ((vk_item || csprite) && butsel == BUT_JNK) {
			lcmd = CMD_JUNK_ITEM;
		}

		if (butsel >= BUT_MOD_WALK0 && butsel <= BUT_MOD_WALK2) {
			lcmd = CMD_SPEED0 + butsel - BUT_MOD_WALK0;
		}

		if (butsel == BUT_HELP_MISC) {
			lcmd = CMD_HELP_MISC;
		}
		if (butsel == BUT_HELP_PREV) {
			lcmd = CMD_HELP_PREV;
		}
		if (butsel == BUT_HELP_NEXT) {
			lcmd = CMD_HELP_NEXT;
		}
		if (butsel == BUT_HELP_CLOSE) {
			lcmd = CMD_HELP_CLOSE;
		}
		if (butsel == BUT_HELP_DRAG) {
			lcmd = CMD_HELP_DRAG;
		}
		if (butsel == BUT_EXIT) {
			lcmd = CMD_EXIT;
		}
		if (butsel == BUT_HELP) {
			lcmd = CMD_HELP;
		}
		if (butsel == BUT_QUEST) {
			lcmd = CMD_QUEST;
		}
		if (butsel == BUT_NOLOOK) {
			lcmd = CMD_NOLOOK;
		}

		if (butsel == BUT_ACT_LCK) {
			lcmd = CMD_ACTION_LOCK;
		}
		if (butsel == BUT_ACT_OPN) {
			lcmd = CMD_ACTION_OPEN;
		}
		if (butsel == BUT_WEA_LCK) {
			lcmd = CMD_WEAR_LOCK;
		}
	}
}

void calculate_rcmd_logic(void)
{
	rcmd = CMD_NONE;
	if (action_ovr == -1) {
		skl_look_sel = get_skl_look(mousex, mousey);
		if (con_cnt == 0 && skl_look_sel != -1) {
			rcmd = CMD_SKL_LOOK;
		} else if (!vk_spell) {
			if (mapsel != -1) {
				rcmd = CMD_MAP_LOOK;
			}
			if (itmsel != -1) {
				rcmd = CMD_ITM_LOOK;
			}
			if (chrsel != -1) {
				rcmd = CMD_CHR_LOOK;
			}
			if (context_key_enabled()) {
				if (invsel != -1) {
					rcmd = CMD_INV_USE;
				}
				if (weasel != -1) {
					rcmd = CMD_WEA_USE;
				}
			} else {
				if (invsel != -1) {
					rcmd = CMD_INV_LOOK;
				}
				if (weasel != -1) {
					rcmd = CMD_WEA_LOOK;
				}
				if (consel != -1) {
					rcmd = CMD_CON_LOOK;
				}
			}
		} else {
			if (mapsel != -1) {
				rcmd = CMD_MAP_CAST_R;
			}
			if (itmsel != -1) {
				rcmd = CMD_ITM_CAST_R;
			}
			if (chrsel != -1) {
				rcmd = CMD_CHR_CAST_R;
			}
		}
	} else {
		rcmd = CMD_ACTION_CANCEL;
	}
}

void apply_gear_lock_logic(void)
{
	if (gear_lock) { // gear lock resets cmds to none if on
		// no fast-equip from inventory
		if (invsel != -1 && lcmd == CMD_INV_USE && !(item_flags[invsel] & IF_USE)) {
			lcmd = CMD_NONE;
		}
		if (invsel != -1 && rcmd == CMD_INV_USE && !(item_flags[invsel] & IF_USE)) {
			rcmd = CMD_NONE;
		}

		// no fast-unequip from equipment
		if (weasel != -1 && lcmd == CMD_WEA_USE && !(item_flags[weatab[weasel]] & IF_USE)) {
			lcmd = CMD_NONE;
		}
		if (weasel != -1 && rcmd == CMD_WEA_USE && !(item_flags[weatab[weasel]] & IF_USE)) {
			rcmd = CMD_NONE;
		}

		// no take/swap/drop from equipment unless it is the left-hand-slot (for torches)
		if (weasel != 2 && (lcmd == CMD_WEA_TAKE || lcmd == CMD_WEA_DROP || lcmd == CMD_WEA_SWAP)) {
			lcmd = CMD_NONE;
		}
		if (weasel != 2 && (rcmd == CMD_WEA_TAKE || rcmd == CMD_WEA_DROP || rcmd == CMD_WEA_SWAP)) {
			rcmd = CMD_NONE;
		}
	}
}

void set_cmd_states(void)
{
	set_cmd_key_states();
	set_map_values(map, tick);
	set_mapadd(-map[mapmn(MAPDX / 2, MAPDY / 2)].xadd, -map[mapmn(MAPDX / 2, MAPDY / 2)].yadd);

	update_ui_layout();
	update_window_title();
	update_fkeyitems();

	if (handle_captured_button()) {
		return;
	}

	detect_hover_target();

	calculate_lcmd_logic();

	set_cmd_invsel();
	set_cmd_weasel();
	set_cmd_consel();

	if (telsel != -1) {
		lcmd = CMD_TELEPORT;
	}
	if (colsel != -1) {
		lcmd = CMD_COLOR;
	}
	if (actsel != -1) {
		lcmd = CMD_ACTION;
	}

	handle_special_buttons_logic();

	calculate_rcmd_logic();
	apply_gear_lock_logic();

	// set cursor
	if (vk_rbut) {
		set_cmd_cursor(rcmd);
	} else {
		set_cmd_cursor(lcmd);
	}
}
