/*
 * Part of Astonia Client (c) Daniel Brockhaus. Please read license.txt.
 *
 * Graphical User Interface - Input handling (keyboard and mouse)
 *
 */

#include <inttypes.h>
#include <time.h>
#include <ctype.h>
#include <SDL2/SDL.h>

#include "astonia.h"
#include "gui/gui.h"
#include "gui/gui_private.h"
#include "client/client.h"
#include "game/game.h"
#include "sdl/sdl.h"
#include "modder/modder.h"

void gui_sdl_keyproc(int wparam)
{
	int i;

	if (wparam != SDLK_ESCAPE && wparam != SDLK_F12 && amod_keydown(wparam)) {
		return;
	}

	switch (wparam) {
	case SDLK_ESCAPE:
		cmd_stop();
		context_stop();
		show_look = 0;
		display_gfx = 0;
		teleporter = 0;
		show_tutor = 0;
		display_help = 0;
		display_quest = 0;
		show_color = 0;
		context_key_reset();
		action_ovr = -1;
		minimap_hide();
		if (context_key_enabled()) {
			cmd_reset();
		}
		context_key_set(0);
		return;
	case SDLK_F1:
		if (fkeyitem[0]) {
			exec_cmd(CMD_USE_FKEYITEM, 0);
		}
		return;
	case SDLK_F2:
		if (fkeyitem[1]) {
			exec_cmd(CMD_USE_FKEYITEM, 1);
		}
		return;
	case SDLK_F3:
		if (fkeyitem[2]) {
			exec_cmd(CMD_USE_FKEYITEM, 2);
		}
		return;
	case SDLK_F4:
		if (fkeyitem[3]) {
			exec_cmd(CMD_USE_FKEYITEM, 3);
		}
		return;

	case SDLK_F5:
		cmd_speed(1);
		return;
	case SDLK_F6:
		cmd_speed(0);
		return;
	case SDLK_F7:
		cmd_speed(2);
		return;

	case SDLK_F8:
		nocut ^= 1;
		return;

	case SDLK_F9:
		if (display_quest) {
			display_quest = 0;
		} else {
			display_help = 0;
			display_quest = 1;
		}
		return;

	case SDLK_F10:
		display_vc ^= 1;
		list_mem();
		dd_list_text();
		return;

	case SDLK_F11:
		if (display_help) {
			display_help = 0;
		} else {
			display_quest = 0;
			display_help = 1;
		}
		return;
	case SDLK_F12:
		quit = 1;
		return;

	case SDLK_RETURN:
	case SDLK_KP_ENTER:
		cmd_proc(CMD_RETURN);
		return;
	case SDLK_DELETE:
		cmd_proc(CMD_DELETE);
		return;
	case SDLK_BACKSPACE:
		cmd_proc(CMD_BACK);
		return;
	case SDLK_LEFT:
		cmd_proc(CMD_LEFT);
		return;
	case SDLK_RIGHT:
		cmd_proc(CMD_RIGHT);
		return;
	case SDLK_HOME:
		cmd_proc(CMD_HOME);
		return;
	case SDLK_END:
		cmd_proc(CMD_END);
		return;
	case SDLK_UP:
		cmd_proc(CMD_UP);
		return;
	case SDLK_DOWN:
		cmd_proc(CMD_DOWN);
		return;
	case SDLK_TAB:
		cmd_proc(9);
		return;

	case SDLK_KP_0:
		wparam = '0';
		goto spellbindkey;
	case SDLK_KP_1:
		wparam = '1';
		goto spellbindkey;
	case SDLK_KP_2:
		wparam = '2';
		goto spellbindkey;
	case SDLK_KP_3:
		wparam = '3';
		goto spellbindkey;
	case SDLK_KP_4:
		wparam = '4';
		goto spellbindkey;
	case SDLK_KP_5:
		wparam = '5';
		goto spellbindkey;
	case SDLK_KP_6:
		wparam = '6';
		goto spellbindkey;
	case SDLK_KP_7:
		wparam = '7';
		goto spellbindkey;
	case SDLK_KP_8:
		wparam = '8';
		goto spellbindkey;
	case SDLK_KP_9:
		wparam = '9';
		goto spellbindkey;

	case 'm':
		if (vk_shift && vk_control && !context_key_enabled()) {
			minimap_toggle();
		} else {
			goto spellbindkey;
		}
		return;

	case '0':
	case '1':
	case '2':
	case '3':
	case '4':
	case '5':
	case '6':
	case '7':
	case '8':
	case '9':
	case 'a':
	case 'b':
	case 'c':
	case 'd':
	case 'e':
	case 'f':
	case 'g':
	case 'h':
	case 'i':
	case 'j':
	case 'k':
	case 'l':
	case 'n':
	case 'o':
	case 'p':
	case 'q':
	case 'r':
	case 's':
	case 't':
	case 'u':
	case 'v':
	case 'w':
	case 'x':
	case 'y':
	case 'z':
	spellbindkey:
		if (!vk_item && !vk_char && !vk_spell) {
			context_keydown(wparam);
			return;
		}

		wparam = toupper(wparam);

		for (i = 0; i < max_keytab; i++) {
			if (keytab[i].keycode != wparam && keytab[i].userdef != wparam) {
				continue;
			}

			if ((keytab[i].vk_item && !vk_item) || (!keytab[i].vk_item && vk_item)) {
				continue;
			}
			if ((keytab[i].vk_char && !vk_char) || (!keytab[i].vk_char && vk_char)) {
				continue;
			}
			if ((keytab[i].vk_spell && !vk_spell) || (!keytab[i].vk_spell && vk_spell)) {
				continue;
			}

			if (keytab[i].cl_spell) {
				if (keytab[i].tgt == TGT_MAP) {
					exec_cmd(CMD_MAP_CAST_K, keytab[i].cl_spell);
				} else if (keytab[i].tgt == TGT_CHR) {
					exec_cmd(CMD_CHR_CAST_K, keytab[i].cl_spell);
				} else if (keytab[i].tgt == TGT_SLF) {
					exec_cmd(CMD_SLF_CAST_K, keytab[i].cl_spell);
				} else {
					return; // hu ?
				}
				keytab[i].usetime = now;
				return;
			}
			return;
		}
		return;

	case SDLK_PAGEUP:
		dd_text_pageup();
		break;
	case SDLK_PAGEDOWN:
		dd_text_pagedown();
		break;

	case '+':
	case '=':
		if (!context_key_isset()) {
			context_action_enable(1);
		}
		break;
	case '-':
		if (!context_key_isset()) {
			context_action_enable(0);
		}
		break;

		// case '<':               dd_sceweup(); break;

	case SDLK_INSERT:
		if (vk_shift && !vk_control && !vk_alt) {
			gui_insert();
		}
		break;
	}
}

void gui_sdl_mouseproc(int x, int y, int what, int clicks)
{
	int delta, tmp;
	static int mdown = 0;

	switch (what) {
	case SDL_MOUM_NONE:
		mousex = x;
		mousey = y;

		if (capbut != -1) {
			if (mousex != XRES / 2 || mousey != YRES / 2) {
				mousedx += (mousex - (XRES / 2)) / sdl_scale;
				mousedy += (mousey - (YRES / 2)) / sdl_scale;
				sdl_set_cursor_pos(XRES / 2, YRES / 2);
			}
		}

		mousex /= sdl_scale;
		mousey /= sdl_scale;
		mousex -= dd_offset_x();
		mousey -= dd_offset_y();

		if (butsel != -1 && vk_lbut && (but[butsel].flags & BUTF_MOVEEXEC)) {
			exec_cmd(lcmd, 0);
		}

		amod_mouse_move(mousex, mousey);
		break;

	case SDL_MOUM_LDOWN:
		vk_lbut = 1;

		if (amod_mouse_click(mousex, mousey, what)) {
			break;
		}

		if (butsel != -1 && capbut == -1 && (but[butsel].flags & BUTF_CAPTURE)) {
			amod_mouse_capture(1);
			sdl_show_cursor(0);
			sdl_capture_mouse(1);
			mousedx = 0;
			mousedy = 0;
			sdl_set_cursor_pos(XRES / 2, YRES / 2);
			capbut = butsel;
		}
		break;


	case SDL_MOUM_MUP:
		shift_override = 0;
		control_override = 0;
		mdown = 0;
		if ((game_options & GO_WHEEL) && special_tab[vk_special].spell) {
			if (special_tab[vk_special].target == TGT_MAP) {
				exec_cmd(CMD_MAP_CAST_K, special_tab[vk_special].spell);
			} else if (special_tab[vk_special].target == TGT_CHR) {
				exec_cmd(CMD_CHR_CAST_K, special_tab[vk_special].spell);
			} else if (special_tab[vk_special].target == TGT_SLF) {
				exec_cmd(CMD_SLF_CAST_K, special_tab[vk_special].spell);
			}
			break;
		}
		// fall through intended
	case SDL_MOUM_LUP:
		vk_lbut = 0;

		if (amod_mouse_click(mousex, mousey, what)) {
			break;
		}
		if (context_click(mousex, mousey)) {
			break;
		}

		if (capbut != -1) {
			sdl_set_cursor_pos(
			    (but[capbut].x + dd_offset_x()) * sdl_scale, (but[capbut].y + dd_offset_y()) * sdl_scale);
			sdl_capture_mouse(0);
			sdl_show_cursor(1);
			amod_mouse_capture(0);
			if (!(but[capbut].flags & BUTF_MOVEEXEC)) {
				exec_cmd(lcmd, 0);
			}
			capbut = -1;
		} else {
			if ((tmp = context_key_click()) != CMD_NONE) {
				exec_cmd(tmp, 0);
			} else {
				exec_cmd(lcmd, 0);
			}
		}
		break;

	case SDL_MOUM_RDOWN:
		vk_rbut = 1;
		if (amod_mouse_click(mousex, mousey, what)) {
			break;
		}
		context_stop();
		break;

	case SDL_MOUM_RUP:
		vk_rbut = 0;
		if (amod_mouse_click(mousex, mousey, what)) {
			break;
		}
		if (rcmd == CMD_MAP_LOOK && context_open(mousex, mousey)) {
			break;
		}
		context_stop();
		exec_cmd(rcmd, 0);
		break;

	case SDL_MOUM_WHEEL:
		delta = y;

		if (amod_mouse_click(0, delta, what)) {
			break;
		}

		if (mousex >= dotx(DOT_SKL) && mousex < dotx(DOT_SK2) && mousey >= doty(DOT_SKL) &&
		    mousey < doty(DOT_SK2)) { // skill / depot / merchant
			while (delta > 0) {
				if (!con_cnt) {
					set_skloff(0, skloff - 1);
				} else {
					set_conoff(0, conoff - 1);
				}
				delta--;
			}
			while (delta < 0) {
				if (!con_cnt) {
					set_skloff(0, skloff + 1);
				} else {
					set_conoff(0, conoff + 1);
				}
				delta++;
			}
			break;
		}

		if (mousex >= dotx(DOT_TXT) && mousex < dotx(DOT_TX2) && mousey >= doty(DOT_TXT) &&
		    mousey < doty(DOT_TX2)) { // chat
			while (delta > 0) {
				dd_text_lineup();
				dd_text_lineup();
				dd_text_lineup();
				delta--;
			}
			while (delta < 0) {
				dd_text_linedown();
				dd_text_linedown();
				dd_text_linedown();
				delta++;
			}
			break;
		}

		if (mousex >= dotx(DOT_IN1) && mousex < dotx(DOT_IN2) && mousey >= doty(DOT_IN1) &&
		    mousey < doty(DOT_IN2)) { // inventory
			while (delta > 0) {
				set_invoff(0, invoff - 1);
				delta--;
			}
			while (delta < 0) {
				set_invoff(0, invoff + 1);
				delta++;
			}
			break;
		}

		if (game_options & GO_WHEEL) {
			while (delta > 0) {
				vk_special_inc();
				delta--;
			}
			while (delta < 0) {
				vk_special_dec();
				delta++;
			}
			vk_special_time = now;

			if (mdown) {
				shift_override = special_tab[vk_special].shift_over;
				control_override = special_tab[vk_special].control_over;
			}
		}
		break;

	case SDL_MOUM_MDOWN:
		if (game_options & GO_WHEEL) {
			shift_override = special_tab[vk_special].shift_over;
			control_override = special_tab[vk_special].control_over;
		} else {
			shift_override = 1;
		}
		mdown = 1;
		break;
	}
}
