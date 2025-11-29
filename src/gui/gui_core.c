/*
 * Part of Astonia Client (c) Daniel Brockhaus. Please read license.txt.
 *
 * Graphical User Interface - Core initialization and main loop
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

// Forward declarations for functions used by gui_insert
void cmd_add_text(const char *buf, int typ);

uint64_t gui_time_misc = 0;

DLL_EXPORT int game_slowdown = 0;

// globals

int skip = 1, idle = 0, tota = 1, frames = 0;

// globals display

int display_vc = 0;
int display_help = 0, display_quest = 0;

int playersprite_override = 0;
int nocut = 0;

int update_skltab = 0;
int show_look = 0;

int gui_topoff; // offset of the top bar *above* the top of the window (0 ... -38)

DLL_EXPORT unsigned short int healthcolor, manacolor, endurancecolor, shieldcolor;
DLL_EXPORT unsigned short int whitecolor, lightgraycolor, graycolor, darkgraycolor, blackcolor;
DLL_EXPORT unsigned short int lightredcolor, redcolor, darkredcolor;
DLL_EXPORT unsigned short int lightgreencolor, greencolor, darkgreencolor;
DLL_EXPORT unsigned short int lightbluecolor, bluecolor, darkbluecolor;

// Global variables from gui.c
DLL_EXPORT unsigned short int textcolor;
DLL_EXPORT unsigned short int lightorangecolor, orangecolor, darkorangecolor;

unsigned int now;

int cur_cursor = 0;
int mousex = 300, mousey = 300, vk_rbut, vk_lbut, shift_override = 0, control_override = 0;
DLL_EXPORT int vk_shift, vk_control, vk_alt;
int mousedx, mousedy;
int vk_item, vk_char, vk_spell;

int vk_special = 0, vk_special_time = 0;

// globals wea

DLL_EXPORT int weatab[12] = {9, 6, 8, 11, 0, 1, 2, 4, 5, 3, 7, 10};
char weaname[12][32] = {"RING", "HAND", "HAND", "RING", "NECK", "HEAD", "BACK", "BODY", "BELT", "ARMS", "LEGS", "FEET"};

KEYTAB keytab[] = {
    {'1', 0, 0, 1, 0, "FIREBALL", TGT_CHR, CL_FIREBALL, V_FIREBALL},
    {'2', 0, 0, 1, 0, "LIGHTNINGBALL", TGT_CHR, CL_BALL, V_FLASH},
    {'3', 0, 0, 1, 0, "FLASH", TGT_SLF, CL_FLASH, V_FLASH},
    {'4', 0, 0, 1, 0, "FREEZE", TGT_SLF, CL_FREEZE, V_FREEZE},
    {'5', 0, 0, 1, 0, "SHIELD", TGT_SLF, CL_MAGICSHIELD, V_MAGICSHIELD},
    {'6', 0, 0, 1, 0, "BLESS", TGT_CHR, CL_BLESS, V_BLESS},
    {'7', 0, 0, 1, 0, "HEAL", TGT_CHR, CL_HEAL, V_HEAL},
    {'8', 0, 0, 1, 0, "WARCRY", TGT_SLF, CL_WARCRY, V_WARCRY},
    {'9', 0, 0, 1, 0, "PULSE", TGT_SLF, CL_PULSE, V_PULSE},
    {'0', 0, 0, 1, 0, "FIRERING", TGT_SLF, CL_FIREBALL, V_FIREBALL},

    {'1', 0, 0, 1, 1, "FIREBALL", TGT_CHR, CL_FIREBALL, V_FIREBALL},
    {'2', 0, 0, 1, 1, "LIGHTNINGBALL", TGT_CHR, CL_BALL, V_FLASH},
    {'3', 0, 0, 1, 1, "FLASH", TGT_SLF, CL_FLASH, V_FLASH},
    {'4', 0, 0, 1, 1, "FREEZE", TGT_SLF, CL_FREEZE, V_FREEZE},
    {'5', 0, 0, 1, 1, "SHIELD", TGT_SLF, CL_MAGICSHIELD, V_MAGICSHIELD},
    {'6', 0, 0, 1, 1, "BLESS", TGT_CHR, CL_BLESS, V_BLESS},
    {'7', 0, 0, 1, 1, "HEAL", TGT_CHR, CL_HEAL, V_HEAL},
    {'8', 0, 0, 1, 1, "WARCRY", TGT_SLF, CL_WARCRY, V_WARCRY},
    {'9', 0, 0, 1, 1, "PULSE", TGT_SLF, CL_PULSE, V_PULSE},
    {'0', 0, 0, 1, 1, "FIRERING", TGT_SLF, CL_FIREBALL, V_FIREBALL},

    {'1', 0, 0, 0, 1, "FIREBALL", TGT_MAP, CL_FIREBALL, V_FIREBALL},
    {'2', 0, 0, 0, 1, "LIGHTNINGBALL", TGT_MAP, CL_BALL, V_FLASH},
    {'3', 0, 0, 0, 1, "FLASH", TGT_SLF, CL_FLASH, V_FLASH},
    {'4', 0, 0, 0, 1, "FREEZE", TGT_SLF, CL_FREEZE, V_FREEZE},
    {'5', 0, 0, 0, 1, "SHIELD", TGT_SLF, CL_MAGICSHIELD, V_MAGICSHIELD},
    {'6', 0, 0, 0, 1, "BLESS SELF", TGT_SLF, CL_BLESS, V_BLESS},
    {'7', 0, 0, 0, 1, "HEAL SELF", TGT_SLF, CL_HEAL, V_HEAL},
    {'8', 0, 0, 0, 1, "WARCRY", TGT_SLF, CL_WARCRY, V_WARCRY},
    {'9', 0, 0, 0, 1, "PULSE", TGT_SLF, CL_PULSE, V_PULSE},
    {'0', 0, 0, 0, 1, "FIRERING", TGT_SLF, CL_FIREBALL, V_FIREBALL},
};

int max_keytab = sizeof(keytab) / sizeof(KEYTAB);

struct special_tab special_tab[] = {{"Walk", 0, 0, 0, 0, 0}, {"Use/Take", 1, 0, 0, 0, 0},
    {"Attack/Give", 0, 1, 0, 0, 0}, {"Warcry", 0, 0, CL_WARCRY, TGT_SLF, V_WARCRY},
    {"Pulse", 0, 0, CL_PULSE, TGT_SLF, V_PULSE}, {"Fireball-CHAR", 0, 1, CL_FIREBALL, TGT_CHR, V_FIREBALL},
    {"Fireball-MAP", 0, 0, CL_FIREBALL, TGT_MAP, V_FIREBALL}, {"Firering", 0, 0, CL_FIREBALL, TGT_SLF, V_FIREBALL},
    {"LBall-CHAR", 0, 1, CL_BALL, TGT_CHR, V_FLASH}, {"LBall-MAP", 0, 0, CL_BALL, TGT_MAP, V_FLASH},
    {"Flash", 0, 0, CL_FLASH, TGT_SLF, V_FLASH}, {"Freeze", 0, 0, CL_FREEZE, TGT_SLF, V_FREEZE},
    {"Shield", 0, 0, CL_MAGICSHIELD, TGT_SLF, V_MAGICSHIELD}, {"Bless-SELF", 0, 0, CL_BLESS, TGT_SLF, V_BLESS},
    {"Bless-CHAR", 0, 1, CL_BLESS, TGT_CHR, V_BLESS}, {"Heal-SELF", 0, 0, CL_HEAL, TGT_SLF, V_HEAL},
    {"Heal-CHAR", 0, 1, CL_HEAL, TGT_CHR, V_HEAL}};
int max_special = sizeof(special_tab) / sizeof(special_tab[0]);

int fkeyitem[4];

// globals cmd

int plrmn; // mn of player
int mapsel; // mn
int itmsel; // mn
int chrsel; // mn
int invsel; // index into item
int weasel; // index into weatab
int consel; // index into item
int sklsel;
int sklsel2;
int butsel; // is always set, if any of the others is set
int telsel;
int helpsel;
int questsel;
int colsel;
int actsel;
int skl_look_sel;
int last_right_click_invsel = -1;

int action_ovr = -1;

int capbut = -1; // the button capturing the mouse

int takegold; // the amout of gold to take

char hitsel[256]; // something in the text (dx_drawtext()) is selected
int hittype = 0;

DLL_EXPORT SKLTAB *skltab = NULL;
int skltab_max = 0;
DLL_EXPORT int skltab_cnt = 0;

int invoff, max_invoff;
int conoff, max_conoff;
int skloff, max_skloff;
int __skldy;
int __invdy;

int lcmd;
int rcmd;

// Function pointers for skill table and help display
int (*do_display_help)(int) = _do_display_help;
int (*get_skltab_sep)(int i) = _get_skltab_sep;
int (*get_skltab_show)(int i) = _get_skltab_show;
int (*get_skltab_index)(int n) = _get_skltab_index;

// transformation

int mapoffx, mapoffy;
int mapaddx, mapaddy; // small offset to smoothen walking

int nextframe, nexttick;
uint64_t gui_time_network = 0;
uint64_t gui_frametime = 0;
uint64_t gui_ticktime = 0;

#define MAXHELP   24
#define MAXQUEST2 10

// Forward declarations for functions in other GUI modules
void set_invoff(int bymouse, int ny);
void set_skloff(int bymouse, int ny);
void set_conoff(int bymouse, int ny);
void display(void);
int calc_tick_delay_short(int size);
int calc_tick_delay_normal(int size);

void init_colors(void)
{
	whitecolor = IRGB(31, 31, 31);
	lightgraycolor = IRGB(28, 28, 28);
	graycolor = IRGB(22, 22, 22);
	darkgraycolor = IRGB(15, 15, 15);
	blackcolor = IRGB(0, 0, 0);

	lightredcolor = IRGB(31, 0, 0);
	redcolor = IRGB(22, 0, 0);
	darkredcolor = IRGB(15, 0, 0);

	lightgreencolor = IRGB(0, 31, 0);
	greencolor = IRGB(0, 22, 0);
	darkgreencolor = IRGB(0, 15, 0);

	lightbluecolor = IRGB(5, 15, 31);
	bluecolor = IRGB(3, 10, 22);
	darkbluecolor = IRGB(1, 5, 15);

	lightorangecolor = IRGB(31, 20, 16);
	orangecolor = IRGB(31, 16, 8);
	darkorangecolor = IRGB(15, 8, 4);

	textcolor = IRGB(27, 22, 22);

	healthcolor = lightredcolor;
	manacolor = lightbluecolor;
	endurancecolor = IRGB(31, 31, 5);
	shieldcolor = IRGB(31, 15, 5);
}

int main_init(void)
{
	init_colors();
	init_dots();

	set_invoff(0, 0);
	set_skloff(0, 0);
	set_conoff(0, 0);

	init_game(dotx(DOT_MCT), doty(DOT_MCT));

	minimap_init();

	return 0;
}

void main_exit(void)
{
	xfree(dot);
	dot = NULL;
	xfree(but);
	but = NULL;
	xfree(skltab);
	skltab = NULL;
	skltab_max = 0;
	skltab_cnt = 0;

	exit_game();
}

void flip_at(unsigned int t)
{
	unsigned int tnow;
	int sdl_pre_do(int curtick);

	do {
		sdl_loop();
		if (!sdl_is_shown() || !sdl_pre_do(tick)) {
			SDL_Delay(1);
		}
		tnow = SDL_GetTicks();
	} while (t > tnow);

	if (sdl_is_shown()) {
		sdl_render();
	}
}

int main_loop(void)
{
	void prefetch_game(int attick);
	int64_t timediff;
	int tmp, ltick = 0, attick;
	long long start;
	int do_one_tick = 1;
	uint64_t gui_last_frame = 0, gui_last_tick = 0;

	amod_gamestart();

	nexttick = SDL_GetTicks() + MPT;
	nextframe = SDL_GetTicks() + MPF;

	while (!quit) {
		now = SDL_GetTicks();

		start = SDL_GetTicks64();
		poll_network();

		// synchronise frames and ticks if at the same speed
		if (sockstate == 4 && MPF == MPT) {
			nextframe = nexttick;
		}

		// check if we can go on
		if (sockstate > 2) {
			// decode as many ticks as we can
			// and add their contents to the prefetch queue
			while ((attick = next_tick())) {
				if (!(attick & 3) || !game_slowdown) {
					prefetch_game(attick);
				}
			}

			// get one tick to display?
			timediff = nexttick - SDL_GetTicks();
			if (timediff < 0 ||
			    nexttick <= nextframe) { // do ticks when they are due, or before the corresponding frame is shown
				do_one_tick = 1;
				gui_ticktime = SDL_GetTicks64() - gui_last_tick;
				gui_last_tick = SDL_GetTicks64();
				do_tick();
				ltick++;

				if (sockstate == 4 && ltick % TICKS == 0) {
					cl_ticker();
				}
				amod_tick();
#ifdef ENABLE_SHAREDMEM
				sharedmem_update();
#endif
			}
		}

		if (sockstate == 4) {
			timediff = nextframe - SDL_GetTicks();
		} else {
			timediff = 1;
		}
		gui_time_network += SDL_GetTicks64() - start;

		if (timediff > -MPF / 2) {
#ifdef TICKPRINT
			printf("Display tick %d\n", tick);
#endif
			gui_frametime = SDL_GetTicks64() - gui_last_frame;
			gui_last_frame = SDL_GetTicks64();

			if (sdl_is_shown() && (!(tick & 3) || !game_slowdown || sockstate != 4)) {
				sdl_clear();
				display();
				amod_frame();
				display_mouseover();
				minimap_update();
			}

			timediff = nextframe - SDL_GetTicks();
			if (timediff > 0) {
				idle += timediff;
			} else {
				skip -= timediff;
			}

			frames++;

			flip_at(nextframe);
		} else {
#ifdef TICKPRINT
			printf("Skip tick %d\n", tick);
#endif
			skip -= timediff;

			sdl_loop();
		}

		if (do_one_tick) {
			if (game_options & GO_SHORT) {
				tmp = calc_tick_delay_short(lasttick + q_size);
			} else {
				tmp = calc_tick_delay_normal(lasttick + q_size);
			}
			nexttick += tmp;
			tota += tmp;
			if (tick % 24 == 0) {
				tota /= 2;
				skip /= 2;
				idle /= 2;
				frames /= 2;
			}

			do_one_tick = 0;
		}

		nextframe += MPF;

		// try to sync frame to tick?
		if (abs(nexttick - nextframe) < MPF / 2) {
			nextframe = nexttick;
		}
	}

	close_client();

	return 0;
}

int calc_tick_delay_short(int size)
{
	int tmp;
	switch (size) {
	case 0:
		tmp = MPT * 2.00;
		break;
	case 1:
		tmp = MPT * 1.25;
		break;
	case 2:
		tmp = MPT * 1.10;
		break;
	case 3:
		tmp = MPT;
		break; // optimal
	case 4:
		tmp = MPT - 1;
		break;
	case 5:
		tmp = MPT - 1;
		break;
	case 6:
		tmp = MPT * 0.90;
		break;
	case 7:
		tmp = MPT * 0.75;
		break;
	case 8:
		tmp = MPT * 0.60;
		break;
	case 9:
		tmp = MPT * 0.50;
		break;
	default:
		tmp = MPT * 0.25;
		break;
	}
	return tmp;
}

int calc_tick_delay_normal(int size)
{
	int tmp;
	switch (size) {
	case 0:
		tmp = MPT * 2.00;
		break;
	case 1:
		tmp = MPT * 1.50;
		break;
	case 2:
		tmp = MPT * 1.40;
		break;
	case 3:
		tmp = MPT * 1.25;
		break;
	case 4:
		tmp = MPT * 1.10;
		break;
	case 5:
		tmp = MPT + 1;
		break;
	case 6:
		tmp = MPT;
		break; // optimal
	case 7:
		tmp = MPT - 1;
		break;
	case 8:
		tmp = MPT - 1;
		break;
	case 9:
		tmp = MPT * 0.90;
		break;
	case 10:
		tmp = MPT * 0.75;
		break;
	case 11:
		tmp = MPT * 0.60;
		break;
	case 12:
		tmp = MPT * 0.50;
		break;
	default:
		tmp = MPT * 0.25;
		break;
	}
	return tmp;
}

int vk_special_dec(void)
{
	int n, panic = 99;

	for (n = (vk_special + max_special - 1) % max_special; panic--; n = (n + max_special - 1) % max_special) {
		if (!special_tab[n].req || value[0][special_tab[n].req]) {
			vk_special = n;
			return 1;
		}
	}
	return 0;
}

int vk_special_inc(void)
{
	int n, panic = 99;

	for (n = (vk_special + 1) % max_special; panic--; n = (n + 1) % max_special) {
		if (!special_tab[n].req || value[0][special_tab[n].req]) {
			vk_special = n;
			return 1;
		}
	}
	return 0;
}

void gui_insert(void)
{
	char *text;

	text = SDL_GetClipboardText();

	if (text != NULL) {
		cmd_add_text(text, 0);
		SDL_free(text);
	}
}

int gui_keymode(void)
{
	SDL_Keymod km;
	int ret = 0;

	km = SDL_GetModState();
	if (km & KMOD_SHIFT) {
		ret |= SDL_KEYM_SHIFT;
	}
	if (km & KMOD_CTRL) {
		ret |= SDL_KEYM_CTRL;
	}
	if (km & KMOD_ALT) {
		ret |= SDL_KEYM_ALT;
	}

	return ret;
}

void gui_dump(FILE *fp)
{
	fprintf(fp, "GUI datadump:\n");

	fprintf(fp, "skip: %d\n", skip);
	fprintf(fp, "idle: %d\n", idle);
	fprintf(fp, "tota: %d\n", tota);
	fprintf(fp, "frames: %d\n", frames);

	fprintf(fp, "\n");
}
