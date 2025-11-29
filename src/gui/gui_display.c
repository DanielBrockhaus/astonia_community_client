/*
 * Part of Astonia Client (c) Daniel Brockhaus. Please read license.txt.
 *
 * Graphical User Interface - Display rendering functions
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

void display_helpandquest(void)
{
	if (display_help || display_quest) {
		render_sprite(opt_sprite(995), dotx(DOT_HLP), doty(DOT_HLP), RENDERFX_NORMAL_LIGHT, RENDER_ALIGN_NORMAL);
	}

	if (display_help) {
		do_display_help(display_help);
	}
	if (display_quest) {
		do_display_questlog(display_quest);
	}
}

char perf_text[256];

static void display_toplogic(void)
{
	static int top_opening = 0, top_closing = 1, top_open = 0;
	static int topframes = 0;

	if (mousey < 10) {
		topframes++;
	} else {
		topframes = 0;
	}

	if (topframes > frames_per_second / 2 && !top_opening && !top_open) {
		top_opening = 1;
		top_closing = 0;
	}
	if (mousey > 60 && !top_closing && top_open) {
		top_closing = 1;
		top_opening = 0;
	}

	if (top_opening) {
		gui_topoff = -38 + top_opening;
		top_opening += 6;
		if (top_opening >= 38) {
			top_open = 1;
			top_opening = 0;
		}
	}

	if (top_open) {
		gui_topoff = 0;
	}

	if (top_closing) {
		gui_topoff = -top_closing;
		top_closing += 6;
		if (top_closing >= 38) {
			top_open = 0;
			top_closing = 0;
		}
	}
}

void display_wheel(void)
{
	int i;

	render_push_clip();
	render_more_clip(0, 0, 800, 600);

	if (now - vk_special_time < 2000) {
		int n, panic = 99;

		render_shaded_rect(mousex + 5, mousey - 7 - 20, mousex + 71, mousey + 31, 0x0000, 95);

		for (n = (vk_special + 1) % max_special, i = -1; panic-- && i > -3; n = (n + 1) % max_special) {
			if (!special_tab[n].req || value[0][special_tab[n].req]) {
				render_text(mousex + 9, mousey - 3 + i * 10, graycolor, RENDER_TEXT_LEFT, special_tab[n].name);
				i--;
			}
		}
		render_text(mousex + 9, mousey - 3, whitecolor, RENDER_TEXT_LEFT, special_tab[vk_special].name);

		for (n = (vk_special + max_special - 1) % max_special, i = 1; panic-- && i < 3;
		    n = (n + max_special - 1) % max_special) {
			if (!special_tab[n].req || value[0][special_tab[n].req]) {
				render_text(mousex + 9, mousey - 3 + i * 10, graycolor, RENDER_TEXT_LEFT, special_tab[n].name);
				i++;
			}
		}
	}
	render_pop_clip();
}

void dx_copysprite_emerald(int scrx, int scry, int emx, int emy)
{
	RenderFX ddfx;

	bzero(&ddfx, sizeof(ddfx));
	ddfx.sprite = 37;
	ddfx.align = RENDER_ALIGN_OFFSET;
	ddfx.clipsx = emx * 10;
	ddfx.clipsy = emy * 10;
	ddfx.clipex = ddfx.clipsx + 10;
	ddfx.clipey = ddfx.clipsy + 10;
	ddfx.ml = ddfx.ll = ddfx.rl = ddfx.ul = ddfx.dl = RENDERFX_NORMAL_LIGHT;
	ddfx.scale = 100;
	render_sprite_fx(&ddfx, scrx - ddfx.clipsx - 5, scry - ddfx.clipsy - 5);
}

size_t get_memory_usage(void);

void display(void)
{
	extern int memptrs[MAX_MEM];
	extern int memsize[MAX_MEM];
	extern int memused;
	extern int memptrused;
	extern long long sdl_time_make, sdl_time_tex, sdl_time_tex_main, sdl_time_text, sdl_time_blit;
	int t, tmp;
	long long start = SDL_GetTicks64();

#if 0
	// Performance for stuff happening during the actual tick only.
	// So zero them now after preload is done.
	sdl_time_make=0;
	sdl_time_tex=0;
	sdl_time_text=0;
	sdl_time_blit=0;
#endif

	if ((tmp = sdl_check_mouse())) {
		mousex = -1;
		if (tmp == -1) {
			mousey = 0;
		} else {
			mousey = YRES / 2;
		}
	}

	display_toplogic();
	if (game_slowdown) {
		display_toplogic();
		display_toplogic();
		display_toplogic();
	}

	set_cmd_states();

	if (sockstate < 4 && ((t = time(NULL) - socktimeout) > 10 || !originx)) {
		render_rect(0, 0, 800, 540, blackcolor);
		display_screen();
		display_text();
		if ((now / 1000) & 1) {
			render_text(800 / 2, 540 / 2 - 60, redcolor, RENDER_ALIGN_CENTER | RENDER_TEXT_LARGE, "not connected");
		}
		render_sprite(60, 800 / 2, (540 - 240) / 2, RENDERFX_NORMAL_LIGHT, RENDER_ALIGN_CENTER);
		if (!kicked_out) {
			render_text_fmt(800 / 2, 540 / 2 - 40, textcolor,
			    RENDER_TEXT_SMALL | RENDER_ALIGN_CENTER | RENDER_TEXT_FRAMED,
			    "Trying to establish connection. %d seconds...", t);
			if (t > 15) {
				render_text_fmt(800 / 2, 540 / 2 - 0, textcolor,
				    RENDER_TEXT_LARGE | RENDER_ALIGN_CENTER | RENDER_TEXT_FRAMED,
				    "Please check %s for troubleshooting advice.", game_url);
			}
		}
		goto display_graphs; // I know, I know. goto considered harmful and all that.
	}

	render_push_clip();
	render_more_clip(dotx(DOT_MTL), doty(DOT_MTL), dotx(DOT_MBR), doty(DOT_MBR));
	display_game();
	render_pop_clip();

	display_screen();

	display_keys();
	if (game_options & GO_WHEEL) {
		display_wheel();
	}
	if (show_look) {
		display_look();
	}
	display_wear();
	display_inventory();
	display_action();
	if (con_cnt) {
		display_container();
	} else {
		display_skill();
	}
	display_scrollbars();
	display_text();
	display_gold();
	display_mode();
	display_selfspells();
	display_exp();
	display_military();
	display_teleport();
	display_color();
	display_rage();
	display_game_special();
	display_tutor();
	display_selfbars();
	display_minimap();
	display_citem();
	context_display(mousex, mousey);
	display_helpandquest(); // display last because it is on top

display_graphs:;

	int duration = SDL_GetTicks64() - start;

	if (display_vc) {
		extern long long texc_miss, texc_pre; // mem_tex,
		extern uint64_t sdl_backgnd_wait, sdl_backgnd_work, sdl_time_preload, sdl_time_load, gui_time_network;
		extern uint64_t gui_frametime, gui_ticktime;
		extern uint64_t sdl_time_pre1, sdl_time_pre2, sdl_time_pre3, sdl_time_mutex, sdl_time_alloc, sdl_time_make_main;
		extern int x_offset, y_offset; // pre_2,pre_in,pre_3;
		// static int dur=0,make=0,tex=0,text=0,blit=0,stay=0;
		static int size;
		static unsigned char dur_graph[100], size1_graph[100], size2_graph[100],
		    size3_graph[100]; //,size_graph[100];load_graph[100],
		static unsigned char pre1_graph[100], pre2_graph[100], pre3_graph[100];
		// static int frame_min=99,frame_max=0,frame_step=0;
		// static int tick_min=99,tick_max=0,tick_step=0;
		int px = 800 - 110, py = 35 + (!(game_options & GO_SMALLTOP) ? 0 : gui_topoff);

		// render_text_fmt(px,py+=10,0xffff,RENDER_TEXT_SMALL|RENDER_TEXT_LEFT|RENDER_TEXT_FRAMED|RENDER_TEXT_NOCACHE,"skip
		// %3.0f%%",100.0*skip/tota);
		// render_text_fmt(px,py+=10,0xffff,RENDER_TEXT_SMALL|RENDER_TEXT_LEFT|RENDER_TEXT_FRAMED|RENDER_TEXT_NOCACHE,"idle
		// %3.0f%%",100.0*idle/tota);
		// render_text_fmt(px,py+=10,IRGB(8,31,8),RENDER_TEXT_LEFT|RENDER_TEXT_FRAMED|RENDER_TEXT_NOCACHE,"Tex: %5.2f
		// MB",mem_tex/(1024.0*1024.0));
		render_text_fmt(px, py += 10, IRGB(8, 31, 8), RENDER_TEXT_LEFT | RENDER_TEXT_FRAMED | RENDER_TEXT_NOCACHE,
		    "Mem: %5.2f MB", get_memory_usage() / (1024.0 * 1024.0));

#if 0
	    if (pre_in>=pre_3) size=pre_in-pre_3;
	    else size=16384+pre_in-pre_3;

	    render_text_fmt(px,py+=10,0xffff,RENDER_TEXT_SMALL|RENDER_TEXT_LEFT|RENDER_TEXT_FRAMED|RENDER_TEXT_NOCACHE,"PreC %d",size);
#endif
#if 0
	    extern int pre_in,pre_1,pre_2,pre_3;
	    extern int texc_used;
	    py+=10;
	    render_text_fmt(px,py+=10,IRGB(8,31,8),RENDER_TEXT_LEFT|RENDER_TEXT_FRAMED|RENDER_TEXT_NOCACHE,"PreI %d",pre_in);
	    render_text_fmt(px,py+=10,IRGB(8,31,8),RENDER_TEXT_LEFT|RENDER_TEXT_FRAMED|RENDER_TEXT_NOCACHE,"Pre1 %d",pre_1);
	    render_text_fmt(px,py+=10,IRGB(8,31,8),RENDER_TEXT_LEFT|RENDER_TEXT_FRAMED|RENDER_TEXT_NOCACHE,"Pre2 %d",pre_2);
	    render_text_fmt(px,py+=10,IRGB(8,31,8),RENDER_TEXT_LEFT|RENDER_TEXT_FRAMED|RENDER_TEXT_NOCACHE,"Pre3 %d",pre_3);
	    render_text_fmt(px,py+=10,IRGB(8,31,8),RENDER_TEXT_LEFT|RENDER_TEXT_FRAMED|RENDER_TEXT_NOCACHE,"Used %d",texc_used);
	    render_text_fmt(px,py+=10,IRGB(8,31,8),RENDER_TEXT_LEFT|RENDER_TEXT_FRAMED|RENDER_TEXT_NOCACHE,"Size %d",sdl_cache_size);
#endif
		// render_text_fmt(px,py+=10,0xffff,RENDER_TEXT_SMALL|RENDER_TEXT_LEFT|RENDER_TEXT_FRAMED|RENDER_TEXT_NOCACHE,"Miss
		// %lld",texc_miss);
		// render_text_fmt(px,py+=10,0xffff,RENDER_TEXT_SMALL|RENDER_TEXT_LEFT|RENDER_TEXT_FRAMED|RENDER_TEXT_NOCACHE,"Prel
		// %lld",texc_pre);

		py += 10;

		size = duration + gui_time_network;
		render_text(px, py += 10, IRGB(8, 31, 8), RENDER_TEXT_LEFT | RENDER_TEXT_FRAMED, "Render");
		sdl_bargraph_add(sizeof(dur_graph), dur_graph, size < 42 ? size : 42);
		sdl_bargraph(px, py += 40, sizeof(dur_graph), dur_graph, x_offset, y_offset);

#if 0
	    if (gui_frametime<frame_min) frame_min=gui_frametime;
	    if (gui_frametime>frame_max) frame_max=gui_frametime;
	    render_text_fmt(px,py+=10,IRGB(8,31,8),RENDER_TEXT_NOCACHE|RENDER_TEXT_LEFT|RENDER_TEXT_FRAMED,"FT %d %d",frame_min,frame_max);

	    if (gui_ticktime<tick_min) tick_min=gui_ticktime;
	    if (gui_ticktime>tick_max) tick_max=gui_ticktime;
	    render_text_fmt(px,py+=10,IRGB(8,31,8),RENDER_TEXT_NOCACHE|RENDER_TEXT_LEFT|RENDER_TEXT_FRAMED,"TT %d %d",tick_min,tick_max);
#endif
		size = gui_frametime / 2;
		render_text_fmt(px, py += 10, IRGB(8, 31, 8), RENDER_TEXT_NOCACHE | RENDER_TEXT_LEFT | RENDER_TEXT_FRAMED,
		    "Frametime %" PRId64, gui_frametime);
		sdl_bargraph_add(sizeof(pre2_graph), pre2_graph, size < 42 ? size : 42);
		sdl_bargraph(px, py += 40, sizeof(pre2_graph), pre2_graph, x_offset, y_offset);

		size = gui_ticktime / 2;
		render_text_fmt(px, py += 10, IRGB(8, 31, 8), RENDER_TEXT_NOCACHE | RENDER_TEXT_LEFT | RENDER_TEXT_FRAMED,
		    "Ticktime %" PRId64, gui_ticktime);
		sdl_bargraph_add(sizeof(pre3_graph), pre3_graph, size < 42 ? size : 42);
		sdl_bargraph(px, py += 40, sizeof(pre3_graph), pre3_graph, x_offset, y_offset);
#if 0
	    size=gui_time_network;
	    render_text_fmt(px,py+=10,IRGB(8,31,8),RENDER_TEXT_LEFT|RENDER_TEXT_FRAMED,"Network");
	    sdl_bargraph_add(sizeof(pre2_graph),pre2_graph,size<42?size:42);
	    sdl_bargraph(px,py+=40,sizeof(pre2_graph),pre2_graph,x_offset,y_offset);

	    size=sdl_time_pre1;
	    render_text(px,py+=10,IRGB(8,31,8),RENDER_TEXT_LEFT|RENDER_TEXT_FRAMED,"Alloc");
	    sdl_bargraph_add(sizeof(size1_graph),size3_graph,size<42?size:42);
	    sdl_bargraph(px,py+=40,sizeof(size1_graph),size3_graph,x_offset,y_offset);
#endif


		size = (lasttick + q_size) * 2;
		render_text_fmt(px, py += 10, IRGB(8, 31, 8), RENDER_TEXT_FRAMED | RENDER_TEXT_LEFT, "Queue %d", size / 2);
		sdl_bargraph_add(sizeof(pre2_graph), size3_graph, size < 42 ? size : 42);
		sdl_bargraph(px, py += 40, sizeof(pre2_graph), size3_graph, x_offset, y_offset);
#if 0
	    size=sdl_time_alloc;
	    render_text(px,py+=10,IRGB(8,31,8),RENDER_TEXT_LEFT|RENDER_TEXT_FRAMED,"Alloc");
	    sdl_bargraph_add(sizeof(size1_graph),load_graph,size<42?size:42);
	    sdl_bargraph(px,py+=40,sizeof(size1_graph),load_graph,x_offset,y_offset);
#endif

		size = sdl_time_pre1 + sdl_time_pre3;
		render_text(px, py += 10, IRGB(8, 31, 8), RENDER_TEXT_LEFT | RENDER_TEXT_FRAMED, "Pre-Main");
		sdl_bargraph_add(sizeof(size1_graph), size2_graph, size < 42 ? size : 42);
		sdl_bargraph(px, py += 40, sizeof(size1_graph), size2_graph, x_offset, y_offset);
#if 0

#endif
		if (sdl_multi) {
			size = sdl_backgnd_work / sdl_multi;
			render_text_fmt(
			    px, py += 10, IRGB(8, 31, 8), RENDER_TEXT_LEFT | RENDER_TEXT_FRAMED, "Pre-Back (%d)", sdl_multi);
		} else {
			size = sdl_time_pre2;
			render_text_fmt(px, py += 10, IRGB(8, 31, 8), RENDER_TEXT_LEFT | RENDER_TEXT_FRAMED, "Make");
		}
		sdl_bargraph_add(sizeof(pre1_graph), pre1_graph, size < 42 ? size : 42);
		sdl_bargraph(px, py += 40, sizeof(pre1_graph), pre1_graph, x_offset, y_offset);
#if 0
	        render_text_fmt(px,py+=10,IRGB(8,31,8),RENDER_TEXT_SMALL|RENDER_TEXT_LEFT|RENDER_TEXT_FRAMED,"Mutex");
	        sdl_bargraph_add(sizeof(pre2_graph),pre2_graph,sdl_time_mutex/sdl_multi<42?sdl_time_mutex/sdl_multi:42);
	        sdl_bargraph(px,py+=40,sizeof(pre2_graph),pre2_graph,x_offset,y_offset);
#endif
#if 0
	    render_text(px,py+=10,IRGB(8,31,8),RENDER_TEXT_SMALL|RENDER_TEXT_LEFT|RENDER_TEXT_FRAMED,"Pre-Queue Tot");
	    sdl_bargraph_add(sizeof(size_graph),size_graph,size/4<42?size/4:42);
	    sdl_bargraph(px,py+=40,sizeof(size_graph),size_graph,x_offset,y_offset);

	    render_text(px,py+=10,IRGB(8,31,8),RENDER_TEXT_SMALL|RENDER_TEXT_LEFT|RENDER_TEXT_FRAMED,"Pre2");
	    sdl_bargraph_add(sizeof(pre2_graph),pre2_graph,sdl_time_pre2<42?sdl_time_pre2:42);
	    sdl_bargraph(px,py+=40,sizeof(pre2_graph),pre2_graph,x_offset,y_offset);

	    render_text(px,py+=10,IRGB(8,31,8),RENDER_TEXT_SMALL|RENDER_TEXT_LEFT|RENDER_TEXT_FRAMED,"Texture");
	    sdl_bargraph_add(sizeof(pre3_graph),pre3_graph,sdl_time_pre3<42?sdl_time_pre3:42);
	    sdl_bargraph(px,py+=40,sizeof(pre3_graph),pre3_graph,x_offset,y_offset);

#endif
#if 0
	    if (pre_2>=pre_3) size=pre_2-pre_3;
	    else size=16384+pre_2-pre_3;

	    render_text(px,py+=10,IRGB(8,31,8),RENDER_TEXT_SMALL|RENDER_TEXT_LEFT|RENDER_TEXT_FRAMED,"Size Tex");
	    sdl_bargraph_add(sizeof(size3_graph),size3_graph,size/4<42?size/4:42);
	    sdl_bargraph(px,py+=40,sizeof(size3_graph),size3_graph,x_offset,y_offset);


	    if (duration>10 && (!stay || duration>dur)) {
	        dur=duration;
	        make=sdl_time_make;
	        tex=sdl_time_tex;
	        text=sdl_time_text;
	        blit=sdl_time_blit;
	        stay=24*6;
	    }

	    if (stay>0) {
	        stay--;
	        render_text_fmt(px,py+=20,0xffff,RENDER_TEXT_SMALL|RENDER_TEXT_LEFT|RENDER_TEXT_FRAMED|RENDER_TEXT_NOCACHE,"Dur %dms (%.0f%%)",dur,100.0*(make+tex+text+blit)/dur);
	        render_text_fmt(px,py+=10,0xffff,RENDER_TEXT_SMALL|RENDER_TEXT_LEFT|RENDER_TEXT_FRAMED|RENDER_TEXT_NOCACHE,"Make %dms (%.0f%%)",make,100.0*make/dur);
	        render_text_fmt(px,py+=10,0xffff,RENDER_TEXT_SMALL|RENDER_TEXT_LEFT|RENDER_TEXT_FRAMED|RENDER_TEXT_NOCACHE,"Tex %dms (%.0f%%)",tex,100.0*tex/dur);
	        render_text_fmt(px,py+=10,0xffff,RENDER_TEXT_SMALL|RENDER_TEXT_LEFT|RENDER_TEXT_FRAMED|RENDER_TEXT_NOCACHE,"Text %dms (%.0f%%)",text,100.0*text/dur);
	        render_text_fmt(px,py+=10,0xffff,RENDER_TEXT_SMALL|RENDER_TEXT_LEFT|RENDER_TEXT_FRAMED|RENDER_TEXT_NOCACHE,"Blit %dms (%.0f%%)",blit,100.0*blit/dur);
	    }
#endif
		sdl_time_preload = 0;
		sdl_time_make = 0;
		sdl_time_tex = 0;
		sdl_time_text = 0;
		sdl_time_blit = 0;
		sdl_backgnd_work = 0;
		sdl_backgnd_wait = 0;
		sdl_time_load = 0;
		sdl_time_pre1 = 0;
		sdl_time_pre2 = 0;
		sdl_time_pre3 = 0;
		sdl_time_mutex = 0;
		sdl_time_tex_main = 0;
		gui_time_misc = 0;
		sdl_time_alloc = 0;
		texc_miss = 0;
		texc_pre = 0;
		sdl_time_make_main = 0;
		gui_time_network = 0;
#if 0
	    if (SDL_GetTicks()-frame_step>1000) {
	        frame_step=SDL_GetTicks();
	        frame_min=99;
	        frame_max=0;
	    }
	    if (SDL_GetTicks()-tick_step>1000) {
	        tick_step=SDL_GetTicks();
	        tick_min=99;
	        tick_max=0;
	    }
#endif
	} // else render_text_fmt(650,15,0xffff,RENDER_TEXT_SMALL|RENDER_TEXT_FRAMED,"Mirror %d",mirror);

	sprintf(perf_text, "mem usage=%.2f/%.2fMB, %.2f/%.2fKBlocks", memsize[0] / 1024.0 / 1024.0,
	    memused / 1024.0 / 1024.0, memptrs[0] / 1024.0, memptrused / 1024.0);
}

// cmd

void update_ui_layout(void)
{
	static int last_con_cnt = 0;

	if (update_skltab) {
		set_skltab();
		update_skltab = 0;
	}
	if (last_con_cnt != con_cnt) {
		conoff = 0;
		max_conoff = (con_cnt / CONDX) - CONDY;
		last_con_cnt = con_cnt;
		set_conoff(0, conoff);
		set_skloff(0, skloff);
	}
	max_invoff = ((INVENTORYSIZE - 30) / INVDX) - INVDY;
	set_button_flags();
}

DLL_EXPORT int _do_display_help(int nr)
{
	int x = dotx(DOT_HLP) + 10, y = doty(DOT_HLP) + 8, oldy;

	switch (nr) {
	case 1:
		y = render_text_break(x, y, x + 192, whitecolor, 0, "Help Index");
		y += 15;

		y = render_text_break(x, y, x + 192, whitecolor, 0, "Fast Help");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0, "Walk: LEFT-CLICK");
		y = render_text_break(x, y, x + 192, graycolor, 0, "Look on Ground:  RIGHT-CLICK");
		y = render_text_break(x, y, x + 192, graycolor, 0, "Take/Drop/Use: SHIFT LEFT-CLICK");
		y = render_text_break(x, y, x + 192, graycolor, 0, "Look at Item: SHIFT RIGHT-CLICK");
		y = render_text_break(x, y, x + 192, graycolor, 0, "Attack/Give: CTRL LEFT-CLICK");
		y = render_text_break(x, y, x + 192, graycolor, 0, "Look at Character: CTRL RIGHT-CLICK");
		y = render_text_break(x, y, x + 192, graycolor, 0, "Use Item in Inventory: LEFT-CLICK or F1...F4");
		y = render_text_break(x, y, x + 192, graycolor, 0, "Fast/Normal/Stealth: F5/F6/F7");
		y = render_text_break(x, y, x + 192, graycolor, 0, "Scroll Chat Window: PAGE-UP/PAGE-DOWN");
		y = render_text_break(x, y, x + 192, graycolor, 0, "Repeat last Tell: TAB");
		y = render_text_break(x, y, x + 192, graycolor, 0, "Close Help: F11");
		y = render_text_break(x, y, x + 192, graycolor, 0, "Show Walls: F8");
		y = render_text_break(x, y, x + 192, graycolor, 0, "Quit Game: F12 - preferably on blue square");
		y = render_text_break(x, y, x + 192, graycolor, 0, "Assign Wheel Button: Use Wheel");
		y += 10;

		oldy = y;
		y = render_text_break(x, y, x + 192, lightbluecolor, 0, "* A");
		y = render_text_break(x, y, x + 192, lightbluecolor, 0, "* A");
		y = render_text_break(x, y, x + 192, lightbluecolor, 0, "* B");
		y = render_text_break(x, y, x + 192, lightbluecolor, 0, "* C");
		y = render_text_break(x, y, x + 192, lightbluecolor, 0, "* C");
		y = render_text_break(x, y, x + 192, lightbluecolor, 0, "* C");
		y = render_text_break(x, y, x + 192, lightbluecolor, 0, "* D");
		y = render_text_break(x, y, x + 192, lightbluecolor, 0, "* E");
		y = render_text_break(x, y, x + 192, lightbluecolor, 0, "* F");
		y = render_text_break(x, y, x + 192, lightbluecolor, 0, "* G");
		y = render_text_break(x, y, x + 192, lightbluecolor, 0, "* I");
		render_text_break(x, y, x + 192, lightbluecolor, 0, "* K");

		y = oldy;
		y = render_text_break(x + 100, y, x + 192, lightbluecolor, 0, "* L");
		y = render_text_break(x + 100, y, x + 192, lightbluecolor, 0, "* M");
		y = render_text_break(x + 100, y, x + 192, lightbluecolor, 0, "* N");
		y = render_text_break(x + 100, y, x + 192, lightbluecolor, 0, "* P");
		y = render_text_break(x + 100, y, x + 192, lightbluecolor, 0, "* Q");
		y = render_text_break(x + 100, y, x + 192, lightbluecolor, 0, "* R");
		y = render_text_break(x + 100, y, x + 192, lightbluecolor, 0, "* S");
		y = render_text_break(x + 100, y, x + 192, lightbluecolor, 0, "* S");
		y = render_text_break(x + 100, y, x + 192, lightbluecolor, 0, "* S");
		y = render_text_break(x + 100, y, x + 192, lightbluecolor, 0, "* T");
		y = render_text_break(x + 100, y, x + 192, lightbluecolor, 0, "* W");
		break;

	case 2:

		y = render_text_break(x, y, x + 192, whitecolor, 0, "Accounts");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "It is your responsibility to store your account in a safe place. If someone steals or messes with your "
		    "account, you're still responsible. If you manage to lose your account, it is lost. If you lose your "
		    "password, the only thing we can do is send it to your account's e-mail address. If that e-mail address "
		    "turns out to be wrong or doesn't exist, there is nothing more we can do for you.");
		y += 10;

		y = render_text_break(x, y, x + 192, whitecolor, 0, "Account Payments");
		y += 5;
		y = render_text_break_fmt(x, y, x + 192, graycolor, 0,
		    "If you are having trouble with your account payments, or if you have questions concerning account "
		    "payments, please write %s.",
		    game_email_cash);
		y += 10;

		y = render_text_break(x, y, x + 192, whitecolor, 0, "Account Sharing");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "When you share accounts with another player, you are risking the security of your game characters and "
		    "their equipment.  In most cases of account sharing, characters are stripped of their equipment and their "
		    "game gold by the one(s) that the account is being shared with.  Characters can end up locked or banned "
		    "from the game, or with negative leveling experience.  Be wise, don't share!");
		y += 10;
		break;
	case 3:

		y = render_text_break(x, y, x + 192, whitecolor, 0, "Alias commands");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "Text phrases that you use repeatedly can be stored as Alias commands and retrieved with a few characters. "
		    "You can store up to 32 alias commands. To store an alias command, you first have to pick a phrase to "
		    "store, then give that phrase a name. The alias command for storing text is: /alias <alias phrase name> "
		    "<phrase>");
		y += 10;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "For example, to get the phrase, \"Let's go penting today!\", whenever you type p1, you'd type: /alias p1 "
		    "Let's go penting today!");
		y += 10;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "To delete an alias, first type: /alias to bring up your list of aliases.  Choose which alias you want to "
		    "delete, then type:  /alias <name of alias>.");
		y += 10;
		break;

	case 4:
		y = render_text_break(x, y, x + 192, whitecolor, 0, "Banking");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "Money and items can be stored in the Imperial Bank.  You have one account per character, and you can "
		    "access your account at any bank.  SHIFT + LEFT CLICK on the cabinet in the bank to access your Depot "
		    "(item storage locker).  Only gold coins can be deposited in your account or depot - silver coins cannot "
		    "be deposited.  Talk to the banker to get more information about banking.");
		y += 10;

		y = render_text_break(x, y, x + 192, whitecolor, 0, "Base/Mod Values");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "All your attributes and skills show two values:  the first one is the base value (it shows how much you "
		    "have raised it); the second is the modified (mod) value.  It consists of the base value, plus bonuses "
		    "from your base attributes and special items.  No skill or spell values can be raised through items by "
		    "more than 50% of its base value.");
		y += 10;
		break;
	case 5:

		y = render_text_break(x, y, x + 192, whitecolor, 0, "Chat and Channels");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "Everything you hear and say is displayed in the chat window at the bottom of your screen.  To talk to a "
		    "character standing next to you, just type what you'd like to say and hit ENTER.  To say something in the "
		    "general chat channel (the \"Gossip\" channel) which will be heard by all other players, type:  /c2 <your "
		    "message> and hit ENTER.  Use the PAGE UP and PAGE DOWN keys on your keyboard to scroll the chat window up "
		    "and down.  To see a list of channels in the game, type:  /channels.  To join a channel, type:  /join "
		    "<channel number>.  To leave a channel, type:  /leave <channel number>.  Spamming, offensive language, and "
		    "disruptive chatter is not allowed.  To send a message to a particular player, type:  /tell <player name> "
		    "and then your message.  Nobody else will hear what you said.");
		y += 10;

		y = render_text_break(x, y, x + 192, whitecolor, 0, "Clans");
		y += 5;
		y = render_text_break_fmt(x, y, x + 192, graycolor, 0,
		    "There is detailed information about clans in the Game Manual at %s. To see a list of clans in the game, "
		    "type: /clan.",
		    game_url);
		y += 10;
		break;

	case 6:
		y = render_text_break(x, y, x + 192, whitecolor, 0, "Colors");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "All characters enter the game with a set of default colors for their clothing and hair, but you can "
		    "change the color of your character's shirt, pants/skirt, and hair/cap if you choose.");
		y += 10;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "Matte Colors.  Use the Color Toolbox in the game to choose matte colors.  Type:  /col1  to bring up the "
		    "Color Toolbox.  From left to right, the three circles at the bottom represent shirt color, pants/skirt "
		    "color, and hair/cap color.  Click on a circle, then move the color bars to find a color that you like.  "
		    "The model in the box displays your color choices.  Click the Exit button to exit the Color Toolbox.");
		y += 10;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "Glossy Colors.  To make glossy colors, you use a command typed into the chat area instead of using the "
		    "Color Toolbox.  Like mixing paints, the number values you choose (between 1-31) for the red (R), green "
		    "(G), and blue (B) amounts determine how much of each is mixed in.  Adding an extra 31 to the red (R) "
		    "value makes the color combination you have chosen a glossy color.");
		y += 10;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "When typing the command, you first start by hitting the spacebar on your keyboard once, then  typing one "
		    "of these commands:  ");
		y += 10;
		y = render_text_break(x, y, x + 192, graycolor, 0, "/col1 <R><G><B> shirt color");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0, "/col2 <R><G><B> pants/skirt/cape color");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0, "/col3 <R><G><B> hair/cap color");
		y += 10;
		break;
	case 7:
		y = render_text_break(x, y, x + 192, whitecolor, 0, "Commands");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "Type: /help to see a list of all available commands.  You can type:  /status  to see a list of optional "
		    "toggle commands that may aid your character's performance.");
		y += 10;

		y = render_text_break(x, y, x + 192, whitecolor, 0, "Complains/Harassment");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "If another player harasses you,  type:  /complain <player><reason>  This command sends a screenshot of "
		    "your chat window to Game Management.  Replace <player> with the name of the player bothering you.  The "
		    "<reason> portion of the command is for you to enter your own comments regarding the situation. Please be "
		    "aware that only the last 80 lines of text are sent and that each server-change (teleport) erases this "
		    "buffer.  You can also type:  /ignore <name>  to ignore the things that player is saying to you.");
		y += 10;
		break;
	case 8:
		y = render_text_break(x, y, x + 192, whitecolor, 0, "Dying");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "When you die, you will suddenly find yourself on a blue square - the last blue square that you stepped "
		    "on.  You may see a message displayed on your screen telling you the name and level of the enemy that "
		    "killed you.  If you were not saved, then your corpse will be at the place where you died and all of your "
		    "items from your Equipment area and your Inventory will still be on your corpse. You have 30 minutes to "
		    "make it back to your corpse to get these items. After 30 minutes, your corpse disappears, along with your "
		    "items.");
		y += 10;
		y = render_text_break(x, y, x + 192, graycolor, 0, "Allowing Access to Your Corpse:");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "You can allow another player to retrieve your items from your corpse by typing: /allow <player name> "
		    "Quest items and keys can only be retrieved from a corpse by the one who has died, even if you /allow "
		    "someone to access to your corpse.");
		y += 10;
		break;

	case 9:
		y = render_text_break(x, y, x + 192, whitecolor, 0, "Enhancing Equipment");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "Enhancing equipment is silver plating and/or gold plating a piece of equipment to make it stronger and "
		    "more valuable.  To silver/gold plate an item, you will need silver/gold nuggets from the mines.  You must "
		    "silver plate an item before you can gold plate it.  Silver adds +1 to all the stat(s) of an item;  for "
		    "example, if you have a +2 parry sword, after silvering it you will have a +3 parry sword.  Gold plating "
		    "then adds another +1 to all stat(s).  Once you have gold plated an item, you can only enhance it further "
		    "by using orbs and/or welds.  To figure how much silver/gold you need for enhancing an item, the formula "
		    "is:  (highest stat on item + 1) x 100 = amount of silver/gold needed. Silvering/guilding will add a level "
		    "to weapons/armors: lvl 20 sword will become lvl 30 sword after silvering etc.");
		y += 10;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "Silvering/guilding an item will also increase its level requirement.  For example, a level 20 sword will "
		    "then become a level 30 sword.");
		y += 10;
		break;
	case 10:
		y = render_text_break(x, y, x + 192, whitecolor, 0, "Fighting");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "To attack somebody, place your cursor over the character you'd like to attack, and then hit CTRL + LEFT "
		    "CLICK.");
		y += 10;
		break;
	case 11:
		y = render_text_break(x, y, x + 192, whitecolor, 0, "Gold");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "Gold and silver are the monetary units used in the game.  To give money to another person, place your "
		    "cursor over your gold (bottom of your screen), LEFT CLICK, and slowly drag your mouse upwards until you "
		    "have the amount on your cursor that you want.  Then, let your cursor rest on the person you wish to give "
		    "the money to, and hit CTRL + LEFT CLICK.");
		y += 10;
		break;
	case 12:
		y = render_text_break(x, y, x + 192, whitecolor, 0, "Items");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "To use or pick up items around you, put your cursor over the item and hit SHIFT + LEFT CLICK.  To use an "
		    "item in your Inventory, LEFT CLICK on it.  To give an item to another character, take the item by using "
		    "SHIFT + LEFT CLICK, then pull it over the other character and hit CTRL + LEFT CLICK.  To loot the corpses "
		    "of slain enemies, place your cursor over the body and hit SHIFT + LEFT CLICK.");
		y += 10;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "Some items have level restrictions and/or skill restrictions.  Some items can only be worn by mages, "
		    "warriors, or seyans.  For example, a mage cannot use a sword and a warrior cannot use a staff.  If you "
		    "cannot equip an item it may be because your class of character cannot wear that particular item, or "
		    "because of level/skill restrictions on that item.  RIGHT click on the item to read more about it.");
		y += 10;
		break;
	case 13:
		y = render_text_break(x, y, x + 192, whitecolor, 0, "Karma");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "Karma is a measurement of how well a player has obeyed game rules. When you receive a Punishment, you "
		    "lose karma. All players enter the game with 0 karma. If you receive a Level 1 punishment, for example, "
		    "your karma will drop to -1. Please review the Laws, Rules, and Regulations section in the Game Manual to "
		    "familiarize yourself with the punishment system.");
		y += 10;
		break;
	case 14:
		y = render_text_break(x, y, x + 192, whitecolor, 0, "Leaving the game");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "To leave the game, step on one of the blue tile rest areas and hit F12. You can also hit F12 when not on "
		    "a blue tile, but your character will stay in that same spot for five minutes and risks being attacked.");
		y += 10;

		y = render_text_break(x, y, x + 192, whitecolor, 0, "Light");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "Torches provide the main source of light in the game.  To use a torch, equip it, then LEFT CLICK on it to "
		    "light it.  It is a good idea to carry extras with you at all times.");
		y += 10;

		y = render_text_break(x, y, x + 192, whitecolor, 0, "Looking at characters/items");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "To look at a character, place your cursor over him and hit CTRL + RIGHT CLICK.  To look at an item around "
		    "you, place your cursor over the item and hit  SHIFT + RIGHT CLICK.  To look at an item in your "
		    "Equipment/Inventory areas or in a shop window, (place your cursor over the item and) RIGHT CLICK.");
		y += 10;
		break;
	case 15:
		y = render_text_break(x, y, x + 192, whitecolor, 0, "Mirrors");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "Each area can have up to 26 mirrors (servers), to allow more players to be online at once.  Your mirror "
		    "number determines which mirror you use.  You can see which mirror you are currently on by \"looking\" at "
		    "yourself (place your cursor over yourself and hit CTRL + RIGHT CLICK).  If you would like to meet a "
		    "player on a different mirror, go to a teleport station, click on the corresponding mirror number (M1 to "
		    "M26) and teleport to the area that the other player is in.  You have to teleport, even if the other "
		    "player is in the same area.");
		y += 10;
		break;
	case 16:
		y = render_text_break(x, y, x + 192, whitecolor, 0, "Navigational Directions");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "Compass directions (North, East, South, West) are the same in the game as in real life.  North, for "
		    "example, would be 'up' (the top of your screen).  East would be to the direct right of your screen.");
		y += 10;

		y = render_text_break(x, y, x + 192, whitecolor, 0, "Negative Experience");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "When you die, you lose experience points. Too many deaths can result in Negative Experience. Once this "
		    "Negative Experience is made up, then experience points obtained will once again count towards leveling.");
		y += 10;
		break;
	case 17:
		y = render_text_break(x, y, x + 192, whitecolor, 0, "Player Killing");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "A PKer (Player Killer) is one that has chosen to kill other PKers - which also means that he can be "
		    "killed by other PKers too.  If you are killed, the items in your Equipment area and your Inventory can be "
		    "taken by the one who killed you.  You must be level 10 or higher and have a paid account to become a "
		    "PKer.  To enable your PK status, type:  /playerkiller.  To attack someone who is a playerkiller and "
		    "within your level range, type:  /hate <name> To disable your PK status, you must wait four (4) weeks "
		    "since you last killed someone, then type:  /playerkiller");
		y += 10;

		y = render_text_break(x, y, x + 192, whitecolor, 0, "The Pentagram Quest");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "The Pentagram Quest is a game that all players (from about level 10 and up) can play together.  It's an "
		    "ongoing game that takes place in \"the pents\" - a large, cavernous area partitioned off according to "
		    "player levels.  The walls and floors of this area are covered with \"stars\" (pentagrams) and the object "
		    "of the game is to touch as many pentagrams as possible as you fight off the evil demons that inhabit the "
		    "area.  Once a randomly chosen number of pentagrams have been touched, the pents are \"solved\", and you "
		    "receive experience points for the pentagrams you touched. The entrances to the Pentagram Quest  are "
		    "southeast of blue squares in Aston - be sure to SHIFT + RIGHT CLICK on the doors to determine which level "
		    "area is right for you!");
		y += 10;
		break;
	case 18:
		y = render_text_break(x, y, x + 192, whitecolor, 0, "Quests");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "Your first quest will be to find Lydia, the daughter of Gwendylon the mage.  She will ask you to find a "
		    "potion which was stolen the night before.  Lydia lives in the grey building across from the fortress (the "
		    "place where you first arrived in the game).");
		y += 10;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "NPCs (Non-Player Characters) give the quests in the game.  Even if you talked to an NPC before, talk to "
		    "him again; he may tell you something new or give you another quest.  Say \"hi\" or <name> \"repeat\" to "
		    "get an NPC to talk to you.   Be sure to step all the way into a room or area as you quest; monsters, "
		    "chests, and doors may be hidden in the shadows.  Carry a torch to light your way, and always check the "
		    "bodies of slain enemies (SHIFT + LEFT CLICK).");
		y += 10;
		y = render_text_break(x, y, x + 192, whitecolor, 0, "Questions");
		y += 5;
		y = render_text_break_fmt(x, y, x + 192, graycolor, 0,
		    "If you have a question while in the game, you can always ask a Staffer. Staffers and other admin can be "
		    "recognized by their name being in capital letters (i.e. \"COLOMAN\" is a member of Admin, \"Coloman\" is "
		    "not).  For any other game related questions, please write to %s.",
		    game_email_main);
		y += 10;
		break;
	case 19:
		y = render_text_break(x, y, x + 192, whitecolor, 0, "Reading books, signs, etc.");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "To read books, use SHIFT + LEFT CLICK.  To read signs, use SHIFT + RIGHT CLICK.");
		y += 10;
		break;
	case 20:
		y = render_text_break(x, y, x + 192, whitecolor, 0, "Saves");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "With each new level you obtain as you play, you also receive a Save. A Save is a gift from Ishtar: if you "
		    "die, your items stay with you instead of having them left on your corpse, and you will not get negative "
		    "experience. The maximum number of Saves that a player can have at any time is 10.");
		y += 10;

		y = render_text_break(x, y, x + 192, whitecolor, 0, "Scamming");
		y += 5;
		y = render_text_break_fmt(x, y, x + 192, graycolor, 0,
		    "Most cases of scamming happen when players share passwords.  NEVER give your password to another player "
		    "for any reason!  Make your passwords hard to guess by using a combination of numbers and letters.  Change "
		    "your password often; go to %s, then click on Account Management to change your password.  Always use an "
		    "NPC Trader when trading with another player.  The NPC Trader can be found in most towns in or near the "
		    "banks - he is a non-playing character that will handle the trade for both parties.  If a player does not "
		    "want to use an NPC Trader for trading with you, then do not trade with him - he could potentially steal "
		    "your items.  Do not put your items on the ground when trading with another player or you risk losing "
		    "them.  Be wary of loaning your equipment to others - unfortunately, many never see their items again.  "
		    "Players are able to perform welding in the game, but welds are very valuable and should not be traded "
		    "away too early.  Hold on to your welds until you learn more about the game!",
		    game_url);
		y += 10;
		break;

	case 21:
		y = render_text_break(x, y, x + 192, whitecolor, 0, "Shops");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "To open a shop window with a merchant, type:  trade <merchant name>  When trading with a merchant, the "
		    "items for sale are shown at the bottom-left of your screen (the view of your skills/stats is temporarily "
		    "replaced by the shop window).  To read about the items, RIGHT CLICK on them.  To buy something, LEFT "
		    "CLICK on it.  To sell an item from your inventory, LEFT CLICK on it.");
		y += 10;

		y = render_text_break(x, y, x + 192, whitecolor, 0, "Skills/Stats");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "In your stats/skills window (bottom-left of your screen) you see red/blue lines below your skills. Blue "
		    "indicates that you have enough experience points to raise the skill; red indicates that you don't have "
		    "enough experience points. To raise a skill, CLICK on the blue orb next to the skill.");
		y += 10;

		y = render_text_break(x, y, x + 192, whitecolor, 0, "Spells");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "To use a spell, hit ALT and the corresponding number of the spell that appears on your screen.  Mages - "
		    "to cast the Bless spell on another player, rest your cursor on him and hit CTRL 6.  The Bless spell "
		    "raises base attributes (Wisdom, Intuition, Agility, Strength) by 1/4 modified bless value (rounded down), "
		    "but by no more than 50%.  Warriors - hit ALT 8 to use Warcry.");
		y += 10;
		break;
	case 22:
		y = render_text_break(x, y, x + 192, whitecolor, 0, "Staffers");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "Staffers are members of Game Management that help keep the in-game playing field running smoothly.  "
		    "Staffers and other admin can be recognized by their name being in capital letters (i.e. \"COLOMAN\" is a "
		    "member of Admin, \"Coloman\" is not).  Staffers help keep the peace, answer questions, and can give out "
		    "karma (if needed) to unruly players.");
		y += 10;
		break;
	case 23:
		y = render_text_break(x, y, x + 192, whitecolor, 0, "Talking");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "Everything you hear and say is displayed in the chat window at the bottom of your screen.  To talk to a "
		    "character standing next to you, just type what you'd like to say and hit ENTER.  To say something in the "
		    "general chat channel (the \"Gossip\" channel) which will be heard by all other players, type:  /c2 <your "
		    "message> and hit ENTER.  Use the PAGE-UP and PAGE-DOWN keys on your keyboard to scroll the chat window up "
		    "and down.");
		y += 10;

		y = render_text_break(x, y, x + 192, whitecolor, 0, "Transport System");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "You will find Teleport Stations, relics of the ancient culture, all over the world.  SHIFT + LEFT CLICK "
		    "on the Teleport Station to see a map of all Teleport Stations.  CLICK on the destination of your choice.  "
		    "You will only be able to teleport to a destination that you have reached at least once before by foot.  "
		    "Touch any new Teleport Station on your way so that you can teleport there in times to come.");
		y += 10;
		break;
	case 24:
		y = render_text_break(x, y, x + 192, whitecolor, 0, "Walking");
		y += 5;
		y = render_text_break(x, y, x + 192, graycolor, 0,
		    "To walk, move your cursor to the place where you'd like to go, then LEFT CLICK on your destination.");
		y += 10;
		break;
	}
	return y;
}
