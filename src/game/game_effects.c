/*
 * Part of Astonia Client (c) Daniel Brockhaus. Please read license.txt.
 *
 * Display Game Map - Spell and Special Effects
 *
 * Functions for rendering spells, magical effects, and special visual effects.
 */

#include <stdint.h>
#include <stddef.h>
#include <SDL2/SDL.h>

#include "astonia.h"
#include "game/game.h"
#include "game/game_private.h"
#include "gui/gui.h"
#include "client/client.h"

DL *dl_call_strike(int layer, int x1, int y1, int h1, int x2, int y2, int h2)
{
	DL *dl;

	dl = dl_next();

	dl->call = DLC_STRIKE;
	dl->layer = layer;
	dl->call_x1 = x1;
	dl->call_y1 = y1 - h1;
	dl->call_x2 = x2;
	dl->call_y2 = y2 - h2;

	if (y1 > y2) {
		dl->x = x1;
		dl->y = y1;
	} else {
		dl->x = x2;
		dl->y = y2;
	}

	return dl;
}

DL *dl_call_pulseback(int layer, int x1, int y1, int h1, int x2, int y2, int h2)
{
	DL *dl;

	dl = dl_next();

	dl->call = DLC_PULSEBACK;
	dl->layer = layer;
	dl->call_x1 = x1;
	dl->call_y1 = y1 - h1;
	dl->call_x2 = x2;
	dl->call_y2 = y2 - h2;

	if (y1 > y2) {
		dl->x = x1;
		dl->y = y1;
	} else {
		dl->x = x2;
		dl->y = y2;
	}

	return dl;
}

DL *dl_call_bless(int layer, int x, int y, int ticker, int strength, int front)
{
	DL *dl;

	dl = dl_next();

	dl->call = DLC_BLESS;
	dl->layer = layer;

	dl->call_x1 = x;
	dl->call_y1 = y;
	dl->call_x2 = ticker;
	dl->call_y2 = strength;
	dl->call_x3 = front;

	dl->x = x;
	if (front) {
		dl->y = y + 8;
	} else {
		dl->y = y - 8;
	}

	return dl;
}

DL *dl_call_pulse(int layer, int x, int y, int nr, int size, int color)
{
	DL *dl;

	dl = dl_next();

	dl->call = DLC_PULSE;
	dl->layer = layer;

	dl->call_x1 = x;
	dl->call_y1 = y - 20;
	dl->call_x2 = nr;
	dl->call_y2 = size;
	dl->call_x3 = color;

	dl->x = x;
	switch (nr) {
	case 0:
		dl->x = x + 20;
		dl->y = y + 10;
		break;
	case 1:
		dl->x = x + 20;
		dl->y = y - 10;
		break;
	case 2:
		dl->x = x - 20;
		dl->y = y - 10;
		break;
	case 3:
		dl->x = x - 20;
		dl->y = y + 10;
		break;
	}

	return dl;
}

DL *dl_call_potion(int layer, int x, int y, int ticker, int strength, int front)
{
	DL *dl;

	dl = dl_next();

	dl->call = DLC_POTION;
	dl->layer = layer;

	dl->call_x1 = x;
	dl->call_y1 = y;
	dl->call_x2 = ticker;
	dl->call_y2 = strength;
	dl->call_x3 = front;

	dl->x = x;
	if (front) {
		dl->y = y + 8;
	} else {
		dl->y = y - 8;
	}

	return dl;
}

DL *dl_call_rain(int layer, int x, int y, int nr, int color)
{
	DL *dl;
	int sy;

	x += ((nr / 30) % 30) + 15;
	sy = y + ((nr / 330) % 20) + 10;
	y = sy - ((nr * 2) % 60) - 60;

	dl = dl_next();

	dl->call = DLC_PIXEL;
	dl->layer = layer;

	dl->call_x1 = x;
	dl->call_y1 = y;
	dl->call_x2 = color;

	dl->x = x;
	dl->y = sy;

	return dl;
}

DL *dl_call_rain2(int layer, int x, int y, int ticker, int strength, int front)
{
	DL *dl;

	dl = dl_next();

	dl->call = DLC_RAIN;
	dl->layer = layer;

	dl->call_x1 = x;
	dl->call_y1 = y;
	dl->call_x2 = ticker;
	dl->call_y2 = strength;
	dl->call_x3 = front;

	dl->x = x;
	if (front) {
		dl->y = y + 10;
	} else {
		dl->y = y - 10;
	}

	return dl;
}

DL *dl_call_number(int layer, int x, int y, int nr)
{
	DL *dl;

	dl = dl_next();

	dl->call = DLC_NUMBER;
	dl->layer = layer;
	dl->call_x1 = x;
	dl->call_y1 = y;
	dl->call_x2 = nr;

	return dl;
}
