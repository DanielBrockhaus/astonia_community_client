/*
 * Part of Astonia Client (c) Daniel Brockhaus. Please read license.txt.
 *
 * Graphical User Interface - Map coordinate functions
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

void set_mapoff(int cx, int cy, int mdx, int mdy)
{
	mapoffx = (cx - (mdx / 2 - mdy / 2) * (FDX / 2));
	mapoffy = (cy - (mdx / 2 + mdy / 2) * (FDY / 2));
}

void set_mapadd(int addx, int addy)
{
	mapaddx = addx;
	mapaddy = addy;
}

void mtos(int mapx, int mapy, int *scrx, int *scry)
{
	*scrx = (mapoffx + mapaddx) + (mapx - mapy) * (FDX / 2);
	*scry = (mapoffy + mapaddy) + (mapx + mapy) * (FDY / 2);
}

int stom(int scrx, int scry, int *mapx, int *mapy)
{
	if (scrx < dotx(DOT_MTL) || scrx >= dotx(DOT_MBR) || scry < doty(DOT_MTL) || scry >= doty(DOT_MBR)) {
		return 0;
	}

	scrx -= stom_off_x;
	scry -= stom_off_y;
	scrx -= (mapoffx + mapaddx);
	scry -= (mapoffy + mapaddy) - 10;
	*mapy = (40 * scry - 20 * scrx - 1) / (20 * 40); // ??? -1 ???
	*mapx = (40 * scry + 20 * scrx) / (20 * 40);

	return 1;
}

DLL_EXPORT int get_near_ground(int x, int y)
{
	int mapx, mapy;

	if (!stom(x, y, &mapx, &mapy)) {
		return -1;
	}

	if (mapx < 0 || mapy < 0 || mapx >= MAPDX || mapy >= MAPDY) {
		return -1;
	}

	return mapmn(mapx, mapy);
}

DLL_EXPORT int get_near_item(int x, int y, int flag, int looksize)
{
	int mapx, mapy, sx, sy, ex, ey, mn, scrx, scry, nearest = -1;
	double dist, nearestdist = 100000000;

	if (!stom(mousex, mousey, &mapx, &mapy)) {
		return -1;
	}

	sx = max(0, mapx - looksize);
	sy = max(0, mapy - looksize);
	;
	ex = min(MAPDX - 1, mapx + looksize);
	ey = min(MAPDY - 1, mapy + looksize);

	for (mapy = sy; mapy <= ey; mapy++) {
		for (mapx = sx; mapx <= ex; mapx++) {
			mn = mapmn(mapx, mapy);

			if (!(map[mn].rlight)) {
				continue;
			}
			if (!(map[mn].flags & flag)) {
				continue;
			}
			if (!(map[mn].isprite)) {
				continue;
			}

			mtos(mapx, mapy, &scrx, &scry);

			dist = (x - scrx) * (x - scrx) + (y - scry) * (y - scry);

			if (dist < nearestdist) {
				nearestdist = dist;
				nearest = mn;
			}
		}
	}

	return nearest;
}

DLL_EXPORT int get_near_char(int x, int y, int looksize)
{
	int mapx, mapy, sx, sy, ex, ey, mn, scrx, scry, nearest = -1;
	double dist, nearestdist = 100000000;

	if (!stom(mousex, mousey, &mapx, &mapy)) {
		return -1;
	}

	mn = mapmn(mapx, mapy);
	if (mn == MAPDX * MAPDY / 2) {
		return mn; // return player character if clicked directly
	}

	sx = max(0, mapx - looksize);
	sy = max(0, mapy - looksize);
	;
	ex = min(MAPDX - 1, mapx + looksize);
	ey = min(MAPDY - 1, mapy + looksize);

	for (mapy = sy; mapy <= ey; mapy++) {
		for (mapx = sx; mapx <= ex; mapx++) {
			mn = mapmn(mapx, mapy);

			if (context_key_enabled() && mn == MAPDX * MAPDY / 2) {
				continue; // ignore player character if NOT clicked directly
			}

			if (!(map[mn].rlight)) {
				continue;
			}
			if (!(map[mn].csprite)) {
				continue;
			}

			mtos(mapx, mapy, &scrx, &scry);

			dist = (x - scrx) * (x - scrx) + (y - scry) * (y - scry);

			if (dist < nearestdist) {
				nearestdist = dist;
				nearest = mn;
			}
		}
	}

	return nearest;
}
