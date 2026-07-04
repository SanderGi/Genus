# SPDX-FileCopyrightText: 2026 Alexander Metzger
# SPDX-License-Identifier: GPL-2.0-only

CC=gcc
MCC=x86_64-w64-mingw32-gcc
WINE=wine
BDIR=.

all: multi_genus planar_draw

run: multi_genus
	cat $(ADJ) | $(BDIR)/multi_genus

draw: multi_genus planar_draw
	cat $(ADJ) | $(BDIR)/multi_genus w | $(BDIR)/planar_draw f l > test.tex

multi_genus: multi_genus.c
	$(CC) -O3 -DLONG -march=native -o "$(BDIR)/multi_genus" multi_genus.c -lm

planar_draw: planar_draw.c
	$(CC) -std=gnu89 -O3 -o "$(BDIR)/planar_draw" planar_draw.c -lm

run_wine: multi_genus.exe
# 	brew install --cask wine@staging
	cat $(ADJ) | WINEDEBUG=-all $(WINE) $(BDIR)/multi_genus.exe

draw_wine: multi_genus.exe planar_draw.exe
# 	brew install --cask wine@staging
	cat $(ADJ) | WINEDEBUG=-all $(WINE) $(BDIR)/multi_genus.exe w | WINEDEBUG=-all $(WINE) $(BDIR)/planar_draw.exe f l > test.tex

multi_genus.exe: multi_genus.c
#   brew install mingw-w64
	$(MCC) -O3 -DLONG -o "$(BDIR)/multi_genus.exe" multi_genus.c -lm

planar_draw.exe: planar_draw.c
#   brew install mingw-w64
	$(MCC) -std=gnu89 -O3 -o "$(BDIR)/planar_draw.exe" planar_draw.c -lm

clean:
	rm -f $(BDIR)/multi_genus $(BDIR)/planar_draw $(BDIR)/*.o $(BDIR)/*.exe
	rm -rf $(BDIR)/*.dSYM
