# SPDX-FileCopyrightText: 2026 Alexander Metzger
# SPDX-License-Identifier: GPL-2.0-only

CC=gcc
MCC=x86_64-w64-mingw32-gcc
WINE=wine
BDIR=.

all: page

run: page
	$(BDIR)/page

run_low_mem: page_low_mem
	$(BDIR)/page_low_mem

page: page.c
	$(CC) -O3 -ftree-vectorize -funroll-loops -Wall -std=c17 -pedantic -g -pthread -o "$(BDIR)/page" page.c

page_low_mem: page_low_mem.c
	$(CC) -O3 -ftree-vectorize -funroll-loops -Wall -Wextra -std=c17 -pedantic -g -o "$(BDIR)/page_low_mem" page_low_mem.c

run_wine: page.exe
# 	brew install --cask wine@staging
	WINEDEBUG=-all $(WINE) $(BDIR)/page.exe

run_low_mem_wine: page_low_mem.exe
	WINEDEBUG=-all $(WINE) $(BDIR)/page_low_mem.exe

page.exe: page.c
#   brew install mingw-w64
	$(MCC) -O3 -ftree-vectorize -funroll-loops -Wall -std=c17 -pedantic -g -o "$(BDIR)/page.exe" page.c 

page_low_mem.exe: page_low_mem.c
	$(MCC) -O3 -ftree-vectorize -funroll-loops -Wall -Wextra -std=c17 -pedantic -g -o "$(BDIR)/page_low_mem.exe" page_low_mem.c

clean:
	rm -f $(BDIR)/page $(BDIR)/page_low_mem $(BDIR)/*.o $(BDIR)/*.exe $(BDIR)/*.out
	rm -rf $(BDIR)/*.dSYM
