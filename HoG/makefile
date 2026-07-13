# SPDX-FileCopyrightText: 2026 Alexander Metzger
# SPDX-License-Identifier: GPL-2.0-only

CC=gcc
BDIR=.

all: genus

run: genus
	$(BDIR)/genus

run_multicode: genus
	$(BDIR)/genus --multicode

run_page: genus
	$(BDIR)/genus --only-page

run_multi_genus: genus
	$(BDIR)/genus --only-multi_genus

genus: genus.c
	$(CC) -O3 -DLONG -ftree-vectorize -funroll-loops -Wall -std=gnu17 -g -pthread -o "$(BDIR)/genus" genus.c -lm

clean:
	rm -f $(BDIR)/genus
	rm -rf $(BDIR)/*.dSYM
