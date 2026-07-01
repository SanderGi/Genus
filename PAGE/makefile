CC=gcc
CPPC=g++
BTYPE=Development
BDIR=.

all: page

run: page
	$(BDIR)/page

page: page.c
	$(CC) -O3 -ftree-vectorize -funroll-loops -Wall -std=c17 -pedantic -g -pthread -o "$(BDIR)/page" page.c

clean:
	rm -f $(BDIR)/page $(BDIR)/*.o
	rm -rf $(BDIR)/*.dSYM
