CC=gcc
CPPC=g++
BTYPE=Development
BDIR=.

all: CalcGenus

run: CalcGenus
	$(BDIR)/CalcGenus

CalcGenus: CalcGenus.c
	$(CC) -O3 -ftree-vectorize -funroll-loops -Wall -std=c17 -pedantic -g -o "$(BDIR)/CalcGenus" CalcGenus.c

clean:
	rm -f $(BDIR)/CalcGenus $(BDIR)/*.o
	rm -rf $(BDIR)/*.dSYM
