CC=gcc
CPPC=g++
BTYPE=Development
BDIR=.

all: CalcGenus

run: CalcGenus
	$(BDIR)/CalcGenus

CalcGenus: CalcGenus.c
	if [ $(CC) = "cl" ]; then\
		$(CC) /std:c17 /W4 /Za /Fe"$(BDIR)/CalcGenus" CalcGenus.c;\
	else\
		$(CC) -Wall -std=c17 -pedantic -g -o "$(BDIR)/CalcGenus" CalcGenus.c;\
    fi

clean:
	rm -f $(BDIR)/CalcGenus $(BDIR)/*.o
	rm -rf $(BDIR)/*.dSYM
