all: CalcGenus

run: CalcGenus
	./CalcGenus

CalcGenus: CalcGenus.c
	gcc -Wall -std=c17 -pedantic -g -o CalcGenus CalcGenus.c

clean:
	rm -f CalcGenus *.o
	rm -rf *.dSYM
