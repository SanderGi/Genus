all: FitCycles

run: FitCycles
	./FitCycles

FitCycles: FitCycles.c
	gcc -Wall -std=c17 -pedantic -g -o FitCycles FitCycles.c

clean:
	rm -f FitCycles *.o
	rm -rf *.dSYM
