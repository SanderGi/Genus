CC=gcc
BTYPE=Development
BDIR=.

all: page

run: page
	$(BDIR)/page

page: page.c
	$(CC) -O3 -ftree-vectorize -funroll-loops -Wall -std=c17 -pedantic -g -pthread -o "$(BDIR)/page" page.c

run_wine: page.exe
# 	brew install --cask wine@staging
	wine $(BDIR)/page.exe

page.exe: page.c
#   brew install mingw-w64
	x86_64-w64-mingw32-gcc -O3 -ftree-vectorize -funroll-loops -Wall -std=c17 -pedantic -g -o "$(BDIR)/page.exe" page.c 


clean:
	rm -f $(BDIR)/page $(BDIR)/*.o
	rm -rf $(BDIR)/*.dSYM
