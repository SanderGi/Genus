CC ?= gcc
NAUTY_PREFIX ?= /opt/homebrew

CFLAGS ?= -O3 -march=native -flto -DNDEBUG
CFLAGS += -std=c17 -Wall -Wextra -pedantic -I$(NAUTY_PREFIX)/include
LDFLAGS += -L$(NAUTY_PREFIX)/lib
LDLIBS += -lnauty -lm -pthread

BIN = genus_properties
SRC = genus_properties.c

.PHONY: all clean run-petersen

all: $(BIN)

$(BIN): $(SRC)
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ $(SRC) $(LDLIBS)

run-petersen: $(BIN)
	printf 'IheA@GUAo\n' | ./$(BIN) --stdin

clean:
	rm -f $(BIN) *.o
