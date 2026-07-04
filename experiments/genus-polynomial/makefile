# SPDX-FileCopyrightText: 2026 Alexander Metzger
# SPDX-License-Identifier: GPL-2.0-only

CC ?= gcc
NAUTY_PREFIX ?= /opt/homebrew
FLINT_PREFIX ?= ./flint

CFLAGS ?= -O3 -march=native -flto -DNDEBUG
CFLAGS += -std=c17 -Wall -Wextra -pedantic -I$(FLINT_PREFIX)/src -I$(NAUTY_PREFIX)/include
LDFLAGS += -L$(FLINT_PREFIX) -L$(NAUTY_PREFIX)/lib -Wl,-rpath,$(abspath $(FLINT_PREFIX))
LDLIBS += -lnauty -lflint -lm -pthread

BIN = compute_stats
SRC = compute_stats.c

.PHONY: all clean run-petersen

all: $(BIN)

$(BIN): $(SRC)
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ $(SRC) $(LDLIBS)

run-petersen: $(BIN)
	printf 'IheA@GUAo\n' | ./$(BIN) --stdin

clean:
	rm -f $(BIN) *.o
