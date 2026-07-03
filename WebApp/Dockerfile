# SPDX-FileCopyrightText: 2026 Alexander Metzger
# SPDX-License-Identifier: GPL-2.0-only

# Compile C code first so we don't need to keep the C compiler in the final image
FROM gcc AS builder

WORKDIR /app

# Copy the C code and compile it
COPY PAGE/page.c page.c
RUN gcc -O3 -ftree-vectorize -funroll-loops -Wall -std=c17 -pedantic -g -o page page.c
RUN gcc -DONLY_SIMPLE_CYCLES=1 -O3 -ftree-vectorize -funroll-loops -Wall -std=c17 -pedantic -g -o pageSC page.c

COPY MultiGenus/multi_genus.c multi_genus.c
RUN gcc -O3 -DLONG -march=native -o multi_genus multi_genus.c -lm
COPY MultiGenus/planar_draw.c planar_draw.c
RUN gcc -std=gnu89 -O3 -o planar_draw planar_draw.c -lm

# Now we take a minimal python image and copy the compiled C binary to it
FROM python:3.9-slim

WORKDIR /app

RUN --mount=type=cache,target=/var/cache/apt \
    --mount=type=cache,target=/var/lib/apt \
    apt-get update \
    && apt-get install -y --no-install-recommends \
        poppler-utils \
        texlive-latex-base \
        texlive-latex-extra \
        texlive-latex-recommended \
        texlive-pictures \
    && rm -rf /var/lib/apt/lists/*

# Python dependencies
COPY WebApp/requirements.txt requirements.txt
RUN pip install --no-cache-dir -r requirements.txt

# Copy compiled C binaries
COPY --from=builder /app/page /app/pageSC /app/multi_genus /app/planar_draw /app/
    
# Copy the rest of the files
COPY PAGE/adjacency_lists/* adjacency_lists/
COPY WebApp/main.py main.py
COPY WebApp/static/ static/

EXPOSE 8080

CMD gunicorn --workers=$((2 * $(python -c 'import os; print(os.cpu_count())') + 1)) --threads=1 --bind=0.0.0.0:8080 --timeout 600 main:app
