// SPDX-License-Identifier: GPL-2.0-only
// Connected simple graphs in PAGE adjacency-list format. Row ends are significant;
// 65535 is optional padding. Incidence positions preserve the input rotation.
#ifndef PAGE_INPUT_H
#define PAGE_INPUT_H

#include <ctype.h>
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
    unsigned n, m, start, width;
    uint32_t* offset;
    uint16_t* neighbors;
    uint16_t* source;
    uint32_t* reverse;
} page_input;

static inline void page_input_error(const char* reason) {
    fprintf(stderr, "PAGE input: %s\n", reason);
    exit(EXIT_FAILURE);
}

static inline unsigned page_setting(const char* name, unsigned fallback, unsigned limit) {
    const char* text = getenv(name);
    if (text == NULL) return fallback;
    if (!isdigit((unsigned char)*text)) page_input_error("invalid numeric setting");

    char* end;
    errno = 0;
    unsigned long value = strtoul(text, &end, 10);
    if (errno || *end != '\0' || value > limit) page_input_error("invalid numeric setting");
    return (unsigned)value;
}

static inline void* page_alloc(size_t count, size_t size) {
    if (size != 0 && count > SIZE_MAX / size) page_input_error("allocation size overflow");
    void* result = calloc(count ? count : 1, size);
    if (result == NULL) page_input_error("could not allocate adjacency data");
    return result;
}

// Consume one unsigned decimal on this line, leaving its delimiter in *ch.
// Return zero at a newline or EOF. The caller alone advances to the next vertex.
static inline int page_row_number(FILE* file, int* ch, unsigned limit, unsigned* number) {
    while (*ch != '\n' && *ch != EOF && isspace((unsigned char)*ch)) *ch = fgetc(file);
    if (*ch == '\n' || *ch == EOF) return 0;
    if (!isdigit((unsigned char)*ch)) page_input_error("expected an unsigned decimal integer");

    unsigned value = 0;
    do {
        unsigned digit = (unsigned)(*ch - '0');
        if (value > limit / 10 || (value == limit / 10 && digit > limit % 10))
            page_input_error("integer out of range");
        value = 10 * value + digit;
        *ch = fgetc(file);
    } while (*ch != EOF && isdigit((unsigned char)*ch));
    if (*ch != EOF && !isspace((unsigned char)*ch)) page_input_error("invalid integer");
    *number = value;
    return 1;
}

// Index each incoming dart by its head. Match that bucket against the outgoing
// row in constant time per incidence, even at a vertex of very high degree.
static inline void page_pair_darts(page_input* g) {
    uint32_t darts = g->offset[g->n];
    g->source = (uint16_t*)page_alloc(darts, sizeof(*g->source));
    g->reverse = (uint32_t*)page_alloc(darts, sizeof(*g->reverse));
    uint32_t* incoming = (uint32_t*)page_alloc(g->n, sizeof(*incoming));
    uint32_t* slot = (uint32_t*)page_alloc(g->n, sizeof(*slot));
    memset(incoming, 0xff, g->n * sizeof(*incoming));
    memset(slot, 0xff, g->n * sizeof(*slot));

    for (unsigned v = 0; v < g->n; ++v) {
        for (uint32_t d = g->offset[v]; d < g->offset[v + 1]; ++d) {
            unsigned u = (unsigned)g->neighbors[d] - g->start;
            if (u >= g->n || u == v) page_input_error("out-of-range or loop incidence");
            g->neighbors[d] = (uint16_t)u;
            g->source[d] = (uint16_t)v;
            g->reverse[d] = incoming[u];
            incoming[u] = d;
        }
    }
    for (unsigned v = 0; v < g->n; ++v) {
        uint32_t begin = g->offset[v];
        uint32_t end = g->offset[v + 1];
        for (uint32_t d = begin; d < end; ++d) {
            unsigned u = g->neighbors[d];
            if (slot[u] != UINT32_MAX && slot[u] >= begin) page_input_error("duplicate neighbor");
            slot[u] = d;
        }
        for (uint32_t d = incoming[v]; d != UINT32_MAX;) {
            uint32_t next = g->reverse[d];
            uint32_t mate = slot[g->source[d]];
            if (mate < begin || mate >= end) page_input_error("asymmetric adjacency");
            g->reverse[d] = mate;
            d = next;
        }
    }
    free(slot);
    free(incoming);
}

static inline void page_check_connected(const page_input* g) {
    uint8_t* seen = (uint8_t*)page_alloc(g->n, sizeof(*seen));
    uint16_t* queue = (uint16_t*)page_alloc(g->n, sizeof(*queue));
    unsigned count = 1;
    seen[0] = 1;
    queue[0] = 0;
    for (unsigned k = 0; k < count; ++k) {
        unsigned v = queue[k];
        for (uint32_t d = g->offset[v]; d < g->offset[v + 1]; ++d) {
            unsigned u = g->neighbors[d];
            if (!seen[u]) {
                seen[u] = 1;
                queue[count++] = (uint16_t)u;
            }
        }
    }
    if (count != g->n) page_input_error("PAGE requires a connected graph");
    free(queue);
    free(seen);
}

static inline page_input page_read_input(const char* filename, unsigned degree_limit,
                                         unsigned edge_limit) {
    FILE* in = fopen(filename, "rb");
    if (in == NULL) page_input_error("could not open adjacency file");

    page_input g;
    int ch = fgetc(in);
    unsigned extra;
    if (!page_row_number(in, &ch, UINT16_MAX - 1, &g.n) ||
        !page_row_number(in, &ch, edge_limit, &g.m))
        page_input_error("missing vertex and edge counts");
    uint64_t darts = 2ULL * g.m;
    if (page_row_number(in, &ch, UINT32_MAX, &extra) || g.n == 0 ||
        darts > (uint64_t)g.n * (g.n - 1))
        page_input_error("invalid graph size");

    g.offset = (uint32_t*)page_alloc(g.n + 1, sizeof(*g.offset));
    g.neighbors = (uint16_t*)page_alloc((size_t)darts, sizeof(*g.neighbors));
    unsigned minimum_label = UINT16_MAX;
    unsigned max_degree = 0;
    for (unsigned v = 0; v < g.n; ++v) {
        if (ch == '\n') ch = fgetc(in);
        if (ch == EOF && g.n != 1) page_input_error("missing adjacency row");
        uint32_t pos = g.offset[v];
        unsigned u;
        while (page_row_number(in, &ch, UINT16_MAX, &u)) {
            if (u == UINT16_MAX) continue;
            if (pos >= darts) page_input_error("too many incidences for edge count");
            g.neighbors[pos++] = (uint16_t)u;
            if (u < minimum_label) minimum_label = u;
        }
        g.offset[v + 1] = pos;
        unsigned degree = pos - g.offset[v];
        if (degree > max_degree) max_degree = degree;
    }
    for (; ch != EOF; ch = fgetc(in))
        if (!isspace((unsigned char)ch)) page_input_error("unexpected data after adjacency rows");
    if (ferror(in)) page_input_error("read error");
    fclose(in);
    if (g.offset[g.n] != darts) page_input_error("edge count differs from adjacency rows");
    g.start = page_setting("S", minimum_label == UINT16_MAX ? 0 : minimum_label, UINT16_MAX - 1);
    g.width = page_setting("DEG", max_degree, degree_limit);
    if (g.width < max_degree || g.width > degree_limit || g.start + g.n > UINT16_MAX)
        page_input_error("invalid label range or degree");
    page_pair_darts(&g);
    page_check_connected(&g);
    return g;
}

static inline void page_free_input(page_input* g) {
    free(g->neighbors);
    free(g->offset);
    free(g->source);
    free(g->reverse);
}
#endif
