// Exact minimum orientable genus by lazy facial-walk generation.
// Copyright (C) 2026 Alexander Metzger

// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2 of the License, or
// (at your option) any later version.

#include <ctype.h>
#include <errno.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_VERTEX UINT16_MAX
#define NO_DART UINT32_MAX
#define REPORT_INTERVAL 1000000ULL
#define COLUMN_PROBE_DARTS 32

typedef uint16_t vertex_t;
typedef uint16_t degree_t;
typedef uint32_t dart_t;
typedef uint32_t face_count_t;

typedef struct {
    vertex_t n;
    uint32_t m;
    dart_t darts;
    degree_t max_degree;
    degree_t* degree;
    vertex_t* adjacency;
    dart_t* slot_dart;
    vertex_t* dart_from;
    vertex_t* dart_to;
    degree_t* dart_from_slot;
    degree_t* dart_to_slot;
    dart_t* reverse;
    vertex_t start_index;
    bool bipartite;
    bool has_bridge;
    uint32_t girth;
} graph_t;

typedef struct {
    graph_t* graph;
    uint8_t* used;
    degree_t* rotation_next;
    degree_t* rotation_prev;
    degree_t* rotation_count;
    dart_t remaining_darts;
    face_count_t target_faces;
    uint32_t target_genus;
    uint32_t min_face_length;
    uint64_t calls;
    uint64_t next_report;
    vertex_t* path_vertices;
    dart_t* path_darts;
    uint32_t* distance;
    vertex_t* bfs_queue;
    vertex_t* face_data;
    size_t face_data_capacity;
    size_t face_data_length;
    size_t* face_offsets;
} search_t;

static FILE* output_file;
static bool print_progress = true;

#define fail_if(condition, ...)       \
    do {                              \
        if (condition) {              \
            fprintf(stderr, __VA_ARGS__); \
            exit(1);                  \
        }                             \
    } while (0)

static void* checked_malloc(size_t count, size_t size, const char* label) {
    fail_if(size != 0 && count > SIZE_MAX / size,
            "Error: allocation size overflow for %s\n", label);
    size_t bytes = count * size;
    void* result = malloc(bytes == 0 ? 1 : bytes);
    fail_if(result == NULL, "Error allocating %s\n", label);
    return result;
}

static void* checked_calloc(size_t count, size_t size, const char* label) {
    fail_if(size != 0 && count > SIZE_MAX / size,
            "Error: allocation size overflow for %s\n", label);
    size_t bytes = count * size;
    void* result = calloc(bytes == 0 ? 1 : count, bytes == 0 ? 1 : size);
    fail_if(result == NULL, "Error allocating %s\n", label);
    return result;
}

static size_t graph_slot(const graph_t* graph, vertex_t vertex, degree_t slot) {
    return (size_t)vertex * graph->max_degree + slot;
}

static dart_t graph_find_dart(const graph_t* graph, vertex_t from, vertex_t to) {
    for (degree_t slot = 0; slot < graph->degree[from]; slot++) {
        if (graph->adjacency[graph_slot(graph, from, slot)] == to) {
            return graph->slot_dart[graph_slot(graph, from, slot)];
        }
    }
    fail_if(true, "Error: missing dart %u -> %u while restoring a face path\n",
            from, to);
    return NO_DART;
}

static void graph_free(graph_t* graph) {
    free(graph->degree);
    free(graph->adjacency);
    free(graph->slot_dart);
    free(graph->dart_from);
    free(graph->dart_to);
    free(graph->dart_from_slot);
    free(graph->dart_to_slot);
    free(graph->reverse);
    memset(graph, 0, sizeof(*graph));
}

static bool graph_connected(const graph_t* graph) {
    uint8_t* seen = checked_calloc(graph->n, sizeof(uint8_t), "connectivity flags");
    vertex_t* queue = checked_malloc(graph->n, sizeof(vertex_t), "connectivity queue");
    uint32_t head = 0;
    uint32_t tail = 0;
    seen[0] = 1;
    queue[tail++] = 0;
    while (head < tail) {
        vertex_t vertex = queue[head++];
        for (degree_t slot = 0; slot < graph->degree[vertex]; slot++) {
            vertex_t neighbor = graph->adjacency[graph_slot(graph, vertex, slot)];
            if (!seen[neighbor]) {
                seen[neighbor] = 1;
                queue[tail++] = neighbor;
            }
        }
    }
    free(seen);
    free(queue);
    return tail == graph->n;
}

static bool graph_bipartite(const graph_t* graph) {
    int8_t* color = checked_malloc(graph->n, sizeof(int8_t), "bipartite colors");
    vertex_t* queue = checked_malloc(graph->n, sizeof(vertex_t), "bipartite queue");
    for (vertex_t vertex = 0; vertex < graph->n; vertex++) {
        color[vertex] = -1;
    }
    for (vertex_t root = 0; root < graph->n; root++) {
        if (color[root] != -1) {
            continue;
        }
        uint32_t head = 0;
        uint32_t tail = 0;
        color[root] = 0;
        queue[tail++] = root;
        while (head < tail) {
            vertex_t vertex = queue[head++];
            for (degree_t slot = 0; slot < graph->degree[vertex]; slot++) {
                vertex_t neighbor = graph->adjacency[graph_slot(graph, vertex, slot)];
                if (color[neighbor] == -1) {
                    color[neighbor] = 1 - color[vertex];
                    queue[tail++] = neighbor;
                } else if (color[neighbor] == color[vertex]) {
                    free(color);
                    free(queue);
                    return false;
                }
            }
        }
    }
    free(color);
    free(queue);
    return true;
}

static void graph_find_bridges(const graph_t* graph, vertex_t vertex,
                               vertex_t parent, uint32_t* clock,
                               uint32_t* discovered, uint32_t* low,
                               bool* has_bridge) {
    discovered[vertex] = low[vertex] = ++*clock;
    for (degree_t slot = 0; slot < graph->degree[vertex]; slot++) {
        vertex_t neighbor = graph->adjacency[graph_slot(graph, vertex, slot)];
        if (neighbor == parent) {
            continue;
        }
        if (discovered[neighbor] == 0) {
            graph_find_bridges(graph, neighbor, vertex, clock, discovered, low,
                               has_bridge);
            if (low[neighbor] > discovered[vertex]) {
                *has_bridge = true;
            }
            if (low[neighbor] < low[vertex]) {
                low[vertex] = low[neighbor];
            }
        } else if (discovered[neighbor] < low[vertex]) {
            low[vertex] = discovered[neighbor];
        }
    }
}

static bool graph_has_bridge(const graph_t* graph) {
    uint32_t* discovered =
        checked_calloc(graph->n, sizeof(uint32_t), "bridge discovery times");
    uint32_t* low = checked_malloc(graph->n, sizeof(uint32_t), "bridge low links");
    uint32_t clock = 0;
    bool has_bridge = false;
    graph_find_bridges(graph, 0, MAX_VERTEX, &clock, discovered, low, &has_bridge);
    free(discovered);
    free(low);
    return has_bridge;
}

static uint32_t graph_girth(const graph_t* graph) {
    int32_t* distance = checked_malloc(graph->n, sizeof(int32_t), "girth distances");
    vertex_t* parent = checked_malloc(graph->n, sizeof(vertex_t), "girth parents");
    vertex_t* queue = checked_malloc(graph->n, sizeof(vertex_t), "girth queue");
    uint32_t best = UINT32_MAX;
    for (vertex_t root = 0; root < graph->n && best > 3; root++) {
        for (vertex_t vertex = 0; vertex < graph->n; vertex++) {
            distance[vertex] = -1;
            parent[vertex] = MAX_VERTEX;
        }
        uint32_t head = 0;
        uint32_t tail = 0;
        distance[root] = 0;
        queue[tail++] = root;
        while (head < tail) {
            vertex_t vertex = queue[head++];
            if ((uint32_t)(2 * distance[vertex] + 1) >= best) {
                continue;
            }
            for (degree_t slot = 0; slot < graph->degree[vertex]; slot++) {
                vertex_t neighbor = graph->adjacency[graph_slot(graph, vertex, slot)];
                if (distance[neighbor] == -1) {
                    distance[neighbor] = distance[vertex] + 1;
                    parent[neighbor] = vertex;
                    queue[tail++] = neighbor;
                } else if (parent[vertex] != neighbor) {
                    uint32_t length =
                        (uint32_t)(distance[vertex] + distance[neighbor] + 1);
                    if (length < best) {
                        best = length;
                    }
                }
            }
        }
    }
    free(distance);
    free(parent);
    free(queue);
    return best == UINT32_MAX ? 0 : best;
}

typedef struct {
    uint32_t start;
    uint32_t degree;
} input_layout_t;

static input_layout_t detect_input_layout(const char* filename,
                                          uint32_t ignored_vertex) {
    FILE* input = fopen(filename, "r");
    fail_if(input == NULL, "Error opening file %s\n", filename);

    unsigned vertex_count;
    unsigned ignored_edge_count;
    fail_if(fscanf(input, "%u %u", &vertex_count, &ignored_edge_count) != 2,
            "Error reading graph size from %s\n", filename);

    int character;
    while ((character = fgetc(input)) != '\n' && character != EOF) {
    }

    size_t line_capacity = (size_t)vertex_count * 6 + 2;
    char* line = checked_malloc(line_capacity, sizeof(char), "input line");
    uint32_t minimum_label = UINT32_MAX;
    uint32_t maximum_degree = 0;

    for (unsigned row = 0; row < vertex_count; row++) {
        fail_if(fgets(line, (int)line_capacity, input) == NULL,
                "Error reading adjacency row %u from %s\n", row, filename);
        fail_if(strchr(line, '\n') == NULL && !feof(input),
                "Error: adjacency row %u is too long\n", row);

        uint32_t row_degree = 0;
        char* cursor = line;
        while (*cursor != '\0') {
            while (isspace((unsigned char)*cursor)) {
                cursor++;
            }
            if (*cursor == '\0') {
                break;
            }

            errno = 0;
            char* end;
            unsigned long value = strtoul(cursor, &end, 10);
            fail_if(errno != 0 || end == cursor || value > ignored_vertex,
                    "Error: invalid neighbor on row %u\n", row);
            if (value != ignored_vertex) {
                row_degree++;
                if (value < minimum_label) {
                    minimum_label = (uint32_t)value;
                }
            }
            cursor = end;
        }

        if (row_degree > maximum_degree) {
            maximum_degree = row_degree;
        }
    }

    free(line);
    fclose(input);
    fail_if(maximum_degree == 0 || minimum_label == UINT32_MAX,
            "Error: graph has no adjacency entries\n");

    return (input_layout_t){
        .start = minimum_label,
        .degree = maximum_degree,
    };
}

static graph_t graph_load(const char* filename, degree_t max_degree,
                          vertex_t start_index) {
    FILE* input = fopen(filename, "r");
    fail_if(input == NULL, "Error opening file %s\n", filename);
    unsigned n_input;
    unsigned m_input;
    fail_if(fscanf(input, "%u %u", &n_input, &m_input) != 2,
            "Error reading graph size from %s\n", filename);
    fail_if(n_input == 0 || n_input >= MAX_VERTEX,
            "Error: vertex count must be between 1 and %u\n", MAX_VERTEX - 1);
    fail_if(max_degree == 0, "Error: DEG must be positive\n");

    graph_t graph = {
        .n = (vertex_t)n_input,
        .m = m_input,
        .max_degree = max_degree,
        .start_index = start_index,
    };
    size_t slots = (size_t)graph.n * max_degree;
    graph.degree = checked_calloc(graph.n, sizeof(degree_t), "vertex degrees");
    graph.adjacency = checked_malloc(slots, sizeof(vertex_t), "adjacency list");
    graph.slot_dart = checked_malloc(slots, sizeof(dart_t), "adjacency dart ids");
    for (size_t i = 0; i < slots; i++) {
        graph.adjacency[i] = MAX_VERTEX;
        graph.slot_dart[i] = NO_DART;
    }

    uint64_t dart_count = 0;
    for (vertex_t vertex = 0; vertex < graph.n; vertex++) {
        for (degree_t input_slot = 0; input_slot < max_degree; input_slot++) {
            unsigned raw_neighbor;
            fail_if(fscanf(input, "%u", &raw_neighbor) != 1,
                    "Error reading adjacency row %u from %s\n", vertex, filename);
            if (raw_neighbor == MAX_VERTEX) {
                continue;
            }
            fail_if(raw_neighbor < start_index || raw_neighbor - start_index >= graph.n,
                    "Error: invalid neighbor %u of vertex %u\n", raw_neighbor, vertex);
            fail_if(raw_neighbor - start_index == vertex,
                    "Error: loops are not supported at vertex %u\n", vertex);
            degree_t compact_slot = graph.degree[vertex]++;
            graph.adjacency[graph_slot(&graph, vertex, compact_slot)] =
                (vertex_t)(raw_neighbor - start_index);
            dart_count++;
        }
    }
    fclose(input);
    fail_if(dart_count != 2ULL * graph.m,
            "Error: adjacency list has %" PRIu64
            " directed edges, expected %" PRIu64 "\n",
            dart_count, 2ULL * graph.m);
    fail_if(dart_count > UINT32_MAX, "Error: too many directed edges\n");
    graph.darts = (dart_t)dart_count;
    graph.dart_from = checked_malloc(graph.darts, sizeof(vertex_t), "dart sources");
    graph.dart_to = checked_malloc(graph.darts, sizeof(vertex_t), "dart targets");
    graph.dart_from_slot =
        checked_malloc(graph.darts, sizeof(degree_t), "dart source slots");
    graph.dart_to_slot =
        checked_malloc(graph.darts, sizeof(degree_t), "dart target slots");
    graph.reverse = checked_malloc(graph.darts, sizeof(dart_t), "reverse darts");

    dart_t dart = 0;
    for (vertex_t vertex = 0; vertex < graph.n; vertex++) {
        for (degree_t slot = 0; slot < graph.degree[vertex]; slot++) {
            vertex_t neighbor = graph.adjacency[graph_slot(&graph, vertex, slot)];
            graph.slot_dart[graph_slot(&graph, vertex, slot)] = dart;
            graph.dart_from[dart] = vertex;
            graph.dart_to[dart] = neighbor;
            graph.dart_from_slot[dart] = slot;
            dart++;
        }
    }
    for (dart_t edge = 0; edge < graph.darts; edge++) {
        vertex_t from = graph.dart_from[edge];
        vertex_t to = graph.dart_to[edge];
        degree_t reverse_slot = MAX_VERTEX;
        for (degree_t slot = 0; slot < graph.degree[to]; slot++) {
            if (graph.adjacency[graph_slot(&graph, to, slot)] == from) {
                fail_if(reverse_slot != MAX_VERTEX,
                        "Error: parallel edges are not supported (%u, %u)\n", from, to);
                reverse_slot = slot;
            }
        }
        fail_if(reverse_slot == MAX_VERTEX,
                "Error: adjacency list is not symmetric at %u -> %u\n", from, to);
        graph.dart_to_slot[edge] = reverse_slot;
        graph.reverse[edge] = graph.slot_dart[graph_slot(&graph, to, reverse_slot)];
    }
    fail_if(!graph_connected(&graph), "Error: PAGE requires a connected graph\n");
    graph.bipartite = graph_bipartite(&graph);
    graph.has_bridge = graph_has_bridge(&graph);
    graph.girth = graph_girth(&graph);
    return graph;
}

static dart_t input_rotation_successor(const graph_t* graph, dart_t dart) {
    vertex_t center = graph->dart_to[dart];
    degree_t incoming = graph->dart_to_slot[dart];
    degree_t outgoing = (degree_t)((incoming + 1) % graph->degree[center]);
    return graph->slot_dart[graph_slot(graph, center, outgoing)];
}

static face_count_t input_rotation_face_count(const graph_t* graph) {
    uint8_t* seen = checked_calloc(graph->darts, sizeof(uint8_t), "face flags");
    face_count_t faces = 0;
    for (dart_t start = 0; start < graph->darts; start++) {
        if (seen[start]) {
            continue;
        }
        faces++;
        dart_t current = start;
        do {
            fail_if(seen[current], "Error: invalid input rotation orbit\n");
            seen[current] = 1;
            current = input_rotation_successor(graph, current);
        } while (current != start);
    }
    free(seen);
    return faces;
}

static uint32_t genus_from_faces(const graph_t* graph, face_count_t faces) {
    int64_t numerator = 2 - (int64_t)graph->n + graph->m - faces;
    fail_if(numerator < 0 || numerator % 2 != 0,
            "Error: invalid Euler characteristic for %u faces\n", faces);
    return (uint32_t)(numerator / 2);
}

static void write_input_rotation_solution(const graph_t* graph, uint32_t genus,
                                          uint64_t calls) {
    uint8_t* seen = checked_calloc(graph->darts, sizeof(uint8_t), "face flags");
    face_count_t faces = input_rotation_face_count(graph);
    fprintf(output_file,
            "Solution with %u cycles (genus %u) found in %" PRIu64 " iterations:\n",
            faces, genus, calls);
    for (dart_t start = 0; start < graph->darts; start++) {
        if (seen[start]) {
            continue;
        }
        dart_t current = start;
        fprintf(output_file, "%u ", graph->dart_from[current] + graph->start_index);
        do {
            seen[current] = 1;
            fprintf(output_file, "%u ", graph->dart_to[current] + graph->start_index);
            current = input_rotation_successor(graph, current);
        } while (current != start);
        fprintf(output_file, "\n");
    }
    free(seen);
}

static void search_free(search_t* search) {
    free(search->used);
    free(search->rotation_next);
    free(search->rotation_prev);
    free(search->rotation_count);
    free(search->path_vertices);
    free(search->path_darts);
    free(search->distance);
    free(search->bfs_queue);
    free(search->face_data);
    free(search->face_offsets);
    memset(search, 0, sizeof(*search));
}

static search_t search_create(graph_t* graph) {
    size_t slots = (size_t)graph->n * graph->max_degree;
    search_t search = {
        .graph = graph,
        .used = checked_calloc(graph->darts, sizeof(uint8_t), "used darts"),
        .rotation_next = checked_malloc(slots, sizeof(degree_t), "rotation successors"),
        .rotation_prev = checked_malloc(slots, sizeof(degree_t), "rotation predecessors"),
        .rotation_count = checked_calloc(graph->n, sizeof(degree_t), "rotation counts"),
        .path_vertices =
            checked_malloc((size_t)graph->darts + 1, sizeof(vertex_t), "face path"),
        .path_darts = checked_malloc(graph->darts, sizeof(dart_t), "face path darts"),
        .distance = checked_malloc(graph->n, sizeof(uint32_t), "face distances"),
        .bfs_queue = checked_malloc(graph->n, sizeof(vertex_t), "face distance queue"),
        .face_data_capacity = (size_t)graph->darts * 2 + 1,
        .face_offsets =
            checked_malloc((size_t)graph->darts + 1, sizeof(size_t), "face offsets"),
    };
    search.face_data =
        checked_malloc(search.face_data_capacity, sizeof(vertex_t), "solution faces");
    return search;
}

static void search_reset(search_t* search, uint32_t genus, face_count_t faces) {
    graph_t* graph = search->graph;
    memset(search->used, 0, graph->darts * sizeof(uint8_t));
    memset(search->rotation_next, 0xff,
           (size_t)graph->n * graph->max_degree * sizeof(degree_t));
    memset(search->rotation_prev, 0xff,
           (size_t)graph->n * graph->max_degree * sizeof(degree_t));
    memset(search->rotation_count, 0, graph->n * sizeof(degree_t));
    search->remaining_darts = graph->darts;
    search->target_faces = faces;
    search->target_genus = genus;
    search->min_face_length = graph->has_bridge || graph->girth == 0
                                  ? 2
                                  : graph->girth;
    search->calls = 0;
    search->next_report = REPORT_INTERVAL;
    search->face_data_length = 0;
    search->face_offsets[0] = 0;
}

static bool rotation_add(search_t* search, vertex_t center, degree_t incoming,
                         degree_t outgoing) {
    graph_t* graph = search->graph;
    degree_t degree = graph->degree[center];
    size_t incoming_index = graph_slot(graph, center, incoming);
    size_t outgoing_index = graph_slot(graph, center, outgoing);
    if (search->rotation_next[incoming_index] != MAX_VERTEX ||
        search->rotation_prev[outgoing_index] != MAX_VERTEX ||
        (incoming == outgoing && degree > 1)) {
        return false;
    }

    search->rotation_next[incoming_index] = outgoing;
    search->rotation_prev[outgoing_index] = incoming;
    search->rotation_count[center]++;

    degree_t cursor = outgoing;
    bool closed = false;
    for (degree_t steps = 0; steps <= degree; steps++) {
        degree_t next = search->rotation_next[graph_slot(graph, center, cursor)];
        if (next == MAX_VERTEX) {
            break;
        }
        cursor = next;
        if (cursor == incoming) {
            closed = true;
            break;
        }
    }
    if ((closed && search->rotation_count[center] < degree) ||
        (!closed && search->rotation_count[center] == degree)) {
        search->rotation_next[incoming_index] = MAX_VERTEX;
        search->rotation_prev[outgoing_index] = MAX_VERTEX;
        search->rotation_count[center]--;
        return false;
    }
    return true;
}

static void rotation_remove(search_t* search, vertex_t center, degree_t incoming,
                            degree_t outgoing) {
    graph_t* graph = search->graph;
    size_t incoming_index = graph_slot(graph, center, incoming);
    size_t outgoing_index = graph_slot(graph, center, outgoing);
    fail_if(search->rotation_next[incoming_index] != outgoing ||
                search->rotation_prev[outgoing_index] != incoming,
            "Error: removing a missing rotation transition\n");
    search->rotation_next[incoming_index] = MAX_VERTEX;
    search->rotation_prev[outgoing_index] = MAX_VERTEX;
    search->rotation_count[center]--;
}

static bool transition_add_for_darts(search_t* search, dart_t incoming,
                                     dart_t outgoing) {
    graph_t* graph = search->graph;
    fail_if(graph->dart_to[incoming] != graph->dart_from[outgoing],
            "Error: nonconsecutive darts in face path\n");
    return rotation_add(search, graph->dart_to[incoming],
                        graph->dart_to_slot[incoming], graph->dart_from_slot[outgoing]);
}

static void transition_remove_for_darts(search_t* search, dart_t incoming,
                                        dart_t outgoing) {
    graph_t* graph = search->graph;
    rotation_remove(search, graph->dart_to[incoming], graph->dart_to_slot[incoming],
                    graph->dart_from_slot[outgoing]);
}

static void compute_distances(search_t* search, vertex_t target) {
    graph_t* graph = search->graph;
    for (vertex_t vertex = 0; vertex < graph->n; vertex++) {
        search->distance[vertex] = UINT32_MAX;
    }
    uint32_t head = 0;
    uint32_t tail = 0;
    search->distance[target] = 0;
    search->bfs_queue[tail++] = target;
    while (head < tail) {
        vertex_t vertex = search->bfs_queue[head++];
        for (degree_t slot = 0; slot < graph->degree[vertex]; slot++) {
            vertex_t neighbor = graph->adjacency[graph_slot(graph, vertex, slot)];
            if (search->distance[neighbor] == UINT32_MAX) {
                search->distance[neighbor] = search->distance[vertex] + 1;
                search->bfs_queue[tail++] = neighbor;
            }
        }
    }
}

static bool search_faces(search_t* search, face_count_t faces_left);

static bool finish_face(search_t* search, uint32_t length,
                        face_count_t faces_left, dart_t start_dart) {
    size_t old_length = search->face_data_length;
    fail_if(old_length + length + 1 > search->face_data_capacity,
            "Error: solution face buffer overflow\n");
    memcpy(&search->face_data[old_length], search->path_vertices,
           (length + 1) * sizeof(vertex_t));
    search->face_data_length += length + 1;
    face_count_t depth = search->target_faces - faces_left;
    search->face_offsets[depth] = old_length;
    search->face_offsets[depth + 1] = search->face_data_length;
    if (search_faces(search, faces_left - 1)) {
        return true;
    }
    memcpy(search->path_vertices, &search->face_data[old_length],
           (length + 1) * sizeof(vertex_t));
    for (uint32_t i = 0; i < length; i++) {
        search->path_darts[i] =
            graph_find_dart(search->graph, search->path_vertices[i],
                            search->path_vertices[i + 1]);
    }
    search->face_data_length = old_length;
    compute_distances(search, search->graph->dart_from[start_dart]);
    return false;
}

static bool generate_face_path(search_t* search, dart_t start_dart,
                               uint32_t target_length, uint32_t length,
                               face_count_t faces_left) {
    graph_t* graph = search->graph;
    vertex_t start = graph->dart_from[start_dart];
    vertex_t current = search->path_vertices[length];
    dart_t incoming = search->path_darts[length - 1];

    if (length == target_length) {
        if (current != start ||
            !transition_add_for_darts(search, incoming, start_dart)) {
            return false;
        }
        if (finish_face(search, length, faces_left, start_dart)) {
            return true;
        }
        transition_remove_for_darts(search, incoming, start_dart);
        return false;
    }
    if (search->distance[current] == UINT32_MAX ||
        length + search->distance[current] > target_length) {
        return false;
    }

    for (int reverse_used = 1; reverse_used >= 0; reverse_used--) {
        for (degree_t slot = 0; slot < graph->degree[current]; slot++) {
            dart_t outgoing = graph->slot_dart[graph_slot(graph, current, slot)];
            if (search->used[outgoing] ||
                (int)search->used[graph->reverse[outgoing]] != reverse_used) {
                continue;
            }
            vertex_t next = graph->dart_to[outgoing];
            if (length + 1 + search->distance[next] > target_length ||
                !transition_add_for_darts(search, incoming, outgoing)) {
                continue;
            }
            search->used[outgoing] = 1;
            search->remaining_darts--;
            search->path_darts[length] = outgoing;
            search->path_vertices[length + 1] = next;
            if (generate_face_path(search, start_dart, target_length, length + 1,
                                   faces_left)) {
                return true;
            }
            search->used[outgoing] = 0;
            search->remaining_darts++;
            transition_remove_for_darts(search, incoming, outgoing);
        }
    }
    return false;
}

static uint32_t count_face_paths(search_t* search, dart_t start_dart,
                                 uint32_t target_length, uint32_t length,
                                 uint32_t limit) {
    graph_t* graph = search->graph;
    vertex_t start = graph->dart_from[start_dart];
    vertex_t current = search->path_vertices[length];
    dart_t incoming = search->path_darts[length - 1];
    if (length == target_length) {
        if (current != start ||
            !transition_add_for_darts(search, incoming, start_dart)) {
            return 0;
        }
        transition_remove_for_darts(search, incoming, start_dart);
        return 1;
    }
    if (search->distance[current] == UINT32_MAX ||
        length + search->distance[current] > target_length) {
        return 0;
    }

    uint32_t count = 0;
    for (int reverse_used = 1; reverse_used >= 0 && count < limit; reverse_used--) {
        for (degree_t slot = 0;
             slot < graph->degree[current] && count < limit; slot++) {
            dart_t outgoing = graph->slot_dart[graph_slot(graph, current, slot)];
            if (search->used[outgoing] ||
                (int)search->used[graph->reverse[outgoing]] != reverse_used) {
                continue;
            }
            vertex_t next = graph->dart_to[outgoing];
            if (length + 1 + search->distance[next] > target_length ||
                !transition_add_for_darts(search, incoming, outgoing)) {
                continue;
            }
            search->used[outgoing] = 1;
            search->remaining_darts--;
            search->path_darts[length] = outgoing;
            search->path_vertices[length + 1] = next;
            count += count_face_paths(search, start_dart, target_length, length + 1,
                                      limit - count);
            search->used[outgoing] = 0;
            search->remaining_darts++;
            transition_remove_for_darts(search, incoming, outgoing);
        }
    }
    return count;
}

static uint32_t count_faces_through_dart(search_t* search, dart_t start_dart,
                                         uint32_t target_length, uint32_t limit) {
    compute_distances(search, search->graph->dart_from[start_dart]);
    search->used[start_dart] = 1;
    search->remaining_darts--;
    search->path_darts[0] = start_dart;
    search->path_vertices[0] = search->graph->dart_from[start_dart];
    search->path_vertices[1] = search->graph->dart_to[start_dart];
    uint32_t count = count_face_paths(search, start_dart, target_length, 1, limit);
    search->used[start_dart] = 0;
    search->remaining_darts++;
    return count;
}

static bool dart_better_for_probe(const search_t* search, dart_t left, dart_t right) {
    graph_t* graph = search->graph;
    bool left_reverse = search->used[graph->reverse[left]] != 0;
    bool right_reverse = search->used[graph->reverse[right]] != 0;
    if (left_reverse != right_reverse) {
        return left_reverse > right_reverse;
    }
    vertex_t left_from = graph->dart_from[left];
    vertex_t left_to = graph->dart_to[left];
    vertex_t right_from = graph->dart_from[right];
    vertex_t right_to = graph->dart_to[right];
    degree_t left_remaining =
        graph->degree[left_to] - search->rotation_count[left_to];
    degree_t right_remaining =
        graph->degree[right_to] - search->rotation_count[right_to];
    if (left_remaining != right_remaining) {
        return left_remaining < right_remaining;
    }
    degree_t left_pressure =
        search->rotation_count[left_from] + search->rotation_count[left_to];
    degree_t right_pressure =
        search->rotation_count[right_from] + search->rotation_count[right_to];
    return left_pressure > right_pressure;
}

static dart_t choose_start_dart(search_t* search, uint32_t probe_length) {
    graph_t* graph = search->graph;
    dart_t probes[COLUMN_PROBE_DARTS];
    uint32_t probe_count = 0;
    for (dart_t dart = 0; dart < graph->darts; dart++) {
        if (search->used[dart]) {
            continue;
        }
        uint32_t position = probe_count;
        if (position > COLUMN_PROBE_DARTS) {
            position = COLUMN_PROBE_DARTS;
        }
        while (position > 0 &&
               dart_better_for_probe(search, dart, probes[position - 1])) {
            if (position < COLUMN_PROBE_DARTS) {
                probes[position] = probes[position - 1];
            }
            position--;
        }
        if (position < COLUMN_PROBE_DARTS) {
            probes[position] = dart;
            if (probe_count < COLUMN_PROBE_DARTS) {
                probe_count++;
            }
        }
    }
    if (probe_count == 0) {
        return NO_DART;
    }

    dart_t best = probes[0];
    uint32_t best_count = UINT32_MAX;
    for (uint32_t i = 0; i < probe_count; i++) {
        uint32_t limit = best_count == UINT32_MAX ? UINT32_MAX : best_count;
        uint32_t count =
            count_faces_through_dart(search, probes[i], probe_length, limit);
        if (count < best_count) {
            best = probes[i];
            best_count = count;
            if (best_count == 0) {
                break;
            }
        }
    }
    return best;
}

static bool rotations_complete(const search_t* search) {
    for (vertex_t vertex = 0; vertex < search->graph->n; vertex++) {
        if (search->rotation_count[vertex] != search->graph->degree[vertex]) {
            return false;
        }
    }
    return true;
}

static bool search_faces(search_t* search, face_count_t faces_left) {
    search->calls++;
    if (print_progress && search->calls >= search->next_report) {
        fprintf(stderr,
                "\rLazy search: %" PRIu64 " states, %u / %u faces fixed",
                search->calls, search->target_faces - faces_left, search->target_faces);
        fflush(stderr);
        search->next_report += REPORT_INTERVAL;
    }
    if (faces_left == 0) {
        return search->remaining_darts == 0 && rotations_complete(search);
    }
    if (search->remaining_darts <
        (uint64_t)faces_left * search->min_face_length) {
        return false;
    }

    uint32_t max_length =
        search->remaining_darts - (faces_left - 1) * search->min_face_length;
    uint32_t first_length = search->min_face_length;
    uint32_t step = search->graph->bipartite ? 2 : 1;
    if (faces_left == 1) {
        first_length = search->remaining_darts;
        max_length = first_length;
    }
    dart_t start_dart = choose_start_dart(search, first_length);
    if (start_dart == NO_DART) {
        return false;
    }

    compute_distances(search, search->graph->dart_from[start_dart]);
    search->used[start_dart] = 1;
    search->remaining_darts--;
    search->path_darts[0] = start_dart;
    search->path_vertices[0] = search->graph->dart_from[start_dart];
    search->path_vertices[1] = search->graph->dart_to[start_dart];

    for (uint32_t length = first_length; length <= max_length; length += step) {
        uint32_t remaining_after = search->remaining_darts + 1 - length;
        if (remaining_after < (uint64_t)(faces_left - 1) * search->min_face_length) {
            continue;
        }
        if (search->graph->bipartite && length % 2 != 0) {
            continue;
        }
        if (generate_face_path(search, start_dart, length, 1, faces_left)) {
            return true;
        }
        if (length > UINT32_MAX - step) {
            break;
        }
    }
    search->used[start_dart] = 0;
    search->remaining_darts++;
    return false;
}

static bool solve_genus(search_t* search, uint32_t genus, face_count_t faces) {
    search_reset(search, genus, faces);
    return search_faces(search, faces);
}

static void write_lazy_solution(const search_t* search) {
    fprintf(output_file,
            "Solution with %u cycles (genus %u) found in %" PRIu64 " iterations:\n",
            search->target_faces, search->target_genus, search->calls);
    for (face_count_t face = 0; face < search->target_faces; face++) {
        for (size_t i = search->face_offsets[face]; i < search->face_offsets[face + 1]; i++) {
            fprintf(output_file, "%u ",
                    search->face_data[i] + search->graph->start_index);
        }
        fprintf(output_file, "\n");
    }
}

int main(void) {
    const char* filename = getenv("ADJ");
    fail_if(filename == NULL, "Usage: ADJ=adjacency_lists/3-8-cage.txt ./page_low_mem\n");
    input_layout_t detected = detect_input_layout(filename, MAX_VERTEX);
    const char* start_text = getenv("S");
    const char* degree_text = getenv("DEG");
    unsigned long start_value = start_text == NULL ? detected.start : strtoul(start_text, NULL, 10);
    unsigned long degree_value = degree_text == NULL ? detected.degree : strtoul(degree_text, NULL, 10);
    fail_if(start_value >= MAX_VERTEX || degree_value == 0 || degree_value >= MAX_VERTEX, "Error: invalid S or DEG value\n");
    
    uint32_t precomputed_lower_bound = 0;
    if (getenv("GLB") != NULL) {
        precomputed_lower_bound = (uint32_t)strtoul(getenv("GLB"), NULL, 10);
    }
    if (getenv("QUIET") != NULL) {
        print_progress = false;
    }

    if (print_progress) {
        fprintf(stderr, "Loading adjacency list...\n");
    }
    graph_t graph = graph_load(filename, (degree_t)degree_value, (vertex_t)start_value);
    if (print_progress) {
        fprintf(stderr,
                "Read %s: %u vertices, %u edges, girth %u%s.\n",
                filename, graph.n, graph.m, graph.girth,
                graph.bipartite ? ", bipartite" : "");
    }

    output_file = getenv("STDOUT") != NULL ? stdout : fopen("page.out", "w");
    fail_if(output_file == NULL, "Error opening page.out\n");
    face_count_t input_faces = input_rotation_face_count(&graph);
    uint32_t upper_genus = genus_from_faces(&graph, input_faces);

    if (graph.girth == 0) {
        if (print_progress) {
            fprintf(stderr, "A connected acyclic graph has genus 0.\n"
                            "Found a solution! The genus is 0.\n");
        }
        write_input_rotation_solution(&graph, 0, 0);
        if (output_file != stdout) fclose(output_file);
        graph_free(&graph);
        return 0;
    }

    uint32_t bound_face_length = graph.has_bridge ? 2 : graph.girth;
    face_count_t face_upper_bound = graph.darts / bound_face_length;
    int64_t lower_numerator =
        2 - (int64_t)graph.n + graph.m - face_upper_bound;
    uint32_t lower_genus =
        lower_numerator <= 0 ? 0 : (uint32_t)((lower_numerator + 1) / 2);
    if (precomputed_lower_bound > lower_genus) {
        lower_genus = precomputed_lower_bound;
    }
    fail_if(lower_genus > upper_genus,
            "Error: genus lower bound %u exceeds input-rotation upper bound %u\n",
            lower_genus, upper_genus);

    search_t search = search_create(&graph);
    uint64_t total_calls = 0;
    if (print_progress) {
        fprintf(stderr, "Beginning lazy genus search between %u and %u.\n",
                lower_genus, upper_genus);
    }
    for (uint32_t genus = lower_genus; genus < upper_genus; genus++) {
        int64_t faces_value = (int64_t)graph.m - graph.n + 2 - 2 * (int64_t)genus;
        if (faces_value <= 0 || faces_value > UINT32_MAX) {
            continue;
        }
        face_count_t faces = (face_count_t)faces_value;
        if (print_progress) {
            fprintf(stderr, "Searching for %u faces (genus %u)...\n", faces, genus);
        }
        if (solve_genus(&search, genus, faces)) {
            total_calls += search.calls;
            if (print_progress) {
                fprintf(stderr,
                        "\nFound a solution! The genus is %u (%" PRIu64 " states).\n",
                        genus, total_calls);
            }
            write_lazy_solution(&search);
            if (output_file != stdout) fclose(output_file);
            search_free(&search);
            graph_free(&graph);
            return 0;
        }
        total_calls += search.calls;
        if (print_progress) {
            fprintf(stderr, "\rNo %u-face embedding after %" PRIu64 " states.\n",
                    faces, search.calls);
        }
    }

    if (print_progress) {
        fprintf(stderr,
                "No smaller embedding exists; using the input rotation system.\n"
                "Found a solution! The genus is %u (%" PRIu64 " states).\n",
                upper_genus, total_calls);
    }
    write_input_rotation_solution(&graph, upper_genus, total_calls);
    if (output_file != stdout) fclose(output_file);
    search_free(&search);
    graph_free(&graph);
    return 0;
}
