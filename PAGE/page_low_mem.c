// Exact minimum orientable genus by lazy facial-walk generation.
// Copyright (C) 2026 Alexander Metzger

// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2 of the License, or
// (at your option) any later version.

#include "page_input.h"

#ifdef _WIN32
#include <windows.h>
#else
#include <sys/resource.h>
#endif
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
    page_input input;
    dart_t darts;
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
    dart_t* path_darts;
    uint32_t* distance;
    vertex_t* bfs_queue;
    dart_t* face_data;
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

static degree_t graph_degree(const graph_t* graph, vertex_t vertex) {
    return (degree_t)(graph->input.offset[vertex + 1] - graph->input.offset[vertex]);
}

static dart_t graph_slot(const graph_t* graph, vertex_t vertex, degree_t slot) {
    return graph->input.offset[vertex] + slot;
}

static degree_t dart_slot(const graph_t* graph, dart_t dart) {
    return (degree_t)(dart - graph->input.offset[graph->input.source[dart]]);
}

static void graph_free(graph_t* graph) {
    page_free_input(&graph->input);
}

static bool graph_bipartite(const graph_t* graph) {
    int8_t* color = checked_malloc(graph->input.n, sizeof(int8_t), "bipartite colors");
    vertex_t* queue = checked_malloc(graph->input.n, sizeof(vertex_t), "bipartite queue");
    for (vertex_t vertex = 0; vertex < graph->input.n; vertex++) {
        color[vertex] = -1;
    }
    for (vertex_t root = 0; root < graph->input.n; root++) {
        if (color[root] != -1) {
            continue;
        }
        uint32_t head = 0;
        uint32_t tail = 0;
        color[root] = 0;
        queue[tail++] = root;
        while (head < tail) {
            vertex_t vertex = queue[head++];
            for (degree_t slot = 0; slot < graph_degree(graph, vertex); slot++) {
                vertex_t neighbor = graph->input.neighbors[graph_slot(graph, vertex, slot)];
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

// Iterative low-link DFS: a long path uses heap space rather than the process stack.
static bool graph_has_bridge(const graph_t* graph) {
    unsigned n = graph->input.n;
    uint32_t* discovered = checked_calloc(n, sizeof(*discovered), "bridge discovery times");
    uint32_t* low = checked_malloc(n, sizeof(*low), "bridge low links");
    dart_t* next = checked_malloc(n, sizeof(*next), "bridge DFS positions");
    dart_t* parent = checked_malloc(n, sizeof(*parent), "bridge DFS parents");
    memcpy(next, graph->input.offset, n * sizeof(*next));
    vertex_t v = 0;
    uint32_t clock = 1;
    discovered[v] = low[v] = clock;
    parent[v] = NO_DART;
    bool bridge = false;
    for (;;) {
        if (next[v] < graph->input.offset[v + 1]) {
            dart_t d = next[v]++;
            vertex_t w = graph->input.neighbors[d];
            if (d == parent[v]) continue;
            if (!discovered[w]) {
                parent[w] = graph->input.reverse[d];
                discovered[w] = low[w] = ++clock;
                v = w;
            } else if (discovered[w] < low[v]) {
                low[v] = discovered[w];
            }
        } else {
            if (parent[v] == NO_DART) break;
            vertex_t w = graph->input.neighbors[parent[v]];
            if (low[v] > discovered[w]) {
                bridge = true;
                break;
            }
            if (low[v] < low[w]) low[w] = low[v];
            v = w;
        }
    }
    free(parent);
    free(next);
    free(low);
    free(discovered);
    return bridge;
}

static uint32_t graph_girth(const graph_t* graph) {
    int32_t* distance = checked_malloc(graph->input.n, sizeof(int32_t), "girth distances");
    vertex_t* parent = checked_malloc(graph->input.n, sizeof(vertex_t), "girth parents");
    vertex_t* queue = checked_malloc(graph->input.n, sizeof(vertex_t), "girth queue");
    uint32_t best = UINT32_MAX;
    for (vertex_t root = 0; root < graph->input.n && best > 3; root++) {
        for (vertex_t vertex = 0; vertex < graph->input.n; vertex++) {
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
            for (degree_t slot = 0; slot < graph_degree(graph, vertex); slot++) {
                vertex_t neighbor = graph->input.neighbors[graph_slot(graph, vertex, slot)];
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

static graph_t graph_load(const char* filename) {
    graph_t graph = {.input = page_read_input(filename, MAX_VERTEX - 1, UINT32_MAX / 2)};
    const page_input* input = &graph.input;
    graph.darts = input->offset[input->n];
    if (input->m == input->n - 1) {
        graph.bipartite = true;
        graph.has_bridge = input->m != 0;
    } else {
        graph.bipartite = graph_bipartite(&graph);
        graph.has_bridge = graph_has_bridge(&graph);
        graph.girth = graph_girth(&graph);
    }
    return graph;
}

static dart_t input_rotation_successor(const graph_t* graph, dart_t dart) {
    vertex_t center = graph->input.neighbors[dart];
    dart_t next = graph->input.reverse[dart] + 1;
    return next == graph->input.offset[center + 1] ? graph->input.offset[center] : next;
}

static face_count_t input_rotation_face_count(const graph_t* graph) {
    uint8_t* seen = checked_calloc(graph->darts, sizeof(uint8_t), "face flags");
    face_count_t faces = graph->darts == 0 ? 1 : 0;
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
    int64_t numerator = 2 - (int64_t)graph->input.n + graph->input.m - faces;
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
    if (graph->darts == 0) fprintf(output_file, "%u\n", graph->input.start);
    for (dart_t start = 0; start < graph->darts; start++) {
        if (seen[start]) {
            continue;
        }
        dart_t current = start;
        fprintf(output_file, "%u ", graph->input.source[current] + graph->input.start);
        do {
            seen[current] = 1;
            fprintf(output_file, "%u ", graph->input.neighbors[current] + graph->input.start);
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
    free(search->path_darts);
    free(search->distance);
    free(search->bfs_queue);
    free(search->face_data);
    free(search->face_offsets);
    memset(search, 0, sizeof(*search));
}

static search_t search_create(graph_t* graph) {
    search_t search = {
        .graph = graph,
        .used = checked_calloc(graph->darts, sizeof(uint8_t), "used darts"),
        .rotation_next = checked_malloc(graph->darts, sizeof(degree_t), "rotation successors"),
        .rotation_prev = checked_malloc(graph->darts, sizeof(degree_t), "rotation predecessors"),
        .rotation_count = checked_calloc(graph->input.n, sizeof(degree_t), "rotation counts"),
        .path_darts = checked_malloc(graph->darts, sizeof(dart_t), "face path darts"),
        .distance = checked_malloc(graph->input.n, sizeof(uint32_t), "face distances"),
        .bfs_queue = checked_malloc(graph->input.n, sizeof(vertex_t), "face distance queue"),
        .face_data = checked_malloc(graph->darts, sizeof(dart_t), "solution face darts"),
        .face_offsets =
            checked_malloc((size_t)graph->darts + 1, sizeof(size_t), "face offsets"),
    };
    return search;
}

static void search_reset(search_t* search, uint32_t genus, face_count_t faces) {
    graph_t* graph = search->graph;
    memset(search->used, 0, graph->darts * sizeof(uint8_t));
    memset(search->rotation_next, 0xff,
           (size_t)graph->darts * sizeof(degree_t));
    memset(search->rotation_prev, 0xff,
           (size_t)graph->darts * sizeof(degree_t));
    memset(search->rotation_count, 0, graph->input.n * sizeof(degree_t));
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
    degree_t degree = graph_degree(graph, center);
    size_t incoming_index = graph_slot(graph, center, incoming);
    size_t outgoing_index = graph_slot(graph, center, outgoing);
    if (search->rotation_next[incoming_index] != MAX_VERTEX ||
        search->rotation_prev[outgoing_index] != MAX_VERTEX) {
        return false;
    }

    // Adding incoming -> outgoing closes a cycle iff the path from outgoing
    // ends at incoming. Such a cycle must include every incidence at the vertex.
    degree_t cursor = outgoing;
    unsigned span = 1;
    while (cursor != incoming) {
        cursor = search->rotation_next[graph_slot(graph, center, cursor)];
        if (cursor == MAX_VERTEX) break;
        ++span;
    }
    if (cursor == incoming && span != degree) return false;
    search->rotation_next[incoming_index] = outgoing;
    search->rotation_prev[outgoing_index] = incoming;
    search->rotation_count[center]++;
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
    fail_if(graph->input.neighbors[incoming] != graph->input.source[outgoing],
            "Error: nonconsecutive darts in face path\n");
    return rotation_add(search, graph->input.neighbors[incoming],
                        dart_slot(graph, graph->input.reverse[incoming]), dart_slot(graph, outgoing));
}

static void transition_remove_for_darts(search_t* search, dart_t incoming,
                                        dart_t outgoing) {
    graph_t* graph = search->graph;
    rotation_remove(search, graph->input.neighbors[incoming], dart_slot(graph, graph->input.reverse[incoming]),
                    dart_slot(graph, outgoing));
}

static void compute_distances(search_t* search, vertex_t target) {
    graph_t* graph = search->graph;
    for (vertex_t vertex = 0; vertex < graph->input.n; vertex++) {
        search->distance[vertex] = UINT32_MAX;
    }
    uint32_t head = 0;
    uint32_t tail = 0;
    search->distance[target] = 0;
    search->bfs_queue[tail++] = target;
    while (head < tail) {
        vertex_t vertex = search->bfs_queue[head++];
        for (degree_t slot = 0; slot < graph_degree(graph, vertex); slot++) {
            vertex_t neighbor = graph->input.neighbors[graph_slot(graph, vertex, slot)];
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
    fail_if(length > search->graph->darts - old_length, "Error: solution face buffer overflow\n");
    memcpy(search->face_data + old_length, search->path_darts, length * sizeof(dart_t));
    search->face_data_length += length;
    face_count_t depth = search->target_faces - faces_left;
    search->face_offsets[depth] = old_length;
    search->face_offsets[depth + 1] = search->face_data_length;
    if (search_faces(search, faces_left - 1)) {
        return true;
    }
    memcpy(search->path_darts, search->face_data + old_length, length * sizeof(dart_t));
    search->face_data_length = old_length;
    compute_distances(search, search->graph->input.source[start_dart]);
    return false;
}

static bool generate_face_path(search_t* search, dart_t start_dart,
                               uint32_t target_length, uint32_t length,
                               face_count_t faces_left) {
    graph_t* graph = search->graph;
    vertex_t start = graph->input.source[start_dart];
    dart_t incoming = search->path_darts[length - 1];
    vertex_t current = graph->input.neighbors[incoming];

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
        for (degree_t slot = 0; slot < graph_degree(graph, current); slot++) {
            dart_t outgoing = graph_slot(graph, current, slot);
            if (search->used[outgoing] ||
                (int)search->used[graph->input.reverse[outgoing]] != reverse_used) {
                continue;
            }
            vertex_t next = graph->input.neighbors[outgoing];
            if (length + 1 + search->distance[next] > target_length ||
                !transition_add_for_darts(search, incoming, outgoing)) {
                continue;
            }
            search->used[outgoing] = 1;
            search->remaining_darts--;
            search->path_darts[length] = outgoing;
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
    vertex_t start = graph->input.source[start_dart];
    dart_t incoming = search->path_darts[length - 1];
    vertex_t current = graph->input.neighbors[incoming];
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
             slot < graph_degree(graph, current) && count < limit; slot++) {
            dart_t outgoing = graph_slot(graph, current, slot);
            if (search->used[outgoing] ||
                (int)search->used[graph->input.reverse[outgoing]] != reverse_used) {
                continue;
            }
            vertex_t next = graph->input.neighbors[outgoing];
            if (length + 1 + search->distance[next] > target_length ||
                !transition_add_for_darts(search, incoming, outgoing)) {
                continue;
            }
            search->used[outgoing] = 1;
            search->remaining_darts--;
            search->path_darts[length] = outgoing;
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
    compute_distances(search, search->graph->input.source[start_dart]);
    search->used[start_dart] = 1;
    search->remaining_darts--;
    search->path_darts[0] = start_dart;
    uint32_t count = count_face_paths(search, start_dart, target_length, 1, limit);
    search->used[start_dart] = 0;
    search->remaining_darts++;
    return count;
}

static bool dart_better_for_probe(const search_t* search, dart_t left, dart_t right) {
    graph_t* graph = search->graph;
    bool left_reverse = search->used[graph->input.reverse[left]] != 0;
    bool right_reverse = search->used[graph->input.reverse[right]] != 0;
    if (left_reverse != right_reverse) {
        return left_reverse > right_reverse;
    }
    vertex_t left_from = graph->input.source[left];
    vertex_t left_to = graph->input.neighbors[left];
    vertex_t right_from = graph->input.source[right];
    vertex_t right_to = graph->input.neighbors[right];
    degree_t left_remaining =
        graph_degree(graph, left_to) - search->rotation_count[left_to];
    degree_t right_remaining =
        graph_degree(graph, right_to) - search->rotation_count[right_to];
    if (left_remaining != right_remaining) {
        return left_remaining < right_remaining;
    }
    unsigned left_pressure =
        search->rotation_count[left_from] + search->rotation_count[left_to];
    unsigned right_pressure =
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
    for (vertex_t vertex = 0; vertex < search->graph->input.n; vertex++) {
        if (search->rotation_count[vertex] != graph_degree(search->graph, vertex)) {
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

    compute_distances(search, search->graph->input.source[start_dart]);
    search->used[start_dart] = 1;
    search->remaining_darts--;
    search->path_darts[0] = start_dart;

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

#ifdef _WIN32
static DWORD WINAPI search_thread(void* context) {
    search_t* search = context;
    return search_faces(search, search->target_faces) ? 1 : 0;
}
#endif

static bool solve_genus(search_t* search, uint32_t genus, face_count_t faces) {
    // At most one active path frame per dart and one completion per face.
    // Reserve HoG's allowance before descending, including the nested probe calls.
    uint64_t levels = (uint64_t)search->graph->darts + faces;
    uint64_t bytes = 4ULL * 1024 * 1024 + 512 * levels;
    search_reset(search, genus, faces);
#ifdef _WIN32
    // Windows fixes the reserve when creating a thread.
    fail_if(bytes > SIZE_MAX, "Error: face search stack exceeds address space\n");
    HANDLE thread = CreateThread(NULL, (SIZE_T)bytes, search_thread, search,
                                 STACK_SIZE_PARAM_IS_A_RESERVATION, NULL);
    fail_if(!thread, "Error reserving face search stack (%" PRIu64 " bytes)\n", bytes);
    DWORD result;
    fail_if(WaitForSingleObject(thread, INFINITE) != WAIT_OBJECT_0 ||
                !GetExitCodeThread(thread, &result) || result > 1,
            "Error running face search thread\n");
    CloseHandle(thread);
    return result == 1;
#else
    struct rlimit limit;
    fail_if(getrlimit(RLIMIT_STACK, &limit) != 0, "Error reading stack limit: %s\n",
            strerror(errno));
    if (limit.rlim_cur != RLIM_INFINITY && (uint64_t)limit.rlim_cur < bytes) {
        fail_if((limit.rlim_max != RLIM_INFINITY && bytes > (uint64_t)limit.rlim_max) ||
                    (uint64_t)(rlim_t)bytes != bytes,
                "Error: face search needs a stack limit of %" PRIu64 " bytes\n", bytes);
        limit.rlim_cur = (rlim_t)bytes;
        fail_if(setrlimit(RLIMIT_STACK, &limit) != 0,
                "Error raising face search stack to %" PRIu64 " bytes: %s\n", bytes,
                strerror(errno));
    }
    return search_faces(search, faces);
#endif
}

static void write_lazy_solution(const search_t* search) {
    fprintf(output_file,
            "Solution with %u cycles (genus %u) found in %" PRIu64 " iterations:\n",
            search->target_faces, search->target_genus, search->calls);
    for (face_count_t face = 0; face < search->target_faces; face++) {
        dart_t first = search->face_data[search->face_offsets[face]];
        fprintf(output_file, "%u ", search->graph->input.source[first] + search->graph->input.start);
        for (size_t i = search->face_offsets[face]; i < search->face_offsets[face + 1]; i++) {
            fprintf(output_file, "%u ",
                    search->graph->input.neighbors[search->face_data[i]] + search->graph->input.start);
        }
        fprintf(output_file, "\n");
    }
}

int main(void) {
    const char* filename = getenv("ADJ");
    fail_if(filename == NULL, "Usage: ADJ=adjacency_lists/3-8-cage.txt ./page_low_mem\n");
    uint32_t precomputed_lower_bound = page_setting("GLB", 0, UINT32_MAX);
    if (getenv("QUIET") != NULL) {
        print_progress = false;
    }

    if (print_progress) {
        fprintf(stderr, "Loading adjacency list...\n");
    }
    graph_t graph = graph_load(filename);
    if (print_progress) {
        fprintf(stderr,
                "Read %s: %u vertices, %u edges, girth %u%s.\n",
                filename, graph.input.n, graph.input.m, graph.girth,
                graph.bipartite ? ", bipartite" : "");
    }

    output_file = getenv("STDOUT") != NULL ? stdout : fopen("page.out", "w");
    fail_if(output_file == NULL, "Error opening page.out\n");
    face_count_t input_faces = input_rotation_face_count(&graph);
    uint32_t upper_genus = genus_from_faces(&graph, input_faces);

    fail_if(precomputed_lower_bound > upper_genus,
            "Error: genus lower bound %u exceeds input-rotation upper bound %u\n",
            precomputed_lower_bound, upper_genus);
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
        2 - (int64_t)graph.input.n + graph.input.m - face_upper_bound;
    uint32_t lower_genus =
        lower_numerator <= 0 ? 0 : (uint32_t)((lower_numerator + 1) / 2);
    if (precomputed_lower_bound > lower_genus) {
        lower_genus = precomputed_lower_bound;
    }
    fail_if(lower_genus > upper_genus,
            "Error: genus lower bound %u exceeds input-rotation upper bound %u\n",
            lower_genus, upper_genus);

    search_t search = {0};
    if (lower_genus < upper_genus) search = search_create(&graph);
    uint64_t total_calls = 0;
    if (print_progress) {
        fprintf(stderr, "Beginning lazy genus search between %u and %u.\n",
                lower_genus, upper_genus);
    }
    for (uint32_t genus = lower_genus; genus < upper_genus; genus++) {
        int64_t faces_value = (int64_t)graph.input.m - graph.input.n + 2 - 2 * (int64_t)genus;
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
