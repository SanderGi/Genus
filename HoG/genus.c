// Race PAGE and MultiGenus from one source-level executable.
// SPDX-FileCopyrightText: 2026 Alexander Metzger
// SPDX-License-Identifier: GPL-2.0-only
//
// Interface:
//   ./genus [--graph6|--multicode] [-j jobs] [--page-only] [--multi_genus-only] < graphs
//
// It prints one integer genus per input graph on stdout. Internally it forks a
// PAGE worker and a MultiGenus worker, then keeps the first valid genus and
// stops the other worker.
//
// Compilation: 
//   gcc -O3 -DLONG -ftree-vectorize -funroll-loops -Wall -std=gnu17 -g -pthread -o "./genus" genus.c -lm


#define _POSIX_C_SOURCE 200809L
#ifdef __APPLE__
#define _DARWIN_C_SOURCE
#endif

#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <limits.h>
#include <math.h>
#include <memory.h>
#include <pthread.h>
#include <signal.h>
#include <stdbool.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#ifdef __APPLE__
#include <sys/sysctl.h>
#endif
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

/* PAGE core. Copyright (C) 2026 Alexander Metzger. */


#define PAGE_THREAD_LOCAL _Thread_local

#define VERTEX_DEGREE vertex_degree


#define VERTEX_USE_LIMIT VERTEX_DEGREE
#define MAX_VERTICES 65535
#define MAX_EDGES 65535
#define MAX_CYCLE_LENGTH 65535
#define MAX_CYCLES 4294967295
#define LENGTH_COMPOSITION_WORK_LIMIT 25000000ULL
#define LENGTH_FEASIBILITY_CACHE_LIMIT 10000000ULL
#define SHORTEST_PACKING_CALL_LIMIT 1000000ULL
#define START_BRANCH_THREAD_CAP 8
#define START_BRANCH_PARALLEL_MIN_CYCLES 750


#define AUTOMORPHISM_VERTEX_LIMIT 120
#define AUTOMORPHISM_LIMIT 128
#define AUTOMORPHISM_SEED_CALL_LIMIT 20000ULL
#define AUTOMORPHISM_TOTAL_CALL_LIMIT 200000ULL
#define DIRECTED_EDGE_LOOKUP_EMPTY UINT32_MAX


#define START_CYCLE_LENGTH 3
typedef uint8_t degree_t;
#define PRIdegree_t PRIu8
typedef uint16_t vertex_t;
#define PRIvertex_t PRIu16
#define SCNvertex_t SCNu16
typedef uint16_t edge_t;
#define PRIedge_t PRIu16
#define SCNedge_t SCNu16
typedef vertex_t cycle_length_t;  
#define PRIcycle_length_t PRIvertex_t
#define SCNcycle_length_t SCNvertex_t
typedef uint32_t cycle_index_t;
#define PRIcycle_index_t PRIu32
#define SCNcycle_index_t SCNu32
typedef vertex_t* adj_t;
typedef vertex_t* cycles_t;
typedef cycle_index_t* cbv_t;
typedef cycle_index_t* cbe_t;
typedef pthread_mutex_t page_mutex_t;
typedef pthread_t page_thread_t;
typedef void* (*page_thread_start_t)(void*);
#define PAGE_MUTEX_INITIALIZER PTHREAD_MUTEX_INITIALIZER
#define PAGE_THREAD_RETURN void*
#define PAGE_THREAD_RESULT NULL
typedef enum {
    PACKING_IMPOSSIBLE,
    PACKING_FOUND,
    PACKING_UNKNOWN
} packing_result_t;
typedef struct {
    bool* cycle_length_available;
    cycle_length_t max_cycle_length;
    cycle_length_t shortest_length;
    cycle_length_t required_length;
    int8_t* cache_without_required;
    int8_t* cache_with_required;
    cycle_index_t cache_width;
} length_feasibility_t;
typedef struct {
    vertex_t num_vertices;
    cycle_index_t count;
    cycle_index_t capacity;
    vertex_t* maps;
} automorphism_list_t;
typedef struct {
    vertex_t num_vertices;
    adj_t adjacency_list;
    vertex_t* distances;
    uint64_t* vertex_signatures;
    vertex_t* map;
    vertex_t* inverse_map;
    vertex_t* result;
    uint64_t calls;
    uint64_t call_limit;
} automorphism_search_t;
typedef struct {
    vertex_t num_vertices;
    edge_t num_edges;
    adj_t adjacency_list;
    cycle_length_t max_cycle_length;
    cycle_index_t num_cycles;
    cycles_t cycles;
    cycle_index_t max_cycles_per_vertex;
    cbv_t cycles_by_vertex;
    cycle_index_t max_cycles_per_edge;
    cbe_t cycles_by_edge;
    cycle_index_t* start_cycles;
    cycle_index_t num_start_cycles;
    cycle_index_t* start_cycle_order;
    cycle_index_t initial_cycles_to_use;
    cycle_index_t max_used_cycles;
    cycle_index_t initial_max_fit;
    bool* initial_directed_edge_remaining;
    length_feasibility_t length_feasibility_template;
    uint64_t length_cache_entries;
    bool require_max_cycle_if_start_is_shorter;
    page_mutex_t mutex;
    cycle_index_t next_start_index;
    cycle_index_t completed_start_cycles;
    cycle_index_t best_max_fit;
    uint64_t total_search_calls;
    bool solution_found;
    bool* solution_used_cycles;
    atomic_bool stop_requested;
} start_branch_search_t;


#define assert(condition, ...)        \
    if (!(condition)) {               \
        fprintf(stderr, __VA_ARGS__); \
        exit(1);                      \
    }

int page_mutex_init(page_mutex_t* mutex) {
    return pthread_mutex_init(mutex, NULL);
}

void page_mutex_lock(page_mutex_t* mutex) {
    pthread_mutex_lock(mutex);
}

void page_mutex_unlock(page_mutex_t* mutex) {
    pthread_mutex_unlock(mutex);
}

void page_mutex_destroy(page_mutex_t* mutex) {
    pthread_mutex_destroy(mutex);
}

int page_thread_create(page_thread_t* thread, page_thread_start_t start, void* arg) {
    return pthread_create(thread, NULL, start, arg);
}

int page_thread_join(page_thread_t thread) {
    return pthread_join(thread, NULL);
}


static FILE* output_file = NULL;
static degree_t vertex_degree = 3;
static cycle_length_t smallest_cycle_length;
static unsigned page_thread_override = 0;
static bool cubic_exact_cover_mode = false;
static degree_t* vertex_degrees = NULL;
static degree_t* initial_vertex_uses = NULL;
static adj_t full_adjacency_list = NULL;
static cycle_index_t num_directed_edges = 0;
static cycle_index_t* directed_edge_ids = NULL;
static uint32_t* directed_edge_lookup_keys = NULL;
static cycle_index_t* directed_edge_lookup_ids = NULL;
static cycle_index_t directed_edge_lookup_capacity = 0;
static automorphism_list_t graph_automorphisms = {0, 0, 0, NULL};
static PAGE_THREAD_LOCAL cycle_index_t num_edges_remaining = 0;
static PAGE_THREAD_LOCAL bool* directed_edge_remaining = NULL;
static PAGE_THREAD_LOCAL bool* transitions_used = NULL;
static PAGE_THREAD_LOCAL size_t transitions_used_size = 0;
static PAGE_THREAD_LOCAL cycle_index_t* cycle_edge_conflicts = NULL;
static PAGE_THREAD_LOCAL vertex_t* rotation_next = NULL;
static PAGE_THREAD_LOCAL vertex_t* rotation_prev = NULL;
static PAGE_THREAD_LOCAL degree_t* rotation_pair_count = NULL;
static PAGE_THREAD_LOCAL size_t rotation_state_size = 0;
static PAGE_THREAD_LOCAL atomic_bool* search_stop_requested = NULL;


vertex_t* adj_get_neighbors(adj_t adjacency_list, vertex_t vertex);
void graph_free(adj_t adjacency_list);
bool graph_has_edge(adj_t adjacency_list, vertex_t start_vertex, vertex_t end_vertex);
uint32_t directed_edge_key(vertex_t start_vertex, vertex_t end_vertex);
cycle_index_t directed_edge_lookup_slot(uint32_t key, bool allow_empty);
void directed_edge_lookup_insert(vertex_t start_vertex, vertex_t end_vertex,
                                 cycle_index_t edge_id);
bool adj_try_edge_id(adj_t adjacency_list, vertex_t start_vertex, vertex_t end_vertex,
                     cycle_index_t* edge_id);
cycle_index_t adj_edge_id(adj_t adjacency_list, vertex_t start_vertex, vertex_t end_vertex);
bool adj_slot_has_edge(vertex_t start_vertex, degree_t neighbor_index);
void adj_remove_edge(adj_t adjacency_list, vertex_t start_vertex, vertex_t end_vertex);
void adj_undo_remove_edge(adj_t adjacency_list, vertex_t start_vertex, vertex_t end_vertex);

cycles_t cycle_generate(adj_t adjacency_list, vertex_t num_vertices, cycle_length_t cycle_length,
                        cycle_index_t* num_cycles);
vertex_t* cycle_get(cycles_t cycles, cycle_length_t max_cycle_length, cycle_index_t cycle_index,
                    cycle_length_t* cycle_length);

cycle_index_t* cbv_generate(vertex_t num_vertices, cycles_t cycles, cycle_index_t num_cycles,
                            cycle_length_t cycle_length, cycle_index_t* max_cycles_per_vertex);
cycle_index_t* cbv_get_cycle_indices(cbv_t cycles_by_vertex, cycle_index_t max_cycles_per_vertex,
                                     vertex_t vertex, cycle_index_t* num_cycles);
cycle_index_t* cbe_generate(vertex_t num_vertices, cycles_t cycles, cycle_index_t num_cycles,
                            cycle_length_t max_cycle_length, cycle_index_t* max_cycles_per_edge);
cycle_index_t* cbe_get_cycle_indices(cbe_t cycles_by_edge, cycle_index_t max_cycles_per_edge,
                                     vertex_t start_vertex, vertex_t end_vertex,
                                     cycle_index_t* num_cycles);

void show_solution(cycle_index_t genus_lower_bound, cycle_index_t genus_lower_bound_implied_fit,
                   uint64_t num_search_calls, cycle_index_t num_cycles, bool* used_cycles,
                   cycles_t cycles, cycle_length_t max_cycle_length);

degree_t adj_neighbor_index(adj_t adjacency_list, vertex_t vertex, vertex_t neighbor);
bool cycle_vertex_uses_fit(vertex_t* cycle, cycle_length_t cycle_length,
                           degree_t* vertex_uses);
void automorphism_list_free(automorphism_list_t* automorphisms);
void automorphism_generate(vertex_t num_vertices, adj_t adjacency_list,
                           automorphism_list_t* automorphisms);
cycle_index_t* start_cycles_prune_by_symmetry(cycles_t cycles,
                                              cycle_length_t max_cycle_length,
                                              cycle_index_t num_cycles,
                                              cbe_t cycles_by_edge,
                                              cycle_index_t max_cycles_per_edge,
                                              cycle_index_t* raw_start_cycles,
                                              cycle_index_t raw_start_count,
                                              cycle_index_t* pruned_start_count);
void cycle_edge_conflicts_init(cycle_index_t num_cycles);
void cycle_edge_conflicts_clear(cycle_index_t num_cycles);
void cycle_edge_conflicts_free(void);
bool candidate_length_possible(cycle_length_t cycle_length,
                               cycle_index_t cycles_to_use,
                               length_feasibility_t* length_feasibility,
                               cycle_index_t required_cycles_to_use);
void cycle_set_edge_conflicts(vertex_t* cycle, cycle_length_t cycle_length,
                              cycle_index_t max_cycles_per_edge, cbe_t cycles_by_edge,
                              bool used);
bool cycle_search_candidate_usable(bool* used_cycles, degree_t* vertex_uses,
                                   adj_t adjacency_list, cycles_t cycles,
                                   cycle_length_t max_cycle_length,
                                   cycle_index_t cycle_index,
                                   cycle_index_t* start_cycle_order,
                                   cycle_index_t current_start_cycle_order,
                                   cycle_index_t cycles_to_use,
                                   length_feasibility_t* length_feasibility,
                                   cycle_index_t required_cycles_to_use,
                                   bool check_row_constraints,
                                   bool check_transitions,
                                   cycle_length_t* cycle_length_out,
                                   vertex_t** cycle_out,
                                   cycle_index_t* next_required_cycles_to_use);
bool cycle_transitions_good(vertex_t* cycle, cycle_length_t cycle_length);
void cycle_set_transitions(vertex_t* cycle, cycle_length_t cycle_length, bool used);
unsigned get_start_branch_thread_count(cycle_index_t num_start_cycles,
                                       cycle_index_t num_cycles);
void precompute_start_cycle_order(cycle_index_t* start_cycle_order,
                                  cycle_index_t* start_cycles,
                                  cycle_index_t num_start_cycles);
bool search_start_cycles_parallel(start_branch_search_t* context,
                                  unsigned num_threads);
PAGE_THREAD_RETURN start_branch_worker(void* arg);
void rotation_state_init(vertex_t num_vertices);
void rotation_state_clear(vertex_t num_vertices);
void rotation_state_free(void);
bool rotation_transition_add(vertex_t center, degree_t prev_index, degree_t next_index);
void rotation_transition_remove(vertex_t center, degree_t prev_index, degree_t next_index);
bool cycle_try_add_rotation_system(vertex_t* cycle, cycle_length_t cycle_length);
void cycle_remove_rotation_system(vertex_t* cycle, cycle_length_t cycle_length);
cycle_index_t choose_start_edge(vertex_t num_vertices, adj_t adjacency_list,
                                cycle_index_t max_cycles_per_edge, cbe_t cycles_by_edge,
                                vertex_t* start_vertex, vertex_t* end_vertex);
bool path_has_reverse_transition(vertex_t* path, cycle_length_t path_length, vertex_t prev_vertex,
                                 vertex_t center_vertex, vertex_t next_vertex);
cycle_index_t genus_lower_bound_from_fit_upper_bound(cycle_index_t fit_upper_bound,
                                                     vertex_t num_vertices, edge_t num_edges);
bool length_composition_possible(cycle_index_t total_length, cycle_index_t cycles_to_use,
                                 bool* cycle_length_available,
                                 cycle_length_t max_cycle_length,
                                 cycle_length_t shortest_length,
                                 cycle_length_t required_length,
                                 cycle_index_t* min_shortest_cycles);
bool cached_length_composition_possible(length_feasibility_t* length_feasibility,
                                        cycle_index_t total_length,
                                        cycle_index_t cycles_to_use,
                                        cycle_index_t required_cycles_to_use);
cycle_index_t max_possible_fit_with_shortest_bound(edge_t num_edges,
                                                   cycle_length_t shortest_length,
                                                   cycle_length_t second_shortest_length,
                                                   cycle_index_t max_shortest_cycles,
                                                   cycle_length_t required_length);
packing_result_t can_pack_shortest_cycles(vertex_t num_vertices, edge_t num_edges,
                                          adj_t adjacency_list, cycles_t cycles,
                                          cycle_length_t max_cycle_length,
                                          cycle_length_t shortest_cycle_length,
                                          cycle_index_t num_shortest_cycles,
                                          cycle_index_t target_shortest_cycles,
                                          uint64_t* num_packing_calls);
bool search(cycle_index_t cycles_to_use,                    
            cycle_index_t max_used_cycles,                  
            bool* used_cycles,                              
            degree_t* vertex_uses, cycle_index_t* max_fit,  
            uint64_t* num_search_calls,                     
            vertex_t num_vertices, edge_t num_edges, adj_t adjacency_list,
            cycle_length_t max_cycle_length, cycle_index_t num_cycles, cycles_t cycles,
            cycle_index_t max_cycles_per_vertex, cbv_t cycles_by_vertex,
            cycle_index_t max_cycles_per_edge, cbe_t cycles_by_edge,
            cycle_index_t* start_cycle_order, cycle_index_t current_start_cycle_order,
            length_feasibility_t* length_feasibility,
            cycle_index_t required_cycles_to_use);

cycle_index_t implied_max_fit_for_genus(cycle_index_t genus, vertex_t num_vertices,
                                        edge_t num_edges) {
    return num_edges - num_vertices + 2 - 2 * genus;
}

cycle_index_t implied_max_genus_for_fit(cycle_index_t fit, vertex_t num_vertices,
                                        edge_t num_edges) {
    int64_t val = 1 - ((int64_t)fit - num_edges + num_vertices) / 2;
    return val < 0 ? 0 : val;
}

cycle_index_t genus_lower_bound_from_fit_upper_bound(cycle_index_t fit_upper_bound,
                                                     vertex_t num_vertices, edge_t num_edges) {
    int64_t numerator = (int64_t)num_edges - num_vertices + 2 - fit_upper_bound;
    if (numerator <= 0) {
        return 0;
    }
    return (cycle_index_t)((numerator + 1) / 2);
}

cycle_length_t gcd_cycle_length(cycle_length_t a, cycle_length_t b) {
    while (b != 0) {
        cycle_length_t r = a % b;
        a = b;
        b = r;
    }
    return a;
}

cycle_index_t ceil_div_u64(uint64_t numerator, uint64_t denominator) {
    return (cycle_index_t)((numerator + denominator - 1) / denominator);
}

bool length_composition_possible(cycle_index_t total_length, cycle_index_t cycles_to_use,
                                 bool* cycle_length_available,
                                 cycle_length_t max_cycle_length,
                                 cycle_length_t shortest_length,
                                 cycle_length_t required_length,
                                 cycle_index_t* min_shortest_cycles) {
    *min_shortest_cycles = 0;
    if (cycles_to_use == 0) {
        return total_length == 0;
    }
    if (required_length != 0 &&
        (required_length > max_cycle_length || !cycle_length_available[required_length])) {
        return false;
    }

    cycle_index_t num_available_lengths = 0;
    cycle_length_t min_available_length = 0;
    cycle_length_t max_available_length = 0;
    cycle_length_t second_available_length = 0;
    cycle_length_t length_gcd = 0;
    for (cycle_length_t length = START_CYCLE_LENGTH; length <= max_cycle_length; length++) {
        if (!cycle_length_available[length]) {
            continue;
        }
        num_available_lengths++;
        if (min_available_length == 0) {
            min_available_length = length;
        }
        max_available_length = length;
        if (length > shortest_length && second_available_length == 0) {
            second_available_length = length;
        }
        length_gcd = gcd_cycle_length(length_gcd, length - min_available_length);
    }
    if (num_available_lengths == 0) {
        return false;
    }

    cycle_index_t start_count = required_length == 0 ? 0 : 1;
    cycle_index_t start_sum = required_length;
    cycle_index_t start_shortest = required_length == shortest_length ? 1 : 0;
    if (start_count > cycles_to_use || start_sum > total_length) {
        return false;
    }

    uint64_t work =
        (uint64_t)(cycles_to_use - start_count) * (total_length + 1) * num_available_lengths;
    if (work <= LENGTH_COMPOSITION_WORK_LIMIT) {
        cycle_index_t* dp = (cycle_index_t*)malloc((total_length + 1) * sizeof(cycle_index_t));
        cycle_index_t* next =
            (cycle_index_t*)malloc((total_length + 1) * sizeof(cycle_index_t));
        assert(dp != NULL && next != NULL,
               "Error allocating memory for the length composition DP\n");
        memset(dp, 0xff, (total_length + 1) * sizeof(cycle_index_t));
        dp[start_sum] = start_shortest;

        for (cycle_index_t count = start_count; count < cycles_to_use; count++) {
            memset(next, 0xff, (total_length + 1) * sizeof(cycle_index_t));
            for (cycle_index_t sum = 0; sum <= total_length; sum++) {
                if (dp[sum] == MAX_CYCLES) {
                    continue;
                }
                for (cycle_length_t length = START_CYCLE_LENGTH; length <= max_cycle_length;
                     length++) {
                    if (!cycle_length_available[length] || sum + length > total_length) {
                        continue;
                    }
                    cycle_index_t shortest_count =
                        dp[sum] + (length == shortest_length ? 1 : 0);
                    if (shortest_count < next[sum + length]) {
                        next[sum + length] = shortest_count;
                    }
                }
            }
            cycle_index_t* tmp = dp;
            dp = next;
            next = tmp;
        }

        bool possible = dp[total_length] != MAX_CYCLES;
        if (possible) {
            *min_shortest_cycles = dp[total_length];
        }
        free(dp);
        free(next);
        return possible;
    }

    cycle_index_t remaining_count = cycles_to_use - start_count;
    cycle_index_t remaining_sum = total_length - start_sum;
    if ((uint64_t)remaining_count * min_available_length > remaining_sum ||
        (uint64_t)remaining_count * max_available_length < remaining_sum) {
        return false;
    }
    if (length_gcd == 0) {
        if (remaining_sum != remaining_count * min_available_length) {
            return false;
        }
    } else if ((remaining_sum - remaining_count * min_available_length) % length_gcd != 0) {
        return false;
    }

    cycle_index_t lower_shortest_count = start_shortest;
    if (remaining_count > 0) {
        if (second_available_length == 0) {
            if (remaining_sum != remaining_count * shortest_length) {
                return false;
            }
            lower_shortest_count += remaining_count;
        } else {
            uint64_t sum_without_shortest = (uint64_t)remaining_count * second_available_length;
            if (sum_without_shortest > remaining_sum) {
                lower_shortest_count +=
                    ceil_div_u64(sum_without_shortest - remaining_sum,
                                 second_available_length - shortest_length);
            }
        }
    }
    *min_shortest_cycles = lower_shortest_count;
    return true;
}

bool cached_length_composition_possible(length_feasibility_t* length_feasibility,
                                        cycle_index_t total_length,
                                        cycle_index_t cycles_to_use,
                                        cycle_index_t required_cycles_to_use) {
    if (length_feasibility == NULL || length_feasibility->cache_without_required == NULL) {
        return true;
    }
    if (required_cycles_to_use > 1 || total_length >= length_feasibility->cache_width) {
        return true;
    }

    int8_t* cache = required_cycles_to_use == 0
                        ? length_feasibility->cache_without_required
                        : length_feasibility->cache_with_required;
    cycle_index_t cache_index = cycles_to_use * length_feasibility->cache_width + total_length;
    if (cache[cache_index] != -1) {
        return cache[cache_index] == 1;
    }

    cycle_index_t min_shortest_cycles;
    bool possible = length_composition_possible(
        total_length, cycles_to_use, length_feasibility->cycle_length_available,
        length_feasibility->max_cycle_length, length_feasibility->shortest_length,
        required_cycles_to_use == 0 ? 0 : length_feasibility->required_length,
        &min_shortest_cycles);
    cache[cache_index] = possible ? 1 : 0;
    return possible;
}

cycle_index_t max_possible_fit_with_shortest_bound(edge_t num_edges,
                                                   cycle_length_t shortest_length,
                                                   cycle_length_t second_shortest_length,
                                                   cycle_index_t max_shortest_cycles,
                                                   cycle_length_t required_length) {
    cycle_index_t total_length = 2 * num_edges;
    if (shortest_length == 0 || required_length > total_length) {
        return 0;
    }

    cycle_length_t non_shortest_length = second_shortest_length;
    if (non_shortest_length == 0 || required_length < non_shortest_length) {
        non_shortest_length = required_length;
    }

    cycle_index_t remaining_length = total_length - required_length;
    cycle_index_t shortest_cycles_to_use = remaining_length / shortest_length;
    if (shortest_cycles_to_use > max_shortest_cycles) {
        shortest_cycles_to_use = max_shortest_cycles;
    }
    remaining_length -= shortest_cycles_to_use * shortest_length;

    return 1 + shortest_cycles_to_use + remaining_length / non_shortest_length;
}

typedef struct {
    vertex_t num_vertices;
    edge_t num_edges;
    adj_t adjacency_list;
    cycles_t cycles;
    cycle_length_t max_cycle_length;
    cycle_length_t shortest_cycle_length;
    cycle_index_t num_shortest_cycles;
    cycle_index_t directed_edges;
    cycle_index_t edge_cycle_row_width;
    cycle_index_t* cycles_by_edge;
    cycle_index_t* cycle_edge_ids;
    bool* edge_used;
    bool* edge_skipped;
    degree_t* vertex_uses;
    uint64_t calls;
    uint64_t call_limit;
} shortest_packing_state_t;

cycle_index_t directed_edge_id(adj_t adjacency_list, cycle_index_t* edge_slot_to_id,
                               vertex_t start_vertex, vertex_t end_vertex) {
    vertex_t* neighbors = adj_get_neighbors(adjacency_list, start_vertex);
    for (degree_t i = 0; i < VERTEX_DEGREE; i++) {
        if (neighbors[i] == end_vertex) {
            return edge_slot_to_id[start_vertex * VERTEX_DEGREE + i];
        }
    }
    assert(false, "Error finding directed edge %" PRIvertex_t " -> %" PRIvertex_t "\n",
           start_vertex, end_vertex);
    return MAX_CYCLES;
}

bool shortest_packing_cycle_usable(shortest_packing_state_t* state, cycle_index_t cycle_index) {
    cycle_index_t edge_offset = cycle_index * state->shortest_cycle_length;
    for (cycle_length_t i = 0; i < state->shortest_cycle_length; i++) {
        cycle_index_t edge_id = state->cycle_edge_ids[edge_offset + i];
        if (state->edge_used[edge_id] || state->edge_skipped[edge_id]) {
            return false;
        }
    }

    cycle_length_t cycle_length;
    vertex_t* cycle = cycle_get(state->cycles, state->max_cycle_length, cycle_index,
                                &cycle_length);
    assert(cycle_length == state->shortest_cycle_length,
           "Error: shortest packing got a non-shortest cycle\n");
    
    for (cycle_length_t i = 0; i < cycle_length; i++) {
        if (state->vertex_uses[cycle[i]] >= vertex_degrees[cycle[i]]) {
            return false;
        }
    }
    return true;
}

void shortest_packing_set_cycle(shortest_packing_state_t* state, cycle_index_t cycle_index,
                                bool used) {
    cycle_index_t edge_offset = cycle_index * state->shortest_cycle_length;
    for (cycle_length_t i = 0; i < state->shortest_cycle_length; i++) {
        state->edge_used[state->cycle_edge_ids[edge_offset + i]] = used;
    }

    cycle_length_t cycle_length;
    vertex_t* cycle = cycle_get(state->cycles, state->max_cycle_length, cycle_index,
                                &cycle_length);
    for (cycle_length_t i = 0; i < cycle_length; i++) {
        if (used) {
            state->vertex_uses[cycle[i]]++;
        } else {
            state->vertex_uses[cycle[i]]--;
        }
    }
}

packing_result_t shortest_packing_search(shortest_packing_state_t* state,
                                         cycle_index_t cycles_left, cycle_index_t skips_left,
                                         cycle_index_t used_edges,
                                         cycle_index_t skipped_edges) {
    state->calls++;
    if (state->calls > state->call_limit) {
        return PACKING_UNKNOWN;
    }
    if (cycles_left == 0) {
        return PACKING_FOUND;
    }
    if ((uint64_t)cycles_left * state->shortest_cycle_length >
        (uint64_t)state->directed_edges - used_edges - skipped_edges) {
        return PACKING_IMPOSSIBLE;
    }

    uint64_t remaining_vertex_capacity = 0;
    for (vertex_t i = 0; i < state->num_vertices; i++) {
        remaining_vertex_capacity += vertex_degrees[i] - state->vertex_uses[i];
    }
    if ((uint64_t)cycles_left * state->shortest_cycle_length > remaining_vertex_capacity) {
        return PACKING_IMPOSSIBLE;
    }

    cycle_index_t chosen_edge = MAX_CYCLES;
    cycle_index_t min_cycle_options = MAX_CYCLES;
    for (cycle_index_t edge_id = 0; edge_id < state->directed_edges; edge_id++) {
        if (state->edge_used[edge_id] || state->edge_skipped[edge_id]) {
            continue;
        }

        cycle_index_t usable_cycles = 0;
        cycle_index_t* row =
            &state->cycles_by_edge[edge_id * (state->edge_cycle_row_width + 1)];
        for (cycle_index_t i = 0; i < row[0]; i++) {
            if (shortest_packing_cycle_usable(state, row[i + 1])) {
                usable_cycles++;
            }
        }

        if (usable_cycles < min_cycle_options) {
            chosen_edge = edge_id;
            min_cycle_options = usable_cycles;
            if (min_cycle_options == 0) {
                break;
            }
        }
    }

    if (chosen_edge == MAX_CYCLES) {
        return PACKING_IMPOSSIBLE;
    }
    if (min_cycle_options == 0 && skips_left == 0) {
        return PACKING_IMPOSSIBLE;
    }

    packing_result_t result = PACKING_IMPOSSIBLE;
    cycle_index_t* row =
        &state->cycles_by_edge[chosen_edge * (state->edge_cycle_row_width + 1)];
    for (cycle_index_t i = 0; i < row[0]; i++) {
        cycle_index_t cycle_index = row[i + 1];
        if (!shortest_packing_cycle_usable(state, cycle_index)) {
            continue;
        }

        shortest_packing_set_cycle(state, cycle_index, true);
        packing_result_t child_result =
            shortest_packing_search(state, cycles_left - 1, skips_left,
                                    used_edges + state->shortest_cycle_length, skipped_edges);
        shortest_packing_set_cycle(state, cycle_index, false);

        if (child_result == PACKING_FOUND) {
            return PACKING_FOUND;
        }
        if (child_result == PACKING_UNKNOWN) {
            result = PACKING_UNKNOWN;
        }
    }

    if (skips_left > 0) {
        state->edge_skipped[chosen_edge] = true;
        packing_result_t child_result =
            shortest_packing_search(state, cycles_left, skips_left - 1, used_edges,
                                    skipped_edges + 1);
        state->edge_skipped[chosen_edge] = false;
        if (child_result == PACKING_FOUND) {
            return PACKING_FOUND;
        }
        if (child_result == PACKING_UNKNOWN) {
            result = PACKING_UNKNOWN;
        }
    }

    return result;
}

packing_result_t can_pack_shortest_cycles(vertex_t num_vertices, edge_t num_edges,
                                          adj_t adjacency_list, cycles_t cycles,
                                          cycle_length_t max_cycle_length,
                                          cycle_length_t shortest_cycle_length,
                                          cycle_index_t num_shortest_cycles,
                                          cycle_index_t target_shortest_cycles,
                                          uint64_t* num_packing_calls) {
    *num_packing_calls = 0;
    if (target_shortest_cycles == 0) {
        return PACKING_FOUND;
    }
    if (target_shortest_cycles > num_shortest_cycles ||
        (uint64_t)target_shortest_cycles * shortest_cycle_length > 2 * num_edges) {
        return PACKING_IMPOSSIBLE;
    }

    cycle_index_t edge_slots = num_vertices * VERTEX_DEGREE;
    cycle_index_t* edge_slot_to_id = (cycle_index_t*)malloc(edge_slots * sizeof(cycle_index_t));
    assert(edge_slot_to_id != NULL, "Error allocating memory for directed edge ids\n");
    for (cycle_index_t i = 0; i < edge_slots; i++) {
        edge_slot_to_id[i] = MAX_CYCLES;
    }

    cycle_index_t directed_edges = 0;
    for (vertex_t vertex = 0; vertex < num_vertices; vertex++) {
        vertex_t* neighbors = adj_get_neighbors(adjacency_list, vertex);
        for (degree_t i = 0; i < VERTEX_DEGREE; i++) {
            if (neighbors[i] == MAX_VERTICES) {
                continue;
            }
            edge_slot_to_id[vertex * VERTEX_DEGREE + i] = directed_edges++;
        }
    }
    assert(directed_edges == 2 * num_edges,
           "Error: found %" PRIcycle_index_t " directed edges but expected %" PRIedge_t "\n",
           directed_edges, 2 * num_edges);

    cycle_index_t* edge_cycle_counts =
        (cycle_index_t*)calloc(directed_edges, sizeof(cycle_index_t));
    assert(edge_cycle_counts != NULL,
           "Error allocating memory for shortest cycles by edge counts\n");
    cycle_index_t* cycle_edge_ids = (cycle_index_t*)malloc(
        (uint64_t)num_shortest_cycles * shortest_cycle_length * sizeof(cycle_index_t));
    assert(cycle_edge_ids != NULL, "Error allocating memory for shortest cycle edge ids\n");

    for (cycle_index_t cycle_index = 0; cycle_index < num_shortest_cycles; cycle_index++) {
        cycle_length_t cycle_length;
        vertex_t* cycle = cycle_get(cycles, max_cycle_length, cycle_index, &cycle_length);
        assert(cycle_length == shortest_cycle_length,
               "Error: shortest cycle prefix contains a longer cycle\n");
        for (cycle_length_t i = 0; i < cycle_length; i++) {
            cycle_index_t edge_id =
                directed_edge_id(adjacency_list, edge_slot_to_id, cycle[i], cycle[i + 1]);
            cycle_edge_ids[cycle_index * shortest_cycle_length + i] = edge_id;
            edge_cycle_counts[edge_id]++;
        }
    }

    cycle_index_t edge_cycle_row_width = 0;
    for (cycle_index_t edge_id = 0; edge_id < directed_edges; edge_id++) {
        if (edge_cycle_counts[edge_id] > edge_cycle_row_width) {
            edge_cycle_row_width = edge_cycle_counts[edge_id];
        }
    }

    cycle_index_t* cycles_by_edge = (cycle_index_t*)malloc(
        directed_edges * (edge_cycle_row_width + 1) * sizeof(cycle_index_t));
    cycle_index_t* edge_cycle_fill =
        (cycle_index_t*)calloc(directed_edges, sizeof(cycle_index_t));
    assert(cycles_by_edge != NULL && edge_cycle_fill != NULL,
           "Error allocating memory for shortest cycles by edge\n");
    for (cycle_index_t edge_id = 0; edge_id < directed_edges; edge_id++) {
        cycles_by_edge[edge_id * (edge_cycle_row_width + 1)] = edge_cycle_counts[edge_id];
    }
    for (cycle_index_t cycle_index = 0; cycle_index < num_shortest_cycles; cycle_index++) {
        for (cycle_length_t i = 0; i < shortest_cycle_length; i++) {
            cycle_index_t edge_id = cycle_edge_ids[cycle_index * shortest_cycle_length + i];
            cycle_index_t fill = edge_cycle_fill[edge_id]++;
            cycles_by_edge[edge_id * (edge_cycle_row_width + 1) + fill + 1] = cycle_index;
        }
    }

    bool* edge_used = (bool*)calloc(directed_edges, sizeof(bool));
    bool* edge_skipped = (bool*)calloc(directed_edges, sizeof(bool));
    degree_t* vertex_uses = (degree_t*)calloc(num_vertices, sizeof(degree_t));
    assert(edge_used != NULL && edge_skipped != NULL && vertex_uses != NULL,
           "Error allocating memory for shortest packing state\n");

    shortest_packing_state_t state = {
        .num_vertices = num_vertices,
        .num_edges = num_edges,
        .adjacency_list = adjacency_list,
        .cycles = cycles,
        .max_cycle_length = max_cycle_length,
        .shortest_cycle_length = shortest_cycle_length,
        .num_shortest_cycles = num_shortest_cycles,
        .directed_edges = directed_edges,
        .edge_cycle_row_width = edge_cycle_row_width,
        .cycles_by_edge = cycles_by_edge,
        .cycle_edge_ids = cycle_edge_ids,
        .edge_used = edge_used,
        .edge_skipped = edge_skipped,
        .vertex_uses = vertex_uses,
        .calls = 0,
        .call_limit = SHORTEST_PACKING_CALL_LIMIT,
    };

    cycle_index_t skips_left =
        directed_edges - target_shortest_cycles * shortest_cycle_length;
    packing_result_t result =
        shortest_packing_search(&state, target_shortest_cycles, skips_left, 0, 0);
    *num_packing_calls = state.calls;

    free(edge_slot_to_id);
    free(edge_cycle_counts);
    free(cycle_edge_ids);
    free(cycles_by_edge);
    free(edge_cycle_fill);
    free(edge_used);
    free(edge_skipped);
    free(vertex_uses);
    return result;
}

static int ph_page_run(adj_t adjacency_list, vertex_t num_vertices, edge_t num_edges,
                       degree_t degree, unsigned page_threads) {
    vertex_degree = degree;
    page_thread_override = page_threads;
    output_file = stdout;

    initial_vertex_uses = (degree_t*)malloc(num_vertices * sizeof(degree_t));
    assert(initial_vertex_uses != NULL,
           "Error allocating memory for the initial vertex use counts\n");
    for (vertex_t i = 0; i < num_vertices; i++) {
        initial_vertex_uses[i] = 0;
        vertex_t* neighbors = adj_get_neighbors(adjacency_list, i);
        for (degree_t j = 0; j < VERTEX_DEGREE; j++) {
            if (neighbors[j] == MAX_VERTICES) {
                initial_vertex_uses[i]++;
            }
        }
    }
    cycle_index_t genus_lower_bound =
        genus_lower_bound_from_fit_upper_bound(2 * num_edges / START_CYCLE_LENGTH,
                                               num_vertices, num_edges);
    cycle_index_t genus_lower_bound_implied_fit =
        implied_max_fit_for_genus(genus_lower_bound, num_vertices, num_edges);
    cycle_index_t max_fit = (2 * num_edges + num_vertices - 1) / num_vertices;
    cycle_index_t genus_upper_bound = implied_max_genus_for_fit(max_fit, num_vertices, num_edges);

    if (genus_lower_bound == genus_upper_bound) {
        
        fprintf(output_file, "%" PRIcycle_index_t "\n", genus_lower_bound);
        fclose(output_file);
        graph_free(adjacency_list);
        return 0;
    }

    uint64_t num_search_calls = 0;
    smallest_cycle_length = num_vertices;
    cycle_length_t second_smallest_cycle_length = 0;
    cycle_index_t num_shortest_cycles = 0;
    cycle_index_t max_shortest_cycles = MAX_CYCLES;
    cycle_index_t verified_packable_shortest_cycles = 0;
    cycle_length_t max_search_cycle_length = num_edges;
    bool* cycle_length_available =
        (bool*)calloc(max_search_cycle_length + 1, sizeof(bool));
    assert(cycle_length_available != NULL,
           "Error allocating memory for the cycle length availability flags\n");
    cycles_t cycles = NULL;
    cycle_index_t num_cycles = 0;
    cycle_length_t cycles_max_cycle_length = 0;
    cycle_index_t current_length_cycle_count = 0;
    cycle_index_t last_searched_fit = MAX_CYCLES;
    for (cycle_length_t cur_max_cycle_length = START_CYCLE_LENGTH;
         cur_max_cycle_length <= max_search_cycle_length; cur_max_cycle_length++) {
        bool reusing_current_length =
            cur_max_cycle_length == cycles_max_cycle_length &&
            current_length_cycle_count > 0;
        cycle_index_t num_new_cycles = current_length_cycle_count;
        if (reusing_current_length) {
        } else {

            cycles_t new_cycles =
                cycle_generate(adjacency_list, num_vertices, cur_max_cycle_length,
                               &num_new_cycles);
            current_length_cycle_count = num_new_cycles;
            num_cycles += num_new_cycles;

            if (num_new_cycles == 0) {
                
                free(new_cycles);
                continue;
            }
            assert(new_cycles != NULL, "Error: new cycles is NULL but there are new cycles\n");

            cycle_length_available[cur_max_cycle_length] = true;

            
            if (num_shortest_cycles == 0 || cur_max_cycle_length < smallest_cycle_length) {
                smallest_cycle_length = cur_max_cycle_length;
                num_shortest_cycles = num_new_cycles;
                max_shortest_cycles = num_new_cycles < 2 * num_edges / smallest_cycle_length
                                          ? num_new_cycles
                                          : 2 * num_edges / smallest_cycle_length;
            } else if (cur_max_cycle_length > smallest_cycle_length &&
                       second_smallest_cycle_length == 0) {
                second_smallest_cycle_length = cur_max_cycle_length;
            }

            
            
            cycle_index_t genus_lower_bound_from_smallest_cycle_length =
                genus_lower_bound_from_fit_upper_bound(2 * num_edges / smallest_cycle_length,
                                                       num_vertices, num_edges);
            if (genus_lower_bound_from_smallest_cycle_length > genus_lower_bound) {
                genus_lower_bound = genus_lower_bound_from_smallest_cycle_length;
                genus_lower_bound_implied_fit =
                    implied_max_fit_for_genus(genus_lower_bound, num_vertices, num_edges);
            }

            
            if (cycles == NULL) {
                cycles = new_cycles;
                cycles_max_cycle_length = cur_max_cycle_length;
            } else {
                cycles_t combined =
                    (cycles_t)malloc(num_cycles * (cur_max_cycle_length + 2) * sizeof(vertex_t));
                assert(combined != NULL, "Error allocating memory for the combined cycles\n");
                for (cycle_index_t i = 0; i < num_cycles - num_new_cycles; i++) {
                    for (cycle_length_t j = 0; j < cycles_max_cycle_length + 2; j++) {
                        combined[i * (cur_max_cycle_length + 2) + j] =
                            cycles[i * (cycles_max_cycle_length + 2) + j];
                    }
                }
                for (cycle_index_t i = 0; i < num_new_cycles; i++) {
                    for (cycle_length_t j = 0; j < cur_max_cycle_length + 2; j++) {
                        combined[(num_cycles - num_new_cycles + i) *
                                     (cur_max_cycle_length + 2) +
                                 j] =
                            new_cycles[i * (cur_max_cycle_length + 2) + j];
                    }
                }
                cycles_max_cycle_length = cur_max_cycle_length;
                free(cycles);
                free(new_cycles);
                cycles = combined;
            }
        }

        cycle_index_t searched_fit = genus_lower_bound_implied_fit;
        bool same_target_fit = last_searched_fit == searched_fit;
        cycle_length_t required_length = same_target_fit ? cur_max_cycle_length : 0;
        cycle_index_t min_shortest_cycles;
        bool length_possible =
            length_composition_possible(2 * num_edges, searched_fit, cycle_length_available,
                                        cur_max_cycle_length, smallest_cycle_length,
                                        required_length, &min_shortest_cycles);

        if (length_possible && min_shortest_cycles > max_shortest_cycles) {
            length_possible = false;
        }

        uint64_t shortest_packing_slack =
            2 * (uint64_t)num_edges -
            (uint64_t)min_shortest_cycles * smallest_cycle_length;
        if (length_possible && min_shortest_cycles > verified_packable_shortest_cycles &&
            shortest_packing_slack <= 2 * (uint64_t)smallest_cycle_length) {
            uint64_t num_packing_calls = 0;
            packing_result_t packing_result = can_pack_shortest_cycles(
                num_vertices, num_edges, adjacency_list, cycles, cur_max_cycle_length,
                smallest_cycle_length, num_shortest_cycles, min_shortest_cycles,
                &num_packing_calls);
            if (packing_result == PACKING_IMPOSSIBLE) {
                max_shortest_cycles = min_shortest_cycles - 1;
                length_possible = false;
            } else if (packing_result == PACKING_FOUND) {
                verified_packable_shortest_cycles = min_shortest_cycles;
            }
        }

        if (!length_possible) {
            last_searched_fit = searched_fit;
            cycle_index_t future_fit_upper_bound = max_possible_fit_with_shortest_bound(
                num_edges, smallest_cycle_length, second_smallest_cycle_length,
                max_shortest_cycles, cur_max_cycle_length + 1);
            cycle_index_t genus_lower_bound_from_fit_bound =
                genus_lower_bound_from_fit_upper_bound(future_fit_upper_bound, num_vertices,
                                                       num_edges);
            if (genus_lower_bound_from_fit_bound > genus_lower_bound) {
                genus_lower_bound = genus_lower_bound_from_fit_bound;
            }
            genus_lower_bound_implied_fit =
                implied_max_fit_for_genus(genus_lower_bound, num_vertices, num_edges);
            genus_upper_bound = implied_max_genus_for_fit(max_fit, num_vertices, num_edges);
            bool target_fit_changed = genus_lower_bound_implied_fit != searched_fit;

            assert(genus_upper_bound >= genus_lower_bound, "\nInvalid state: genus lower bound exceeded the upper bound. Check the inputs.\n");

            if (target_fit_changed) {
                cur_max_cycle_length--;
            }
            continue;
        }

        cycle_index_t max_cycles_per_vertex;
        cbv_t cycles_by_vertex = cbv_generate(num_vertices, cycles, num_cycles,
                                              cur_max_cycle_length, &max_cycles_per_vertex);
        cycle_index_t max_cycles_per_edge;
        cbe_t cycles_by_edge =
            cbe_generate(num_vertices, cycles, num_cycles, cur_max_cycle_length,
                         &max_cycles_per_edge);

        
        
        bool* used_cycles = (bool*)calloc(num_cycles, sizeof(bool));
        assert(used_cycles != NULL, "Error allocating memory for the used cycles\n");
        
        
        
        
        
        degree_t* vertex_uses = (degree_t*)malloc(num_vertices * sizeof(degree_t));
        assert(vertex_uses != NULL, "Error allocating memory for the vertices most used order\n");
        transitions_used_size = (size_t)num_vertices * VERTEX_DEGREE * VERTEX_DEGREE;
        transitions_used = (bool*)malloc(transitions_used_size * sizeof(bool));
        assert(transitions_used != NULL,
               "Error allocating memory for the used transition table\n");
        cycle_edge_conflicts_init(num_cycles);
        rotation_state_init(num_vertices);

        vertex_t start_vertex;
        vertex_t end_vertex;
        cycle_index_t num_edge_start_cycles =
            choose_start_edge(num_vertices, adjacency_list, max_cycles_per_edge, cycles_by_edge,
                              &start_vertex, &end_vertex);
        bool forced_single_new_cycle =
            same_target_fit && min_shortest_cycles == searched_fit - 1;
        bool use_max_length_start =
            same_target_fit &&
            (forced_single_new_cycle || num_new_cycles <= num_edge_start_cycles);
        cycle_index_t num_start_cycles_for_vertex = num_new_cycles;
        cycle_index_t* fixed_edge_start_cycles = NULL;
        cycle_index_t* start_cycle_order =
            (cycle_index_t*)malloc(num_cycles * sizeof(cycle_index_t));
        assert(start_cycle_order != NULL, "Error allocating memory for the start cycle order\n");
        memset(start_cycle_order, 0xff, num_cycles * sizeof(cycle_index_t));
        int8_t* length_cache_without_required = NULL;
        int8_t* length_cache_with_required = NULL;
        cycle_index_t length_cache_width = 2 * num_edges + 1;
        uint64_t length_cache_entries = (uint64_t)(searched_fit + 1) * length_cache_width;
        if (length_cache_entries <= LENGTH_FEASIBILITY_CACHE_LIMIT) {
            length_cache_without_required =
                (int8_t*)malloc(length_cache_entries * sizeof(int8_t));
            length_cache_with_required =
                (int8_t*)malloc(length_cache_entries * sizeof(int8_t));
            assert(length_cache_without_required != NULL && length_cache_with_required != NULL,
                   "Error allocating memory for length feasibility caches\n");
            memset(length_cache_without_required, 0xff,
                   length_cache_entries * sizeof(int8_t));
            memset(length_cache_with_required, 0xff, length_cache_entries * sizeof(int8_t));
        }
        length_feasibility_t length_feasibility = {
            .cycle_length_available = cycle_length_available,
            .max_cycle_length = cur_max_cycle_length,
            .shortest_length = smallest_cycle_length,
            .required_length = cur_max_cycle_length,
            .cache_without_required = length_cache_without_required,
            .cache_with_required = length_cache_with_required,
            .cache_width = length_cache_width,
        };
        if (!use_max_length_start) {
            fixed_edge_start_cycles = cbe_get_cycle_indices(cycles_by_edge, max_cycles_per_edge,
                                                            start_vertex, end_vertex,
                                                            &num_start_cycles_for_vertex);
        }

        
        
        
        
        cycle_index_t raw_start_count =
            use_max_length_start ? num_new_cycles : num_start_cycles_for_vertex;
        cycle_index_t* raw_start_cycles =
            (cycle_index_t*)malloc((raw_start_count == 0 ? 1 : raw_start_count) *
                                   sizeof(cycle_index_t));
        assert(raw_start_cycles != NULL, "Error allocating memory for start cycles\n");
        for (cycle_index_t start_i = 0; start_i < raw_start_count; start_i++) {
            raw_start_cycles[start_i] = use_max_length_start
                                            ? num_cycles - num_new_cycles + start_i
                                            : fixed_edge_start_cycles[start_i];
        }
        if (graph_automorphisms.maps == NULL) {
            automorphism_generate(num_vertices, adjacency_list, &graph_automorphisms);
        }
        cycle_index_t num_start_cycles;
        cycle_index_t* start_cycles = start_cycles_prune_by_symmetry(
            cycles, cur_max_cycle_length, num_cycles, cycles_by_edge, max_cycles_per_edge,
            raw_start_cycles, raw_start_count, &num_start_cycles);
        free(raw_start_cycles);
        precompute_start_cycle_order(start_cycle_order, start_cycles, num_start_cycles);

        unsigned num_start_threads =
            get_start_branch_thread_count(num_start_cycles, num_cycles);
        if (num_start_threads > 1) {
            bool* solution_used_cycles = (bool*)calloc(num_cycles, sizeof(bool));
            assert(solution_used_cycles != NULL,
                   "Error allocating memory for the parallel search solution\n");
            start_branch_search_t context = {
                .num_vertices = num_vertices,
                .num_edges = num_edges,
                .adjacency_list = adjacency_list,
                .max_cycle_length = cur_max_cycle_length,
                .num_cycles = num_cycles,
                .cycles = cycles,
                .max_cycles_per_vertex = max_cycles_per_vertex,
                .cycles_by_vertex = cycles_by_vertex,
                .max_cycles_per_edge = max_cycles_per_edge,
                .cycles_by_edge = cycles_by_edge,
                .start_cycles = start_cycles,
                .num_start_cycles = num_start_cycles,
                .start_cycle_order = start_cycle_order,
                .initial_cycles_to_use = genus_lower_bound_implied_fit - 1,
                .max_used_cycles = genus_lower_bound_implied_fit,
                .initial_max_fit = max_fit,
                .initial_directed_edge_remaining = directed_edge_remaining,
                .length_feasibility_template = length_feasibility,
                .length_cache_entries = length_cache_entries,
                .require_max_cycle_if_start_is_shorter = same_target_fit,
                .solution_used_cycles = solution_used_cycles,
            };
            if (search_start_cycles_parallel(&context, num_start_threads)) {
                num_search_calls += context.total_search_calls;
                max_fit = context.best_max_fit;
                memcpy(used_cycles, solution_used_cycles, num_cycles * sizeof(bool));
                free(solution_used_cycles);
                                show_solution(genus_lower_bound, genus_lower_bound_implied_fit, num_search_calls,
                              num_cycles, used_cycles, cycles, cur_max_cycle_length);
                graph_free(adjacency_list);
                free(vertex_uses);
                free(cycles);
                free(cycles_by_vertex);
                free(cycles_by_edge);
                free(used_cycles);
                free(start_cycle_order);
                free(cycle_length_available);
                free(length_cache_without_required);
                free(length_cache_with_required);
                free(start_cycles);
                cycle_edge_conflicts_free();
                rotation_state_free();
                free(transitions_used);
                transitions_used = NULL;
                fclose(output_file);
                return 0;
            }
            num_search_calls += context.total_search_calls;
            if (context.best_max_fit > max_fit) {
                max_fit = context.best_max_fit;
            }
            free(solution_used_cycles);
        } else {
            for (cycle_index_t start_i = 0; start_i < num_start_cycles; start_i++) {
                cycle_index_t c = start_cycles[start_i];
                cycle_length_t cycle_length;
                cycles_t cycle = cycle_get(cycles, cur_max_cycle_length, c, &cycle_length);
                memset(transitions_used, 0, transitions_used_size * sizeof(bool));
                cycle_edge_conflicts_clear(num_cycles);
                rotation_state_clear(num_vertices);
                cycle_index_t current_start_cycle_order = start_cycle_order[c];
                if (VERTEX_DEGREE > 2 && !cycle_transitions_good(cycle, cycle_length)) {
                    continue;
                }
                if (!cycle_try_add_rotation_system(cycle, cycle_length)) {
                    continue;
                }

                memcpy(vertex_uses, initial_vertex_uses, num_vertices * sizeof(degree_t));

                
                used_cycles[c] = true;
                cycle_set_transitions(cycle, cycle_length, true);
                cycle_set_edge_conflicts(cycle, cycle_length, max_cycles_per_edge,
                                         cycles_by_edge, true);
                for (cycle_length_t i = 0; i < cycle_length; i++) {
                    adj_remove_edge(adjacency_list, cycle[i], cycle[i + 1]);

                    
                    vertex_uses[cycle[i]] += 1;
                }

                if (search(genus_lower_bound_implied_fit - 1, genus_lower_bound_implied_fit,
                           used_cycles, vertex_uses, &max_fit, &num_search_calls, num_vertices,
                           num_edges, adjacency_list, cur_max_cycle_length, num_cycles, cycles,
                           max_cycles_per_vertex, cycles_by_vertex, max_cycles_per_edge,
                           cycles_by_edge, start_cycle_order,
                           current_start_cycle_order, &length_feasibility,
                           same_target_fit && cycle_length != cur_max_cycle_length ? 1 : 0)) {
                    
                                        show_solution(genus_lower_bound, genus_lower_bound_implied_fit, num_search_calls,
                                  num_cycles, used_cycles, cycles, cur_max_cycle_length);
                    graph_free(adjacency_list);
                    free(vertex_uses);
                    free(cycles);
                    free(cycles_by_vertex);
                    free(cycles_by_edge);
                    free(used_cycles);
                    free(start_cycle_order);
                    free(cycle_length_available);
                    free(length_cache_without_required);
                    free(length_cache_with_required);
                    free(start_cycles);
                    cycle_edge_conflicts_free();
                    rotation_state_free();
                    free(transitions_used);
                    transitions_used = NULL;
                    fclose(output_file);
                    return 0;
                }

                
                used_cycles[c] = false;
                cycle_set_transitions(cycle, cycle_length, false);
                cycle_set_edge_conflicts(cycle, cycle_length, max_cycles_per_edge,
                                         cycles_by_edge, false);
                cycle_remove_rotation_system(cycle, cycle_length);
                for (cycle_length_t i = 0; i < cycle_length; i++) {
                    adj_undo_remove_edge(adjacency_list, cycle[i], cycle[i + 1]);
                }
            }
        }

                last_searched_fit = searched_fit;

        
        cycle_index_t future_fit_upper_bound = max_possible_fit_with_shortest_bound(
            num_edges, smallest_cycle_length, second_smallest_cycle_length,
            max_shortest_cycles, cur_max_cycle_length + 1);
        cycle_index_t genus_lower_bound_from_fit_bound =
            genus_lower_bound_from_fit_upper_bound(future_fit_upper_bound, num_vertices,
                                                   num_edges);
        if (genus_lower_bound_from_fit_bound > genus_lower_bound) {
            genus_lower_bound = genus_lower_bound_from_fit_bound;
        }
        genus_lower_bound_implied_fit =
            implied_max_fit_for_genus(genus_lower_bound, num_vertices, num_edges);
        
        genus_upper_bound = implied_max_genus_for_fit(max_fit, num_vertices, num_edges);
        bool target_fit_changed = genus_lower_bound_implied_fit != searched_fit;

        if (genus_lower_bound == genus_upper_bound && max_fit == genus_lower_bound_implied_fit) {
            
            if (num_cycles == genus_lower_bound_implied_fit) {
                show_solution(genus_lower_bound, max_fit, num_search_calls, num_cycles, used_cycles,
                              cycles, cur_max_cycle_length);
                free(used_cycles);
                free(start_cycle_order);
                free(start_cycles);
                free(vertex_uses);
                graph_free(adjacency_list);
                free(cycles);
                free(cycles_by_vertex);
                free(cycles_by_edge);
                free(cycle_length_available);
                free(length_cache_without_required);
                free(length_cache_with_required);
                cycle_edge_conflicts_free();
                rotation_state_free();
                free(transitions_used);
                transitions_used = NULL;
                fclose(output_file);
                return 0;
            } else {
                {
                    fprintf(output_file, "%" PRIcycle_index_t "\n", genus_lower_bound);
                    free(used_cycles);
                    free(start_cycle_order);
                    free(start_cycles);
                    free(vertex_uses);
                    graph_free(adjacency_list);
                    free(cycles);
                    free(cycles_by_vertex);
                    free(cycles_by_edge);
                    free(cycle_length_available);
                    free(length_cache_without_required);
                    free(length_cache_with_required);
                    cycle_edge_conflicts_free();
                    rotation_state_free();
                    free(transitions_used);
                    transitions_used = NULL;
                    fclose(output_file);
                    return 0;
                }
            }
        }
        assert(genus_upper_bound >= genus_lower_bound, "\nInvalid state: genus lower bound exceeded the upper bound. Check the inputs.\n");


        free(used_cycles);
        free(start_cycle_order);
        free(start_cycles);
        free(vertex_uses);
        free(cycles_by_vertex);
        free(cycles_by_edge);
        free(length_cache_without_required);
        free(length_cache_with_required);
        cycle_edge_conflicts_free();
        rotation_state_free();
        free(transitions_used);
        transitions_used = NULL;
        if (target_fit_changed) {
            cur_max_cycle_length--;
        }
    }

    genus_lower_bound_implied_fit--;
    genus_lower_bound =
        implied_max_genus_for_fit(genus_lower_bound_implied_fit, num_vertices, num_edges);
    if (max_fit < (2 * num_edges + cycles_max_cycle_length - 1) / cycles_max_cycle_length) {
        max_fit = (2 * num_edges + cycles_max_cycle_length - 1) / cycles_max_cycle_length;
        genus_upper_bound = implied_max_genus_for_fit(max_fit, num_vertices, num_edges);
    }
    cycle_index_t max_cycles_per_vertex;
    cbv_t cycles_by_vertex = cbv_generate(num_vertices, cycles, num_cycles, cycles_max_cycle_length,
                                          &max_cycles_per_vertex);
    cycle_index_t max_cycles_per_edge;
    cbe_t cycles_by_edge =
        cbe_generate(num_vertices, cycles, num_cycles, cycles_max_cycle_length,
                     &max_cycles_per_edge);
    bool* used_cycles = (bool*)calloc(num_cycles, sizeof(bool));
    assert(used_cycles != NULL, "Error allocating memory for the used cycles\n");
    degree_t* vertex_uses = (degree_t*)malloc(num_vertices * sizeof(degree_t));
    assert(vertex_uses != NULL, "Error allocating memory for the vertices most used order\n");
    transitions_used_size = (size_t)num_vertices * VERTEX_DEGREE * VERTEX_DEGREE;
    transitions_used = (bool*)malloc(transitions_used_size * sizeof(bool));
    assert(transitions_used != NULL,
           "Error allocating memory for the used transition table\n");
    cycle_edge_conflicts_init(num_cycles);
    rotation_state_init(num_vertices);
    vertex_t start_vertex;
    vertex_t end_vertex;
    choose_start_edge(num_vertices, adjacency_list, max_cycles_per_edge, cycles_by_edge,
                      &start_vertex, &end_vertex);
    cycle_index_t num_start_cycles_for_vertex;
    cycle_index_t* start_cycle_indices = cbe_get_cycle_indices(
        cycles_by_edge, max_cycles_per_edge, start_vertex, end_vertex,
        &num_start_cycles_for_vertex);
    if (graph_automorphisms.maps == NULL) {
        automorphism_generate(num_vertices, adjacency_list, &graph_automorphisms);
    }
    cycle_index_t num_start_cycles;
    cycle_index_t* start_cycles = start_cycles_prune_by_symmetry(
        cycles, cycles_max_cycle_length, num_cycles, cycles_by_edge, max_cycles_per_edge,
        start_cycle_indices, num_start_cycles_for_vertex, &num_start_cycles);
    cycle_index_t* start_cycle_order = (cycle_index_t*)malloc(num_cycles * sizeof(cycle_index_t));
    assert(start_cycle_order != NULL, "Error allocating memory for the start cycle order\n");
    memset(start_cycle_order, 0xff, num_cycles * sizeof(cycle_index_t));
    precompute_start_cycle_order(start_cycle_order, start_cycles, num_start_cycles);

    while (genus_lower_bound <= genus_upper_bound) {
        
        int8_t* length_cache_without_required = NULL;
        int8_t* length_cache_with_required = NULL;
        cycle_index_t length_cache_width = 2 * num_edges + 1;
        uint64_t length_cache_entries =
            (uint64_t)(genus_lower_bound_implied_fit + 1) * length_cache_width;
        if (length_cache_entries <= LENGTH_FEASIBILITY_CACHE_LIMIT) {
            length_cache_without_required =
                (int8_t*)malloc(length_cache_entries * sizeof(int8_t));
            length_cache_with_required =
                (int8_t*)malloc(length_cache_entries * sizeof(int8_t));
            assert(length_cache_without_required != NULL && length_cache_with_required != NULL,
                   "Error allocating memory for length feasibility caches\n");
            memset(length_cache_without_required, 0xff,
                   length_cache_entries * sizeof(int8_t));
            memset(length_cache_with_required, 0xff, length_cache_entries * sizeof(int8_t));
        }
        length_feasibility_t length_feasibility = {
            .cycle_length_available = cycle_length_available,
            .max_cycle_length = cycles_max_cycle_length,
            .shortest_length = smallest_cycle_length,
            .required_length = 0,
            .cache_without_required = length_cache_without_required,
            .cache_with_required = length_cache_with_required,
            .cache_width = length_cache_width,
        };

        
        
        unsigned num_start_threads =
            get_start_branch_thread_count(num_start_cycles, num_cycles);
        if (num_start_threads > 1) {
            bool* solution_used_cycles = (bool*)calloc(num_cycles, sizeof(bool));
            assert(solution_used_cycles != NULL,
                   "Error allocating memory for the parallel search solution\n");
            start_branch_search_t context = {
                .num_vertices = num_vertices,
                .num_edges = num_edges,
                .adjacency_list = adjacency_list,
                .max_cycle_length = cycles_max_cycle_length,
                .num_cycles = num_cycles,
                .cycles = cycles,
                .max_cycles_per_vertex = max_cycles_per_vertex,
                .cycles_by_vertex = cycles_by_vertex,
                .max_cycles_per_edge = max_cycles_per_edge,
                .cycles_by_edge = cycles_by_edge,
                .start_cycles = start_cycles,
                .num_start_cycles = num_start_cycles,
                .start_cycle_order = start_cycle_order,
                .initial_cycles_to_use = genus_lower_bound_implied_fit - 1,
                .max_used_cycles = genus_lower_bound_implied_fit,
                .initial_max_fit = max_fit,
                .initial_directed_edge_remaining = directed_edge_remaining,
                .length_feasibility_template = length_feasibility,
                .length_cache_entries = length_cache_entries,
                .require_max_cycle_if_start_is_shorter = false,
                .solution_used_cycles = solution_used_cycles,
            };
            if (search_start_cycles_parallel(&context, num_start_threads)) {
                num_search_calls += context.total_search_calls;
                max_fit = context.best_max_fit;
                memcpy(used_cycles, solution_used_cycles, num_cycles * sizeof(bool));
                free(solution_used_cycles);
                                show_solution(genus_lower_bound, genus_lower_bound_implied_fit, num_search_calls,
                              num_cycles, used_cycles, cycles, cycles_max_cycle_length);
                graph_free(adjacency_list);
                free(vertex_uses);
                free(cycles);
                free(cycles_by_vertex);
                free(cycles_by_edge);
                free(used_cycles);
                free(start_cycle_order);
                free(start_cycles);
                free(cycle_length_available);
                free(length_cache_without_required);
                free(length_cache_with_required);
                cycle_edge_conflicts_free();
                rotation_state_free();
                free(transitions_used);
                transitions_used = NULL;
                fclose(output_file);
                return 0;
            }
            num_search_calls += context.total_search_calls;
            if (context.best_max_fit > max_fit) {
                max_fit = context.best_max_fit;
            }
            free(solution_used_cycles);
        } else {
            for (cycle_index_t start_i = 0; start_i < num_start_cycles; start_i++) {
                cycle_index_t c = start_cycles[start_i];
                cycle_length_t cycle_length;
                cycles_t cycle = cycle_get(cycles, cycles_max_cycle_length, c, &cycle_length);
                memset(transitions_used, 0, transitions_used_size * sizeof(bool));
                cycle_edge_conflicts_clear(num_cycles);
                rotation_state_clear(num_vertices);
                cycle_index_t current_start_cycle_order = start_cycle_order[c];
                if (VERTEX_DEGREE > 2 && !cycle_transitions_good(cycle, cycle_length)) {
                    continue;
                }
                if (!cycle_try_add_rotation_system(cycle, cycle_length)) {
                    continue;
                }

                memcpy(vertex_uses, initial_vertex_uses, num_vertices * sizeof(degree_t));

                
                used_cycles[c] = true;
                cycle_set_transitions(cycle, cycle_length, true);
                cycle_set_edge_conflicts(cycle, cycle_length, max_cycles_per_edge,
                                         cycles_by_edge, true);
                for (cycle_length_t i = 0; i < cycle_length; i++) {
                    adj_remove_edge(adjacency_list, cycle[i], cycle[i + 1]);

                    
                    vertex_uses[cycle[i]] += 1;
                }

                if (search(genus_lower_bound_implied_fit - 1, genus_lower_bound_implied_fit,
                           used_cycles, vertex_uses, &max_fit, &num_search_calls, num_vertices,
                           num_edges, adjacency_list, cycles_max_cycle_length, num_cycles, cycles,
                           max_cycles_per_vertex, cycles_by_vertex, max_cycles_per_edge,
                           cycles_by_edge, start_cycle_order,
                           current_start_cycle_order, &length_feasibility, 0)) {
                    
                                        show_solution(genus_lower_bound, genus_lower_bound_implied_fit, num_search_calls,
                                  num_cycles, used_cycles, cycles, cycles_max_cycle_length);
                    graph_free(adjacency_list);
                    free(vertex_uses);
                    free(cycles);
                    free(cycles_by_vertex);
                    free(cycles_by_edge);
                    free(used_cycles);
                    free(start_cycle_order);
                    free(start_cycles);
                    free(cycle_length_available);
                    free(length_cache_without_required);
                    free(length_cache_with_required);
                    cycle_edge_conflicts_free();
                    rotation_state_free();
                    free(transitions_used);
                    transitions_used = NULL;
                    fclose(output_file);
                    return 0;
                }

                
                used_cycles[c] = false;
                cycle_set_transitions(cycle, cycle_length, false);
                cycle_set_edge_conflicts(cycle, cycle_length, max_cycles_per_edge,
                                         cycles_by_edge, false);
                cycle_remove_rotation_system(cycle, cycle_length);
                for (cycle_length_t i = 0; i < cycle_length; i++) {
                    adj_undo_remove_edge(adjacency_list, cycle[i], cycle[i + 1]);
                }
            }
        }

        free(length_cache_without_required);
        free(length_cache_with_required);
                fprintf(stderr,
                "\nFit does not exist. Adjusting bounds. Used %" PRId64 " iterations so far.\n",
                num_search_calls);
        genus_lower_bound_implied_fit--;
        genus_lower_bound =
            implied_max_genus_for_fit(genus_lower_bound_implied_fit, num_vertices, num_edges);
    }

    graph_free(adjacency_list);
    free(cycles);
    free(cycles_by_vertex);
    free(cycles_by_edge);
    free(used_cycles);
    free(start_cycle_order);
    free(start_cycles);
    free(vertex_uses);
    free(cycle_length_available);
    cycle_edge_conflicts_free();
    rotation_state_free();
    free(transitions_used);
    transitions_used = NULL;
    fclose(output_file);

    fprintf(stderr,
        "Was not able to fit any cycles. Double check the settings "
        "and adjacency list.\n");
    return 1;
}

void show_solution(cycle_index_t genus_lower_bound, cycle_index_t genus_lower_bound_implied_fit,
                   uint64_t num_search_calls, cycle_index_t num_cycles, bool* used_cycles,
                   cycles_t cycles, cycle_length_t max_cycle_length) {
    (void)genus_lower_bound_implied_fit;
    (void)num_search_calls;
    (void)num_cycles;
    (void)used_cycles;
    (void)cycles;
    (void)max_cycle_length;
    fprintf(output_file, "%" PRIcycle_index_t "\n", genus_lower_bound);
}

bool search(cycle_index_t cycles_to_use,                    
            cycle_index_t max_used_cycles,                  
            bool* used_cycles,                              
            degree_t* vertex_uses, cycle_index_t* max_fit,  
            uint64_t* num_search_calls,                     
            vertex_t num_vertices, edge_t num_edges, adj_t adjacency_list,
            cycle_length_t max_cycle_length, cycle_index_t num_cycles, cycles_t cycles,
            cycle_index_t max_cycles_per_vertex, cbv_t cycles_by_vertex,
            cycle_index_t max_cycles_per_edge, cbe_t cycles_by_edge,
            cycle_index_t* start_cycle_order, cycle_index_t current_start_cycle_order,
            length_feasibility_t* length_feasibility,
            cycle_index_t required_cycles_to_use) {
    if (search_stop_requested != NULL && atomic_load(search_stop_requested)) {
        return false;
    }
    (*num_search_calls)++;

    
    
    
    vertex_t vertex = 0;
    bool found = false;
    cycle_index_t* cycle_indices = NULL;
    cycle_index_t num_cycles_for_column = 0;
    if (true) {
        degree_t max_column_pressure = 0;
        cycle_index_t min_cycle_options = MAX_CYCLES;
        
        
        
        bool exact_column_count = VERTEX_DEGREE != 5;

        for (vertex_t i = 0; i < num_vertices; i++) {
            vertex_t* neighbors = adj_get_neighbors(adjacency_list, i);
            for (degree_t j = 0; j < VERTEX_DEGREE; j++) {
                if (neighbors[j] == MAX_VERTICES || !adj_slot_has_edge(i, j)) {
                    continue;
                }

                cycle_index_t num_cycles_for_constraint;
                cycle_index_t* cycle_indices_for_edge =
                    cbe_get_cycle_indices(cycles_by_edge, max_cycles_per_edge, i, neighbors[j],
                                          &num_cycles_for_constraint);
                cycle_index_t cycle_options = 0;
                degree_t column_pressure = vertex_uses[i] + vertex_uses[neighbors[j]];
                for (cycle_index_t k = 0; k < num_cycles_for_constraint; k++) {
                    cycle_index_t cycle_index = cycle_indices_for_edge[k];
                    if (cycle_search_candidate_usable(
                            used_cycles, vertex_uses, adjacency_list, cycles,
                            max_cycle_length, cycle_index, start_cycle_order,
                            current_start_cycle_order, cycles_to_use,
                            length_feasibility, required_cycles_to_use,
                            exact_column_count, false, NULL, NULL, NULL)) {
                        cycle_options++;
                        if (found &&
                            (cycle_options > min_cycle_options ||
                             (cycle_options == min_cycle_options &&
                              column_pressure <= max_column_pressure))) {
                            break;
                        }
                    }
                }

                if (!found || cycle_options < min_cycle_options ||
                    (cycle_options == min_cycle_options &&
                     column_pressure > max_column_pressure)) {
                    found = true;
                    vertex = i;
                    cycle_indices = cycle_indices_for_edge;
                    num_cycles_for_column = num_cycles_for_constraint;
                    max_column_pressure = column_pressure;
                    min_cycle_options = cycle_options;

                    if (min_cycle_options == 0) {
                        break;  
                    }
                }
            }
            if (min_cycle_options == 0) {
                break;  
            }
        }

    } else {
        
        
        degree_t max_uses = 0;
        for (vertex_t i = 0; i < num_vertices; i++) {
            if (vertex_uses[i] < VERTEX_USE_LIMIT && (!found || vertex_uses[i] > max_uses)) {
                found = true;
                vertex = i;
                max_uses = vertex_uses[i];

                if (max_uses == VERTEX_USE_LIMIT - 1) {
                    break;  
                }
            }
        }

        if (found) {
            cycle_indices = cbv_get_cycle_indices(cycles_by_vertex, max_cycles_per_vertex, vertex,
                                                  &num_cycles_for_column);
        }
    }
    
    if (!found) {
        return false;
    }
    if (num_cycles_for_column == 0) {
        return false;
    }

    
    if (max_used_cycles - cycles_to_use > *max_fit) {
        
        bool all_used = true;
        for (vertex_t i = 0; i < num_vertices; i++) {
            if (vertex_uses[i] < VERTEX_USE_LIMIT) {
                all_used = false;
                break;
            }
        }

        if (all_used) {
            *max_fit = max_used_cycles - cycles_to_use;
        }
    }

    
    for (cycle_index_t i = 0; i < num_cycles_for_column; i++) {
        
        cycle_index_t cycle_index = cycle_indices[i];
        cycle_length_t cycle_length;
        vertex_t* cycle;
        cycle_index_t next_required_cycles_to_use;
        if (!cycle_search_candidate_usable(
                used_cycles, vertex_uses, adjacency_list, cycles, max_cycle_length,
                cycle_index, start_cycle_order, current_start_cycle_order, cycles_to_use,
                length_feasibility, required_cycles_to_use, true, true, &cycle_length,
                &cycle, &next_required_cycles_to_use)) {
            continue;
        }
        if (!cycle_try_add_rotation_system(cycle, cycle_length)) {
            continue;
        }

        
        used_cycles[cycle_index] = true;
        cycle_set_transitions(cycle, cycle_length, true);
        cycle_set_edge_conflicts(cycle, cycle_length, max_cycles_per_edge,
                                 cycles_by_edge, true);
        for (cycle_length_t j = 0; j < cycle_length; j++) {
            adj_remove_edge(adjacency_list, cycle[j], cycle[j + 1]);

            
            vertex_uses[cycle[j]]++;
            assert(vertex_uses[cycle[j]] <= VERTEX_USE_LIMIT,
                   "\nVertex %" PRIvertex_t " used too many times\n", cycle[j]);
        }

        
        bool is_final_cycle = cycles_to_use == 1;
        if (is_final_cycle) {
            if (next_required_cycles_to_use > 0) {
                used_cycles[cycle_index] = false;
                cycle_set_transitions(cycle, cycle_length, false);
                cycle_set_edge_conflicts(cycle, cycle_length, max_cycles_per_edge,
                                         cycles_by_edge, false);
                cycle_remove_rotation_system(cycle, cycle_length);
                for (cycle_length_t j = 0; j < cycle_length; j++) {
                    adj_undo_remove_edge(adjacency_list, cycle[j], cycle[j + 1]);

                    
                    vertex_uses[cycle[j]]--;
                }
                continue;
            }
            if (!cubic_exact_cover_mode) {
                
                bool all_vertices_used = true;
                for (vertex_t i = 0; i < num_vertices; i++) {
                    if (vertex_uses[i] < VERTEX_USE_LIMIT) {
                        all_vertices_used = false;
                        break;
                    }
                }
                if (!all_vertices_used) {
                    used_cycles[cycle_index] = false;
                    cycle_set_transitions(cycle, cycle_length, false);
                    cycle_set_edge_conflicts(cycle, cycle_length, max_cycles_per_edge,
                                             cycles_by_edge, false);
                    cycle_remove_rotation_system(cycle, cycle_length);
                    for (cycle_length_t j = 0; j < cycle_length; j++) {
                        adj_undo_remove_edge(adjacency_list, cycle[j], cycle[j + 1]);

                        
                        vertex_uses[cycle[j]]--;
                    }
                    continue;
                }
            }
            return true;
        }

        
        if (search(cycles_to_use - 1, max_used_cycles, used_cycles, vertex_uses, max_fit,
                   num_search_calls, num_vertices, num_edges, adjacency_list, max_cycle_length,
                   num_cycles, cycles, max_cycles_per_vertex, cycles_by_vertex,
                   max_cycles_per_edge, cycles_by_edge,
                   start_cycle_order, current_start_cycle_order, length_feasibility,
                   next_required_cycles_to_use)) {
            return true;  
        }

        
        used_cycles[cycle_index] = false;
        cycle_set_transitions(cycle, cycle_length, false);
        cycle_set_edge_conflicts(cycle, cycle_length, max_cycles_per_edge,
                                 cycles_by_edge, false);
        cycle_remove_rotation_system(cycle, cycle_length);
        for (cycle_length_t j = 0; j < cycle_length; j++) {
            adj_undo_remove_edge(adjacency_list, cycle[j], cycle[j + 1]);

            
            vertex_uses[cycle[j]]--;
        }
    }

    
    return false;
}

degree_t adj_neighbor_index(adj_t adjacency_list, vertex_t vertex, vertex_t neighbor) {
    vertex_t* neighbors = adj_get_neighbors(adjacency_list, vertex);
    for (degree_t i = 0; i < VERTEX_DEGREE; i++) {
        if (neighbors[i] == neighbor) {
            return i;
        }
    }
    assert(false, "Error finding neighbor %" PRIvertex_t " of vertex %" PRIvertex_t "\n",
           neighbor, vertex);
    return 0;
}


bool cycle_vertex_uses_fit(vertex_t* cycle, cycle_length_t cycle_length,
                           degree_t* vertex_uses) {
    for (cycle_length_t i = 0; i < cycle_length; i++) {
        degree_t projected_uses = vertex_uses[cycle[i]] + 1;
        for (cycle_length_t j = 0; j < i; j++) {
            if (cycle[j] == cycle[i]) {
                projected_uses++;
            }
        }
        if (projected_uses > VERTEX_USE_LIMIT) {
            return false;
        }
    }
    return true;
}

void cycle_edge_conflicts_init(cycle_index_t num_cycles) {
    cycle_index_t slots = num_cycles == 0 ? 1 : num_cycles;
    cycle_edge_conflicts = (cycle_index_t*)calloc(slots, sizeof(cycle_index_t));
    assert(cycle_edge_conflicts != NULL,
           "Error allocating memory for cycle edge conflicts\n");
}

void cycle_edge_conflicts_clear(cycle_index_t num_cycles) {
    assert(cycle_edge_conflicts != NULL,
           "Error clearing uninitialized cycle edge conflicts\n");
    memset(cycle_edge_conflicts, 0, num_cycles * sizeof(cycle_index_t));
}

void cycle_edge_conflicts_free(void) {
    free(cycle_edge_conflicts);
    cycle_edge_conflicts = NULL;
}

bool candidate_length_possible(cycle_length_t cycle_length,
                               cycle_index_t cycles_to_use,
                               length_feasibility_t* length_feasibility,
                               cycle_index_t required_cycles_to_use) {
    if (cycle_length > num_edges_remaining) {
        return false;
    }

    if (((cycles_to_use - 1) * smallest_cycle_length > num_edges_remaining - cycle_length) ||
        ((cycles_to_use - 1) * length_feasibility->max_cycle_length <
         num_edges_remaining - cycle_length)) {
        return false;
    }

    cycle_index_t remaining_required_cycles_to_use = required_cycles_to_use;
    if (remaining_required_cycles_to_use > 0 &&
        cycle_length == length_feasibility->required_length) {
        remaining_required_cycles_to_use--;
    }
    return cached_length_composition_possible(length_feasibility,
                                              num_edges_remaining - cycle_length,
                                              cycles_to_use - 1,
                                              remaining_required_cycles_to_use);
}

void cycle_set_edge_conflicts(vertex_t* cycle, cycle_length_t cycle_length,
                              cycle_index_t max_cycles_per_edge, cbe_t cycles_by_edge,
                              bool used) {
    assert(cycle_edge_conflicts != NULL,
           "Error updating uninitialized cycle edge conflicts\n");
    for (cycle_length_t i = 0; i < cycle_length; i++) {
        cycle_index_t num_cycles_for_edge;
        cycle_index_t* cycle_indices =
            cbe_get_cycle_indices(cycles_by_edge, max_cycles_per_edge, cycle[i],
                                  cycle[i + 1], &num_cycles_for_edge);
        for (cycle_index_t j = 0; j < num_cycles_for_edge; j++) {
            cycle_index_t cycle_index = cycle_indices[j];
            if (used) {
                cycle_edge_conflicts[cycle_index]++;
            } else {
                assert(cycle_edge_conflicts[cycle_index] > 0,
                       "Error removing missing cycle edge conflict\n");
                cycle_edge_conflicts[cycle_index]--;
            }
        }
    }
}

bool cycle_search_candidate_usable(bool* used_cycles, degree_t* vertex_uses,
                                   adj_t adjacency_list, cycles_t cycles,
                                   cycle_length_t max_cycle_length,
                                   cycle_index_t cycle_index,
                                   cycle_index_t* start_cycle_order,
                                   cycle_index_t current_start_cycle_order,
                                   cycle_index_t cycles_to_use,
                                   length_feasibility_t* length_feasibility,
                                   cycle_index_t required_cycles_to_use,
                                   bool check_row_constraints,
                                   bool check_transitions,
                                   cycle_length_t* cycle_length_out,
                                   vertex_t** cycle_out,
                                   cycle_index_t* next_required_cycles_to_use) {
    if (start_cycle_order[cycle_index] < current_start_cycle_order ||
        used_cycles[cycle_index]) {
        return false;
    }

    cycle_length_t cycle_length;
    vertex_t* cycle = cycle_get(cycles, max_cycle_length, cycle_index, &cycle_length);
    cycle_index_t remaining_required_cycles_to_use = required_cycles_to_use;
    if (remaining_required_cycles_to_use > 0 &&
        cycle_length == length_feasibility->required_length) {
        remaining_required_cycles_to_use--;
    }
    if (!candidate_length_possible(cycle_length, cycles_to_use, length_feasibility,
                                   required_cycles_to_use)) {
        return false;
    }

    if (check_row_constraints) {
        (void)adjacency_list;
        assert(cycle_edge_conflicts != NULL, "Error: cycle edge conflicts not initialized\n");
        if (cycle_edge_conflicts[cycle_index] != 0 ||
            (!cubic_exact_cover_mode &&
             !cycle_vertex_uses_fit(cycle, cycle_length, vertex_uses))) {
            return false;
        }
    }

    if (check_transitions && VERTEX_DEGREE > 2 &&
        !cycle_transitions_good(cycle, cycle_length)) {
        return false;
    }

    if (cycle_length_out != NULL) {
        *cycle_length_out = cycle_length;
    }
    if (cycle_out != NULL) {
        *cycle_out = cycle;
    }
    if (next_required_cycles_to_use != NULL) {
        *next_required_cycles_to_use = remaining_required_cycles_to_use;
    }
    return true;
}

bool cycle_transitions_good(vertex_t* cycle, cycle_length_t cycle_length) {
    for (cycle_length_t i = 0; i < cycle_length; i++) {
        vertex_t center = cycle[i];
        if (vertex_degrees[center] <= 2) {
            continue;
        }

        vertex_t prev = i == 0 ? cycle[cycle_length - 1] : cycle[i - 1];
        vertex_t next = i + 1 == cycle_length ? cycle[0] : cycle[i + 1];
        degree_t prev_index = adj_neighbor_index(full_adjacency_list, center, prev);
        degree_t next_index = adj_neighbor_index(full_adjacency_list, center, next);
        size_t reverse_transition_index =
            ((size_t)center * VERTEX_DEGREE + next_index) * VERTEX_DEGREE + prev_index;
        if (transitions_used[reverse_transition_index]) {
            return false;
        }
    }
    return true;
}

void cycle_set_transitions(vertex_t* cycle, cycle_length_t cycle_length, bool used) {
    for (cycle_length_t i = 0; i < cycle_length; i++) {
        vertex_t center = cycle[i];
        if (vertex_degrees[center] <= 2) {
            continue;
        }

        vertex_t prev = i == 0 ? cycle[cycle_length - 1] : cycle[i - 1];
        vertex_t next = i + 1 == cycle_length ? cycle[0] : cycle[i + 1];
        degree_t prev_index = adj_neighbor_index(full_adjacency_list, center, prev);
        degree_t next_index = adj_neighbor_index(full_adjacency_list, center, next);
        size_t transition_index =
            ((size_t)center * VERTEX_DEGREE + prev_index) * VERTEX_DEGREE + next_index;
        transitions_used[transition_index] = used;
    }
}

unsigned get_start_branch_thread_count(cycle_index_t num_start_cycles,
                                       cycle_index_t num_cycles) {
    (void)num_cycles;
    if (num_start_cycles < 4) {
        return 1;
    }

    unsigned threads = page_thread_override > START_BRANCH_THREAD_CAP
                           ? START_BRANCH_THREAD_CAP
                           : page_thread_override;

    if (threads < 2) {
        return 1;
    }
    if (threads > num_start_cycles) {
        threads = num_start_cycles;
    }
    return threads;
}

void precompute_start_cycle_order(cycle_index_t* start_cycle_order,
                                  cycle_index_t* start_cycles,
                                  cycle_index_t num_start_cycles) {
    for (cycle_index_t i = 0; i < num_start_cycles; i++) {
        start_cycle_order[start_cycles[i]] = i;
    }
}

bool search_start_cycles_parallel(start_branch_search_t* context,
                                  unsigned num_threads) {
    context->next_start_index = 0;
    context->completed_start_cycles = 0;
    context->best_max_fit = context->initial_max_fit;
    context->total_search_calls = 0;
    context->solution_found = false;
    atomic_init(&context->stop_requested, false);
    assert(page_mutex_init(&context->mutex) == 0,
           "Error initializing start branch mutex\n");

    page_thread_t* threads = (page_thread_t*)malloc(num_threads * sizeof(page_thread_t));
    assert(threads != NULL, "Error allocating start branch threads\n");
    for (unsigned i = 0; i < num_threads; i++) {
        assert(page_thread_create(&threads[i], start_branch_worker, context) == 0,
               "Error creating start branch worker thread\n");
    }
    for (unsigned i = 0; i < num_threads; i++) {
        assert(page_thread_join(threads[i]) == 0,
               "Error joining start branch worker thread\n");
    }
    free(threads);
    page_mutex_destroy(&context->mutex);
    return context->solution_found;
}

PAGE_THREAD_RETURN start_branch_worker(void* arg) {
    start_branch_search_t* context = (start_branch_search_t*)arg;
    bool* used_cycles = (bool*)calloc(context->num_cycles, sizeof(bool));
    degree_t* vertex_uses =
        (degree_t*)malloc(context->num_vertices * sizeof(degree_t));
    directed_edge_remaining =
        (bool*)malloc((num_directed_edges == 0 ? 1 : num_directed_edges) * sizeof(bool));
    transitions_used_size =
        (size_t)context->num_vertices * VERTEX_DEGREE * VERTEX_DEGREE;
    transitions_used = (bool*)malloc(transitions_used_size * sizeof(bool));
    assert(used_cycles != NULL && vertex_uses != NULL &&
               directed_edge_remaining != NULL && transitions_used != NULL,
           "Error allocating start branch worker state\n");
    cycle_edge_conflicts_init(context->num_cycles);
    rotation_state_init(context->num_vertices);

    int8_t* length_cache_without_required = NULL;
    int8_t* length_cache_with_required = NULL;
    if (context->length_feasibility_template.cache_without_required != NULL) {
        length_cache_without_required =
            (int8_t*)malloc(context->length_cache_entries * sizeof(int8_t));
        length_cache_with_required =
            (int8_t*)malloc(context->length_cache_entries * sizeof(int8_t));
        assert(length_cache_without_required != NULL && length_cache_with_required != NULL,
               "Error allocating worker length feasibility caches\n");
    }
    length_feasibility_t length_feasibility = context->length_feasibility_template;
    length_feasibility.cache_without_required = length_cache_without_required;
    length_feasibility.cache_with_required = length_cache_with_required;
    search_stop_requested = &context->stop_requested;

    while (!atomic_load(&context->stop_requested)) {
        page_mutex_lock(&context->mutex);
        if (context->solution_found ||
            context->next_start_index >= context->num_start_cycles) {
            page_mutex_unlock(&context->mutex);
            break;
        }
        cycle_index_t start_i = context->next_start_index++;
        page_mutex_unlock(&context->mutex);

        if (length_cache_without_required != NULL) {
            memset(length_cache_without_required, 0xff,
                   context->length_cache_entries * sizeof(int8_t));
            memset(length_cache_with_required, 0xff,
                   context->length_cache_entries * sizeof(int8_t));
        }
        memset(used_cycles, 0, context->num_cycles * sizeof(bool));
        memcpy(vertex_uses, initial_vertex_uses,
               context->num_vertices * sizeof(degree_t));
        memcpy(directed_edge_remaining, context->initial_directed_edge_remaining,
               (num_directed_edges == 0 ? 1 : num_directed_edges) * sizeof(bool));
        num_edges_remaining = num_directed_edges;
        memset(transitions_used, 0, transitions_used_size * sizeof(bool));
        cycle_edge_conflicts_clear(context->num_cycles);
        rotation_state_clear(context->num_vertices);

        cycle_index_t c = context->start_cycles[start_i];
        cycle_length_t cycle_length;
        cycles_t cycle =
            cycle_get(context->cycles, context->max_cycle_length, c, &cycle_length);
        bool branch_found = false;
        cycle_index_t local_max_fit = context->initial_max_fit;
        uint64_t local_search_calls = 0;
        if ((VERTEX_DEGREE <= 2 || cycle_transitions_good(cycle, cycle_length)) &&
            cycle_try_add_rotation_system(cycle, cycle_length)) {
            used_cycles[c] = true;
            cycle_set_transitions(cycle, cycle_length, true);
            cycle_set_edge_conflicts(cycle, cycle_length, context->max_cycles_per_edge,
                                     context->cycles_by_edge, true);
            for (cycle_length_t i = 0; i < cycle_length; i++) {
                adj_remove_edge(context->adjacency_list, cycle[i], cycle[i + 1]);
                vertex_uses[cycle[i]] += 1;
            }

            cycle_index_t required_cycles_to_use =
                context->require_max_cycle_if_start_is_shorter &&
                        cycle_length != context->max_cycle_length
                    ? 1
                    : 0;
            branch_found = search(
                context->initial_cycles_to_use, context->max_used_cycles,
                used_cycles, vertex_uses, &local_max_fit, &local_search_calls,
                context->num_vertices, context->num_edges, context->adjacency_list,
                context->max_cycle_length, context->num_cycles, context->cycles,
                context->max_cycles_per_vertex, context->cycles_by_vertex,
                context->max_cycles_per_edge, context->cycles_by_edge,
                context->start_cycle_order, start_i, &length_feasibility,
                required_cycles_to_use);
        }

        page_mutex_lock(&context->mutex);
        context->total_search_calls += local_search_calls;
        if (local_max_fit > context->best_max_fit) {
            context->best_max_fit = local_max_fit;
        }
        if (branch_found && !context->solution_found) {
            context->solution_found = true;
            memcpy(context->solution_used_cycles, used_cycles,
                   context->num_cycles * sizeof(bool));
            atomic_store(&context->stop_requested, true);
        }
        context->completed_start_cycles++;
        page_mutex_unlock(&context->mutex);
    }

    search_stop_requested = NULL;
    free(length_cache_without_required);
    free(length_cache_with_required);
    cycle_edge_conflicts_free();
    rotation_state_free();
    free(transitions_used);
    transitions_used = NULL;
    transitions_used_size = 0;
    free(directed_edge_remaining);
    directed_edge_remaining = NULL;
    num_edges_remaining = 0;
    free(vertex_uses);
    free(used_cycles);
    return PAGE_THREAD_RESULT;
}

void rotation_state_init(vertex_t num_vertices) {
    if (VERTEX_DEGREE <= 5) {
        rotation_next = NULL;
        rotation_prev = NULL;
        rotation_pair_count = NULL;
        rotation_state_size = 0;
        return;
    }

    rotation_state_size = (size_t)num_vertices * VERTEX_DEGREE;
    rotation_next = (vertex_t*)malloc(rotation_state_size * sizeof(vertex_t));
    rotation_prev = (vertex_t*)malloc(rotation_state_size * sizeof(vertex_t));
    rotation_pair_count = (degree_t*)malloc(num_vertices * sizeof(degree_t));
    assert(rotation_next != NULL && rotation_prev != NULL && rotation_pair_count != NULL,
           "Error allocating memory for the rotation system state\n");
    rotation_state_clear(num_vertices);
}

void rotation_state_clear(vertex_t num_vertices) {
    if (VERTEX_DEGREE <= 5) {
        return;
    }

    assert(rotation_state_size == (size_t)num_vertices * VERTEX_DEGREE,
           "Error clearing rotation system state with unexpected size\n");
    for (size_t i = 0; i < rotation_state_size; i++) {
        rotation_next[i] = MAX_VERTICES;
        rotation_prev[i] = MAX_VERTICES;
    }
    for (vertex_t i = 0; i < num_vertices; i++) {
        rotation_pair_count[i] = 0;
    }
}

void rotation_state_free(void) {
    free(rotation_next);
    free(rotation_prev);
    free(rotation_pair_count);
    rotation_next = NULL;
    rotation_prev = NULL;
    rotation_pair_count = NULL;
    rotation_state_size = 0;
}

bool rotation_transition_add(vertex_t center, degree_t prev_index, degree_t next_index) {
    if (VERTEX_DEGREE <= 5) {
        return true;
    }

    size_t source = (size_t)center * VERTEX_DEGREE + prev_index;
    size_t target = (size_t)center * VERTEX_DEGREE + next_index;
    if (prev_index == next_index || rotation_next[source] != MAX_VERTICES ||
        rotation_prev[target] != MAX_VERTICES) {
        return false;
    }

    vertex_t component_size = 1;
    bool closes_component = false;
    vertex_t cursor = next_index;
    while (rotation_next[(size_t)center * VERTEX_DEGREE + cursor] != MAX_VERTICES) {
        cursor = rotation_next[(size_t)center * VERTEX_DEGREE + cursor];
        component_size++;
        if (cursor == prev_index) {
            closes_component = true;
            break;
        }
        if (component_size > vertex_degrees[center]) {
            return false;
        }
    }

    if (closes_component && component_size < vertex_degrees[center]) {
        return false;
    }
    if (!closes_component && rotation_pair_count[center] + 1 == vertex_degrees[center]) {
        return false;
    }

    rotation_next[source] = next_index;
    rotation_prev[target] = prev_index;
    rotation_pair_count[center]++;
    return true;
}

void rotation_transition_remove(vertex_t center, degree_t prev_index, degree_t next_index) {
    if (VERTEX_DEGREE <= 5) {
        return;
    }

    size_t source = (size_t)center * VERTEX_DEGREE + prev_index;
    size_t target = (size_t)center * VERTEX_DEGREE + next_index;
    assert(rotation_next[source] == next_index && rotation_prev[target] == prev_index &&
               rotation_pair_count[center] > 0,
           "Error removing missing rotation system transition\n");
    rotation_next[source] = MAX_VERTICES;
    rotation_prev[target] = MAX_VERTICES;
    rotation_pair_count[center]--;
}

bool cycle_try_add_rotation_system(vertex_t* cycle, cycle_length_t cycle_length) {
    if (VERTEX_DEGREE <= 5) {
        return true;
    }

    for (cycle_length_t i = 0; i < cycle_length; i++) {
        vertex_t center = cycle[i];
        vertex_t prev = i == 0 ? cycle[cycle_length - 1] : cycle[i - 1];
        vertex_t next = i + 1 == cycle_length ? cycle[0] : cycle[i + 1];
        degree_t prev_index = adj_neighbor_index(full_adjacency_list, center, prev);
        degree_t next_index = adj_neighbor_index(full_adjacency_list, center, next);
        if (!rotation_transition_add(center, prev_index, next_index)) {
            for (cycle_length_t j = 0; j < i; j++) {
                vertex_t undo_center = cycle[j];
                vertex_t undo_prev = j == 0 ? cycle[cycle_length - 1] : cycle[j - 1];
                vertex_t undo_next = j + 1 == cycle_length ? cycle[0] : cycle[j + 1];
                degree_t undo_prev_index =
                    adj_neighbor_index(full_adjacency_list, undo_center, undo_prev);
                degree_t undo_next_index =
                    adj_neighbor_index(full_adjacency_list, undo_center, undo_next);
                rotation_transition_remove(undo_center, undo_prev_index, undo_next_index);
            }
            return false;
        }
    }

    return true;
}

void cycle_remove_rotation_system(vertex_t* cycle, cycle_length_t cycle_length) {
    if (VERTEX_DEGREE <= 5) {
        return;
    }

    for (cycle_length_t i = 0; i < cycle_length; i++) {
        vertex_t center = cycle[i];
        vertex_t prev = i == 0 ? cycle[cycle_length - 1] : cycle[i - 1];
        vertex_t next = i + 1 == cycle_length ? cycle[0] : cycle[i + 1];
        degree_t prev_index = adj_neighbor_index(full_adjacency_list, center, prev);
        degree_t next_index = adj_neighbor_index(full_adjacency_list, center, next);
        rotation_transition_remove(center, prev_index, next_index);
    }
}

cycle_index_t choose_start_edge(vertex_t num_vertices, adj_t adjacency_list,
                                cycle_index_t max_cycles_per_edge, cbe_t cycles_by_edge,
                                vertex_t* start_vertex, vertex_t* end_vertex) {
    bool found_edge = false;
    cycle_index_t min_cycle_options = MAX_CYCLES;

    for (vertex_t i = 0; i < num_vertices; i++) {
        vertex_t* neighbors = adj_get_neighbors(adjacency_list, i);
        for (degree_t j = 0; j < VERTEX_DEGREE; j++) {
            if (neighbors[j] == MAX_VERTICES) {
                continue;
            }

            cycle_index_t cycle_options;
            cbe_get_cycle_indices(cycles_by_edge, max_cycles_per_edge, i, neighbors[j],
                                  &cycle_options);

            if (!found_edge || cycle_options < min_cycle_options) {
                found_edge = true;
                *start_vertex = i;
                *end_vertex = neighbors[j];
                min_cycle_options = cycle_options;

                if (min_cycle_options == 0) {
                    break;
                }
            }
        }
        if (min_cycle_options == 0) {
            break;
        }
    }

    assert(found_edge, "Error finding a starting edge\n");
    return min_cycle_options;
}

bool path_has_reverse_transition(vertex_t* path, cycle_length_t path_length, vertex_t prev_vertex,
                                 vertex_t center_vertex, vertex_t next_vertex) {
    if (vertex_degrees[center_vertex] <= 2) {
        return false;
    }

    for (cycle_length_t i = 1; i + 1 < path_length; i++) {
        if (path[i - 1] == next_vertex && path[i] == center_vertex &&
            path[i + 1] == prev_vertex) {
            return true;
        }
    }
    return false;
}


vertex_t* adj_get_neighbors(adj_t adjacency_list, vertex_t vertex) {
    return &adjacency_list[vertex * VERTEX_DEGREE];
}

void graph_free(adj_t adjacency_list) {
    free(adjacency_list);
    free(full_adjacency_list);
    full_adjacency_list = NULL;
    free(vertex_degrees);
    vertex_degrees = NULL;
    free(initial_vertex_uses);
    initial_vertex_uses = NULL;
    free(directed_edge_ids);
    directed_edge_ids = NULL;
    free(directed_edge_remaining);
    directed_edge_remaining = NULL;
    free(directed_edge_lookup_keys);
    directed_edge_lookup_keys = NULL;
    free(directed_edge_lookup_ids);
    directed_edge_lookup_ids = NULL;
    directed_edge_lookup_capacity = 0;
    num_directed_edges = 0;
    num_edges_remaining = 0;
    cubic_exact_cover_mode = false;
    automorphism_list_free(&graph_automorphisms);
}

bool graph_has_edge(adj_t adjacency_list, vertex_t start_vertex, vertex_t end_vertex) {
    vertex_t* neighbors = adj_get_neighbors(adjacency_list, start_vertex);
    for (degree_t i = 0; i < VERTEX_DEGREE; i++) {
        if (neighbors[i] == end_vertex) {
            return true;
        }
    }
    return false;
}

void automorphism_list_free(automorphism_list_t* automorphisms) {
    free(automorphisms->maps);
    automorphisms->num_vertices = 0;
    automorphisms->count = 0;
    automorphisms->capacity = 0;
    automorphisms->maps = NULL;
}

bool automorphism_is_identity(vertex_t* map, vertex_t num_vertices) {
    for (vertex_t i = 0; i < num_vertices; i++) {
        if (map[i] != i) {
            return false;
        }
    }
    return true;
}

bool automorphism_list_contains(automorphism_list_t* automorphisms, vertex_t* map) {
    for (cycle_index_t i = 0; i < automorphisms->count; i++) {
        vertex_t* existing = &automorphisms->maps[i * automorphisms->num_vertices];
        if (memcmp(existing, map, automorphisms->num_vertices * sizeof(vertex_t)) == 0) {
            return true;
        }
    }
    return false;
}

void automorphism_list_add_if_new(automorphism_list_t* automorphisms, vertex_t* map) {
    if (automorphisms->count >= automorphisms->capacity ||
        automorphism_is_identity(map, automorphisms->num_vertices) ||
        automorphism_list_contains(automorphisms, map)) {
        return;
    }

    memcpy(&automorphisms->maps[automorphisms->count * automorphisms->num_vertices], map,
           automorphisms->num_vertices * sizeof(vertex_t));
    automorphisms->count++;
}

vertex_t* automorphism_distances_generate(vertex_t num_vertices, adj_t adjacency_list) {
    vertex_t* distances =
        (vertex_t*)malloc((size_t)num_vertices * num_vertices * sizeof(vertex_t));
    vertex_t* queue = (vertex_t*)malloc(num_vertices * sizeof(vertex_t));
    assert(distances != NULL && queue != NULL,
           "Error allocating memory for automorphism distances\n");

    for (vertex_t source = 0; source < num_vertices; source++) {
        vertex_t* source_distances = &distances[(size_t)source * num_vertices];
        for (vertex_t i = 0; i < num_vertices; i++) {
            source_distances[i] = MAX_VERTICES;
        }

        cycle_index_t head = 0;
        cycle_index_t tail = 0;
        source_distances[source] = 0;
        queue[tail++] = source;
        while (head < tail) {
            vertex_t vertex = queue[head++];
            vertex_t* neighbors = adj_get_neighbors(adjacency_list, vertex);
            for (degree_t i = 0; i < VERTEX_DEGREE; i++) {
                vertex_t neighbor = neighbors[i];
                if (neighbor == MAX_VERTICES ||
                    source_distances[neighbor] != MAX_VERTICES) {
                    continue;
                }
                source_distances[neighbor] = source_distances[vertex] + 1;
                queue[tail++] = neighbor;
            }
        }
    }

    free(queue);
    return distances;
}

uint64_t automorphism_mix(uint64_t hash, uint64_t value) {
    hash ^= value + 0x9e3779b97f4a7c15ULL + (hash << 6) + (hash >> 2);
    return hash;
}

uint64_t* automorphism_vertex_signatures_generate(vertex_t num_vertices, vertex_t* distances) {
    uint64_t* signatures = (uint64_t*)malloc(num_vertices * sizeof(uint64_t));
    vertex_t* distance_counts = (vertex_t*)malloc((num_vertices + 1) * sizeof(vertex_t));
    assert(signatures != NULL && distance_counts != NULL,
           "Error allocating memory for automorphism signatures\n");

    for (vertex_t vertex = 0; vertex < num_vertices; vertex++) {
        memset(distance_counts, 0, (num_vertices + 1) * sizeof(vertex_t));
        for (vertex_t other = 0; other < num_vertices; other++) {
            vertex_t distance = distances[(size_t)vertex * num_vertices + other];
            if (distance == MAX_VERTICES || distance > num_vertices) {
                distance = num_vertices;
            }
            distance_counts[distance]++;
        }

        uint64_t hash = 1469598103934665603ULL;
        hash = automorphism_mix(hash, vertex_degrees[vertex]);
        for (vertex_t distance = 0; distance <= num_vertices; distance++) {
            hash = automorphism_mix(hash, distance_counts[distance]);
        }
        signatures[vertex] = hash;
    }

    free(distance_counts);
    return signatures;
}

bool automorphism_candidate_ok(automorphism_search_t* state, vertex_t domain_vertex,
                               vertex_t image_vertex) {
    if (state->inverse_map[image_vertex] != MAX_VERTICES ||
        vertex_degrees[domain_vertex] != vertex_degrees[image_vertex] ||
        state->vertex_signatures[domain_vertex] != state->vertex_signatures[image_vertex]) {
        return false;
    }

    for (vertex_t other = 0; other < state->num_vertices; other++) {
        vertex_t other_image = state->map[other];
        if (other_image == MAX_VERTICES) {
            continue;
        }
        if (state->distances[(size_t)domain_vertex * state->num_vertices + other] !=
            state->distances[(size_t)image_vertex * state->num_vertices + other_image]) {
            return false;
        }
        if (graph_has_edge(state->adjacency_list, domain_vertex, other) !=
            graph_has_edge(state->adjacency_list, image_vertex, other_image)) {
            return false;
        }
    }

    return true;
}

void automorphism_assign(automorphism_search_t* state, vertex_t domain_vertex,
                         vertex_t image_vertex) {
    state->map[domain_vertex] = image_vertex;
    state->inverse_map[image_vertex] = domain_vertex;
}

void automorphism_unassign(automorphism_search_t* state, vertex_t domain_vertex,
                           vertex_t image_vertex) {
    state->map[domain_vertex] = MAX_VERTICES;
    state->inverse_map[image_vertex] = MAX_VERTICES;
}

bool automorphism_assign_fixed(automorphism_search_t* state, vertex_t domain_vertex,
                               vertex_t image_vertex) {
    if (state->map[domain_vertex] != MAX_VERTICES) {
        return state->map[domain_vertex] == image_vertex;
    }
    if (!automorphism_candidate_ok(state, domain_vertex, image_vertex)) {
        return false;
    }
    automorphism_assign(state, domain_vertex, image_vertex);
    return true;
}

bool automorphism_valid(automorphism_search_t* state) {
    for (vertex_t vertex = 0; vertex < state->num_vertices; vertex++) {
        if (state->map[vertex] == MAX_VERTICES) {
            return false;
        }
        vertex_t* neighbors = adj_get_neighbors(state->adjacency_list, vertex);
        for (degree_t i = 0; i < VERTEX_DEGREE; i++) {
            vertex_t neighbor = neighbors[i];
            if (neighbor != MAX_VERTICES &&
                !graph_has_edge(state->adjacency_list, state->map[vertex],
                                state->map[neighbor])) {
                return false;
            }
        }
    }
    return true;
}

vertex_t automorphism_choose_domain(automorphism_search_t* state,
                                    cycle_index_t* num_candidates) {
    vertex_t best_vertex = MAX_VERTICES;
    cycle_index_t best_candidates = MAX_CYCLES;

    for (vertex_t vertex = 0; vertex < state->num_vertices; vertex++) {
        if (state->map[vertex] != MAX_VERTICES) {
            continue;
        }

        cycle_index_t candidates = 0;
        for (vertex_t image = 0; image < state->num_vertices; image++) {
            if (automorphism_candidate_ok(state, vertex, image)) {
                candidates++;
            }
        }

        if (candidates < best_candidates) {
            best_vertex = vertex;
            best_candidates = candidates;
            if (best_candidates == 0) {
                break;
            }
        }
    }

    *num_candidates = best_candidates;
    return best_vertex;
}

bool automorphism_search_dfs(automorphism_search_t* state) {
    if (state->calls >= state->call_limit) {
        return false;
    }
    state->calls++;

    cycle_index_t num_candidates;
    vertex_t domain_vertex = automorphism_choose_domain(state, &num_candidates);
    if (domain_vertex == MAX_VERTICES) {
        if (!automorphism_valid(state)) {
            return false;
        }
        memcpy(state->result, state->map, state->num_vertices * sizeof(vertex_t));
        return true;
    }
    if (num_candidates == 0) {
        return false;
    }

    for (vertex_t image_vertex = 0; image_vertex < state->num_vertices; image_vertex++) {
        if (!automorphism_candidate_ok(state, domain_vertex, image_vertex)) {
            continue;
        }

        automorphism_assign(state, domain_vertex, image_vertex);
        if (automorphism_search_dfs(state)) {
            return true;
        }
        automorphism_unassign(state, domain_vertex, image_vertex);
    }

    return false;
}

bool automorphism_find_one(vertex_t num_vertices, adj_t adjacency_list, vertex_t* distances,
                           uint64_t* vertex_signatures, vertex_t* fixed_domain,
                           vertex_t* fixed_image, vertex_t fixed_count,
                           uint64_t call_limit, vertex_t* result, uint64_t* calls) {
    automorphism_search_t state = {
        .num_vertices = num_vertices,
        .adjacency_list = adjacency_list,
        .distances = distances,
        .vertex_signatures = vertex_signatures,
        .map = (vertex_t*)malloc(num_vertices * sizeof(vertex_t)),
        .inverse_map = (vertex_t*)malloc(num_vertices * sizeof(vertex_t)),
        .result = result,
        .calls = 0,
        .call_limit = call_limit,
    };
    assert(state.map != NULL && state.inverse_map != NULL,
           "Error allocating memory for automorphism search\n");
    for (vertex_t i = 0; i < num_vertices; i++) {
        state.map[i] = MAX_VERTICES;
        state.inverse_map[i] = MAX_VERTICES;
    }

    bool fixed_ok = true;
    for (vertex_t i = 0; i < fixed_count; i++) {
        if (!automorphism_assign_fixed(&state, fixed_domain[i], fixed_image[i])) {
            fixed_ok = false;
            break;
        }
    }

    bool found = fixed_ok && automorphism_search_dfs(&state);
    *calls = state.calls;
    free(state.map);
    free(state.inverse_map);
    return found;
}

void automorphism_generate(vertex_t num_vertices, adj_t adjacency_list,
                           automorphism_list_t* automorphisms) {
    automorphism_list_free(automorphisms);
    automorphisms->num_vertices = num_vertices;
    automorphisms->capacity = AUTOMORPHISM_LIMIT;
    automorphisms->count = 0;
    automorphisms->maps =
        (vertex_t*)malloc((size_t)AUTOMORPHISM_LIMIT *
                          (num_vertices == 0 ? 1 : num_vertices) * sizeof(vertex_t));
    assert(automorphisms->maps != NULL,
           "Error allocating memory for graph automorphisms\n");

    if (num_vertices == 0 || num_vertices > AUTOMORPHISM_VERTEX_LIMIT ||
        AUTOMORPHISM_LIMIT == 0) {
        return;
    }

    vertex_t* distances = automorphism_distances_generate(num_vertices, adjacency_list);
    uint64_t* vertex_signatures =
        automorphism_vertex_signatures_generate(num_vertices, distances);
    vertex_t* result = (vertex_t*)malloc(num_vertices * sizeof(vertex_t));
    assert(result != NULL, "Error allocating memory for an automorphism result\n");

    uint64_t total_calls = 0;
    vertex_t root = 0;
    vertex_t root_neighbor = MAX_VERTICES;
    vertex_t* root_neighbors = adj_get_neighbors(adjacency_list, root);
    for (degree_t i = 0; i < VERTEX_DEGREE; i++) {
        if (root_neighbors[i] != MAX_VERTICES) {
            root_neighbor = root_neighbors[i];
            break;
        }
    }

    for (vertex_t target = 0; target < num_vertices &&
                                automorphisms->count < automorphisms->capacity &&
                                total_calls < AUTOMORPHISM_TOTAL_CALL_LIMIT;
         target++) {
        if (vertex_signatures[root] != vertex_signatures[target]) {
            continue;
        }
        vertex_t fixed_domain[1] = {root};
        vertex_t fixed_image[1] = {target};
        uint64_t calls;
        uint64_t remaining = AUTOMORPHISM_TOTAL_CALL_LIMIT - total_calls;
        uint64_t call_limit =
            remaining < AUTOMORPHISM_SEED_CALL_LIMIT ? remaining : AUTOMORPHISM_SEED_CALL_LIMIT;
        if (automorphism_find_one(num_vertices, adjacency_list, distances, vertex_signatures,
                                  fixed_domain, fixed_image, 1, call_limit, result, &calls)) {
            automorphism_list_add_if_new(automorphisms, result);
        }
        total_calls += calls;
    }

    if (root_neighbor != MAX_VERTICES) {
        for (vertex_t target = 0; target < num_vertices &&
                                    automorphisms->count < automorphisms->capacity &&
                                    total_calls < AUTOMORPHISM_TOTAL_CALL_LIMIT;
             target++) {
            if (vertex_signatures[root] != vertex_signatures[target]) {
                continue;
            }
            vertex_t* target_neighbors = adj_get_neighbors(adjacency_list, target);
            for (degree_t i = 0; i < VERTEX_DEGREE &&
                                     automorphisms->count < automorphisms->capacity &&
                                     total_calls < AUTOMORPHISM_TOTAL_CALL_LIMIT;
                 i++) {
                vertex_t target_neighbor = target_neighbors[i];
                if (target_neighbor == MAX_VERTICES ||
                    vertex_signatures[root_neighbor] != vertex_signatures[target_neighbor]) {
                    continue;
                }

                vertex_t fixed_domain[2] = {root, root_neighbor};
                vertex_t fixed_image[2] = {target, target_neighbor};
                uint64_t calls;
                uint64_t remaining = AUTOMORPHISM_TOTAL_CALL_LIMIT - total_calls;
                uint64_t call_limit = remaining < AUTOMORPHISM_SEED_CALL_LIMIT
                                          ? remaining
                                          : AUTOMORPHISM_SEED_CALL_LIMIT;
                if (automorphism_find_one(num_vertices, adjacency_list, distances,
                                          vertex_signatures, fixed_domain, fixed_image, 2,
                                          call_limit, result, &calls)) {
                    automorphism_list_add_if_new(automorphisms, result);
                }
                total_calls += calls;
            }
        }
    }


    free(result);
    free(distances);
    free(vertex_signatures);
}

uint32_t directed_edge_key(vertex_t start_vertex, vertex_t end_vertex) {
    assert(start_vertex != MAX_VERTICES && end_vertex != MAX_VERTICES,
           "Error: invalid directed edge key %" PRIvertex_t " -> %" PRIvertex_t "\n",
           start_vertex, end_vertex);
    return ((uint32_t)start_vertex << 16) | end_vertex;
}

cycle_index_t directed_edge_lookup_slot(uint32_t key, bool allow_empty) {
    assert(directed_edge_lookup_capacity > 0 && directed_edge_lookup_keys != NULL,
           "Error: directed edge lookup has not been initialized\n");
    cycle_index_t slot =
        (cycle_index_t)((key * 2654435761u) & (directed_edge_lookup_capacity - 1));
    while (directed_edge_lookup_keys[slot] != key) {
        if (directed_edge_lookup_keys[slot] == DIRECTED_EDGE_LOOKUP_EMPTY) {
            if (allow_empty) {
                return slot;
            }
            assert(false, "Error finding directed edge key %" PRIu32 "\n", key);
        }
        slot = (slot + 1) & (directed_edge_lookup_capacity - 1);
    }
    return slot;
}

void directed_edge_lookup_insert(vertex_t start_vertex, vertex_t end_vertex,
                                 cycle_index_t edge_id) {
    uint32_t key = directed_edge_key(start_vertex, end_vertex);
    cycle_index_t slot = directed_edge_lookup_slot(key, true);
    assert(directed_edge_lookup_keys[slot] == DIRECTED_EDGE_LOOKUP_EMPTY,
           "Error: duplicate directed edge %" PRIvertex_t " -> %" PRIvertex_t "\n",
           start_vertex, end_vertex);
    directed_edge_lookup_keys[slot] = key;
    directed_edge_lookup_ids[slot] = edge_id;
}

bool adj_try_edge_id(adj_t adjacency_list, vertex_t start_vertex, vertex_t end_vertex,
                     cycle_index_t* edge_id) {
    (void)adjacency_list;
    uint32_t key = directed_edge_key(start_vertex, end_vertex);
    cycle_index_t slot = directed_edge_lookup_slot(key, true);
    if (directed_edge_lookup_keys[slot] == DIRECTED_EDGE_LOOKUP_EMPTY) {
        return false;
    }
    *edge_id = directed_edge_lookup_ids[slot];
    return true;
}

cycle_index_t adj_edge_id(adj_t adjacency_list, vertex_t start_vertex, vertex_t end_vertex) {
    cycle_index_t edge_id;
    assert(adj_try_edge_id(adjacency_list, start_vertex, end_vertex, &edge_id),
           "Error finding directed edge %" PRIvertex_t " -> %" PRIvertex_t "\n",
           start_vertex, end_vertex);
    return edge_id;
}

bool adj_slot_has_edge(vertex_t start_vertex, degree_t neighbor_index) {
    cycle_index_t edge_id = directed_edge_ids[start_vertex * VERTEX_DEGREE + neighbor_index];
    return edge_id != MAX_CYCLES && directed_edge_remaining[edge_id];
}

void adj_remove_edge(adj_t adjacency_list, vertex_t start_vertex, vertex_t end_vertex) {
    cycle_index_t edge_id = adj_edge_id(adjacency_list, start_vertex, end_vertex);
    assert(directed_edge_remaining[edge_id],
           "Error: directed edge %" PRIvertex_t " -> %" PRIvertex_t
           " was removed twice\n",
           start_vertex, end_vertex);
    num_edges_remaining -= 1;
    directed_edge_remaining[edge_id] = false;
}


void adj_undo_remove_edge(adj_t adjacency_list, vertex_t start_vertex, vertex_t end_vertex) {
    cycle_index_t edge_id = adj_edge_id(adjacency_list, start_vertex, end_vertex);
    assert(!directed_edge_remaining[edge_id],
           "Error: directed edge %" PRIvertex_t " -> %" PRIvertex_t
           " was restored before being removed\n",
           start_vertex, end_vertex);
    num_edges_remaining += 1;
    directed_edge_remaining[edge_id] = true;
}


struct fifo {
    vertex_t* data;
    cycle_index_t head;
    cycle_index_t tail;
    cycle_index_t capacity;
    cycle_length_t path_length;
};
void fifo_init(struct fifo* fifo, cycle_index_t initial_capacity, cycle_length_t path_length) {
    fifo->data = (vertex_t*)malloc(initial_capacity * path_length * sizeof(vertex_t));
    assert(fifo->data != NULL, "Error allocating memory for the fifo\n");
    fifo->head = 0;
    fifo->tail = 0;
    fifo->capacity = initial_capacity;
    fifo->path_length = path_length;
}
bool fifo_empty(struct fifo* fifo) { return fifo->head == fifo->tail; }
void fifo_push(struct fifo* fifo, vertex_t* path) {
    if ((fifo->tail + 1) % fifo->capacity == fifo->head) {
        
        vertex_t* new_data =
            (vertex_t*)malloc(2 * fifo->capacity * fifo->path_length * sizeof(vertex_t));
        assert(new_data != NULL, "Error allocating memory for the fifo\n");
        for (cycle_index_t i = 0; i < fifo->capacity; i++) {
            for (cycle_length_t j = 0; j < fifo->path_length; j++) {
                new_data[i * fifo->path_length + j] =
                    fifo->data[((fifo->head + i) % fifo->capacity) * fifo->path_length + j];
            }
        }
        free(fifo->data);
        fifo->data = new_data;
        fifo->head = 0;
        fifo->tail = fifo->capacity - 1;
        fifo->capacity *= 2;
    }

    for (cycle_length_t i = 0; i < fifo->path_length; i++) {
        fifo->data[fifo->tail * fifo->path_length + i] = path[i];
    }
    fifo->tail = (fifo->tail + 1) % fifo->capacity;
}
void fifo_pop(struct fifo* fifo, vertex_t* path) {
    for (cycle_length_t i = 0; i < fifo->path_length; i++) {
        path[i] = fifo->data[fifo->head * fifo->path_length + i];
    }
    fifo->head = (fifo->head + 1) % fifo->capacity;
}
cycle_index_t fifo_size(struct fifo* fifo) {
    return (fifo->tail - fifo->head + fifo->capacity) % fifo->capacity;
}
void fifo_free(struct fifo* fifo) {
    free(fifo->data);
    fifo->data = NULL;
}

cycles_t cycle_generate(adj_t adjacency_list, vertex_t num_vertices, cycle_length_t cycle_length,
                        cycle_index_t* num_cycles) {
    vertex_t* buffer = (vertex_t*)malloc((cycle_length + 2) * sizeof(vertex_t));
    assert(buffer != NULL, "Error allocating memory for the buffer\n");

    struct fifo cycle_list;
    fifo_init(&cycle_list, cycle_length * num_vertices, cycle_length + 2);
    struct fifo queue;
    fifo_init(&queue, cycle_length * num_vertices, cycle_length + 2);

    for (cycle_length_t i = 2; i < cycle_length + 2; i++) {
        buffer[i] = 0;
    }
    for (vertex_t i = 0; i < num_vertices; i++) {
        buffer[0] = 1;
        buffer[1] = i;
        fifo_push(&queue, buffer);
    }
    while (!fifo_empty(&queue)) {
        fifo_pop(&queue, buffer);
        cycle_length_t path_length = buffer[0];
        vertex_t* path = &buffer[1];
        vertex_t* neighbors = adj_get_neighbors(adjacency_list, path[path_length - 1]);
        if (path_length == cycle_length) {
            for (degree_t i = 0; i < VERTEX_DEGREE; i++) {
                if (neighbors[i] != path[0]) {
                    continue;  
                }
                if (path[1] == path[path_length - 1] || path[path_length - 2] == path[0]) {
                    break;
                }

                bool repeated_edge = false;
                for (cycle_length_t j = 0; j < path_length - 1; j++) {
                    if (path[j] == path[path_length - 1] && path[j + 1] == path[0]) {
                        repeated_edge = true;
                        break;
                    }
                }
                if (repeated_edge) {
                    break;
                }

                if (path_has_reverse_transition(path, path_length, path[path_length - 2],
                                                path[path_length - 1], path[0]) ||
                    path_has_reverse_transition(path, path_length, path[path_length - 1], path[0],
                                                path[1])) {
                    break;
                }
                buffer[cycle_length + 1] = path[0];
                fifo_push(&cycle_list, buffer);
                break;
            }
        } else {
            for (degree_t i = 0; i < VERTEX_DEGREE; i++) {
                vertex_t neighbor = neighbors[i];
                if (neighbor == MAX_VERTICES) continue;
                if (neighbor < path[0]) {
                    continue;
                }
                if (path_length >= 2 && neighbor == path[path_length - 2]) {
                    continue;
                }

                bool repeated_edge = false;
                for (cycle_length_t j = 0; j < path_length - 1; j++) {
                    if (path[j] == path[path_length - 1] && path[j + 1] == neighbor) {
                        repeated_edge = true;
                        break;
                    }
                }
                if (repeated_edge) {
                    continue;
                }

                if (path_length >= 2 &&
                    path_has_reverse_transition(path, path_length, path[path_length - 2],
                                                path[path_length - 1], neighbor)) {
                    continue;
                }

                buffer[0] = path_length + 1;
                path[path_length] = neighbor;
                fifo_push(&queue, buffer);
            }
        }
    }

    fifo_free(&queue);
    free(buffer);
    *num_cycles = fifo_size(&cycle_list);
    vertex_t* cycles = NULL;
    if (*num_cycles != 0) {
        cycles = (vertex_t*)realloc(cycle_list.data,
                                    *num_cycles * (cycle_length + 2) * sizeof(vertex_t));
        assert(cycles != NULL, "Error reallocating memory for the cycles\n");
    }
    cycle_list.data = NULL;
    fifo_free(&cycle_list);


    return cycles;
}

vertex_t* cycle_get(cycles_t cycles, cycle_length_t max_cycle_length, cycle_index_t cycle_index,
                    cycle_length_t* cycle_length) {
    vertex_t* row = &cycles[cycle_index * (max_cycle_length + 2)];
    if (cycle_length != NULL) {
        *cycle_length = row[0];
    }
    return &row[1];
}

cycle_index_t* cbv_generate(vertex_t num_vertices, cycles_t cycles, cycle_index_t num_cycles,
                            cycle_length_t max_cycle_length, cycle_index_t* max_cycles_per_vertex) {
    
    cycle_index_t* cycles_per_vertex = (cycle_index_t*)malloc(num_vertices * sizeof(cycle_index_t));
    assert(cycles_per_vertex != NULL, "Error allocating memory for the cycles per vertex\n");
    for (vertex_t i = 0; i < num_vertices; i++) {
        cycles_per_vertex[i] = 0;
    }
    cycle_length_t cycle_length;
    for (cycle_index_t i = 0; i < num_cycles; i++) {
        vertex_t* cycle = cycle_get(cycles, max_cycle_length, i, &cycle_length);
        for (cycle_length_t j = 0; j < cycle_length; j++) {
            cycles_per_vertex[cycle[j]]++;
        }
    }

    
    *max_cycles_per_vertex = 0;
    for (vertex_t i = 0; i < num_vertices; i++) {
        if (cycles_per_vertex[i] > *max_cycles_per_vertex) {
            *max_cycles_per_vertex = cycles_per_vertex[i];
        }
    }

    cbv_t cycles_by_vertex =
        (cbv_t)malloc(num_vertices * (*max_cycles_per_vertex + 1) * sizeof(cycle_index_t));
    assert(cycles_by_vertex != NULL, "Error allocating memory for the cycles by vertex\n");

    
    for (vertex_t i = 0; i < num_vertices; i++) {
        cycles_by_vertex[i * (*max_cycles_per_vertex + 1)] = cycles_per_vertex[i];
        cycle_index_t num_cycles_for_vertex = 0;
        for (cycle_index_t j = 0; j < num_cycles && num_cycles_for_vertex < cycles_per_vertex[i];
             j++) {
            bool cycle_contains_vertex = false;
            vertex_t* cycle = cycle_get(cycles, max_cycle_length, j, &cycle_length);
            for (cycle_length_t k = 0; k < cycle_length; k++) {
                if (cycle[k] == i) {
                    cycle_contains_vertex = true;
                    break;
                }
            }
            if (cycle_contains_vertex) {
                cycles_by_vertex[i * (*max_cycles_per_vertex + 1) + num_cycles_for_vertex + 1] = j;
                num_cycles_for_vertex++;
            }
        }
        cycles_by_vertex[i * (*max_cycles_per_vertex + 1)] = num_cycles_for_vertex;
    }


    free(cycles_per_vertex);
    return cycles_by_vertex;
}

cycle_index_t* cbv_get_cycle_indices(cbv_t cycles_by_vertex, cycle_index_t max_cycles_per_vertex,
                                     vertex_t vertex, cycle_index_t* num_cycles) {
    cycle_index_t* row = &cycles_by_vertex[vertex * (max_cycles_per_vertex + 1)];
    *num_cycles = row[0];
    return &row[1];
}

cycle_index_t* cbe_generate(vertex_t num_vertices, cycles_t cycles, cycle_index_t num_cycles,
                            cycle_length_t max_cycle_length, cycle_index_t* max_cycles_per_edge) {
    cycle_index_t edge_slots = num_vertices * VERTEX_DEGREE;
    cycle_index_t* cycles_per_edge = (cycle_index_t*)calloc(edge_slots, sizeof(cycle_index_t));
    assert(cycles_per_edge != NULL, "Error allocating memory for cycles per edge\n");

    cycle_length_t cycle_length;
    for (cycle_index_t i = 0; i < num_cycles; i++) {
        vertex_t* cycle = cycle_get(cycles, max_cycle_length, i, &cycle_length);
        for (cycle_length_t j = 0; j < cycle_length; j++) {
            degree_t neighbor_index =
                adj_neighbor_index(full_adjacency_list, cycle[j], cycle[j + 1]);
            cycles_per_edge[cycle[j] * VERTEX_DEGREE + neighbor_index]++;
        }
    }

    *max_cycles_per_edge = 0;
    for (cycle_index_t i = 0; i < edge_slots; i++) {
        if (cycles_per_edge[i] > *max_cycles_per_edge) {
            *max_cycles_per_edge = cycles_per_edge[i];
        }
    }

    cbe_t cycles_by_edge =
        (cbe_t)malloc(edge_slots * (*max_cycles_per_edge + 1) * sizeof(cycle_index_t));
    cycle_index_t* edge_fill = (cycle_index_t*)calloc(edge_slots, sizeof(cycle_index_t));
    assert(cycles_by_edge != NULL && edge_fill != NULL,
           "Error allocating memory for cycles by edge\n");

    for (cycle_index_t i = 0; i < edge_slots; i++) {
        cycles_by_edge[i * (*max_cycles_per_edge + 1)] = cycles_per_edge[i];
    }

    for (cycle_index_t i = 0; i < num_cycles; i++) {
        vertex_t* cycle = cycle_get(cycles, max_cycle_length, i, &cycle_length);
        for (cycle_length_t j = 0; j < cycle_length; j++) {
            degree_t neighbor_index =
                adj_neighbor_index(full_adjacency_list, cycle[j], cycle[j + 1]);
            cycle_index_t edge_index = cycle[j] * VERTEX_DEGREE + neighbor_index;
            cycle_index_t fill = edge_fill[edge_index]++;
            cycles_by_edge[edge_index * (*max_cycles_per_edge + 1) + fill + 1] = i;
        }
    }

    free(cycles_per_edge);
    free(edge_fill);
    return cycles_by_edge;
}

cycle_index_t* cbe_get_cycle_indices(cbe_t cycles_by_edge, cycle_index_t max_cycles_per_edge,
                                     vertex_t start_vertex, vertex_t end_vertex,
                                     cycle_index_t* num_cycles) {
    degree_t neighbor_index = adj_neighbor_index(full_adjacency_list, start_vertex, end_vertex);
    cycle_index_t* row =
        &cycles_by_edge[(start_vertex * VERTEX_DEGREE + neighbor_index) *
                        (max_cycles_per_edge + 1)];
    *num_cycles = row[0];
    return &row[1];
}

cycle_index_t cycle_image_index(cycles_t cycles, cycle_length_t max_cycle_length,
                                cbe_t cycles_by_edge, cycle_index_t max_cycles_per_edge,
                                cycle_index_t cycle_index, vertex_t* automorphism,
                                vertex_t* image) {
    cycle_length_t cycle_length;
    vertex_t* cycle = cycle_get(cycles, max_cycle_length, cycle_index, &cycle_length);
    vertex_t min_vertex = MAX_VERTICES;
    for (cycle_length_t i = 0; i < cycle_length; i++) {
        image[i] = automorphism[cycle[i]];
        if (image[i] < min_vertex) {
            min_vertex = image[i];
        }
    }

    for (cycle_length_t start = 0; start < cycle_length; start++) {
        if (image[start] != min_vertex) {
            continue;
        }

        cycle_index_t num_cycles_for_edge;
        cycle_index_t* cycle_indices = cbe_get_cycle_indices(
            cycles_by_edge, max_cycles_per_edge, image[start],
            image[(start + 1) % cycle_length], &num_cycles_for_edge);
        for (cycle_index_t i = 0; i < num_cycles_for_edge; i++) {
            cycle_index_t candidate_index = cycle_indices[i];
            cycle_length_t candidate_length;
            vertex_t* candidate =
                cycle_get(cycles, max_cycle_length, candidate_index, &candidate_length);
            if (candidate_length != cycle_length) {
                continue;
            }

            bool matches = true;
            for (cycle_length_t j = 0; j < cycle_length; j++) {
                if (candidate[j] != image[(start + j) % cycle_length]) {
                    matches = false;
                    break;
                }
            }
            if (matches) {
                return candidate_index;
            }
        }
    }

    return MAX_CYCLES;
}

cycle_index_t* start_cycles_prune_by_symmetry(cycles_t cycles,
                                              cycle_length_t max_cycle_length,
                                              cycle_index_t num_cycles,
                                              cbe_t cycles_by_edge,
                                              cycle_index_t max_cycles_per_edge,
                                              cycle_index_t* raw_start_cycles,
                                              cycle_index_t raw_start_count,
                                              cycle_index_t* pruned_start_count) {
    
    
    
    cycle_index_t* start_cycles =
        (cycle_index_t*)malloc((raw_start_count == 0 ? 1 : raw_start_count) *
                               sizeof(cycle_index_t));
    assert(start_cycles != NULL, "Error allocating memory for pruned start cycles\n");
    *pruned_start_count = 0;

    if (raw_start_count == 0) {
        return start_cycles;
    }
    if (graph_automorphisms.count == 0 || raw_start_count == 1) {
        memcpy(start_cycles, raw_start_cycles, raw_start_count * sizeof(cycle_index_t));
        *pruned_start_count = raw_start_count;
        return start_cycles;
    }

    bool* is_start_cycle = (bool*)calloc((num_cycles == 0 ? 1 : num_cycles), sizeof(bool));
    bool* start_cycle_seen = (bool*)calloc((num_cycles == 0 ? 1 : num_cycles), sizeof(bool));
    cycle_index_t* queue =
        (cycle_index_t*)malloc(raw_start_count * sizeof(cycle_index_t));
    vertex_t* image = (vertex_t*)malloc((max_cycle_length == 0 ? 1 : max_cycle_length) *
                                        sizeof(vertex_t));
    assert(is_start_cycle != NULL && start_cycle_seen != NULL && queue != NULL &&
               image != NULL,
           "Error allocating memory for start cycle symmetry pruning\n");
    for (cycle_index_t i = 0; i < raw_start_count; i++) {
        is_start_cycle[raw_start_cycles[i]] = true;
    }

    for (cycle_index_t i = 0; i < raw_start_count; i++) {
        cycle_index_t cycle_index = raw_start_cycles[i];
        if (start_cycle_seen[cycle_index]) {
            continue;
        }

        start_cycles[*pruned_start_count] = cycle_index;
        (*pruned_start_count)++;

        cycle_index_t head = 0;
        cycle_index_t tail = 0;
        start_cycle_seen[cycle_index] = true;
        queue[tail++] = cycle_index;
        while (head < tail) {
            cycle_index_t current = queue[head++];
            for (cycle_index_t automorphism_index = 0;
                 automorphism_index < graph_automorphisms.count; automorphism_index++) {
                vertex_t* automorphism =
                    &graph_automorphisms.maps[automorphism_index *
                                               graph_automorphisms.num_vertices];
                cycle_index_t image_index =
                    cycle_image_index(cycles, max_cycle_length, cycles_by_edge,
                                      max_cycles_per_edge, current, automorphism, image);
                if (image_index == MAX_CYCLES || !is_start_cycle[image_index] ||
                    start_cycle_seen[image_index]) {
                    continue;
                }

                start_cycle_seen[image_index] = true;
                queue[tail++] = image_index;
            }
        }
    }


    free(is_start_cycle);
    free(start_cycle_seen);
    free(queue);
    free(image);
    return start_cycles;
}

#undef assert


/* MultiGenus core. Copyright (C) 2026 Gunnar Brinkmann. */
#define leer 255

#ifdef LONG
#define knoten 128
#define d_kanten 1024  
#define LONGTYPE unsigned __int128
#else
#define knoten 64
#define LONGTYPE unsigned long long
#define d_kanten 512  
#endif

typedef unsigned char GRAPH[knoten + 1][knoten];
typedef unsigned char ADJAZENZ[knoten + 1];


typedef struct K {
  unsigned short ursprung; 
  unsigned short name;     

  unsigned char is_embedded;
  LONGTYPE *faceleft;
  struct K *prev;   
  struct K *next;   
  struct K *invers; 
} KANTE;


KANTE edges[d_kanten];  


KANTE red_edges[4 * knoten];  
                              
KANTE *last_edge;
int em_vertices = 0, em_faces = 0;
int knotenzahl;
KANTE *firstedge[knoten + 1];
ADJAZENZ adj_embedded;
LONGTYPE faces[d_kanten / 3];
LONGTYPE *face_pointer[d_kanten / 3];


LONGTYPE rememberfaces[d_kanten];


int globalnv, globalne, edgelimit = 0;
int compute_lower_bound = 1;

int reduce2 = 1;  
int reconstruct[knoten + 1][4], number_reconstruct;


int bfsnummer[knoten + 1], invbfsnummer[knoten + 1];
int good_approx[100] = {0};

#define bit(i) (((LONGTYPE)1) << ((i) - 1))
#define DELBIT(a, i) ((a) &= (~bit(i)))
#define SETBIT(a, i) ((a) |= (bit(i)))
#define IS_SET(a, i) ((a) & (bit(i)))

#define ULBIT(i) ((1UL) << ((i) - 1))
#define FFSL(x) (__builtin_ffsl(x))

#define LESS_THAN_2BIT(a) (((a) & ((a) - (LONGTYPE)1)) == ((LONGTYPE)0))
#define ATLEAST2BIT(a) ((a) & ((a) - (LONGTYPE)1))

#define MIN0(a) ((a) < 0 ? 0 : (a))

int edgemarks_m[knoten][knoten] = {0};
int edgemark_m = 1;
#define RESET_EDGEMARKS                                     \
  {                                                         \
    int i, j;                                               \
    if (edgemark_m < INT_MAX)                               \
      edgemark_m++;                                         \
    else {                                                  \
      edgemark_m = 1;                                       \
      for (i = 0; i < knoten; i++)                          \
        for (j = 0; j < knoten; j++) edgemarks_m[i][j] = 0; \
    }                                                       \
  }
#define SET_EDGE_MARK(i, j) (edgemarks_m[(i) - 1][(j) - 1] = edgemark_m)
#define IS_EDGE_MARKED(i, j) (edgemarks_m[(i) - 1][(j) - 1] == edgemark_m)
#define NOT_EDGE_MARKED(i, j) (edgemarks_m[(i) - 1][(j) - 1] != edgemark_m)
#define EDGE_MARKED(i, j) (edgemarks_m[(i) - 1][(j) - 1] == edgemark_m)


void add_edge_face(KANTE *right1, KANTE *right2, KANTE *e1)


{
  LONGTYPE *face, *newface;
  int k;
  KANTE *run, *e2;

  k = (int)(e1 - edges);

  rememberfaces[k] = *(right1->faceleft);
  rememberfaces[k + 1] = *(right2->faceleft);

  e2 = e1 + 1;
  e1->is_embedded = e2->is_embedded = 1;

  e1->prev = right1->prev;
  right1->prev = e1->prev->next = e1;
  e1->next = right1;

  e2->prev = right2->prev;
  right2->prev = e2->prev->next = e2;
  e2->next = right2;

  face = e2->faceleft =
      right1->faceleft;  
  *face = (bit(e1->ursprung) | bit(e1->name));
  for (run = right1->invers->next; run != e2; run = run->invers->next) {
    *face |= bit(run->ursprung);
  }
  newface = face_pointer[em_faces];
  em_faces++;
  e1->faceleft = newface;
  *newface = (bit(e1->ursprung) | bit(e1->name));
  right2->faceleft = newface;
  for (run = right2->invers->next; run != e1; run = run->invers->next) {
    *newface |= bit(run->ursprung);
    run->faceleft = newface;
  }

  return;
}


KANTE *add_edge(KANTE *right1, KANTE *right2, KANTE *e1, int *genus,
                int max_genus)


{
  LONGTYPE *face, *newface;
  int search, k;
  KANTE *run, *e2;

  if (((*genus) == max_genus) && (right1->faceleft != right2->faceleft))
    return NULL;
  

  k = (int)(e1 - edges);

  rememberfaces[k] = *(right1->faceleft);
  rememberfaces[k + 1] = *(right2->faceleft);

  e2 = e1 + 1;
  e1->is_embedded = e2->is_embedded = 1;

  e1->prev = right1->prev;
  right1->prev = e1->prev->next = e1;
  e1->next = right1;

  e2->prev = right2->prev;
  right2->prev = e2->prev->next = e2;
  e2->next = right2;

  if (right1->faceleft == right2->faceleft)  
                                             
  {
    face = e2->faceleft =
        right1->faceleft;  
    *face = (bit(e1->ursprung) | bit(e1->name));
    for (run = right1->invers->next; run != e2; run = run->invers->next) {
      *face |= bit(run->ursprung);
    }
    newface = face_pointer[em_faces];
    em_faces++;
    e1->faceleft = newface;
    *newface = (bit(e1->ursprung) | bit(e1->name));
    right2->faceleft = newface;
    for (run = right2->invers->next; run != e1; run = run->invers->next) {
      *newface |= bit(run->ursprung);
      run->faceleft = newface;
    }
  } else  
  {
    (*genus)++;
    face = right1->faceleft;
    *face |= (*right2->faceleft);
    em_faces--;
    for (search = 0; face_pointer[search] != right2->faceleft; search++);
    face_pointer[search] = face_pointer[em_faces];
    face_pointer[em_faces] = right2->faceleft;
    e1->faceleft = e2->faceleft = face;
    for (run = right2; run != e2; run = run->invers->next) run->faceleft = face;
  }
  return e1;
}


KANTE *add_new(KANTE *right, KANTE *e1)


{
  int to;
  LONGTYPE *face;
  KANTE *e2;

  to = e1->name;
  face = right->faceleft;

  SETBIT(*face, to);

  em_vertices++;
  e2 = e1 + 1;
  e1->is_embedded = e2->is_embedded = 1;

  e1->prev = right->prev;
  right->prev = e1->prev->next = e1;
  e1->next = right;
  e1->faceleft = face;

  e2->prev = e2->next = e2;
  e2->faceleft = face;

  firstedge[to] = e2;

  return e2;
}

int get_initial_embedding(GRAPH graph, ADJAZENZ adj, int *genus)


{
  int i, j, x, y, doorgaan, em_edges = 0, mindeg_g3, starttop;
  KANTE *e1, *e2, *new1, *new2, *fedge;
  int path = 0, cycle = 0;

  *genus = 0;

  knotenzahl = mindeg_g3 = graph[0][0];

  for (i = (d_kanten / 3) - 1; i >= 0; i--) face_pointer[i] = faces + i;

  starttop = 0;
  for (i = 1; i <= knotenzahl; i++) {
    firstedge[i] = NULL;
    adj_embedded[i] = 0;
    if ((adj[i] >= 3) && (adj[i] < mindeg_g3)) {
      starttop = i;
      mindeg_g3 = adj[i];
    }
  }

  if (starttop == 0)  
  {
    mindeg_g3 = knotenzahl;
    for (i = 1; i <= knotenzahl; i++)
      if (adj[i] && (adj[i] < mindeg_g3)) {
        starttop = i;
        mindeg_g3 = adj[i];
      }
    if (adj[starttop] == 1)
      path = 1;
    else
      cycle = 1;
  }

  x = starttop;

  y = graph[x][0];
  faces[0] = bit(y) | bit(x);
  em_vertices = 2;
  em_faces = 1;
  adj_embedded[x] = adj_embedded[y] = 1;
  firstedge[y] = e1 = edges + em_edges;
  em_edges++;
  e1->ursprung = y;
  e1->name = x;
  e1->invers = firstedge[x] = e2 = edges + em_edges;
  em_edges++;
  e2->ursprung = x;
  e2->name = y;
  e2->invers = e1;

  e1->prev = e1->next = e1;
  e1->faceleft = faces + 0;

  e2->prev = e2->next = e2;
  e2->faceleft = faces + 0;

  if (path && (adj[y] == 1))  
    return 2;

  if (path || cycle) {
    
    for (doorgaan = 1; doorgaan;) {
      for (i = 0; (i < adj[x]) && adj_embedded[graph[x][i]]; i++) {
      };
      
      if (i >= adj[x])
        doorgaan = 0;
      else  
      {
        e1 = e2;
        new1 = edges + em_edges;
        em_edges++;
        new2 = edges + em_edges;
        em_edges++;
        y = x;
        x = graph[y][i];  
        new1->invers = new2;
        new2->invers = new1;
        new1->ursprung = y;
        new1->name = x;
        new2->ursprung = x;
        new2->name = y;
        e2 = add_new(e1, new1);
        adj_embedded[x]++;
        adj_embedded[y]++;
      }
    }

    if (path) return em_edges;
    

    
    

    if (graph[x][0] == y)
      i = 1;
    else
      i = 0;
    

    new1 = edges + em_edges;
    em_edges++;
    new2 = edges + em_edges;
    em_edges++;
    y = graph[x][i];  
    new1->invers = new2;
    new2->invers = new1;
    new1->ursprung = x;
    new1->name = y;
    new2->ursprung = y;
    new2->name = x;

    adj_embedded[x]++;
    adj_embedded[y]++;
    add_edge(firstedge[x], firstedge[graph[x][i]], new1, genus, INT_MAX);
    return em_edges;
  }  

  
  

  new1 = edges + em_edges;
  em_edges++;
  new2 = edges + em_edges;
  em_edges++;
  y = graph[x][1];  
  new1->invers = new2;
  new2->invers = new1;
  new1->ursprung = x;
  new1->name = y;
  new2->ursprung = y;
  new2->name = x;
  adj_embedded[x]++;
  adj_embedded[y]++;
  add_new(firstedge[x], new1);

  new1 = edges + em_edges;
  em_edges++;
  new2 = edges + em_edges;
  em_edges++;
  y = graph[x][2];  
  new1->invers = new2;
  new2->invers = new1;
  new1->ursprung = x;
  new1->name = y;
  new2->ursprung = y;
  new2->name = x;
  adj_embedded[x]++;
  adj_embedded[y]++;
  add_new(firstedge[x]->next, new1);

  

  for (j = 0, fedge = firstedge[starttop]; j < 3; j++) {
    x = fedge->name;
    e2 = fedge->invers;
    for (doorgaan = 1; doorgaan;) {
      for (i = 0; (i < adj[x]) && adj_embedded[graph[x][i]]; i++) {
      };
      
      if (i >= adj[x])
        doorgaan = 0;
      else  
      {
        e1 = e2;
        new1 = edges + em_edges;
        em_edges++;
        new2 = edges + em_edges;
        em_edges++;
        y = x;
        x = graph[y][i];  
        new1->invers = new2;
        new2->invers = new1;
        new1->ursprung = y;
        new1->name = x;
        new2->ursprung = x;
        new2->name = y;
        e2 = add_new(e1, new1);
        adj_embedded[x]++;
        adj_embedded[y]++;
      }
    }
    fedge = fedge->next;
  }

  
  return em_edges;
}

void einfugen(GRAPH graph, ADJAZENZ adj, int v, int w) {
  graph[v][adj[v]++] = w;
  graph[w][adj[w]++] = v;
}

void remove_e(GRAPH g, ADJAZENZ adj, int v, int w)

{
  int i;

  for (i = 0; g[v][i] != w; i++);
  adj[v]--;
  g[v][i] = g[v][adj[v]];

  for (i = 0; g[w][i] != v; i++);
  adj[w]--;
  g[w][i] = g[w][adj[w]];

  return;
}

int adjacent(GRAPH g, ADJAZENZ adj, int v1, int v2) {
  int i;
  for (i = 0; i < adj[v1]; i++)
    if (g[v1][i] == v2) return 1;
  return 0;
}


void preprocess(GRAPH old, ADJAZENZ a_old, GRAPH new, ADJAZENZ a_new)


{
  int list[2 * knoten], ll, i, v1, v2, v3;

  memcpy(new, old, sizeof(GRAPH));
  memcpy(a_new, a_old, sizeof(ADJAZENZ));

  for (i = 1, ll = 0; i <= old[0][0]; i++)
    if (a_new[i] < 3) {
      list[ll] = i;
      ll++;
    }

  number_reconstruct = 0;
  for (i = 0; i < ll; i++) {
    v1 = list[i];
    if (a_new[v1] == 1) {
      v2 = new[v1][0];
      if (a_new[v2] > 1)  
      {
        reconstruct[number_reconstruct][0] = 0;
        reconstruct[number_reconstruct][1] = v1;
        reconstruct[number_reconstruct][2] = v2;
        number_reconstruct++;
        remove_e(new, a_new, v1, v2);
        if (a_new[v2] < 3) {
          list[ll] = v2;
          ll++;
        }
      }
    } else if (a_new[v1] == 2)  
    {
      v2 = new[v1][0];
      v3 = new[v1][1];
      if (adjacent(new, a_new, v2, v3)) {
        remove_e(new, a_new, v1, v2);
        if (a_new[v2] < 3) {
          list[ll] = v2;
          ll++;
        }
        remove_e(new, a_new, v1, v3);
        if (a_new[v3] < 3) {
          list[ll] = v3;
          ll++;
        }
        reconstruct[number_reconstruct][0] = 2;
        reconstruct[number_reconstruct][1] = v1;
        reconstruct[number_reconstruct][2] = v2;
        reconstruct[number_reconstruct][3] = v3;
        number_reconstruct++;

      } else {
        remove_e(new, a_new, v1, v2);
        remove_e(new, a_new, v1, v3);
        einfugen(new, a_new, v2, v3);
        reconstruct[number_reconstruct][0] = 1;
        reconstruct[number_reconstruct][1] = v1;
        reconstruct[number_reconstruct][2] = v2;
        reconstruct[number_reconstruct][3] = v3;
        number_reconstruct++;
      }
    }  
  }  
}


void remove_edge(KANTE *edge, int *genus) {
  int end, search, k;
  KANTE *invedge, *run, *endedge;
  LONGTYPE *face;

  k = (int)(edge - edges);

  
  

  end = edge->name;
  invedge = edge->invers;
  edge->is_embedded = invedge->is_embedded = 0;

  if (invedge->next ==
      invedge)  
  {
    
    firstedge[end] = NULL;
    
    DELBIT(*(edge->faceleft), end);
    edge->prev->next = edge->next;
    edge->next->prev = edge->prev;
    em_vertices--;
  } else {
    if (edge->faceleft ==
        invedge->faceleft)  
    {
      edge->prev->next = edge->next;
      edge->next->prev = edge->prev;
      invedge->prev->next = invedge->next;
      invedge->next->prev = invedge->prev;
      
      *(edge->next->faceleft) = rememberfaces[k];

      run = endedge =
          invedge->next;  
      face = face_pointer[em_faces];
      *face = rememberfaces[k + 1];
      em_faces++;
      do {
        run->faceleft = face;
        run = run->invers->next;
      } while (run != endedge);

      (*genus)--;
    } else  
    {
      em_faces--;
      for (search = 0; face_pointer[search] != invedge->faceleft; search++);
      face_pointer[search] = face_pointer[em_faces];
      face_pointer[em_faces] = invedge->faceleft;
      face = edge->faceleft;
      *face |= *(invedge->faceleft);
      for (run = invedge->invers->next; run != invedge;
           run = run->invers->next) {
        run->faceleft = face;
      }
      edge->prev->next = edge->next;
      edge->next->prev = edge->prev;
      invedge->prev->next = invedge->next;
      invedge->next->prev = invedge->prev;
    }
  }
}


void make_edgelist(GRAPH graph, ADJAZENZ adj, KANTE edgelist[],
                   LONGTYPE bit_edgelist[], int *ell) {
  
  

  int localedgelist[d_kanten / 2][2], lell, best, bestdist, besti, i, j;
  unsigned char is_embedded[knoten + 1][knoten + 1];
  KANTE *run;
  ADJAZENZ local_adj_embedded;

  memcpy(local_adj_embedded, adj_embedded, sizeof(ADJAZENZ));

  for (i = 1; i <= graph[0][0]; i++) {
    for (j = 0; j < adj[i]; j++) is_embedded[i][graph[i][j]] = 0;
  }

  for (i = 1; i <= graph[0][0]; i++)
    if (local_adj_embedded[i]) {
      run = firstedge[i];
      do {
        run->is_embedded = 1;
        is_embedded[run->ursprung][run->name] = 1;
        run = run->next;
      } while (run != firstedge[i]);
    }

  for (i = 1, lell = 0; i <= graph[0][0]; i++)
    for (j = 0; j < adj[i]; j++) {
      if ((i < graph[i][j]) && !is_embedded[i][graph[i][j]]) {
        localedgelist[lell][0] = i;
        localedgelist[lell][1] = graph[i][j];
        lell++;
      }
    }

  edgelimit = lell;
  
  
  

#define ways(x) ((x) == 0 ? 1 : ((x) << 7))
  
  
  

  
  *ell = 0;
  while (lell) {
    best = bestdist = INT_MAX;
    
    for (i = 0; i < lell; i++)
      if (local_adj_embedded[localedgelist[i][0]] ||
          local_adj_embedded[localedgelist[i][1]])
        if (ways(local_adj_embedded[localedgelist[i][0]]) *
                ways(local_adj_embedded[localedgelist[i][1]]) <
            best) {
          best = ways(local_adj_embedded[localedgelist[i][0]]) *
                 ways(local_adj_embedded[localedgelist[i][1]]);
          besti = i;
        }

    if (local_adj_embedded[localedgelist[besti][0]])  
                                                      
                                                      
    {
      edgelist[*ell].ursprung = localedgelist[besti][0];
      edgelist[*ell].name = localedgelist[besti][1];
      edgelist[*ell].invers = edgelist + (*ell) + 1;
      edgelist[*ell].is_embedded = 0;
      bit_edgelist[*ell] =
          bit(localedgelist[besti][0]) | bit(localedgelist[besti][1]);
      (*ell)++;
      edgelist[*ell].ursprung = localedgelist[besti][1];
      edgelist[*ell].name = localedgelist[besti][0];
      edgelist[*ell].invers = edgelist + (*ell) - 1;
      edgelist[*ell].is_embedded = 0;
      bit_edgelist[*ell] =
          bit(localedgelist[besti][0]) | bit(localedgelist[besti][1]);
      (*ell)++;
    } else {
      edgelist[*ell].ursprung = localedgelist[besti][1];
      edgelist[*ell].name = localedgelist[besti][0];
      edgelist[*ell].invers = edgelist + (*ell) + 1;
      edgelist[*ell].is_embedded = 0;
      bit_edgelist[*ell] =
          bit(localedgelist[besti][0]) | bit(localedgelist[besti][1]);
      (*ell)++;
      edgelist[*ell].ursprung = localedgelist[besti][0];
      edgelist[*ell].name = localedgelist[besti][1];
      edgelist[*ell].invers = edgelist + (*ell) - 1;
      edgelist[*ell].is_embedded = 0;
      bit_edgelist[*ell] =
          bit(localedgelist[besti][0]) | bit(localedgelist[besti][1]);
      (*ell)++;
    }
    local_adj_embedded[localedgelist[besti][0]]++;
    local_adj_embedded[localedgelist[besti][1]]++;
    lell--;
    localedgelist[besti][0] = localedgelist[lell][0];
    localedgelist[besti][1] = localedgelist[lell][1];
  }

  last_edge = edgelist + (*ell);
}

void rec_genus_max(KANTE edgelist[], LONGTYPE bit_edgelist[], int ell,
                   int genus, int *found, KANTE *last, LONGTYPE lastsub1,
                   LONGTYPE lastsub2)


{
  int i, j, found2, ell2;
  KANTE *run, *end, *run2, *end2, *edgelist2;
  LONGTYPE *bit_edgelist2;

  while (ell && (edgelist->is_embedded)) {
    edgelist += 2;
    bit_edgelist += 2;
    ell -= 2;
  }

  if (ell == 0) {
    *found = 1;
    return;
  }

  ell2 = ell - 2;
  edgelist2 = edgelist + 2;
  bit_edgelist2 = bit_edgelist + 2;

  


  if (last->faceleft == last->invers->faceleft)
    i = MIN0(last - edgelist + 2);
  else
    i = 0;
  
  
  for (; i < ell; i += 2)
    if ((bit_edgelist[i] & lastsub1) && (bit_edgelist[i] & lastsub2) &&
        (!((edgelist + i)->is_embedded)))
    
    {
      {
        found2 = 0;  
        for (j = 0; j < em_faces; j++) {
          if (ATLEAST2BIT(bit_edgelist[i] & (*(face_pointer[j])))) {
            found2 = 1;
            j = em_faces;
          }
        }
        if (!found2) return;
      }
    }

  
  

  run = end = firstedge[edgelist->ursprung];
  do {
    run2 = end2 = firstedge[edgelist->name];
    do {
      if (run2->faceleft == run->faceleft) {
        add_edge_face(run, run2, edgelist);
        rec_genus_max(
            edgelist2, bit_edgelist2, ell2, genus, found, edgelist,
            (*(edgelist->faceleft)) & (~(*(edgelist->invers->faceleft))),
            (*(edgelist->invers->faceleft) & (~(*(edgelist->faceleft)))));
        remove_edge(edgelist, &genus);
      }
      run2 = run2->next;
    } while ((run2 != end2) && (!(*found)));
    run = run->next;
  } while ((run != end) && (!(*found)));

}

void rec_genus(KANTE edgelist[], LONGTYPE bit_edgelist[], int ell, int genus,
               int max_genus, int *found, KANTE *last, LONGTYPE lastsub1,
               LONGTYPE lastsub2)


{
  int i, j, found2, ell2, changed, best, old_genus;
  KANTE *run, *end, *run2, *end2, *edgelist2, *old_edgelist;
  LONGTYPE *bit_edgelist2;

  while (ell && (edgelist->is_embedded)) {
    edgelist += 2;
    bit_edgelist += 2;
    ell -= 2;
  }

  if (ell == 0) {
    if (max_genus == genus) {
      *found = 1;
      }
    return;
  }

  ell2 = ell - 2;
  edgelist2 = edgelist + 2;
  bit_edgelist2 = bit_edgelist + 2;

  
  
  
  
  
  
  

  


  if (ell < edgelimit)  
  {
    if (last->faceleft == last->invers->faceleft)
      i = MIN0(last - edgelist + 2);
    else
      i = 0;
    
    
    for (; i < ell; i += 2)
      if ((bit_edgelist[i] & lastsub1) && (bit_edgelist[i] & lastsub2) &&
          (!((edgelist + i)->is_embedded)))
      
      {
        {
          found2 = 0;  
          for (j = 0; j < em_faces; j++) {
            if (ATLEAST2BIT(bit_edgelist[i] & (*(face_pointer[j])))) {
              found2 = 1;
              j = em_faces;
            }
          }
          if (!found2) {
            if (genus == max_genus) return;
            
            ell2 = ell;
            edgelist2 = edgelist;
            bit_edgelist2 =
                bit_edgelist;  
            edgelist = edgelist + i;
            i = ell;
          }
        }
      }
  } else {  
            
    
    old_edgelist = edgelist;
    changed = 0;
    for (j = best = 0; j < em_faces; j++) {
      if (ATLEAST2BIT(bit_edgelist[0] & (*(face_pointer[j])))) {
        best++;
      }
    }
    if (!best) {
      if (genus == max_genus) return;
    } else {
      for (i = 2; (i < ell) && best; i += 2)
        if (!((old_edgelist + i)->is_embedded)) {
          found2 = 0;  
          for (j = 0; j < em_faces; j++) {
            if (ATLEAST2BIT(bit_edgelist[i] & (*(face_pointer[j])))) {
              found2++;
              if (found2 >= best) j = em_faces;
            }
          }
          if (found2 < best) {
            if ((found2 == 0) && (genus == max_genus)) return;
            best = found2;
            if (!changed) {
              
              ell2 = ell;
              edgelist2 = edgelist;
              bit_edgelist2 =
                  bit_edgelist;  
              edgelist = edgelist + i;
              changed = 1;
            } else
              edgelist = old_edgelist + i;
          }
        }  
    }
  }  

  

  

  old_genus = genus;

  run = end = firstedge[edgelist->ursprung];
  do {
    run2 = end2 = firstedge[edgelist->name];
    do {
      if (add_edge(run, run2, edgelist, &genus, max_genus) != NULL) {
        if (old_genus != genus) {
          if (genus < max_genus)
            rec_genus(edgelist2, bit_edgelist2, ell2, genus, max_genus, found,
                      edgelist, lastsub1, lastsub2);
          else
            rec_genus_max(edgelist2, bit_edgelist2, ell2, genus, found,
                          edgelist, lastsub1, lastsub2);
        } else  
                
        {
          rec_genus(
              edgelist2, bit_edgelist2, ell2, genus, max_genus, found, edgelist,
              (*(edgelist->faceleft)) & (~(*(edgelist->invers->faceleft))),
              (*(edgelist->invers->faceleft) & (~(*(edgelist->faceleft)))));
        }
        remove_edge(edgelist, &genus);
      }
      run2 = run2->next;
    } while ((run2 != end2) && (!(*found)));
    run = run->next;
  } while ((run != end) && (!(*found)));

}

void pre_rec_genus(KANTE edgelist[], LONGTYPE bit_edgelist[], int ell,
                   int genus, int max_genus, int *found, KANTE *last)


{
  KANTE *run, *end, *run2, *end2;

  if (ell == 0) {
    if (max_genus == genus) {
      *found = 1;
      }
    return;
  }

  
  
  
  

  if (firstedge[edgelist->name] == NULL) {
    run = end = firstedge[edgelist->ursprung];
    do {
      add_new(run, edgelist);
      pre_rec_genus(edgelist + 2, bit_edgelist + 2, ell - 2, genus, max_genus,
                    found, edgelist);
      remove_edge(edgelist, &genus);
      run = run->next;
    } while ((run != end) && (!(*found)));
  } else  
  {
    run = end = firstedge[edgelist->ursprung];
    do {
      run2 = end2 = firstedge[edgelist->name];
      do {
        if (add_edge(run, run2, edgelist, &genus, max_genus) != NULL) {
          if (max_genus > 0)
            rec_genus(
                edgelist + 2, bit_edgelist + 2, ell - 2, genus, max_genus,
                found, edgelist,
                (*(edgelist->faceleft)) & (~(*(edgelist->invers->faceleft))),
                (*(edgelist->invers->faceleft) & (~(*(edgelist->faceleft)))));
          else  
            rec_genus_max(
                edgelist + 2, bit_edgelist + 2, ell - 2, genus, found, edgelist,
                (*(edgelist->faceleft)) & (~(*(edgelist->invers->faceleft))),
                (*(edgelist->invers->faceleft) & (~(*(edgelist->faceleft)))));
          remove_edge(edgelist, &genus);
        }
        run2 = run2->next;
      } while ((run2 != end2) && (!(*found)));
      run = run->next;
    } while ((run != end) && (!(*found)));
  }

  return;
}


int getshortestdpath(GRAPH graph, ADJAZENZ adj, int start, int ziel)


{
  int list[d_kanten], previous[d_kanten], length[d_kanten], run, ll;
  int top, new, i;

  if ((adj[start] == 1) && (adj[ziel] == 1)) return 2;

  RESET_EDGEMARKS;

  

  list[0] = ziel;
  previous[0] = start;
  length[0] = 1;
  SET_EDGE_MARK(start, ziel);
  run = 0;
  ll = 1;

  while (1) {
    top = list[run];
    if (adj[top] == 1) {
      if ((top == start) && (graph[top][0] == ziel)) return length[run];
      list[ll] = graph[top][0];
      previous[ll] = top;
      length[ll] = length[run] + 1;
      ll++;
      SET_EDGE_MARK(top, graph[top][0]);
    } else {
      for (i = 0; i < adj[top]; i++) {
        new = graph[top][i];
        if (new != previous[run]) {
          if (NOT_EDGE_MARKED(top, new)) {
            SET_EDGE_MARK(top, new);
            list[ll] = new;
            previous[ll] = top;
            length[ll] = length[run] + 1;
            ll++;
          } else {
            if ((top == start) && (new == ziel)) return length[run];
          }
        }  
      }  
    }
    run++;
  }  
  return 0;  
             
}


double compute_fractions(GRAPH graph, ADJAZENZ adj)


{
  int knotenzahl, i, j, k, start, end, buffer;
  double facebound1, facebound2;
  int lengtharray[d_kanten], sizes[d_kanten], max, ll;
  int sizes_aroundvertex[knoten + 1][d_kanten], max_a[knoten + 1];

  knotenzahl = graph[0][0];
  for (i = 1; i <= knotenzahl; i++) {
    max_a[i] = 1;
  }
  max = 1;

  for (start = 1; start < knotenzahl; start++)
    for (j = 0; j < adj[start]; j++)
      if ((end = graph[start][j]) > start) {
        buffer = getshortestdpath(graph, adj, start, end);
        if (buffer > max_a[start]) {
          for (i = max_a[start] + 1; i < buffer; i++)
            sizes_aroundvertex[start][i] = 0;
          max_a[start] = buffer;
          sizes_aroundvertex[start][buffer] = 1;
        } else
          (sizes_aroundvertex[start][buffer])++;
        if (buffer > max_a[end]) {
          for (i = max_a[end] + 1; i < buffer; i++)
            sizes_aroundvertex[end][i] = 0;
          max_a[end] = buffer;
          sizes_aroundvertex[end][buffer] = 1;
        } else
          (sizes_aroundvertex[end][buffer])++;

        if (buffer > max) {
          for (i = max + 1; i < buffer; i++) sizes[i] = 0;
          max = buffer;
          sizes[max] = 2;
        } else
          sizes[buffer] += 2;
      }

  

  for (j = 2, ll = 0; j <= max; j++) {
    for (k = 0; k < sizes[j]; k++, ll++) {
      lengtharray[ll] = j;
    }
  }

  
  

  for (j = 1; j < max; j++) lengtharray[ll - j] = max;

  for (j = 0, facebound1 = 0.0; j < ll; j++)
    facebound1 += 1.0 / ((double)lengtharray[j]);

  
  
  
  
  
  
  
  
  

  facebound2 = 0.0;
  for (start = 1; start <= knotenzahl; start++)
    if (adj[start]) {
      for (j = 2; sizes_aroundvertex[start][j] == 0; j++);  
      if (j == max_a[start])
        facebound2 += ((double)sizes_aroundvertex[start][j]) / ((double)j);
      else {
        facebound2 += ((double)(sizes_aroundvertex[start][j] - 1)) /
                      ((double)j);  
        for (j++; j < max_a[start]; j++)
          facebound2 += ((double)sizes_aroundvertex[start][j]) / ((double)j);
        facebound2 += ((double)(sizes_aroundvertex[start][j] + 1)) /
                      ((double)j);  
      }
    }


  if (facebound2 > facebound1)
    return facebound1;
  else
    return facebound2;
}


int get_genus(GRAPH graph, ADJAZENZ adj) {
  int i, genus;   
  int max_genus;  
                  
  int do_reduce2;
  GRAPH newgraph;
  ADJAZENZ newadj;
  int ell, found, min_genus, restvertices, restedges;
  LONGTYPE bit_edgelist[d_kanten];
  KANTE *edgelist;
  double x_sum, buffer;

  number_reconstruct = 0;

  knotenzahl = graph[0][0];

  do_reduce2 = 0;
  if (reduce2) {
    for (i = 1; i <= knotenzahl; i++)
      if (adj[i] < 3) {
        do_reduce2 = 1;
        i = knotenzahl;
      }
  }

  if (do_reduce2) {
    preprocess(graph, adj, newgraph, newadj);
    
    

    restvertices =
        graph[0][0] - number_reconstruct;  

    if (restvertices == 2) return 0;
    for (i = 1, restedges = 0; i <= knotenzahl; i++) restedges += newadj[i];
    restedges = restedges / 2;
    edgelist = edges + get_initial_embedding(newgraph, newadj, &genus);
    make_edgelist(newgraph, newadj, edgelist, bit_edgelist, &ell);
  } else {
    restvertices = globalnv;
    restedges = globalne;
    edgelist = edges + get_initial_embedding(graph, adj, &genus);
    
    make_edgelist(graph, adj, edgelist, bit_edgelist, &ell);
  }

  if ((restedges - (3 * restvertices) + 6) <= 0)
    min_genus = 0;
  else if ((restedges - (3 * restvertices)) %
           6)  
    min_genus = ((restedges - (3 * restvertices) + 6) / 6) + 1;
  else
    min_genus = ((restedges - (3 * restvertices) + 6) / 6);


  if (compute_lower_bound) {
    if (do_reduce2) {
      x_sum = compute_fractions(newgraph, newadj);
    } else {
      x_sum = compute_fractions(graph, adj);
    }
    buffer = 1.0 + (((double)restedges) - ((double)restvertices) - x_sum) / 2.0;
    buffer = ceil(buffer - 0.0000001);

    if (buffer > (double)min_genus) {  
                                       
      min_genus = buffer;
    }
  }
  


  for (found = 0, max_genus = min_genus; !found; max_genus++) {
    pre_rec_genus(edgelist, bit_edgelist, ell, genus, max_genus, &found,
                  edgelist - 2);
  }

  if (max_genus - 1 == min_genus) good_approx[min_genus]++;

  return max_genus - 1;
}



/* Shared parser and race driver. */
#define PAGEHOG_MAX_VERTEX 65535
#define PAGEHOG_TMP_TEMPLATE "/tmp/page_hog_XXXXXX"

typedef struct {
    int n;
    int m;
    int max_degree;
    int* degree;
    int* capacity;
    int** adj;
} hog_graph_t;

typedef struct {
    char* data;
    size_t size;
    size_t capacity;
} hog_bytes_t;

typedef enum {
    HOG_INPUT_GRAPH6,
    HOG_INPUT_MULTICODE
} hog_input_format_t;

typedef enum {
    HOG_WORKER_PAGE,
    HOG_WORKER_MULTI_GENUS
} hog_worker_kind_t;

typedef struct {
    hog_worker_kind_t kind;
    pid_t pid;
    char output_path[4096];
} hog_child_t;

static void hog_graph_free(hog_graph_t* graph) {
    if (graph == NULL) return;
    if (graph->adj != NULL) {
        for (int i = 0; i < graph->n; i++) {
            free(graph->adj[i]);
        }
    }
    free(graph->adj);
    free(graph->degree);
    free(graph->capacity);
    memset(graph, 0, sizeof(*graph));
}

static bool hog_graph_init(hog_graph_t* graph, int n) {
    memset(graph, 0, sizeof(*graph));
    if (n <= 0 || n > PAGEHOG_MAX_VERTEX) return false;
    graph->n = n;
    graph->degree = (int*)calloc((size_t)n, sizeof(int));
    graph->capacity = (int*)calloc((size_t)n, sizeof(int));
    graph->adj = (int**)calloc((size_t)n, sizeof(int*));
    return graph->degree != NULL && graph->capacity != NULL && graph->adj != NULL;
}

static bool hog_graph_has_edge(const hog_graph_t* graph, int u, int v) {
    for (int i = 0; i < graph->degree[u]; i++) {
        if (graph->adj[u][i] == v) return true;
    }
    return false;
}

static bool hog_graph_add_half_edge(hog_graph_t* graph, int u, int v) {
    if (u < 0 || v < 0 || u >= graph->n || v >= graph->n || u == v) return false;
    if (graph->degree[u] == graph->capacity[u]) {
        int new_capacity = graph->capacity[u] == 0 ? 4 : 2 * graph->capacity[u];
        int* new_adj = (int*)realloc(graph->adj[u], (size_t)new_capacity * sizeof(int));
        if (new_adj == NULL) return false;
        graph->adj[u] = new_adj;
        graph->capacity[u] = new_capacity;
    }
    graph->adj[u][graph->degree[u]++] = v;
    if (graph->degree[u] > graph->max_degree) graph->max_degree = graph->degree[u];
    return true;
}

static bool hog_graph_add_edge(hog_graph_t* graph, int u, int v) {
    if (hog_graph_has_edge(graph, u, v)) return false;
    if (!hog_graph_add_half_edge(graph, u, v)) return false;
    if (!hog_graph_add_half_edge(graph, v, u)) return false;
    graph->m++;
    return true;
}

static bool hog_bytes_append(hog_bytes_t* bytes, const void* data, size_t size) {
    if (size == 0) return true;
    if (bytes->size + size > bytes->capacity) {
        size_t new_capacity = bytes->capacity == 0 ? 4096 : 2 * bytes->capacity;
        while (new_capacity < bytes->size + size) new_capacity *= 2;
        char* new_data = (char*)realloc(bytes->data, new_capacity);
        if (new_data == NULL) return false;
        bytes->data = new_data;
        bytes->capacity = new_capacity;
    }
    memcpy(bytes->data + bytes->size, data, size);
    bytes->size += size;
    return true;
}

static void hog_bytes_free(hog_bytes_t* bytes) {
    free(bytes->data);
    memset(bytes, 0, sizeof(*bytes));
}

static bool hog_read_stdin(hog_bytes_t* bytes) {
    char buffer[16384];
    memset(bytes, 0, sizeof(*bytes));
    while (true) {
        size_t nread = fread(buffer, 1, sizeof(buffer), stdin);
        if (nread > 0 && !hog_bytes_append(bytes, buffer, nread)) return false;
        if (nread < sizeof(buffer)) {
            if (feof(stdin)) return true;
            return false;
        }
    }
}

static int hog_graph6_read_n(const unsigned char* values, size_t size, size_t* pos) {
    if (*pos >= size) return -1;
    if (values[*pos] <= 62) return values[(*pos)++];
    if (values[*pos] == 63) {
        int n;
        (*pos)++;
        if (*pos + 3 > size) return -1;
        n = (values[*pos] << 12) | (values[*pos + 1] << 6) | values[*pos + 2];
        *pos += 3;
        return n;
    }
    return -1;
}

static bool hog_parse_graph6_line(const char* line, size_t length, hog_graph_t* graph) {
    const char header[] = ">>graph6<<";
    unsigned char* values;
    size_t value_count = 0;
    size_t pos = 0;
    int n;
    uint64_t needed_bits;
    uint64_t bit_index = 0;

    while (length > 0 && isspace((unsigned char)line[length - 1])) length--;
    while (length > 0 && isspace((unsigned char)*line)) {
        line++;
        length--;
    }
    if (length == 0) return false;
    if (length >= sizeof(header) - 1 &&
        memcmp(line, header, sizeof(header) - 1) == 0) {
        line += sizeof(header) - 1;
        length -= sizeof(header) - 1;
    }
    if (length == 0 || line[0] == ':') return false;

    values = (unsigned char*)malloc(length);
    if (values == NULL) return false;
    for (size_t i = 0; i < length; i++) {
        int value = (int)((unsigned char)line[i]) - 63;
        if (value < 0 || value > 63) {
            free(values);
            return false;
        }
        values[value_count++] = (unsigned char)value;
    }

    n = hog_graph6_read_n(values, value_count, &pos);
    if (n <= 0 || !hog_graph_init(graph, n)) {
        free(values);
        return false;
    }
    needed_bits = (uint64_t)n * (uint64_t)(n - 1) / 2;
    if ((uint64_t)(value_count - pos) * 6 < needed_bits) {
        free(values);
        hog_graph_free(graph);
        return false;
    }

    for (int j = 1; j < n; j++) {
        for (int i = 0; i < j; i++) {
            unsigned char value = values[pos + (size_t)(bit_index / 6)];
            int bit = (value >> (5 - (bit_index % 6))) & 1;
            if (bit && !hog_graph_add_edge(graph, i, j)) {
                free(values);
                hog_graph_free(graph);
                return false;
            }
            bit_index++;
        }
    }
    free(values);
    return true;
}

static bool hog_graphs_push(hog_graph_t** graphs, int* count, int* capacity,
                            hog_graph_t* graph) {
    if (*count == *capacity) {
        int new_capacity = *capacity == 0 ? 16 : 2 * *capacity;
        hog_graph_t* new_graphs =
            (hog_graph_t*)realloc(*graphs, (size_t)new_capacity * sizeof(hog_graph_t));
        if (new_graphs == NULL) return false;
        *graphs = new_graphs;
        *capacity = new_capacity;
    }
    (*graphs)[(*count)++] = *graph;
    memset(graph, 0, sizeof(*graph));
    return true;
}

static bool hog_parse_graph6_input(const hog_bytes_t* input, hog_graph_t** graphs_out,
                                   int* count_out) {
    hog_graph_t* graphs = NULL;
    int count = 0;
    int capacity = 0;
    size_t start = 0;

    *graphs_out = NULL;
    *count_out = 0;
    for (size_t i = 0; i <= input->size; i++) {
        if (i == input->size || input->data[i] == '\n') {
            hog_graph_t graph;
            if (hog_parse_graph6_line(input->data + start, i - start, &graph)) {
                if (!hog_graphs_push(&graphs, &count, &capacity, &graph)) {
                    hog_graph_free(&graph);
                    for (int j = 0; j < count; j++) hog_graph_free(&graphs[j]);
                    free(graphs);
                    return false;
                }
            }
            start = i + 1;
        }
    }
    *graphs_out = graphs;
    *count_out = count;
    return count > 0;
}

static bool hog_parse_multicode_input(const hog_bytes_t* input, hog_graph_t** graphs_out,
                                      int* count_out) {
    const unsigned char header[] = ">>multi_code<<";
    size_t pos = 0;
    hog_graph_t* graphs = NULL;
    int count = 0;
    int capacity = 0;

    *graphs_out = NULL;
    *count_out = 0;
    if (input->size >= sizeof(header) - 1 &&
        memcmp(input->data, header, sizeof(header) - 1) == 0) {
        pos = sizeof(header) - 1;
    }

    while (pos < input->size) {
        int n = (unsigned char)input->data[pos++];
        int current = 0;
        int zeros = 0;
        hog_graph_t graph;

        if (n == 0 || !hog_graph_init(&graph, n)) goto fail;
        while (pos < input->size && zeros < n - 1) {
            int value = (unsigned char)input->data[pos++];
            if (value == 0) {
                current++;
                zeros++;
            } else if (!hog_graph_add_edge(&graph, current, value - 1)) {
                hog_graph_free(&graph);
                goto fail;
            }
        }
        if (zeros != n - 1 || !hog_graphs_push(&graphs, &count, &capacity, &graph)) {
            hog_graph_free(&graph);
            goto fail;
        }
    }

    *graphs_out = graphs;
    *count_out = count;
    return count > 0;

fail:
    for (int j = 0; j < count; j++) hog_graph_free(&graphs[j]);
    free(graphs);
    return false;
}

static bool hog_make_temp_path(char* path, size_t path_size) {
    char tmpl[] = PAGEHOG_TMP_TEMPLATE;
    int fd = mkstemp(tmpl);
    if (fd < 0) return false;
    close(fd);
    snprintf(path, path_size, "%s", tmpl);
    return true;
}

static adj_t hog_to_page_adjacency(const hog_graph_t* graph) {
    if (graph->n > MAX_VERTICES || graph->m > MAX_EDGES ||
        graph->max_degree > UINT8_MAX) {
        return NULL;
    }
    vertex_degree = (degree_t)graph->max_degree;
    adj_t adjacency = (adj_t)malloc((size_t)graph->n * (size_t)graph->max_degree *
                                    sizeof(vertex_t));
    if (adjacency == NULL) return NULL;
    vertex_degrees = (degree_t*)calloc((size_t)graph->n, sizeof(degree_t));
    full_adjacency_list = (adj_t)malloc((size_t)graph->n * (size_t)graph->max_degree *
                                        sizeof(vertex_t));
    if (vertex_degrees == NULL || full_adjacency_list == NULL) {
        graph_free(adjacency);
        return NULL;
    }
    for (int v = 0; v < graph->n; v++) {
        vertex_t* row = adj_get_neighbors(adjacency, (vertex_t)v);
        for (int i = 0; i < graph->max_degree; i++) {
            row[i] = i < graph->degree[v] ? (vertex_t)graph->adj[v][i] : MAX_VERTICES;
            full_adjacency_list[(size_t)v * (size_t)graph->max_degree + (size_t)i] = row[i];
            if (row[i] != MAX_VERTICES) vertex_degrees[v]++;
        }
    }

    cycle_index_t edge_slot_capacity = (cycle_index_t)graph->n * (degree_t)graph->max_degree;
    num_directed_edges = 2 * (cycle_index_t)graph->m;
    directed_edge_ids = (cycle_index_t*)malloc(edge_slot_capacity * sizeof(cycle_index_t));
    directed_edge_remaining =
        (bool*)malloc((num_directed_edges == 0 ? 1 : num_directed_edges) * sizeof(bool));
    if (directed_edge_ids == NULL || directed_edge_remaining == NULL) {
        graph_free(adjacency);
        return NULL;
    }
    for (cycle_index_t i = 0; i < edge_slot_capacity; i++) directed_edge_ids[i] = MAX_CYCLES;

    directed_edge_lookup_capacity = 1;
    while (directed_edge_lookup_capacity < 4 * num_directed_edges) {
        directed_edge_lookup_capacity <<= 1;
    }
    directed_edge_lookup_keys =
        (uint32_t*)malloc(directed_edge_lookup_capacity * sizeof(uint32_t));
    directed_edge_lookup_ids =
        (cycle_index_t*)malloc(directed_edge_lookup_capacity * sizeof(cycle_index_t));
    if (directed_edge_lookup_keys == NULL || directed_edge_lookup_ids == NULL) {
        graph_free(adjacency);
        return NULL;
    }
    for (cycle_index_t i = 0; i < directed_edge_lookup_capacity; i++) {
        directed_edge_lookup_keys[i] = DIRECTED_EDGE_LOOKUP_EMPTY;
    }

    cycle_index_t edge_id = 0;
    for (vertex_t vertex = 0; vertex < (vertex_t)graph->n; vertex++) {
        vertex_t* neighbors = adj_get_neighbors(adjacency, vertex);
        for (degree_t neighbor_index = 0; neighbor_index < (degree_t)graph->max_degree;
             neighbor_index++) {
            if (neighbors[neighbor_index] == MAX_VERTICES) continue;
            if (edge_id >= num_directed_edges) {
                graph_free(adjacency);
                return NULL;
            }
            directed_edge_ids[vertex * VERTEX_DEGREE + neighbor_index] = edge_id;
            directed_edge_remaining[edge_id] = true;
            directed_edge_lookup_insert(vertex, neighbors[neighbor_index], edge_id);
            edge_id++;
        }
    }
    if (edge_id != num_directed_edges) {
        graph_free(adjacency);
        return NULL;
    }

    cubic_exact_cover_mode = VERTEX_DEGREE == 3;
    for (vertex_t i = 0; i < (vertex_t)graph->n && cubic_exact_cover_mode; i++) {
        cubic_exact_cover_mode = vertex_degrees[i] == 3;
    }
    num_edges_remaining = num_directed_edges;
    return adjacency;
}

static bool hog_to_multigenus_graph(const hog_graph_t* graph, GRAPH mg_graph, ADJAZENZ mg_adj) {
    if (graph->n > knoten || 2 * graph->m > d_kanten) return false;
    memset(mg_graph, 0, sizeof(GRAPH));
    memset(mg_adj, 0, sizeof(ADJAZENZ));
    globalnv = graph->n;
    globalne = graph->m;
    knotenzahl = graph->n;
    mg_graph[0][0] = graph->n;
    for (int v = 0; v < graph->n; v++) {
        mg_adj[v + 1] = (unsigned char)graph->degree[v];
        for (int i = 0; i < graph->degree[v]; i++) {
            mg_graph[v + 1][i] = (unsigned char)(graph->adj[v][i] + 1);
        }
    }
    return true;
}

static void hog_reset_multigenus_options(void) {
    edgelimit = 0;
    compute_lower_bound = 1;
    reduce2 = 1;
    number_reconstruct = 0;
}

static int hog_parse_uint_after(const char* text, const char* pattern) {
    const char* p = strstr(text, pattern);
    if (p == NULL) return -1;
    p += strlen(pattern);
    while (*p && !isdigit((unsigned char)*p)) p++;
    if (!*p) return -1;
    return (int)strtol(p, NULL, 10);
}

static int hog_parse_genus_text(const char* output) {
    int genus = -1;
    char* lower = strdup(output == NULL ? "" : output);
    if (lower == NULL) return -1;
    for (char* p = lower; *p; p++) *p = (char)tolower((unsigned char)*p);

    genus = hog_parse_uint_after(lower, "(genus ");
    if (genus < 0) genus = hog_parse_uint_after(lower, "genus found:");
    if (genus < 0) genus = hog_parse_uint_after(lower, "the genus is ");
    if (genus < 0) genus = hog_parse_uint_after(lower, "graphs with genus ");
    if (genus < 0) {
        char* end = NULL;
        long value = strtol(lower, &end, 10);
        if (end != lower && value >= 0 && value <= INT32_MAX) genus = (int)value;
    }

    free(lower);
    return genus;
}

static char* hog_read_file(const char* path) {
    FILE* file = fopen(path, "rb");
    char* data = NULL;
    long size;
    if (file == NULL) return NULL;
    if (fseek(file, 0, SEEK_END) != 0) goto done;
    size = ftell(file);
    if (size < 0 || fseek(file, 0, SEEK_SET) != 0) goto done;
    data = (char*)malloc((size_t)size + 1);
    if (data == NULL) goto done;
    if (size > 0 && fread(data, 1, (size_t)size, file) != (size_t)size) {
        free(data);
        data = NULL;
        goto done;
    }
    data[size] = '\0';
done:
    fclose(file);
    return data;
}

static void hog_redirect_to_file(const char* path) {
    int fd = open(path, O_WRONLY | O_TRUNC);
    if (fd < 0) _exit(127);
    dup2(fd, STDOUT_FILENO);
    dup2(fd, STDERR_FILENO);
    close(fd);
}

static void hog_child_page(const hog_graph_t* graph, const char* output_path, int page_threads) {
    adj_t adjacency_list = hog_to_page_adjacency(graph);
    if (adjacency_list == NULL) _exit(125);

    hog_redirect_to_file(output_path);
    ph_page_run(adjacency_list, (vertex_t)graph->n, (edge_t)graph->m,
                (degree_t)graph->max_degree, (unsigned)(page_threads < 1 ? 1 : page_threads));
    _exit(0);
}

static void hog_child_multigenus(const hog_graph_t* graph, const char* output_path) {
    GRAPH mg_graph;
    ADJAZENZ mg_adj;
    int genus;

    hog_redirect_to_file(output_path);
    if (!hog_to_multigenus_graph(graph, mg_graph, mg_adj)) _exit(125);
    hog_reset_multigenus_options();
    genus = graph->n < 3 ? 0 : get_genus(mg_graph, mg_adj);
    printf("%d\n", genus);
    fflush(stdout);
    _exit(0);
}

static bool hog_spawn_child(const hog_graph_t* graph, hog_worker_kind_t kind, int page_threads,
                            hog_child_t* child) {
    if (!hog_make_temp_path(child->output_path, sizeof(child->output_path))) return false;
    child->kind = kind;
    child->pid = fork();
    if (child->pid < 0) {
        unlink(child->output_path);
        child->output_path[0] = '\0';
        return false;
    }
    if (child->pid == 0) {
        if (kind == HOG_WORKER_PAGE) {
            hog_child_page(graph, child->output_path, page_threads);
        } else {
            hog_child_multigenus(graph, child->output_path);
        }
        _exit(127);
    }
    return true;
}

static int hog_child_result(const hog_child_t* child) {
    char* output = hog_read_file(child->output_path);
    int genus = hog_parse_genus_text(output);
    free(output);
    return genus;
}

static void hog_cleanup_child(hog_child_t* child) {
    if (child->pid > 0) {
        kill(child->pid, SIGTERM);
        waitpid(child->pid, NULL, 0);
        child->pid = 0;
    }
    if (child->output_path[0] != '\0') {
        unlink(child->output_path);
        child->output_path[0] = '\0';
    }
}

static bool hog_run_graph(const hog_graph_t* graph, int jobs, int* genus_out, bool page_only, bool multi_genus_only) {
    hog_child_t children[2];
    int child_count = 0;
    int finished = 0;
    int page_threads = jobs > 1 ? jobs - 1 : 1;
    bool multigenus_ok = graph->n <= knoten && 2 * graph->m <= d_kanten;

    memset(children, 0, sizeof(children));
    if (graph->max_degree < 2) {
        *genus_out = 0;
        return true;
    }

    if (!multi_genus_only) {
        if (!hog_spawn_child(graph, HOG_WORKER_PAGE, page_threads, &children[child_count])) {
            return false;
        }
        child_count++;
    }
    if (!page_only && multigenus_ok &&
        hog_spawn_child(graph, HOG_WORKER_MULTI_GENUS, 1, &children[child_count])) {
        child_count++;
    }

    while (finished < child_count) {
        int status = 0;
        pid_t pid = waitpid(-1, &status, 0);
        if (pid < 0) {
            if (errno == EINTR) continue;
            break;
        }
        for (int i = 0; i < child_count; i++) {
            if (children[i].pid != pid) continue;
            children[i].pid = 0;
            finished++;
            if (WIFEXITED(status) && WEXITSTATUS(status) == 0) {
                int genus = hog_child_result(&children[i]);
                if (genus >= 0) {
                    *genus_out = genus;
                    for (int j = 0; j < child_count; j++) {
                        if (j != i) hog_cleanup_child(&children[j]);
                    }
                    for (int j = 0; j < child_count; j++) {
                        if (children[j].output_path[0] != '\0') unlink(children[j].output_path);
                    }
                    return true;
                }
            }
        }
    }

    for (int i = 0; i < child_count; i++) hog_cleanup_child(&children[i]);
    return false;
}

static int hog_online_jobs(void) {
#ifdef _SC_NPROCESSORS_ONLN
    long value = sysconf(_SC_NPROCESSORS_ONLN);
    if (value < 2) return 2;
    return value > 1024 ? 1024 : (int)value;
#elif defined(__APPLE__)
    int value = 0;
    size_t size = sizeof(value);
    if (sysctlbyname("hw.ncpu", &value, &size, NULL, 0) == 0 && value >= 2) {
        return value > 1024 ? 1024 : value;
    }
    return 2;
#else
    return 2;
#endif
}

static bool hog_parse_args(int argc, char** argv, hog_input_format_t* format, int* jobs, bool* page_only, bool* multi_genus_only) {
    *format = HOG_INPUT_GRAPH6;
    *jobs = hog_online_jobs();
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--graph6") == 0 || strcmp(argv[i], "-g") == 0) {
            *format = HOG_INPUT_GRAPH6;
        } else if (strcmp(argv[i], "--multicode") == 0 || strcmp(argv[i], "-m") == 0) {
            *format = HOG_INPUT_MULTICODE;
        } else if (strcmp(argv[i], "--page-only")) {
            *page_only = true;
        } else if (strcmp(argv[i], "--multi_genus-only")) {
            *multi_genus_only = true;
        } else if ((strcmp(argv[i], "--jobs") == 0 || strcmp(argv[i], "-j") == 0) &&
                   i + 1 < argc) {
            *jobs = atoi(argv[++i]);
            if (*jobs < 1) *jobs = 1;
        } else if (strcmp(argv[i], "--help") == 0 || strcmp(argv[i], "-h") == 0) {
            puts("usage: page_hog [--graph6|--multicode] [-j jobs] [--page-only] [--multi_genus-only] < graphs");
            exit(0);
        } else {
            return false;
        }
    }
    return true;
}

int main(int argc, char** argv) {
    hog_input_format_t format;
    hog_bytes_t input;
    hog_graph_t* graphs = NULL;
    int graph_count = 0;
    int jobs;
    bool ok;
    bool page_only = false;
    bool multi_genus_only = false;

    if (!hog_parse_args(argc, argv, &format, &jobs, &page_only, &multi_genus_only)) return 2;
    if (!hog_read_stdin(&input)) return 1;

    ok = format == HOG_INPUT_GRAPH6
             ? hog_parse_graph6_input(&input, &graphs, &graph_count)
             : hog_parse_multicode_input(&input, &graphs, &graph_count);
    hog_bytes_free(&input);
    if (!ok) return 1;

    for (int i = 0; i < graph_count; i++) {
        int genus = -1;
        if (!hog_run_graph(&graphs[i], jobs, &genus, page_only, multi_genus_only)) {
            for (int j = 0; j < graph_count; j++) hog_graph_free(&graphs[j]);
            free(graphs);
            return 1;
        }
        printf("%d\n", genus);
        fflush(stdout);
    }

    for (int i = 0; i < graph_count; i++) hog_graph_free(&graphs[i]);
    free(graphs);
    return 0;
}
