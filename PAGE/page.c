// Calculate the minimum genus of an arbitrary connected undirected graph.
// Copyright (C) 2026 Alexander Metzger

// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License along
// with this program; if not, write to the Free Software Foundation, Inc.,
// 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA.

#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdatomic.h>
#ifdef _WIN32
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#define PAGE_THREAD_LOCAL __declspec(thread)
#else
#include <pthread.h>
#include <unistd.h>
#define PAGE_THREAD_LOCAL _Thread_local
#endif

// configuration options:
#define PRINT_PROGRESS true  // whether to print progress messages
#define PROGRESS_BAR_NEWLINE progress_bar_newline // whether to print a newline after each progress bar update
#define DEBUG false  // whether to print debug messages
#define OUTPUT_TO_STDOUT output_to_stdout // whether to output to stdout instead of file
#define ADJACENCY_LIST_FILENAME adj_filename  // input file
#define ADJACENCY_LIST_START start_index      // vertex numbering starts from
#define OUTPUT_FILENAME "page.out"            // output file
#define VERTEX_DEGREE vertex_degree           // must be >= 2
#define PRE_GENUS_LOWER_BOUND pre_genus_lower_bound  // pre-computed lower bound on the genus
#define FIND_FULL_CYCLE_FITTING true // true if the certificate should always be found, otherwise allow stopping if the genus can be determined via formula
#define CONSTRAINED_BY_TWO true // true to branch on a remaining directed edge, otherwise uses the most used vertex
#ifndef ONLY_SIMPLE_CYCLES
#define ONLY_SIMPLE_CYCLES false  // only consider simple cycles
#endif

// assumptions of the program (don't change these):
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
// Symmetry discovery is opportunistic: found automorphisms are used for sound
// pruning, but large graphs skip discovery when it costs more than it saves.
// TODO: find a proper criteria for when/how much symmetry pruning makes sense. 
// For now, the VERTEX_LIMIT and LIMIT will need to be tuned based on the graph
#define AUTOMORPHISM_VERTEX_LIMIT 120
#define AUTOMORPHISM_LIMIT 128
#define AUTOMORPHISM_SEED_CALL_LIMIT 20000ULL
#define AUTOMORPHISM_TOTAL_CALL_LIMIT 200000ULL
#define DIRECTED_EDGE_LOOKUP_EMPTY UINT32_MAX

// consequences of assumptions:
#define START_CYCLE_LENGTH 3
typedef uint8_t degree_t;
#define PRIdegree_t PRIu8
typedef uint16_t vertex_t;
#define PRIvertex_t PRIu16
#define SCNvertex_t SCNu16
typedef uint16_t edge_t;
#define PRIedge_t PRIu16
#define SCNedge_t SCNu16
typedef vertex_t cycle_length_t;  // max length should always be max vertices
#define PRIcycle_length_t PRIvertex_t
#define SCNcycle_length_t SCNvertex_t
typedef uint32_t cycle_index_t;
#define PRIcycle_index_t PRIu32
#define SCNcycle_index_t SCNu32
typedef vertex_t* adj_t;
typedef vertex_t* cycles_t;
typedef cycle_index_t* cbv_t;
typedef cycle_index_t* cbe_t;
#ifdef _WIN32
typedef SRWLOCK page_mutex_t;
typedef HANDLE page_thread_t;
typedef DWORD (WINAPI *page_thread_start_t)(LPVOID);
#define PAGE_MUTEX_INITIALIZER SRWLOCK_INIT
#define PAGE_THREAD_RETURN DWORD WINAPI
#define PAGE_THREAD_RESULT 0
#else
typedef pthread_mutex_t page_mutex_t;
typedef pthread_t page_thread_t;
typedef void* (*page_thread_start_t)(void*);
#define PAGE_MUTEX_INITIALIZER PTHREAD_MUTEX_INITIALIZER
#define PAGE_THREAD_RETURN void*
#define PAGE_THREAD_RESULT NULL
#endif
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

// macros
// assert(condition, message, ...fmt_args)
#define assert(condition, ...)        \
    if (!(condition)) {               \
        fprintf(stderr, __VA_ARGS__); \
        exit(1);                      \
    }

int page_mutex_init(page_mutex_t* mutex) {
#ifdef _WIN32
    InitializeSRWLock(mutex);
    return 0;
#else
    return pthread_mutex_init(mutex, NULL);
#endif
}

void page_mutex_lock(page_mutex_t* mutex) {
#ifdef _WIN32
    AcquireSRWLockExclusive(mutex);
#else
    pthread_mutex_lock(mutex);
#endif
}

void page_mutex_unlock(page_mutex_t* mutex) {
#ifdef _WIN32
    ReleaseSRWLockExclusive(mutex);
#else
    pthread_mutex_unlock(mutex);
#endif
}

void page_mutex_destroy(page_mutex_t* mutex) {
#ifdef _WIN32
    (void)mutex;
#else
    pthread_mutex_destroy(mutex);
#endif
}

int page_thread_create(page_thread_t* thread, page_thread_start_t start, void* arg) {
#ifdef _WIN32
    *thread = CreateThread(NULL, 0, start, arg, 0, NULL);
    return *thread == NULL ? -1 : 0;
#else
    return pthread_create(thread, NULL, start, arg);
#endif
}

int page_thread_join(page_thread_t thread) {
#ifdef _WIN32
    DWORD wait_result = WaitForSingleObject(thread, INFINITE);
    CloseHandle(thread);
    return wait_result == WAIT_OBJECT_0 ? 0 : -1;
#else
    return pthread_join(thread, NULL);
#endif
}

// static variables
static FILE* output_file = NULL;
static vertex_t start_index = 0;
static degree_t vertex_degree = 3;
static cycle_index_t pre_genus_lower_bound = 0;
static char* adj_filename = NULL;
static cycle_length_t smallest_cycle_length;
static bool output_to_stdout = false;
static bool progress_bar_newline = false;
static bool cubic_exact_cover_mode = false;
static degree_t* vertex_degrees = NULL;
static degree_t* initial_vertex_uses = NULL;
static adj_t full_adjacency_list = NULL;
static cycle_index_t num_directed_edges = 0;
static cycle_index_t* directed_edge_ids = NULL;
#ifdef _WIN32
typedef struct {
    cycle_index_t num_edges_remaining;
    bool* directed_edge_remaining;
    bool* transitions_used;
    size_t transitions_used_size;
    cycle_index_t* cycle_edge_conflicts;
    vertex_t* rotation_next;
    vertex_t* rotation_prev;
    degree_t* rotation_pair_count;
    size_t rotation_state_size;
    atomic_bool* search_stop_requested;
} page_worker_state_t;

static DWORD page_worker_state_tls = TLS_OUT_OF_INDEXES;
static page_worker_state_t page_main_worker_state = {0};

page_worker_state_t* page_worker_state_current(void) {
    if (page_worker_state_tls != TLS_OUT_OF_INDEXES) {
        page_worker_state_t* state =
            (page_worker_state_t*)TlsGetValue(page_worker_state_tls);
        if (state != NULL) {
            return state;
        }
    }
    return &page_main_worker_state;
}

#define num_edges_remaining (page_worker_state_current()->num_edges_remaining)
#define directed_edge_remaining (page_worker_state_current()->directed_edge_remaining)
#define transitions_used (page_worker_state_current()->transitions_used)
#define transitions_used_size (page_worker_state_current()->transitions_used_size)
#define cycle_edge_conflicts (page_worker_state_current()->cycle_edge_conflicts)
#define rotation_next (page_worker_state_current()->rotation_next)
#define rotation_prev (page_worker_state_current()->rotation_prev)
#define rotation_pair_count (page_worker_state_current()->rotation_pair_count)
#define rotation_state_size (page_worker_state_current()->rotation_state_size)
#define search_stop_requested (page_worker_state_current()->search_stop_requested)
#else
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
#endif
static uint32_t* directed_edge_lookup_keys = NULL;
static cycle_index_t* directed_edge_lookup_ids = NULL;
static cycle_index_t directed_edge_lookup_capacity = 0;
static automorphism_list_t graph_automorphisms = {0, 0, 0, NULL};
static page_mutex_t output_file_mutex = PAGE_MUTEX_INITIALIZER;

// auxiliary data structures
adj_t adj_load(char* filename, vertex_t* num_vertices, edge_t* num_edges);
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
bool adj_has_edge(adj_t adjacency_list, vertex_t start_vertex, vertex_t end_vertex);

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

void show_progress(double fraction);
void show_solution(cycle_index_t genus_lower_bound, cycle_index_t genus_lower_bound_implied_fit,
                   uint64_t num_search_calls, cycle_index_t num_cycles, bool* used_cycles,
                   cycles_t cycles, cycle_length_t max_cycle_length);

degree_t adj_neighbor_index(adj_t adjacency_list, vertex_t vertex, vertex_t neighbor);
bool cycle_edges_available(adj_t adjacency_list, vertex_t* cycle, cycle_length_t cycle_length);
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
bool search(cycle_index_t cycles_to_use,                    // state
            cycle_index_t max_used_cycles,                  // state
            bool* used_cycles,                              // state
            degree_t* vertex_uses, cycle_index_t* max_fit,  // state
            uint64_t* num_search_calls,                     // state
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
    // NOTE: deliberately does not account for duplicate vertices because this faster more lenient check is advantageous in practice
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

int main(void) {
    start_index = atoi(getenv("S"));
    vertex_degree = atoi(getenv("DEG"));
    if (getenv("GLB") != NULL) {
        pre_genus_lower_bound = atoi(getenv("GLB"));
    }
    adj_filename = getenv("ADJ");
    output_to_stdout = getenv("STDOUT") != NULL;
    progress_bar_newline = getenv("PBN") != NULL;

    if (PRINT_PROGRESS) {
        fprintf(stderr, "Loading adjacency list...\n");
    }

    vertex_t num_vertices;
    edge_t num_edges;
    adj_t adjacency_list = adj_load(ADJACENCY_LIST_FILENAME, &num_vertices, &num_edges);
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
    if (OUTPUT_TO_STDOUT) {
        output_file = stdout;
    } else {
        output_file = fopen(OUTPUT_FILENAME, "w");
        assert(output_file != NULL, "Error opening file %s\n", OUTPUT_FILENAME);
        fprintf(stderr, "Output file: %s\n", OUTPUT_FILENAME);
    }

    cycle_index_t genus_lower_bound =
        genus_lower_bound_from_fit_upper_bound(2 * num_edges / START_CYCLE_LENGTH,
                                               num_vertices, num_edges);
    cycle_index_t genus_lower_bound_implied_fit =
        implied_max_fit_for_genus(genus_lower_bound, num_vertices, num_edges);
    if (PRE_GENUS_LOWER_BOUND > genus_lower_bound) {
        genus_lower_bound = PRE_GENUS_LOWER_BOUND;
        genus_lower_bound_implied_fit =
            implied_max_fit_for_genus(genus_lower_bound, num_vertices, num_edges);
    }
    cycle_index_t max_fit = (2 * num_edges + num_vertices - 1) / num_vertices;
    cycle_index_t genus_upper_bound = implied_max_genus_for_fit(max_fit, num_vertices, num_edges);

    if (genus_lower_bound == genus_upper_bound && !FIND_FULL_CYCLE_FITTING) {
        // we've found the genus!
        if (PRINT_PROGRESS) {
            fprintf(stderr,
                    "Found the genus! It is %" PRIcycle_index_t
                    ". No computation needed when the genus is found via the "
                    "theoretical formula.\n",
                    genus_lower_bound);
        }
        fprintf(output_file, "Genus found: %" PRIcycle_index_t " in 0 iterations:\n",
                genus_lower_bound);
        fclose(output_file);
        graph_free(adjacency_list);
        return 0;
    }

    if (PRINT_PROGRESS) {
        fprintf(stderr,
                "Beginning to narrow down genus (currently between %" PRIcycle_index_t
                " and %" PRIcycle_index_t " with implied fit %" PRIcycle_index_t ")...\n",
                genus_lower_bound, genus_upper_bound, genus_lower_bound_implied_fit);
    }

    uint64_t num_search_calls = 0;
    smallest_cycle_length = num_vertices;
    cycle_length_t second_smallest_cycle_length = 0;
    cycle_index_t num_shortest_cycles = 0;
    cycle_index_t max_shortest_cycles = MAX_CYCLES;
    cycle_index_t verified_packable_shortest_cycles = 0;
    cycle_length_t max_search_cycle_length = ONLY_SIMPLE_CYCLES ? num_vertices : num_edges;
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
            if (PRINT_PROGRESS) {
                fprintf(stderr,
                        "Rechecking cycles of length up to %" PRIcycle_length_t
                        " for the new target fit.\n",
                        cur_max_cycle_length);
            }
        } else {
            if (PRINT_PROGRESS) {
                fprintf(stderr,
                        "Loading auxiliary data structures for cycles of length "
                        "%" PRIcycle_length_t "... ",
                        cur_max_cycle_length);
            }

            cycles_t new_cycles =
                cycle_generate(adjacency_list, num_vertices, cur_max_cycle_length,
                               &num_new_cycles);
            current_length_cycle_count = num_new_cycles;
            num_cycles += num_new_cycles;

            if (num_new_cycles == 0) {
                // no cycles of this length, skip to the next length
                free(new_cycles);
                if (PRINT_PROGRESS) {
                    fprintf(stderr,
                            "No cycles of length %" PRIcycle_length_t " found. Skipping.\n",
                            cur_max_cycle_length);
                }
                continue;
            }
            assert(new_cycles != NULL, "Error: new cycles is NULL but there are new cycles\n");
            if (PRINT_PROGRESS) {
                fprintf(stderr,
                        "Found %" PRIcycle_index_t " cycles of length %" PRIcycle_length_t ".\n",
                        num_new_cycles, cur_max_cycle_length);
            }

            cycle_length_available[cur_max_cycle_length] = true;

            // keep the smallest cycle length up to date
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

            // the smallest cycle length limits how many cycles we can fit and hence the
            // genus
            cycle_index_t genus_lower_bound_from_smallest_cycle_length =
                genus_lower_bound_from_fit_upper_bound(2 * num_edges / smallest_cycle_length,
                                                       num_vertices, num_edges);
            if (genus_lower_bound_from_smallest_cycle_length > genus_lower_bound) {
                genus_lower_bound = genus_lower_bound_from_smallest_cycle_length;
                genus_lower_bound_implied_fit =
                    implied_max_fit_for_genus(genus_lower_bound, num_vertices, num_edges);
            }

            // add the new cycles to the old ones
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

        if (genus_lower_bound < PRE_GENUS_LOWER_BOUND) {
            continue;
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
            if (PRINT_PROGRESS) {
                fprintf(stderr,
                        "Any such fit needs at least %" PRIcycle_index_t
                        " shortest cycles, but at most %" PRIcycle_index_t
                        " can be packed. Skipping search.\n",
                        min_shortest_cycles, max_shortest_cycles);
            }
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
                if (PRINT_PROGRESS) {
                    fprintf(stderr,
                            "Proved at most %" PRIcycle_index_t
                            " shortest cycles can be packed in %" PRId64
                            " packing iterations. Skipping search.\n",
                            max_shortest_cycles, num_packing_calls);
                }
            } else if (packing_result == PACKING_FOUND) {
                verified_packable_shortest_cycles = min_shortest_cycles;
            } else if (PRINT_PROGRESS) {
                fprintf(stderr,
                        "Shortest-cycle packing check inconclusive after %" PRId64
                        " iterations; continuing with full search.\n",
                        num_packing_calls);
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
                if (PRINT_PROGRESS) {
                    fprintf(stderr, "Found proof the implied fit does not exist. ");
                }
            } else if (PRINT_PROGRESS) {
                fprintf(stderr,
                        "Did not find proof the fit does not exist, cannot increase "
                        "lowerbound. ");
            }
            genus_lower_bound_implied_fit =
                implied_max_fit_for_genus(genus_lower_bound, num_vertices, num_edges);
            genus_upper_bound = implied_max_genus_for_fit(max_fit, num_vertices, num_edges);
            bool target_fit_changed = genus_lower_bound_implied_fit != searched_fit;

            assert(genus_upper_bound >= genus_lower_bound, "\nInvalid state: genus lower bound exceeded the upper bound. Check the inputs.\n");

            if (PRINT_PROGRESS) {
                fprintf(stderr,
                        "Narrowing down the genus to "
                        "between %" PRIcycle_index_t " and %" PRIcycle_index_t ". Used %" PRId64
                        " iterations so far.\n",
                        genus_lower_bound, genus_upper_bound, num_search_calls);
            }
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

        if (PRINT_PROGRESS) {
            fprintf(stderr,
                    "Starting search for fit with %" PRIcycle_index_t
                    " cycles or proof it doesn't exist (genus between %" PRIcycle_index_t
                    " and %" PRIcycle_index_t ")...\n",
                    genus_lower_bound_implied_fit, genus_lower_bound, genus_upper_bound);
        }
        show_progress(0.0);

        // keep track of used cycles and vertices
        bool* used_cycles = (bool*)calloc(num_cycles, sizeof(bool));
        assert(used_cycles != NULL, "Error allocating memory for the used cycles\n");
        // vertices should be used exactly VERTEX_USE_LIMIT times
        // so we keep track of the number of times each vertex has been used.
        // this allows us to fail early if a vertex can't be used enough times
        // and to prioritize vertices exploring vertices that have been used more
        // since they constrain the number of possible cycles containing them more
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

        // If the same fit was already ruled out with shorter cycles, any new
        // solution must contain a cycle of the current max length. Every fitting
        // also uses the chosen directed edge exactly once, so use whichever
        // valid start set is smaller.
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
            if (PRINT_PROGRESS) {
                fprintf(stderr,
                        "\nSearching start-cycle branches with %u worker threads.\n",
                        num_start_threads);
            }
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
                show_progress(1.0);
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
            cycle_index_t start_cycles_seen = 0;
            for (cycle_index_t start_i = 0; start_i < num_start_cycles; start_i++) {
                cycle_index_t c = start_cycles[start_i];
                cycle_length_t cycle_length;
                cycles_t cycle = cycle_get(cycles, cur_max_cycle_length, c, &cycle_length);
                memset(transitions_used, 0, transitions_used_size * sizeof(bool));
                cycle_edge_conflicts_clear(num_cycles);
                rotation_state_clear(num_vertices);
                start_cycles_seen++;
                cycle_index_t current_start_cycle_order = start_cycle_order[c];
                if (VERTEX_DEGREE > 2 && !cycle_transitions_good(cycle, cycle_length)) {
                    show_progress(start_cycles_seen / (double)num_start_cycles);
                    continue;
                }
                if (!cycle_try_add_rotation_system(cycle, cycle_length)) {
                    show_progress(start_cycles_seen / (double)num_start_cycles);
                    continue;
                }

                memcpy(vertex_uses, initial_vertex_uses, num_vertices * sizeof(degree_t));

                // mark start cycle as used
                used_cycles[c] = true;
                cycle_set_transitions(cycle, cycle_length, true);
                cycle_set_edge_conflicts(cycle, cycle_length, max_cycles_per_edge,
                                         cycles_by_edge, true);
                for (cycle_length_t i = 0; i < cycle_length; i++) {
                    adj_remove_edge(adjacency_list, cycle[i], cycle[i + 1]);

                    // mark cycle vertices as used
                    vertex_uses[cycle[i]] += 1;
                }

                if (search(genus_lower_bound_implied_fit - 1, genus_lower_bound_implied_fit,
                           used_cycles, vertex_uses, &max_fit, &num_search_calls, num_vertices,
                           num_edges, adjacency_list, cur_max_cycle_length, num_cycles, cycles,
                           max_cycles_per_vertex, cycles_by_vertex, max_cycles_per_edge,
                           cycles_by_edge, start_cycle_order,
                           current_start_cycle_order, &length_feasibility,
                           same_target_fit && cycle_length != cur_max_cycle_length ? 1 : 0)) {
                    // Success!
                    show_progress(1.0);
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

                // mark start cycle as unused
                used_cycles[c] = false;
                cycle_set_transitions(cycle, cycle_length, false);
                cycle_set_edge_conflicts(cycle, cycle_length, max_cycles_per_edge,
                                         cycles_by_edge, false);
                cycle_remove_rotation_system(cycle, cycle_length);
                for (cycle_length_t i = 0; i < cycle_length; i++) {
                    adj_undo_remove_edge(adjacency_list, cycle[i], cycle[i + 1]);
                }

                show_progress(start_cycles_seen / (double)num_start_cycles);
            }
        }

        show_progress(1.0);
        last_searched_fit = searched_fit;

        // we weren't able to find the implied fit, so the bounds need adjusting
        cycle_index_t future_fit_upper_bound = max_possible_fit_with_shortest_bound(
            num_edges, smallest_cycle_length, second_smallest_cycle_length,
            max_shortest_cycles, cur_max_cycle_length + 1);
        cycle_index_t genus_lower_bound_from_fit_bound =
            genus_lower_bound_from_fit_upper_bound(future_fit_upper_bound, num_vertices,
                                                   num_edges);
        if (genus_lower_bound_from_fit_bound > genus_lower_bound) {
            genus_lower_bound = genus_lower_bound_from_fit_bound;
            if (PRINT_PROGRESS) {
                fprintf(stderr, "\nFound proof the implied fit does not exist. ");
            }
        } else if (PRINT_PROGRESS) {
            fprintf(stderr,
                    "\nDid not find proof the fit does not exist, cannot increase "
                    "lowerbound. ");
        }
        genus_lower_bound_implied_fit =
            implied_max_fit_for_genus(genus_lower_bound, num_vertices, num_edges);
        // as a bonus, we might have found a better upper bound
        genus_upper_bound = implied_max_genus_for_fit(max_fit, num_vertices, num_edges);
        bool target_fit_changed = genus_lower_bound_implied_fit != searched_fit;

        if (genus_lower_bound == genus_upper_bound && max_fit == genus_lower_bound_implied_fit) {
            // we've found the genus!
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
                if (!FIND_FULL_CYCLE_FITTING) {
                    if (PRINT_PROGRESS) {
                        fprintf(stderr,
                                "Found the genus! It is %" PRIcycle_index_t
                                ". No further computation needed when the upper and lower bounds have converged.\n",
                                genus_lower_bound);
                    }
                    fprintf(output_file, "Genus found: %" PRIcycle_index_t " in 0 iterations:\n",
                            genus_lower_bound);
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

        if (PRINT_PROGRESS) {
            fprintf(stderr,
                    "Narrowing down the genus to "
                    "between %" PRIcycle_index_t " and %" PRIcycle_index_t ". Used %" PRId64
                    " iterations so far.\n",
                    genus_lower_bound, genus_upper_bound, num_search_calls);
        }

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
    if (PRE_GENUS_LOWER_BOUND > genus_lower_bound) {
        genus_lower_bound = PRE_GENUS_LOWER_BOUND;
        genus_lower_bound_implied_fit =
            implied_max_fit_for_genus(genus_lower_bound, num_vertices, num_edges);
    }
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
        if (PRINT_PROGRESS) {
            fprintf(stderr,
                    "Starting search for fit with %" PRIcycle_index_t
                    " cycles or proof it doesn't exist (genus between %" PRIcycle_index_t
                    " and %" PRIcycle_index_t ")...\n",
                    genus_lower_bound_implied_fit, genus_lower_bound, genus_upper_bound);
        }
        show_progress(0.0);

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

        // Every fitting uses the chosen directed edge exactly once, so it is
        // enough to try the cycles that contain that edge.
        unsigned num_start_threads =
            get_start_branch_thread_count(num_start_cycles, num_cycles);
        if (num_start_threads > 1) {
            if (PRINT_PROGRESS) {
                fprintf(stderr,
                        "\nSearching start-cycle branches with %u worker threads.\n",
                        num_start_threads);
            }
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
                show_progress(1.0);
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
            cycle_index_t start_cycles_seen = 0;
            for (cycle_index_t start_i = 0; start_i < num_start_cycles; start_i++) {
                cycle_index_t c = start_cycles[start_i];
                cycle_length_t cycle_length;
                cycles_t cycle = cycle_get(cycles, cycles_max_cycle_length, c, &cycle_length);
                memset(transitions_used, 0, transitions_used_size * sizeof(bool));
                cycle_edge_conflicts_clear(num_cycles);
                rotation_state_clear(num_vertices);
                start_cycles_seen++;
                cycle_index_t current_start_cycle_order = start_cycle_order[c];
                if (VERTEX_DEGREE > 2 && !cycle_transitions_good(cycle, cycle_length)) {
                    show_progress(start_cycles_seen / (double)num_start_cycles);
                    continue;
                }
                if (!cycle_try_add_rotation_system(cycle, cycle_length)) {
                    show_progress(start_cycles_seen / (double)num_start_cycles);
                    continue;
                }

                memcpy(vertex_uses, initial_vertex_uses, num_vertices * sizeof(degree_t));

                // mark start cycle as used
                used_cycles[c] = true;
                cycle_set_transitions(cycle, cycle_length, true);
                cycle_set_edge_conflicts(cycle, cycle_length, max_cycles_per_edge,
                                         cycles_by_edge, true);
                for (cycle_length_t i = 0; i < cycle_length; i++) {
                    adj_remove_edge(adjacency_list, cycle[i], cycle[i + 1]);

                    // mark cycle vertices as used
                    vertex_uses[cycle[i]] += 1;
                }

                if (search(genus_lower_bound_implied_fit - 1, genus_lower_bound_implied_fit,
                           used_cycles, vertex_uses, &max_fit, &num_search_calls, num_vertices,
                           num_edges, adjacency_list, cycles_max_cycle_length, num_cycles, cycles,
                           max_cycles_per_vertex, cycles_by_vertex, max_cycles_per_edge,
                           cycles_by_edge, start_cycle_order,
                           current_start_cycle_order, &length_feasibility, 0)) {
                    // Success!
                    show_progress(1.0);
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

                // mark start cycle as unused
                used_cycles[c] = false;
                cycle_set_transitions(cycle, cycle_length, false);
                cycle_set_edge_conflicts(cycle, cycle_length, max_cycles_per_edge,
                                         cycles_by_edge, false);
                cycle_remove_rotation_system(cycle, cycle_length);
                for (cycle_length_t i = 0; i < cycle_length; i++) {
                    adj_undo_remove_edge(adjacency_list, cycle[i], cycle[i + 1]);
                }

                show_progress(start_cycles_seen / (double)num_start_cycles);
            }
        }

        free(length_cache_without_required);
        free(length_cache_with_required);
        show_progress(1.0);
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
    if (PRINT_PROGRESS) {
        fprintf(stderr,
                "\nFound a solution! The genus is %" PRIcycle_index_t
                ". Check the output for the %" PRIcycle_index_t " cycles. \n",
                genus_lower_bound, genus_lower_bound_implied_fit);
    }
    fprintf(output_file,
            "Solution with %" PRIcycle_index_t " cycles (genus %" PRIcycle_index_t
            ") found in %" PRId64 " iterations:\n",
            genus_lower_bound_implied_fit, genus_lower_bound, num_search_calls);
    for (cycle_index_t i = 0; i < num_cycles; i++) {
        if (used_cycles[i]) {
            cycle_length_t cycle_length;
            cycles_t cycle = cycle_get(cycles, max_cycle_length, i, &cycle_length);
            for (cycle_length_t j = 0; j < cycle_length + 1; j++) {
                fprintf(output_file, "%" PRIvertex_t " ", cycle[j] + ADJACENCY_LIST_START);
            }
            fprintf(output_file, "\n");
        }
    }
}

static int prev_percent = -1;
void show_progress(double fraction) {
    // E.g. [##########          ] 50%

    if (!PRINT_PROGRESS || ((int)(fraction * 100) == prev_percent)) {
        return;
    }

    if (!PROGRESS_BAR_NEWLINE) {
        fflush(stderr);
        fprintf(stderr, "\r[");
    } else {
        fprintf(stderr, "[");
    }
    for (int i = 0; i < 50; i++) {
        if (i < fraction * 50) {
            fprintf(stderr, "#");
        } else {
            fprintf(stderr, " ");
        }
    }
    fprintf(stderr, "] %d%%", (int)(fraction * 100));
    if (PROGRESS_BAR_NEWLINE) {
        fprintf(stderr, "\n");
    }
    prev_percent = (int)(fraction * 100);
}

bool search(cycle_index_t cycles_to_use,                    // state
            cycle_index_t max_used_cycles,                  // state
            bool* used_cycles,                              // state
            degree_t* vertex_uses, cycle_index_t* max_fit,  // state
            uint64_t* num_search_calls,                     // state
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

    // Pick the tightest uncovered directed-edge column to explore, DLX style.
    // Vertex-use limits are secondary row constraints: a candidate row is
    // counted only if it still fits all vertex capacities.
    vertex_t vertex = 0;
    bool found = false;
    cycle_index_t* cycle_indices = NULL;
    cycle_index_t num_cycles_for_column = 0;
    if (CONSTRAINED_BY_TWO) {
        degree_t max_column_pressure = 0;
        cycle_index_t min_cycle_options = MAX_CYCLES;
        // Degree-5 incidence-style graphs have enough symmetric rows that exact
        // column lookahead can dominate; row acceptance still checks conflicts.
        // TODO: figure out the proper reason and make the optimal fix/tuning for all graphs.
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
                        break;  // we can't do better than this
                    }
                }
            }
            if (min_cycle_options == 0) {
                break;  // we can't do better than this
            }
        }

    } else {
        // we pick the most used vertex that hasn't reached the limit since it
        // constrains the search space of possible cycles more
        degree_t max_uses = 0;
        for (vertex_t i = 0; i < num_vertices; i++) {
            if (vertex_uses[i] < VERTEX_USE_LIMIT && (!found || vertex_uses[i] > max_uses)) {
                found = true;
                vertex = i;
                max_uses = vertex_uses[i];

                if (max_uses == VERTEX_USE_LIMIT - 1) {
                    break;  // we can't do better than this
                }
            }
        }

        if (found) {
            cycle_indices = cbv_get_cycle_indices(cycles_by_vertex, max_cycles_per_vertex, vertex,
                                                  &num_cycles_for_column);
        }
    }
    // if we've explored all vertices fully, this cannot be extended further
    if (!found) {
        return false;
    }
    if (num_cycles_for_column == 0) {
        return false;
    }

    // if we've reached a new maximum fit, print it
    if (max_used_cycles - cycles_to_use > *max_fit) {
        // make sure all vertices are fully used
        bool all_used = true;
        for (vertex_t i = 0; i < num_vertices; i++) {
            if (vertex_uses[i] < VERTEX_USE_LIMIT) {
                all_used = false;
                break;
            }
        }

        if (all_used) {
            *max_fit = max_used_cycles - cycles_to_use;
            page_mutex_lock(&output_file_mutex);
            fprintf(output_file,
                    "New max fit: %" PRIcycle_index_t " (about to try vertex %" PRIvertex_t ")\n",
                    *max_fit, vertex);
            for (cycle_index_t i = 0; i < num_cycles; i++) {
                if (used_cycles[i]) {
                    cycle_length_t cycle_length;
                    vertex_t* cycle = cycle_get(cycles, max_cycle_length, i, &cycle_length);
                    for (cycle_length_t j = 0; j < cycle_length + 1; j++) {
                        fprintf(output_file, "%" PRIvertex_t " ", cycle[j] + ADJACENCY_LIST_START);
                    }
                    fprintf(output_file, "\n");
                }
            }
            fprintf(output_file, "\n");
            fflush(output_file);
            page_mutex_unlock(&output_file_mutex);
        }
    }

    // Look through the possible cycles that satisfy the selected column.
    for (cycle_index_t i = 0; i < num_cycles_for_column; i++) {
        // skip if the cycle is already used
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

        // use the cycle
        used_cycles[cycle_index] = true;
        cycle_set_transitions(cycle, cycle_length, true);
        cycle_set_edge_conflicts(cycle, cycle_length, max_cycles_per_edge,
                                 cycles_by_edge, true);
        for (cycle_length_t j = 0; j < cycle_length; j++) {
            adj_remove_edge(adjacency_list, cycle[j], cycle[j + 1]);

            // mark cycle vertices as used
            vertex_uses[cycle[j]]++;
            assert(vertex_uses[cycle[j]] <= VERTEX_USE_LIMIT,
                   "\nVertex %" PRIvertex_t " used too many times\n", cycle[j]);
        }

        // if this is the final cycle needed to cover all edges, we're done
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

                    // un-use the cycle vertices
                    vertex_uses[cycle[j]]--;
                }
                continue;
            }
            if (!cubic_exact_cover_mode) {
                // check that all vertices have been used enough times
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

                        // un-use the cycle vertices
                        vertex_uses[cycle[j]]--;
                    }
                    continue;
                }
            }
            return true;
        }

        // otherwise, continue adding cycles
        if (search(cycles_to_use - 1, max_used_cycles, used_cycles, vertex_uses, max_fit,
                   num_search_calls, num_vertices, num_edges, adjacency_list, max_cycle_length,
                   num_cycles, cycles, max_cycles_per_vertex, cycles_by_vertex,
                   max_cycles_per_edge, cycles_by_edge,
                   start_cycle_order, current_start_cycle_order, length_feasibility,
                   next_required_cycles_to_use)) {
            return true;  // as soon as we succeed, we're done
        }

        // un-use the cycle
        used_cycles[cycle_index] = false;
        cycle_set_transitions(cycle, cycle_length, false);
        cycle_set_edge_conflicts(cycle, cycle_length, max_cycles_per_edge,
                                 cycles_by_edge, false);
        cycle_remove_rotation_system(cycle, cycle_length);
        for (cycle_length_t j = 0; j < cycle_length; j++) {
            adj_undo_remove_edge(adjacency_list, cycle[j], cycle[j + 1]);

            // un-use the cycle vertices
            vertex_uses[cycle[j]]--;
        }
    }

    // if we haven't returned true by now, we've failed
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

bool cycle_edges_available(adj_t adjacency_list, vertex_t* cycle, cycle_length_t cycle_length) {
    for (cycle_length_t i = 0; i < cycle_length; i++) {
        if (!adj_has_edge(adjacency_list, cycle[i], cycle[i + 1])) {
            return false;
        }
    }
    return true;
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

unsigned get_online_processor_count(void) {
#ifdef _WIN32
    SYSTEM_INFO system_info;
    GetSystemInfo(&system_info);
    return system_info.dwNumberOfProcessors > 0 ? system_info.dwNumberOfProcessors : 1;
#elif defined(_SC_NPROCESSORS_ONLN)
    long online_processors = sysconf(_SC_NPROCESSORS_ONLN);
    return online_processors > 0 ? (unsigned)online_processors : 1;
#else
    return 1;
#endif
}

unsigned get_start_branch_thread_count(cycle_index_t num_start_cycles,
                                       cycle_index_t num_cycles) {
    if (num_start_cycles < 4) {
        return 1;
    }

    char* thread_env = getenv("CG_THREADS");
    if (thread_env == NULL || thread_env[0] == '\0') {
        thread_env = getenv("THREADS");
    }
    bool explicit_thread_count = thread_env != NULL && thread_env[0] != '\0';
    unsigned threads = 0;
    if (explicit_thread_count) {
        char* end = NULL;
        unsigned long parsed = strtoul(thread_env, &end, 10);
        if (end != thread_env && parsed > 0) {
            threads = parsed > START_BRANCH_THREAD_CAP ? START_BRANCH_THREAD_CAP
                                                       : (unsigned)parsed;
        }
    } else {
        if (num_cycles < START_BRANCH_PARALLEL_MIN_CYCLES) {
            return 1;
        }
        threads = get_online_processor_count();
        if (threads > START_BRANCH_THREAD_CAP) {
            threads = START_BRANCH_THREAD_CAP;
        }
    }

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
#ifdef _WIN32
    page_worker_state_tls = TlsAlloc();
    assert(page_worker_state_tls != TLS_OUT_OF_INDEXES,
           "Error allocating start branch worker TLS\n");
#endif

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
#ifdef _WIN32
    TlsFree(page_worker_state_tls);
    page_worker_state_tls = TLS_OUT_OF_INDEXES;
#endif
    page_mutex_destroy(&context->mutex);
    return context->solution_found;
}

PAGE_THREAD_RETURN start_branch_worker(void* arg) {
#ifdef _WIN32
    page_worker_state_t worker_state = {0};
    assert(TlsSetValue(page_worker_state_tls, &worker_state) != 0,
           "Error setting start branch worker TLS\n");
#endif
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
        if (PRINT_PROGRESS) {
            show_progress(context->completed_start_cycles /
                          (double)context->num_start_cycles);
        }
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
#ifdef _WIN32
    TlsSetValue(page_worker_state_tls, NULL);
#endif
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

adj_t adj_load(char* filename, vertex_t* num_vertices, edge_t* num_edges) {
    FILE* fp = fopen(filename, "r");
    assert(fp != NULL, "Error opening file %s\n", filename);

    // number of vertices and edges are the two first numbers
    assert(fscanf(fp, "%" SCNvertex_t " %" SCNedge_t "", num_vertices, num_edges) == 2,
           "Error reading the first line of %s\n", filename);

    adj_t adjacency_list = (adj_t)malloc(*num_vertices * VERTEX_DEGREE * sizeof(vertex_t));
    assert(adjacency_list != NULL, "Error allocating memory for the adjacency list\n");
    vertex_degrees = (degree_t*)malloc(*num_vertices * sizeof(degree_t));
    assert(vertex_degrees != NULL, "Error allocating memory for the vertex degrees\n");
    for (vertex_t i = 0; i < *num_vertices; i++) {
        vertex_degrees[i] = 0;
    }
    for (vertex_t i = 0; i < *num_vertices * VERTEX_DEGREE; i++) {
        assert(fscanf(fp, "%" SCNvertex_t, &adjacency_list[i]) == 1,
               "Error reading the adjacency list from %s\n", filename);
        if (adjacency_list[i] != MAX_VERTICES) {
            adjacency_list[i] -= ADJACENCY_LIST_START;
            vertex_degrees[i / VERTEX_DEGREE]++;
        }
    }
    full_adjacency_list =
        (adj_t)malloc(*num_vertices * VERTEX_DEGREE * sizeof(vertex_t));
    assert(full_adjacency_list != NULL,
           "Error allocating memory for the full adjacency list\n");
    for (vertex_t i = 0; i < *num_vertices * VERTEX_DEGREE; i++) {
        full_adjacency_list[i] = adjacency_list[i];
    }

    cycle_index_t edge_slot_capacity = (cycle_index_t)(*num_vertices) * VERTEX_DEGREE;
    num_directed_edges = 2 * (cycle_index_t)(*num_edges);
    directed_edge_ids =
        (cycle_index_t*)malloc(edge_slot_capacity * sizeof(cycle_index_t));
    directed_edge_remaining =
        (bool*)malloc((num_directed_edges == 0 ? 1 : num_directed_edges) * sizeof(bool));
    assert(directed_edge_ids != NULL && directed_edge_remaining != NULL,
           "Error allocating memory for the directed edge state\n");
    for (cycle_index_t i = 0; i < edge_slot_capacity; i++) {
        directed_edge_ids[i] = MAX_CYCLES;
    }

    directed_edge_lookup_capacity = 1;
    while (directed_edge_lookup_capacity < 4 * num_directed_edges) {
        directed_edge_lookup_capacity <<= 1;
    }
    directed_edge_lookup_keys =
        (uint32_t*)malloc(directed_edge_lookup_capacity * sizeof(uint32_t));
    directed_edge_lookup_ids =
        (cycle_index_t*)malloc(directed_edge_lookup_capacity * sizeof(cycle_index_t));
    assert(directed_edge_lookup_keys != NULL && directed_edge_lookup_ids != NULL,
           "Error allocating memory for the directed edge lookup\n");
    for (cycle_index_t i = 0; i < directed_edge_lookup_capacity; i++) {
        directed_edge_lookup_keys[i] = DIRECTED_EDGE_LOOKUP_EMPTY;
    }

    cycle_index_t edge_id = 0;
    for (vertex_t vertex = 0; vertex < *num_vertices; vertex++) {
        vertex_t* neighbors = adj_get_neighbors(adjacency_list, vertex);
        for (degree_t neighbor_index = 0; neighbor_index < VERTEX_DEGREE; neighbor_index++) {
            if (neighbors[neighbor_index] == MAX_VERTICES) {
                continue;
            }
            assert(edge_id < num_directed_edges,
                   "Error: adjacency list contains more than %" PRIcycle_index_t
                   " directed edges\n",
                   num_directed_edges);
            directed_edge_ids[vertex * VERTEX_DEGREE + neighbor_index] = edge_id;
            directed_edge_remaining[edge_id] = true;
            directed_edge_lookup_insert(vertex, neighbors[neighbor_index], edge_id);
            edge_id++;
        }
    }
    assert(edge_id == num_directed_edges,
           "Error: adjacency list contains %" PRIcycle_index_t
           " directed edges, expected %" PRIcycle_index_t "\n",
           edge_id, num_directed_edges);

    cubic_exact_cover_mode = VERTEX_DEGREE == 3;
    for (vertex_t i = 0; i < *num_vertices && cubic_exact_cover_mode; i++) {
        cubic_exact_cover_mode = vertex_degrees[i] == 3;
    }

    fclose(fp);

    if (PRINT_PROGRESS) {
        fprintf(stderr, "Read the adjacency list from %s\n", filename);
        fprintf(stderr, "\tNumber of vertices: %" PRIvertex_t " \n", *num_vertices);
        fprintf(stderr, "\tNumber of edges: %" PRIedge_t " (%" PRIedge_t " directed)\n", *num_edges,
                2 * *num_edges);
        fprintf(stderr, "\tFirst 5 vertices (with neighbors): ");
        vertex_t vertices_to_print = *num_vertices < 5 ? *num_vertices : 5;
        degree_t neighbors_to_print = VERTEX_DEGREE < 3 ? VERTEX_DEGREE : 3;
        for (vertex_t v = 0; v < vertices_to_print; v++) {
            fprintf(stderr, "%" PRIvertex_t "(", v);
            for (degree_t d = 0; d < neighbors_to_print; d++) {
                if (d > 0) {
                    fprintf(stderr, " ");
                }
                fprintf(stderr, "%" PRIvertex_t,
                        adj_get_neighbors(adjacency_list, v)[d] + ADJACENCY_LIST_START);
            }
            fprintf(stderr, ") ");
        }
        fprintf(stderr, "\n");
    }

    num_edges_remaining = num_directed_edges;
    return adjacency_list;
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

    if (PRINT_PROGRESS && automorphisms->count > 0) {
        fprintf(stderr,
                "\033[2K\rFound %" PRIcycle_index_t
                " graph automorphism(s) for symmetry pruning.\n",
                automorphisms->count);
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

// must have been previously removed, otherwise undefined behavior
void adj_undo_remove_edge(adj_t adjacency_list, vertex_t start_vertex, vertex_t end_vertex) {
    cycle_index_t edge_id = adj_edge_id(adjacency_list, start_vertex, end_vertex);
    assert(!directed_edge_remaining[edge_id],
           "Error: directed edge %" PRIvertex_t " -> %" PRIvertex_t
           " was restored before being removed\n",
           start_vertex, end_vertex);
    num_edges_remaining += 1;
    directed_edge_remaining[edge_id] = true;
}

bool adj_has_edge(adj_t adjacency_list, vertex_t start_vertex, vertex_t end_vertex) {
    cycle_index_t edge_id;
    if (!adj_try_edge_id(adjacency_list, start_vertex, end_vertex, &edge_id)) {
        return false;
    }
    return directed_edge_remaining[edge_id];
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
        // double the capacity
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
                    continue;  // if this doesn't complete a cycle, keep looking
                }
                if (!ONLY_SIMPLE_CYCLES) {
                    // when not dealing with purely simple cycles, we need some extra
                    // checks

                    // prevent backtracking
                    if (path[1] == path[path_length - 1] || path[path_length - 2] == path[0]) {
                        break;
                    }

                    // prevent repeated directed edges
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
                        path_has_reverse_transition(path, path_length, path[path_length - 1],
                                                    path[0], path[1])) {
                        break;
                    }
                }
                // we've found a cycle
                buffer[cycle_length + 1] = path[0];
                fifo_push(&cycle_list, buffer);
                break;
            }
        } else {
            for (degree_t i = 0; i < VERTEX_DEGREE; i++) {
                vertex_t neighbor = neighbors[i];
                if (neighbor == MAX_VERTICES) continue;
                if (ONLY_SIMPLE_CYCLES ? (neighbor <= path[0]) : (neighbor < path[0])) {
                    continue;
                }
                if (ONLY_SIMPLE_CYCLES) {
                    // don't allow repeated vertices in the path (implicitly also prevents
                    // backtracking and repeated directed edges)
                    bool neighbor_in_path = false;
                    for (cycle_length_t j = 0; j < path_length; j++) {
                        if (path[j] == neighbor) {
                            neighbor_in_path = true;
                            break;
                        }
                    }
                    if (neighbor_in_path) {
                        continue;
                    }
                } else {
                    if (path_length >= 2 && neighbor == path[path_length - 2]) {
                        // Skip the neighbor if it is the previous vertex in the path (no
                        // backtracking).
                        continue;
                    }

                    // skip if any directed edge is repeated, i.e. matches the one we are
                    // currently adding from path[path_length - 1] to neighbor
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

    if (DEBUG) {
        fprintf(stderr, "Generated cycles of length: %" PRIcycle_length_t "\n", cycle_length);
        fprintf(stderr, "\tNumber of cycles: %" PRIcycle_index_t "\n", *num_cycles);
        fprintf(stderr, "\tFirst 5 cycles:\n");
        for (cycle_index_t i = 0; i < (*num_cycles > 5 ? 5 : *num_cycles); i++) {
            fprintf(stderr, "\t\t%d: ", i);
            for (cycle_length_t j = 0; j < cycle_length + 1; j++) {
                fprintf(stderr, "%02" PRIvertex_t " ", cycle_get(cycles, cycle_length, i, NULL)[j]);
            }
            fprintf(stderr, "\n");
        }
    }

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
    // find the number of cycles per vertex
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

    // find the maximum number of cycles per vertex
    *max_cycles_per_vertex = 0;
    for (vertex_t i = 0; i < num_vertices; i++) {
        if (cycles_per_vertex[i] > *max_cycles_per_vertex) {
            *max_cycles_per_vertex = cycles_per_vertex[i];
        }
    }

    cbv_t cycles_by_vertex =
        (cbv_t)malloc(num_vertices * (*max_cycles_per_vertex + 1) * sizeof(cycle_index_t));
    assert(cycles_by_vertex != NULL, "Error allocating memory for the cycles by vertex\n");

    // fill in the cycles by vertex
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
        if (ONLY_SIMPLE_CYCLES) {
            // For simple cycles, each vertex can only occur once in a cycle so we
            // already have the correct number of cycles
            assert(num_cycles_for_vertex == cycles_per_vertex[i],
                   "Error filling in the cycles by vertex %" PRIvertex_t " (%" PRIcycle_index_t
                   " != %" PRIcycle_index_t ")\n",
                   i, num_cycles_for_vertex, cycles_per_vertex[i]);
        } else {
            // otherwise, we overcounted and need to correct
            cycles_by_vertex[i * (*max_cycles_per_vertex + 1)] = num_cycles_for_vertex;
        }
    }

    if (DEBUG) {
        fprintf(stderr, "Organized cycles by vertex\n");
        fprintf(stderr, "\tMax cycles per vertex: %" PRIcycle_index_t "\n", *max_cycles_per_vertex);
        fprintf(stderr, "\tLast 2 cycles of vertex 0 and 1:\n");
        for (uint8_t i = num_vertices - 2; i < num_vertices; i++) {
            cycle_index_t num_cycles;
            cycle_index_t* cycle_indices =
                cbv_get_cycle_indices(cycles_by_vertex, *max_cycles_per_vertex, i, &num_cycles);
            fprintf(stderr, "\t\t%d:\n", i);
            for (cycle_index_t j = 0; j < num_cycles && j < 2; j++) {
                fprintf(stderr, "\t\t\t%" PRIcycle_index_t " / %" PRIcycle_index_t ": ", j,
                        num_cycles);
                vertex_t* cycle =
                    cycle_get(cycles, max_cycle_length, cycle_indices[j], &cycle_length);
                for (cycle_length_t h = 0; h < cycle_length + 1; h++) {
                    fprintf(stderr, "%02" PRIvertex_t " ", cycle[h]);
                }
                fprintf(stderr, "\n");
            }
        }
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
    // Every valid fitting contains at least one raw start cycle. If an
    // automorphism maps one raw start cycle to another, searching the earlier
    // representative also searches an isomorphic fitting.
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

    if (PRINT_PROGRESS && *pruned_start_count < raw_start_count) {
        fprintf(stderr,
                "\033[2K\rSymmetry pruning reduced start cycles from %" PRIcycle_index_t
                " to %" PRIcycle_index_t ".\n",
                raw_start_count, *pruned_start_count);
        show_progress(0.0);
    }

    free(is_start_cycle);
    free(start_cycle_seen);
    free(queue);
    free(image);
    return start_cycles;
}
