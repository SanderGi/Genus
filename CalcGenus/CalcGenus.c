// Narrows down the genus of an arbitrary graph given its adjacency list.
// Prints the maximum cycle fitting as evidence. A fitting is a set of simple
// cycles (length greater than 2) that use each directed edge exactly once.
// These are the faces in Euler's formula: F - E + V = 2 - 2g. Run with `make
// run`. Works better for regular graphs (preferably of low degree).

#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// configuration options:
#define PRINT_PROGRESS true  // whether to print progress messages
// whether to print a newline after each progress bar update:
#define PROGRESS_BAR_NEWLINE progress_bar_newline
#define DEBUG false  // whether to print debug messages
// whether to output to stdout instead of file:
#define OUTPUT_TO_STDOUT output_to_stdout
#define ADJACENCY_LIST_FILENAME adj_filename  // input file
#define ADJACENCY_LIST_START start_index      // vertex numbering starts from
#define OUTPUT_FILENAME "CalcGenus.out"       // output file
#define VERTEX_DEGREE vertex_degree           // must be >= 2
#define PRE_GENUS_LOWER_BOUND pre_genus_lower_bound  // pre-computed lower bound on the genus
// true if it should to find the full cycle fitting, otherwise stops early once
// it is clear it exists (doesn't quite work with value false yet):
#define FIND_FULL_CYCLE_FITTING true
// true to branch on a remaining directed edge, otherwise uses the most used vertex
#define CONSTRAINED_BY_TWO true
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

// macros
// assert(condition, message, ...fmt_args)
#define assert(condition, ...)        \
    if (!(condition)) {               \
        fprintf(stderr, __VA_ARGS__); \
        exit(1);                      \
    }

// static variables
static FILE* output_file = NULL;
static vertex_t start_index = 0;
static degree_t vertex_degree = 3;
static cycle_index_t pre_genus_lower_bound = 0;
static char* adj_filename = NULL;
static edge_t num_edges_remaining = 0;
static cycle_length_t smallest_cycle_length;
static bool output_to_stdout = false;
static bool progress_bar_newline = false;
static degree_t* vertex_degrees = NULL;
static degree_t* initial_vertex_uses = NULL;
static adj_t full_adjacency_list = NULL;
static bool* transitions_used = NULL;
static size_t transitions_used_size = 0;

// auxiliary data structures
adj_t adj_load(char* filename, vertex_t* num_vertices, edge_t* num_edges);
vertex_t* adj_get_neighbors(adj_t adjacency_list, vertex_t vertex);
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

bool is_valid_rotation_system(bool* used_cycles, cycles_t cycles, cycle_length_t max_cycle_length,
                              cycle_index_t num_cycles, vertex_t num_vertices,
                              cycle_index_t cycle_to_check);
degree_t adj_neighbor_index(adj_t adjacency_list, vertex_t vertex, vertex_t neighbor);
bool cycle_transitions_good(vertex_t* cycle, cycle_length_t cycle_length);
void cycle_set_transitions(vertex_t* cycle, cycle_length_t cycle_length, bool used);
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

    if (genus_lower_bound == genus_upper_bound) {
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
        free(adjacency_list);
        free(vertex_degrees);
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
    cycle_index_t last_searched_fit = MAX_CYCLES;
    for (cycle_length_t cur_max_cycle_length = START_CYCLE_LENGTH;
         cur_max_cycle_length <= max_search_cycle_length; cur_max_cycle_length++) {
        if (PRINT_PROGRESS) {
            fprintf(stderr,
                    "Loading auxiliary data structures for cycles of length "
                    "%" PRIcycle_length_t "... ",
                    cur_max_cycle_length);
        }

        cycle_index_t num_new_cycles;
        cycles_t new_cycles =
            cycle_generate(adjacency_list, num_vertices, cur_max_cycle_length, &num_new_cycles);
        num_cycles += num_new_cycles;

        if (num_new_cycles == 0) {
            // no cycles of this length, skip to the next length
            free(new_cycles);
            if (PRINT_PROGRESS) {
                fprintf(stderr, "No cycles of length %" PRIcycle_length_t " found. Skipping.\n",
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
        if (cur_max_cycle_length < smallest_cycle_length) {
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
                    combined[(num_cycles - num_new_cycles + i) * (cur_max_cycle_length + 2) + j] =
                        new_cycles[i * (cur_max_cycle_length + 2) + j];
                }
            }
            cycles_max_cycle_length = cur_max_cycle_length;
            free(cycles);
            free(new_cycles);
            cycles = combined;
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

            if (genus_lower_bound == genus_upper_bound && !FIND_FULL_CYCLE_FITTING) {
                fprintf(stderr, "The genus is %" PRIcycle_index_t ".\n", genus_lower_bound);
                free(adjacency_list);
                free(vertex_degrees);
                free(cycles);
                free(cycle_length_available);
                fclose(output_file);
                return 0;
            }

            if (PRINT_PROGRESS) {
                fprintf(stderr,
                        "Narrowing down the genus to "
                        "between %" PRIcycle_index_t " and %" PRIcycle_index_t ". Used %" PRId64
                        " iterations so far.\n",
                        genus_lower_bound, genus_upper_bound, num_search_calls);
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
        cycle_index_t num_start_cycles =
            use_max_length_start ? num_new_cycles : num_edge_start_cycles;
        cycle_index_t num_start_cycles_for_vertex = num_new_cycles;
        cycle_index_t* start_cycle_indices = NULL;
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
            start_cycle_indices = cbe_get_cycle_indices(cycles_by_edge, max_cycles_per_edge,
                                                        start_vertex, end_vertex,
                                                        &num_start_cycles_for_vertex);
        }

        // If the same fit was already ruled out with shorter cycles, any new
        // solution must contain a cycle of the current max length. Every fitting
        // also uses the chosen directed edge exactly once, so use whichever
        // valid start set is smaller.
        cycle_index_t start_cycles_seen = 0;
        for (cycle_index_t start_i = 0; start_i < num_start_cycles_for_vertex; start_i++) {
            cycle_index_t c = use_max_length_start ? num_cycles - num_new_cycles + start_i
                                                   : start_cycle_indices[start_i];
            cycle_length_t cycle_length;
            cycles_t cycle = cycle_get(cycles, cur_max_cycle_length, c, &cycle_length);
            memset(transitions_used, 0, transitions_used_size * sizeof(bool));
            start_cycle_order[c] = start_cycles_seen;
            start_cycles_seen++;
            cycle_index_t current_start_cycle_order = start_cycle_order[c];
            if (VERTEX_DEGREE > 2 && !cycle_transitions_good(cycle, cycle_length)) {
                show_progress(start_cycles_seen / (double)num_start_cycles);
                continue;
            }
            if (!is_valid_rotation_system(used_cycles, cycles, cur_max_cycle_length, num_cycles,
                                          num_vertices, c)) {
                show_progress(start_cycles_seen / (double)num_start_cycles);
                continue;
            }

            memcpy(vertex_uses, initial_vertex_uses, num_vertices * sizeof(degree_t));

            // mark start cycle as used
            used_cycles[c] = true;
            cycle_set_transitions(cycle, cycle_length, true);
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
                free(adjacency_list);
                free(vertex_degrees);
                free(vertex_uses);
                free(cycles);
                free(cycles_by_vertex);
                free(cycles_by_edge);
                free(used_cycles);
                free(start_cycle_order);
                free(cycle_length_available);
                free(length_cache_without_required);
                free(length_cache_with_required);
                free(transitions_used);
                transitions_used = NULL;
                fclose(output_file);
                return 0;
            }

            // mark start cycle as unused
            used_cycles[c] = false;
            cycle_set_transitions(cycle, cycle_length, false);
            for (cycle_length_t i = 0; i < cycle_length; i++) {
                adj_undo_remove_edge(adjacency_list, cycle[i], cycle[i + 1]);
            }

            show_progress(start_cycles_seen / (double)num_start_cycles);
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

        if (genus_lower_bound == genus_upper_bound &&
            (!FIND_FULL_CYCLE_FITTING || max_fit == genus_lower_bound_implied_fit)) {
            // we've found the genus!
            show_solution(genus_lower_bound, max_fit, num_search_calls, num_cycles, used_cycles,
                          cycles, cur_max_cycle_length);
            free(used_cycles);
            free(start_cycle_order);
            free(vertex_uses);
            free(adjacency_list);
            free(vertex_degrees);
            free(cycles);
            free(cycles_by_vertex);
            free(cycles_by_edge);
            free(cycle_length_available);
            free(length_cache_without_required);
            free(length_cache_with_required);
            free(transitions_used);
            transitions_used = NULL;
            fclose(output_file);
            return 0;
        }
        assert(FIND_FULL_CYCLE_FITTING || (genus_lower_bound < genus_upper_bound),
               "Error: genus lower bound (%" PRIcycle_index_t
               ") is greater than upper bound (%" PRIcycle_index_t
               " from max_fit %" PRIcycle_index_t ")\n",
               genus_lower_bound, genus_upper_bound, max_fit);

        if (PRINT_PROGRESS) {
            fprintf(stderr,
                    "Narrowing down the genus to "
                    "between %" PRIcycle_index_t " and %" PRIcycle_index_t ". Used %" PRId64
                    " iterations so far.\n",
                    genus_lower_bound, genus_upper_bound, num_search_calls);
        }

        free(used_cycles);
        free(start_cycle_order);
        free(vertex_uses);
        free(cycles_by_vertex);
        free(cycles_by_edge);
        free(length_cache_without_required);
        free(length_cache_with_required);
        free(transitions_used);
        transitions_used = NULL;
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
    vertex_t start_vertex;
    vertex_t end_vertex;
    cycle_index_t num_start_cycles =
        choose_start_edge(num_vertices, adjacency_list, max_cycles_per_edge, cycles_by_edge,
                          &start_vertex, &end_vertex);
    cycle_index_t num_start_cycles_for_vertex;
    cycle_index_t* start_cycle_indices = cbe_get_cycle_indices(
        cycles_by_edge, max_cycles_per_edge, start_vertex, end_vertex,
        &num_start_cycles_for_vertex);
    cycle_index_t* start_cycle_order = (cycle_index_t*)malloc(num_cycles * sizeof(cycle_index_t));
    assert(start_cycle_order != NULL, "Error allocating memory for the start cycle order\n");
    memset(start_cycle_order, 0xff, num_cycles * sizeof(cycle_index_t));

    while (FIND_FULL_CYCLE_FITTING ? genus_lower_bound <= genus_upper_bound
                                   : genus_lower_bound < genus_upper_bound) {
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
        cycle_index_t start_cycles_seen = 0;
        for (cycle_index_t start_i = 0; start_i < num_start_cycles_for_vertex; start_i++) {
            cycle_index_t c = start_cycle_indices[start_i];
            cycle_length_t cycle_length;
            cycles_t cycle = cycle_get(cycles, cycles_max_cycle_length, c, &cycle_length);
            memset(transitions_used, 0, transitions_used_size * sizeof(bool));
            start_cycle_order[c] = start_cycles_seen;
            start_cycles_seen++;
            cycle_index_t current_start_cycle_order = start_cycle_order[c];
            if (VERTEX_DEGREE > 2 && !cycle_transitions_good(cycle, cycle_length)) {
                show_progress(start_cycles_seen / (double)num_start_cycles);
                continue;
            }
            if (!is_valid_rotation_system(used_cycles, cycles, cycles_max_cycle_length, num_cycles,
                                          num_vertices, c)) {
                show_progress(start_cycles_seen / (double)num_start_cycles);
                continue;
            }

            memcpy(vertex_uses, initial_vertex_uses, num_vertices * sizeof(degree_t));

            // mark start cycle as used
            used_cycles[c] = true;
            cycle_set_transitions(cycle, cycle_length, true);
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
                free(adjacency_list);
                free(vertex_degrees);
                free(vertex_uses);
                free(cycles);
                free(cycles_by_vertex);
                free(cycles_by_edge);
                free(used_cycles);
                free(start_cycle_order);
                free(cycle_length_available);
                free(length_cache_without_required);
                free(length_cache_with_required);
                free(transitions_used);
                transitions_used = NULL;
                fclose(output_file);
                return 0;
            }

            // mark start cycle as unused
            used_cycles[c] = false;
            cycle_set_transitions(cycle, cycle_length, false);
            for (cycle_length_t i = 0; i < cycle_length; i++) {
                adj_undo_remove_edge(adjacency_list, cycle[i], cycle[i + 1]);
            }

            show_progress(start_cycles_seen / (double)num_start_cycles);
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

    free(adjacency_list);
    free(vertex_degrees);
    free(cycles);
    free(cycles_by_vertex);
    free(cycles_by_edge);
    free(used_cycles);
    free(start_cycle_order);
    free(vertex_uses);
    free(cycle_length_available);
    free(transitions_used);
    transitions_used = NULL;
    fclose(output_file);

    if (FIND_FULL_CYCLE_FITTING) {
        fprintf(stderr,
                "Was not able to fit any cycles. Double check the settings "
                "and adjacency list.\n");
        return 1;
    } else {
        fprintf(stderr, "The genus is %" PRIcycle_index_t ".\n", genus_lower_bound);
        return 0;
    }
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

bool is_valid_rotation_system(bool* used_cycles, cycles_t cycles, cycle_length_t max_cycle_length,
                              cycle_index_t num_cycles, vertex_t num_vertices,
                              cycle_index_t cycle_to_check) {
    if (VERTEX_DEGREE <= 5) {
        return true;  // ijk criterion is sufficient
    }

    // TODO: optimize by storing the rotation in the adjacency list as cycles
    // are added

    edge_t row_size = 2 * VERTEX_DEGREE + 1;
    vertex_t* pairs = (vertex_t*)malloc(row_size * num_vertices * sizeof(vertex_t));
    assert(pairs != NULL, "Error allocating memory for the pairs\n");
    bool* pair_seen = (bool*)malloc(VERTEX_DEGREE * sizeof(bool));
    assert(pair_seen != NULL, "Error allocating memory for the pair seen flags\n");
    for (vertex_t i = 0; i < num_vertices; i++) {
        pairs[i * row_size] = 0;
    }

    for (cycle_index_t c = 0; c < num_cycles; c++) {
        if (used_cycles[c] || c == cycle_to_check) {
            cycle_length_t cycle_length;
            vertex_t* cycle = cycle_get(cycles, max_cycle_length, c, &cycle_length);

            degree_t num_pairs = pairs[cycle[0] * row_size];
            pairs[cycle[0] * row_size + 2 * num_pairs + 1] = cycle[cycle_length - 1];
            pairs[cycle[0] * row_size + 2 * num_pairs + 2] = cycle[1];
            pairs[cycle[0] * row_size] = num_pairs + 1;

            for (cycle_length_t i = 1; i < cycle_length - 1; i++) {
                degree_t num_pairs = pairs[cycle[i] * row_size];
                pairs[cycle[i] * row_size + 2 * num_pairs + 1] = cycle[i - 1];
                pairs[cycle[i] * row_size + 2 * num_pairs + 2] = cycle[i + 1];
                pairs[cycle[i] * row_size] = num_pairs + 1;
            }

            num_pairs = pairs[cycle[cycle_length - 1] * row_size];
            pairs[cycle[cycle_length - 1] * row_size + 2 * num_pairs + 1] = cycle[cycle_length - 2];
            pairs[cycle[cycle_length - 1] * row_size + 2 * num_pairs + 2] = cycle[cycle_length];
            pairs[cycle[cycle_length - 1] * row_size] = num_pairs + 1;
        }
    }

    for (vertex_t i = 0; i < num_vertices; i++) {
        degree_t num_pairs = pairs[i * row_size];
        if (num_pairs == 0) continue;

        for (degree_t start_pair = 0; start_pair < num_pairs; start_pair++) {
            vertex_t start = pairs[i * row_size + 2 * start_pair + 1];
            vertex_t next = pairs[i * row_size + 2 * start_pair + 2];
            degree_t component_size = 1;
            for (degree_t j = 0; j < num_pairs; j++) {
                pair_seen[j] = false;
            }
            pair_seen[start_pair] = true;

            while (next != start) {
                bool found = false;
                for (degree_t j = 0; j < num_pairs; j++) {
                    if (pairs[i * row_size + 2 * j + 1] == next) {
                        if (pair_seen[j]) {
                            free(pair_seen);
                            free(pairs);
                            return false;
                        }
                        next = pairs[i * row_size + 2 * j + 2];
                        pair_seen[j] = true;
                        component_size++;
                        found = true;
                        break;
                    }
                }
                if (!found) {
                    break;
                }
            }

            if (next == start && component_size < vertex_degrees[i]) {
                free(pair_seen);
                free(pairs);
                return false;
            }
        }

        if (num_pairs == vertex_degrees[i]) {
            degree_t pairs_used = 0;
            vertex_t start = pairs[i * row_size + 1];
            vertex_t next = start;
            do {
                bool found = false;
                for (degree_t j = 0; j < num_pairs; j++) {
                    if (pairs[i * row_size + 2 * j + 1] == next) {
                        next = pairs[i * row_size + 2 * j + 2];
                        pairs_used++;
                        found = true;
                        break;
                    }
                }
                if (!found) {
                    free(pair_seen);
                    free(pairs);
                    return false;
                }
            } while (next != start && pairs_used <= num_pairs);

            if (pairs_used != num_pairs || next != start) {
                free(pair_seen);
                free(pairs);
                return false;
            }
        }
    }

    free(pair_seen);
    free(pairs);
    return true;
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
    (*num_search_calls)++;

    // pick a vertex to explore
    vertex_t vertex = 0;
    vertex_t neighbor_vertex = MAX_VERTICES;
    bool found = false;
    if (CONSTRAINED_BY_TWO) {
        // Pick a remaining directed edge. Every complete fitting must use it, and
        // choosing the edge with the fewest available trails keeps the branching
        // factor low.
        degree_t max_comb_uses = 0;
        cycle_index_t min_cycle_options = MAX_CYCLES;
        for (vertex_t i = 0; i < num_vertices; i++) {
            if (vertex_uses[i] >= VERTEX_USE_LIMIT) {
                continue;
            }

            vertex_t* neighbors = adj_get_neighbors(adjacency_list, i);
            for (degree_t j = 0; j < VERTEX_DEGREE; j++) {
                if (neighbors[j] == MAX_VERTICES || vertex_uses[neighbors[j]] >= VERTEX_USE_LIMIT) {
                    continue;
                }
                degree_t comb_uses = vertex_uses[i] + vertex_uses[neighbors[j]];
                cycle_index_t cycle_options = 0;
                cycle_index_t num_cycles_for_edge;
                cycle_index_t* cycle_indices_for_edge =
                    cbe_get_cycle_indices(cycles_by_edge, max_cycles_per_edge, i, neighbors[j],
                                          &num_cycles_for_edge);
                for (cycle_index_t k = 0; k < num_cycles_for_edge; k++) {
                    cycle_index_t cycle_index = cycle_indices_for_edge[k];
                    if (start_cycle_order[cycle_index] < current_start_cycle_order ||
                        used_cycles[cycle_index]) {
                        continue;
                    }
                    cycle_length_t cycle_length;
                    cycle_get(cycles, max_cycle_length, cycle_index, &cycle_length);
                    if (cycle_length > num_edges_remaining) {
                        continue;
                    }
                    cycle_index_t next_required_cycles_to_use = required_cycles_to_use;
                    if (next_required_cycles_to_use > 0 &&
                        cycle_length == length_feasibility->required_length) {
                        next_required_cycles_to_use--;
                    }
                    if (((cycles_to_use - 1) * smallest_cycle_length >
                         num_edges_remaining - cycle_length) ||
                        ((cycles_to_use - 1) * max_cycle_length <
                         num_edges_remaining - cycle_length) ||
                        !cached_length_composition_possible(length_feasibility,
                                                            num_edges_remaining - cycle_length,
                                                            cycles_to_use - 1,
                                                            next_required_cycles_to_use)) {
                        continue;
                    }
                    cycle_options++;
                }
                if (!found || cycle_options < min_cycle_options ||
                    (cycle_options == min_cycle_options && comb_uses > max_comb_uses)) {
                    found = true;
                    vertex = i;
                    neighbor_vertex = neighbors[j];
                    max_comb_uses = comb_uses;
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
    }
    // if we've explored all vertices fully, this cannot be extended further
    if (!found) {
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
        }
    }

    // look through the possible cycles that contain this vertex
    // if none can be used, this is a failed end and we backtrack
    // otherwise, we have our solution
    cycle_index_t num_cycles_for_vertex;
    cbv_t cycle_indices;
    if (CONSTRAINED_BY_TWO && neighbor_vertex != MAX_VERTICES) {
        cycle_indices = cbe_get_cycle_indices(cycles_by_edge, max_cycles_per_edge, vertex,
                                              neighbor_vertex, &num_cycles_for_vertex);
        if (num_cycles_for_vertex == 0) {
            return false;
        }
    } else {
        cycle_indices = cbv_get_cycle_indices(cycles_by_vertex, max_cycles_per_vertex, vertex,
                                              &num_cycles_for_vertex);
    }

    for (cycle_index_t i = 0; i < num_cycles_for_vertex; i++) {
        // skip if the cycle is already used
        cycle_index_t cycle_index = cycle_indices[i];
        if (start_cycle_order[cycle_index] < current_start_cycle_order) {
            continue;
        }
        if (used_cycles[cycle_index]) {
            continue;
        }

        cycle_length_t cycle_length;
        vertex_t* cycle = cycle_get(cycles, max_cycle_length, cycle_index, &cycle_length);
        if (cycle_length > num_edges_remaining) {
            continue;
        }

        // If the cycle is too long and doesn't leave enough edges for our desired
        // fit, we can't use it; similarly, if it is too short and doesn't allow us
        // to use all the edges, we can't use it
        if (((cycles_to_use - 1) * smallest_cycle_length > num_edges_remaining - cycle_length) ||
            ((cycles_to_use - 1) * max_cycle_length < num_edges_remaining - cycle_length)) {
            continue;
        }
        cycle_index_t next_required_cycles_to_use = required_cycles_to_use;
        if (next_required_cycles_to_use > 0 &&
            cycle_length == length_feasibility->required_length) {
            next_required_cycles_to_use--;
        }
        if (!cached_length_composition_possible(length_feasibility,
                                                num_edges_remaining - cycle_length,
                                                cycles_to_use - 1,
                                                next_required_cycles_to_use)) {
            continue;
        }

        // cycle is only usable if all edges are available
        bool can_use = true;
        for (cycle_length_t j = 0; j < cycle_length; j++) {
            if (!adj_has_edge(adjacency_list, cycle[j], cycle[j + 1])) {
                can_use = false;
                break;
            }
        }
        if (!can_use) {
            continue;
        }

        // make sure the cycle satisfies the ijk condition
        if (VERTEX_DEGREE > 2 && !cycle_transitions_good(cycle, cycle_length)) {
            continue;
        }
        if (!is_valid_rotation_system(used_cycles, cycles, max_cycle_length, num_cycles,
                                      num_vertices, cycle_index)) {
            continue;
        }

        // use the cycle
        used_cycles[cycle_index] = true;
        cycle_set_transitions(cycle, cycle_length, true);
        for (cycle_length_t j = 0; j < cycle_length; j++) {
            adj_remove_edge(adjacency_list, cycle[j], cycle[j + 1]);

            // mark cycle vertices as used
            vertex_uses[cycle[j]]++;
            assert(vertex_uses[cycle[j]] <= VERTEX_USE_LIMIT,
                   "\nVertex %" PRIvertex_t " used too many times\n", cycle[j]);
        }

        // if this is the final cycle needed to cover all edges, we're done
        bool is_final_cycle =
            FIND_FULL_CYCLE_FITTING
                ? cycles_to_use == 1
                : (cycles_to_use == 1 ||
                   implied_max_genus_for_fit(max_used_cycles - cycles_to_use + 1, num_vertices,
                                             num_edges) ==
                       implied_max_genus_for_fit(max_used_cycles, num_vertices, num_edges));
        if (is_final_cycle) {
            if (next_required_cycles_to_use > 0) {
                used_cycles[cycle_index] = false;
                cycle_set_transitions(cycle, cycle_length, false);
                for (cycle_length_t j = 0; j < cycle_length; j++) {
                    adj_undo_remove_edge(adjacency_list, cycle[j], cycle[j + 1]);

                    // un-use the cycle vertices
                    vertex_uses[cycle[j]]--;
                }
                continue;
            }
            if (FIND_FULL_CYCLE_FITTING) {
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

    num_edges_remaining = 2 * *num_edges;
    return adjacency_list;
}

vertex_t* adj_get_neighbors(adj_t adjacency_list, vertex_t vertex) {
    return &adjacency_list[vertex * VERTEX_DEGREE];
}

void adj_remove_edge(adj_t adjacency_list, vertex_t start_vertex, vertex_t end_vertex) {
    vertex_t* neighbors = adj_get_neighbors(adjacency_list, start_vertex);
    for (degree_t i = 0; i < VERTEX_DEGREE; i++) {
        if (neighbors[i] == end_vertex) {
            num_edges_remaining -= 1;
            neighbors[i] = MAX_VERTICES;
            return;
        }
    }
}

// must have been previously removed, otherwise undefined behavior
void adj_undo_remove_edge(adj_t adjacency_list, vertex_t start_vertex, vertex_t end_vertex) {
    vertex_t* neighbors = adj_get_neighbors(adjacency_list, start_vertex);
    for (degree_t i = 0; i < VERTEX_DEGREE; i++) {
        if (neighbors[i] == MAX_VERTICES) {
            num_edges_remaining += 1;
            neighbors[i] = end_vertex;
            return;
        }
    }
}

bool adj_has_edge(adj_t adjacency_list, vertex_t start_vertex, vertex_t end_vertex) {
    vertex_t* neighbors = adj_get_neighbors(adjacency_list, start_vertex);
    for (degree_t i = 0; i < VERTEX_DEGREE; i++) {
        if (neighbors[i] == end_vertex) {
            return true;
        }
    }
    return false;
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
