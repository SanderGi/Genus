// Narrows down the genus of a regular graph given its adjacency list.
// Prints the maximum cycle fitting as evidence. A fitting is a set of simple
// cycles (length greater than 2) that use each directed edge exactly once.
// These are the faces in Euler's formula: F - E + V = 2 - 2g. Run with `make
// run`

#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

// configuration options:
#define PRINT_PROGRESS true  // whether to print progress messages
#define DEBUG false          // whether to print debug messages
#define ADJACENCY_LIST_FILENAME "adjacency_lists/3-7-cage.txt"  // input file
#define ADJACENCY_LIST_START 0  // change if vertex numbering doesn't start at 0
#define OUTPUT_FILENAME "CalcGenus.out"  // output file
#define VERTEX_DEGREE 3                  // must be >= 2

// assumptions of the program (don't change these):
#define VERTEX_USE_LIMIT VERTEX_DEGREE
#define MAX_VERTICES 65535
#define MAX_EDGES 65535
#define MAX_CYCLE_LENGTH 65535
#define MAX_CYCLES 4294967295

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

// macros
// assert(condition, message, ...fmt_args)
#define assert(condition, ...)    \
  if (!(condition)) {             \
    fprintf(stderr, __VA_ARGS__); \
    exit(1);                      \
  }

// static variables
static FILE* output_file = NULL;

// auxiliary data structures
adj_t adj_load(char* filename, vertex_t* num_vertices, edge_t* num_edges);
vertex_t* adj_get_neighbors(adj_t adjacency_list, vertex_t vertex);
void adj_remove_edge(adj_t adjacency_list, vertex_t start_vertex,
                     vertex_t end_vertex);
void adj_undo_remove_edge(adj_t adjacency_list, vertex_t start_vertex,
                          vertex_t end_vertex);
bool adj_has_edge(adj_t adjacency_list, vertex_t start_vertex,
                  vertex_t end_vertex);

cycles_t cycle_generate(adj_t adjacency_list, vertex_t num_vertices,
                        cycle_length_t cycle_length, cycle_index_t* num_cycles);
vertex_t* cycle_get(cycles_t cycles, cycle_length_t max_cycle_length,
                    cycle_index_t cycle_index, cycle_length_t* cycle_length);

cycle_index_t* cbv_generate(vertex_t num_vertices, cycles_t cycles,
                            cycle_index_t num_cycles,
                            cycle_length_t cycle_length,
                            cycle_index_t* max_cycles_per_vertex);
cycle_index_t* cbv_get_cycle_indices(cbv_t cycles_by_vertex,
                                     cycle_index_t max_cycles_per_vertex,
                                     vertex_t vertex,
                                     cycle_index_t* num_cycles);

struct fifo {
  vertex_t* data;
  cycle_index_t head;
  cycle_index_t tail;
  cycle_index_t capacity;
  cycle_length_t path_length;
};
void fifo_init(struct fifo* fifo, cycle_index_t initial_capacity,
               cycle_length_t path_length);
bool fifo_empty(struct fifo* fifo);
void fifo_push(struct fifo* fifo, vertex_t* path);
void fifo_pop(struct fifo* fifo, vertex_t* path);
vertex_t* fifo_peek(struct fifo* fifo, cycle_index_t ix);
cycle_index_t fifo_size(struct fifo* fifo);
void fifo_free(struct fifo* fifo);

void show_progress(double fraction);

bool is_ijk_good(bool* used_cycles, cycles_t cycles,
                 cycle_length_t max_cycle_length, cycle_index_t num_cycles,
                 cycle_index_t cycle_to_check);

bool search(vertex_t* distribution,             // state
            cycle_length_t max_cycle_length,    // state
            bool** used_cycles_by_length,       // state
            cycle_index_t num_used_cycles,      // state
            cycle_index_t target_fit,           // state
            uint64_t* num_search_calls,         // state
            cycle_index_t current_start_cycle,  // state (=0 for initial call)
            cycle_length_t smallest_cycle_length, adj_t adjacency_list,
            cycles_t* cycles_by_length, cycle_index_t* num_cycles_by_length);
// bool search(cycle_index_t cycles_to_use,                    // state
//             cycle_index_t max_used_cycles,                  // state
//             bool* used_cycles,                              // state
//             degree_t* vertex_uses, cycle_index_t* max_fit,  // state
//             uint64_t* num_search_calls,                     // state
//             vertex_t num_vertices, edge_t num_edges, adj_t adjacency_list,
//             cycle_length_t max_cycle_length, cycle_index_t num_cycles,
//             cycles_t cycles, cycle_index_t max_cycles_per_vertex,
//             cbv_t cycles_by_vertex, cycle_index_t current_start_cycle);

cycle_index_t implied_max_fit_for_genus(cycle_index_t genus,
                                        vertex_t num_vertices,
                                        edge_t num_edges) {
  return num_edges - num_vertices + 2 - 2 * genus;
}

cycle_index_t implied_max_genus_for_fit(cycle_index_t fit,
                                        vertex_t num_vertices,
                                        edge_t num_edges) {
  int64_t val = 1 - ((int64_t)fit - num_edges + num_vertices) / 2;
  return val < 0 ? 0 : val;
}

cycle_index_t generate_cycle_length(
    cycle_length_t cycle_length,                    // Input
    adj_t adjacency_list,                           // Input
    vertex_t num_vertices,                          // Input
    edge_t num_edges,                               // Input
    cycles_t* cycles_by_length,                     // Modified
    cycle_index_t* num_cycles_by_length,            // Modified
    cycle_index_t** cycles_by_vertex_by_length,     // Modified
    cycle_index_t* max_cycles_per_vertex_by_length  // Modified
) {
  cycles_by_length[cycle_length] =
      cycle_generate(adjacency_list, num_vertices, cycle_length,
                     &num_cycles_by_length[cycle_length]);
  cycles_by_vertex_by_length[cycle_length] =
      cbv_generate(num_vertices, cycles_by_length[cycle_length],
                   num_cycles_by_length[cycle_length], cycle_length,
                   &max_cycles_per_vertex_by_length[cycle_length]);
  return num_cycles_by_length[cycle_length];
}

int main(void) {
  // Load data
  if (PRINT_PROGRESS) {
    fprintf(stderr, "Loading adjacency list...\n");
  }
  vertex_t num_vertices;
  edge_t num_edges;
  adj_t adjacency_list =
      adj_load(ADJACENCY_LIST_FILENAME, &num_vertices, &num_edges);
  edge_t num_directed_edges = 2 * num_edges;

  // Configure output
  output_file = fopen(OUTPUT_FILENAME, "w");
  assert(output_file != NULL, "Error opening file %s\n", OUTPUT_FILENAME);
  fprintf(stderr, "Output file: %s\n", OUTPUT_FILENAME);

  // Track perf/progress
  uint64_t num_search_calls = 0;

  // Prepare data structures to hold cycles
  cycles_t* cycles_by_length =
      (cycles_t*)malloc((num_vertices + 1) * sizeof(cycles_t));
  assert(cycles_by_length != NULL,
         "Error allocating memory for the cycles by length\n");

  cycle_index_t* num_cycles_by_length =
      (cycle_index_t*)malloc((num_vertices + 1) * sizeof(cycle_index_t));
  assert(num_cycles_by_length != NULL,
         "Error allocating memory for the number of cycles by length\n");
  for (cycle_length_t i = 0; i <= num_vertices; i++) {
    num_cycles_by_length[i] = 0;
  }

  bool** used_cycles_by_length =
      (bool**)malloc((num_vertices + 1) * sizeof(bool*));
  assert(used_cycles_by_length != NULL,
         "Error allocating memory for the used cycles by length");
  for (vertex_t i = 0; i <= num_vertices; i++) {
    used_cycles_by_length[i] = NULL;
  }

  cycle_index_t** cycles_by_vertex_by_length =
      (cycle_index_t**)malloc((num_vertices + 1) * sizeof(cycle_index_t*));
  assert(cycles_by_vertex_by_length != NULL,
         "Error allocating memory for the cycles by vertex by length\n");
  cycle_index_t* max_cycles_per_vertex_by_length =
      (cycle_index_t*)malloc((num_vertices + 1) * sizeof(cycle_index_t));
  assert(max_cycles_per_vertex_by_length != NULL,
         "Error allocating memory for the max cycles per vertex by length\n");

  // Find the smallest cycle length
  cycle_length_t smallest_cycle_length = START_CYCLE_LENGTH - 1;
  while (generate_cycle_length(++smallest_cycle_length, adjacency_list,
                               num_vertices, num_edges, cycles_by_length,
                               num_cycles_by_length, cycles_by_vertex_by_length,
                               max_cycles_per_vertex_by_length) == 0) {
  }
  fprintf(stderr, "Smallest Cycle Length: %" PRIcycle_index_t "\n",
          smallest_cycle_length);

  // Initial bounds
  vertex_t max_possible_fit = num_directed_edges / smallest_cycle_length;
  cycle_index_t genus_lower_bound =
      implied_max_genus_for_fit(max_possible_fit, num_vertices, num_edges);
  cycle_index_t genus_upper_bound =
      implied_max_genus_for_fit(0, num_vertices, num_edges);
  fprintf(stderr,
          "Initial Genus bound = [%" PRIcycle_index_t ", %" PRIcycle_index_t
          "]\n",
          genus_lower_bound, genus_upper_bound);

  // Iterate through cycle distributions
  vertex_t* distribution_buf =
      (vertex_t*)malloc((num_vertices + 1) * sizeof(vertex_t));
  assert(distribution_buf != NULL,
         "Error allocating memory for the distribution buffer");
  for (vertex_t i = 0; i <= num_vertices; i++) {
    distribution_buf[i] = 0;
  }
  // array = [[()]] + [[] for _ in range(s)]
  struct fifo* cycle_distributions_by_edges_used =
      (struct fifo*)malloc((num_directed_edges + 1) * sizeof(struct fifo));
  assert(cycle_distributions_by_edges_used != NULL,
         "Error allocating memory for the cycle distributions by edges used\n");
  for (edge_t i = 0; i <= num_directed_edges; i++) {
    fifo_init(&cycle_distributions_by_edges_used[i], 1, num_vertices + 1);
  }
  fifo_push(&cycle_distributions_by_edges_used[0], distribution_buf);

  struct fifo* cycle_distributions_by_fit =
      (struct fifo*)malloc((max_possible_fit + 1) * sizeof(struct fifo));
  assert(cycle_distributions_by_fit != NULL,
         "Error allocating memory for the cycle distributions by fit\n");
  for (edge_t i = 0; i <= max_possible_fit; i++) {
    fifo_init(&cycle_distributions_by_fit[i], 1, num_vertices + 1);
  }

  // for v, c in population:
  for (cycle_length_t cycle_length = smallest_cycle_length;
       cycle_length <= num_vertices; cycle_length++) {
    show_progress((double)cycle_length / num_vertices);
    fprintf(stderr, " (Cycle Length: %" PRIcycle_length_t ")\n", cycle_length);

    cycle_index_t num_cycles = num_cycles_by_length[cycle_length];
    cycle_index_t max_usable_cycles = num_directed_edges / cycle_length;
    if (num_cycles < max_usable_cycles) {
      max_usable_cycles = num_cycles;
    }

    used_cycles_by_length[cycle_length] =
        (bool*)malloc(num_cycles * sizeof(bool));
    assert(
        used_cycles_by_length[cycle_length] != NULL,
        "Error allocating memory for used cycles of length %" PRIcycle_length_t
        "\n",
        cycle_length);
    for (cycle_index_t i = 0; i < num_cycles; i++) {
      used_cycles_by_length[cycle_length][i] = false;
    }

    // for j in range(1, c + 1):
    for (cycle_index_t count = 1; count <= max_usable_cycles; count++) {
      // for num in range(s - j * v, -1, -1):
      for (cycle_index_t remaining_edges =
               num_directed_edges - count * cycle_length;
           remaining_edges <= num_directed_edges; remaining_edges--) {
        // if array[num]:
        //   for subset in array[num]:
        for (cycle_index_t distribution_ix = 0;
             distribution_ix <
             fifo_size(&cycle_distributions_by_edges_used[remaining_edges]);
             distribution_ix++) {
          vertex_t* distribution =
              fifo_peek(&cycle_distributions_by_edges_used[remaining_edges],
                        distribution_ix);
          // if v not in subset:
          if (distribution[cycle_length] == 0) {
            edge_t edges_used = remaining_edges + count * cycle_length;
            // array[num + j * v] += [subset + tuple([v] * j)]
            distribution[cycle_length] = count;
            fifo_push(&cycle_distributions_by_edges_used[edges_used],
                      distribution);
            // if num + j * v == s:
            if (edges_used == num_directed_edges) {
              // yield array[num + j * v][-1], sum(array[num +
              // j * v][-1]), len(array[num + j * v][-1])
              vertex_t fit = 0;
              for (vertex_t i = smallest_cycle_length; i <= num_vertices; i++) {
                fit += distribution[i];
              }
              fifo_push(&cycle_distributions_by_fit[fit], distribution);

              if (true) {
                fprintf(stderr,
                        "Distribution of fit %" PRIvertex_t " found: ", fit);
                for (vertex_t i = smallest_cycle_length; i <= num_vertices;
                     i++) {
                  if (distribution[i] != 0)
                    fprintf(stderr, "%" PRIvertex_t "x%" PRIvertex_t " ",
                            distribution[i], i);
                }
                fprintf(stderr, "\n");
              }

              // // If the distribution fit matches the lower bound, we'll try
              // to
              // // rule it out
              // if (fit = implied_max_fit_for_genus(genus_lower_bound,
              //                                     num_vertices, num_edges)) {
              //   // TODO
              // }

              // If the distribution fit can improve the current genus upper
              // bound
              if (fit > implied_max_fit_for_genus(genus_upper_bound,
                                                  num_vertices, num_edges)) {
                bool improved_upper_bound =
                    search(distribution,           // state
                           cycle_length,           // state
                           used_cycles_by_length,  // state
                           0,                      // state
                           fit,                    // state
                           &num_search_calls,      // state
                           0, smallest_cycle_length, adjacency_list,
                           cycles_by_length, num_cycles_by_length);
                if (improved_upper_bound) {
                  genus_upper_bound =
                      implied_max_genus_for_fit(fit, num_vertices, num_edges);
                  fprintf(stderr,
                          "Improved Genus bound = [%" PRIcycle_index_t
                          ", %" PRIcycle_index_t "]\n",
                          genus_lower_bound, genus_upper_bound);
                  if (genus_lower_bound == genus_upper_bound) {
                    return 0;
                  }
                }
              }
            }
            distribution[cycle_length] = 0;
          }
        }
      }
    }

    cycle_length_t next_cycle_length = cycle_length + 1;
    // The most cycles we can possibly fit given at least one of
    // next_cycle_length is that cycle and every other cycle as the
    // smallest cycle length
    cycle_index_t best_possible_fit_with_max_cycle =
        (num_directed_edges - next_cycle_length) / smallest_cycle_length + 1;
    if (next_cycle_length > num_vertices ||
        implied_max_genus_for_fit(best_possible_fit_with_max_cycle,
                                  num_vertices,
                                  num_edges) > genus_lower_bound) {
      // Since the current lower bound can't be reached using cycles smaller
      // than next_cycle_length, it can't be reached at all, increase the lower
      // bound.
      genus_lower_bound++;
      fprintf(stderr,
              "Improved Genus bound = [%" PRIcycle_index_t
              ", %" PRIcycle_index_t "]\n",
              genus_lower_bound, genus_upper_bound);
      if (genus_lower_bound == genus_upper_bound) {
        return 0;
      }

      // TODO: test all current next fits
    }

    if (next_cycle_length <= num_vertices) {
      // Calculate cycles of next_cycle_length
      generate_cycle_length(next_cycle_length, adjacency_list, num_vertices,
                            num_edges, cycles_by_length, num_cycles_by_length,
                            cycles_by_vertex_by_length,
                            max_cycles_per_vertex_by_length);
    }
  }

  return 1;
}

void show_progress(double fraction) {
  // E.g. [##########          ] 50%

  if (!PRINT_PROGRESS) {
    return;
  }

  fflush(stderr);
  fprintf(stderr, "\r[");
  for (int i = 0; i < 50; i++) {
    if (i < fraction * 50) {
      fprintf(stderr, "#");
    } else {
      fprintf(stderr, " ");
    }
  }
  fprintf(stderr, "] %d%%", (int)(fraction * 100));
}

// if sequence i -> j -> k occurs in any of the used cycles such that k -> j ->
// i occurs in the cycle_to_check return false
// if no such sequence occurs return true
bool is_ijk_good(bool* used_cycles, cycles_t cycles,
                 cycle_length_t max_cycle_length, cycle_index_t num_cycles,
                 cycle_index_t cycle_to_check) {
  // TODO: optimize by storing the rotation in the adjacency list as cycles are
  // added
  cycle_length_t cycle_length;
  vertex_t* cycle =
      cycle_get(cycles, max_cycle_length, cycle_to_check, &cycle_length);

  vertex_t* padded_cycle =
      (vertex_t*)malloc((cycle_length + 2) * sizeof(vertex_t));
  assert(padded_cycle != NULL,
         "Error allocating memory for the padded cycle\n");
  for (cycle_length_t i = 0; i < cycle_length; i++) {
    padded_cycle[i] = cycle[i];
  }
  padded_cycle[cycle_length] = cycle[0];
  padded_cycle[cycle_length + 1] = cycle[1];

  for (cycle_index_t c = 0; c < num_cycles; c++) {
    if (used_cycles[c]) {
      cycle_length_t other_cycle_length;
      vertex_t* other_cycle =
          cycle_get(cycles, max_cycle_length, c, &other_cycle_length);

      vertex_t* padded_other_cycle =
          (vertex_t*)malloc((other_cycle_length + 2) * sizeof(vertex_t));
      assert(padded_other_cycle != NULL,
             "Error allocating memory for the padded other cycle\n");
      for (cycle_length_t i = 0; i < other_cycle_length; i++) {
        padded_other_cycle[i] = other_cycle[i];
      }
      padded_other_cycle[other_cycle_length] = other_cycle[0];
      padded_other_cycle[other_cycle_length + 1] = other_cycle[1];

      for (cycle_length_t i = 0; i < cycle_length; i++) {
        for (cycle_length_t j = 0; j < other_cycle_length; j++) {
          if (padded_cycle[i] == padded_other_cycle[j + 2] &&
              padded_cycle[i + 1] == padded_other_cycle[j + 1] &&
              padded_cycle[i + 2] == padded_other_cycle[j]) {
            free(padded_cycle);
            free(padded_other_cycle);
            return false;
          }
        }
      }

      free(padded_other_cycle);
    }
  }

  free(padded_cycle);
  return true;
}

bool search(vertex_t* distribution,             // state
            cycle_length_t max_cycle_length,    // state
            bool** used_cycles_by_length,       // state
            cycle_index_t num_used_cycles,      // state
            cycle_index_t target_fit,           // state
            uint64_t* num_search_calls,         // state
            cycle_index_t current_start_cycle,  // state (=0 for initial call)
            cycle_length_t smallest_cycle_length, adj_t adjacency_list,
            cycles_t* cycles_by_length, cycle_index_t* num_cycles_by_length) {
  // bool search(vertex_t* distribution,             // state
  //             cycle_length_t max_cycle_length,    // state
  //             bool** used_cycles_by_length,       // state
  //             cycle_index_t num_used_cycles,      // state
  //             cycle_index_t target_fit,           // state
  //             uint64_t* num_search_calls,         // state
  //             cycle_index_t current_start_cycle,  // state (=0 for initial
  //             call) cycle_length_t smallest_cycle_length, adj_t
  //             adjacency_list, cycles_t* cycles_by_length, cycle_index_t*
  //             num_cycles_by_length, cycle_index_t**
  //             cycles_by_vertex_by_length, cycle_index_t*
  //             max_cycles_per_vertex_by_length) {
  (*num_search_calls)++;  // keep track of search calls for perf measurements
                          // and progress messages

  while (distribution[max_cycle_length] == 0 &&
         max_cycle_length >= smallest_cycle_length) {
    max_cycle_length--;
    current_start_cycle = 0;
  }
  if (max_cycle_length < smallest_cycle_length) return false;

  cycles_t cycles = cycles_by_length[max_cycle_length];
  cycle_index_t num_cycles = num_cycles_by_length[max_cycle_length];
  // cycle_index_t* cycles_by_vertex =
  //     cycles_by_vertex_by_length[max_cycle_length];
  // cycle_index_t* max_cycles_per_vertex =
  //     max_cycles_per_vertex_by_length[max_cycle_length];
  bool* used_cycles = used_cycles_by_length[max_cycle_length];

  // loop through unused cycles
  for (cycle_index_t i = current_start_cycle; i < num_cycles; i++) {
    // skip if the cycle is already used
    if (used_cycles[i]) {
      continue;
    }

    cycle_length_t cycle_length;
    vertex_t* cycle = cycle_get(cycles, max_cycle_length, i, &cycle_length);

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
    if (VERTEX_DEGREE > 2 &&
        !is_ijk_good(used_cycles, cycles, max_cycle_length, num_cycles, i)) {
      continue;
    }

    // use the cycle
    used_cycles[i] = true;
    num_used_cycles++;
    distribution[max_cycle_length]--;
    for (cycle_length_t j = 0; j < cycle_length; j++) {
      adj_remove_edge(adjacency_list, cycle[j], cycle[j + 1]);
    }

    bool success = false;
    // if this is the final cycle needed to cover all edges, we're done
    assert(target_fit >= num_used_cycles, "Should not happen");
    if (target_fit == num_used_cycles) {
      success = true;
    }
    // otherwise, continue adding cycles
    else if (search(distribution, max_cycle_length, used_cycles_by_length,
                    num_used_cycles, target_fit, num_search_calls, i + 1,
                    smallest_cycle_length, adjacency_list, cycles_by_length,
                    num_cycles_by_length)) {
      success = true;  // as soon as we succeed, we're done
    }

    // un-use the cycle
    used_cycles[i] = false;
    num_used_cycles--;
    distribution[max_cycle_length]++;
    for (uint8_t j = 0; j < cycle_length; j++) {
      adj_undo_remove_edge(adjacency_list, cycle[j], cycle[j + 1]);
    }

    if (success) {
      return true;
    }
  }

  // if we are unable to use the required cycles of the current length, this
  // is a fail
  return false;
}

// bool search(cycle_index_t cycles_to_use,                    // state
//             cycle_index_t max_used_cycles,                  // state
//             bool* used_cycles,                              // state
//             degree_t* vertex_uses, cycle_index_t* max_fit,  // state
//             uint64_t* num_search_calls,                     // state
//             vertex_t num_vertices, edge_t num_edges, adj_t adjacency_list,
//             cycle_length_t max_cycle_length, cycle_index_t num_cycles,
//             cycles_t cycles, cycle_index_t max_cycles_per_vertex,
//             cbv_t cycles_by_vertex, cycle_index_t current_start_cycle) {
//   (*num_search_calls)++;

//   // pick a vertex to explore
//   // we pick the most used vertex that hasn't reached the limit since it
//   // constrains the search space of possible cycles more
//   vertex_t vertex = 0;
//   degree_t max_uses = 0;
//   for (vertex_t i = 0; i < num_vertices; i++) {
//     if (vertex_uses[i] < VERTEX_USE_LIMIT && vertex_uses[i] > max_uses) {
//       vertex = i;
//       max_uses = vertex_uses[i];

//       if (max_uses == VERTEX_USE_LIMIT - 1) {
//         break;  // we can't do better than this
//       }
//     }
//   }
//   // if we've explored all vertices fully, this cannot be extended further
//   if (max_uses == VERTEX_USE_LIMIT) {
//     return false;
//   }

//   // if we've reached a new maximum fit, print it
//   if (max_used_cycles - cycles_to_use > *max_fit) {
//     *max_fit = max_used_cycles - cycles_to_use;
//     fprintf(output_file,
//             "New max fit: %" PRIcycle_index_t
//             " (about to try vertex %" PRIvertex_t ")\n",
//             *max_fit, vertex);
//     for (cycle_index_t i = 0; i < num_cycles; i++) {
//       if (used_cycles[i]) {
//         cycle_length_t cycle_length;
//         vertex_t* cycle = cycle_get(cycles, max_cycle_length, i,
//         &cycle_length); for (cycle_length_t j = 0; j < cycle_length + 1; j++)
//         {
//           fprintf(output_file, "%" PRIvertex_t " ",
//                   cycle[j] + ADJACENCY_LIST_START);
//         }
//         fprintf(output_file, "\n");
//       }
//     }
//     fprintf(output_file, "\n");
//     fflush(output_file);
//   }

//   // look through the possible cycles that contain this vertex
//   // if none can be used, this is a failed end and we backtrack
//   // otherwise, we have our solution
//   cycle_index_t num_cycles_for_vertex;
//   cbv_t cycle_indices = cbv_get_cycle_indices(
//       cycles_by_vertex, max_cycles_per_vertex, vertex,
//       &num_cycles_for_vertex);
//   for (cycle_index_t i = 0; i < num_cycles_for_vertex; i++) {
//     // skip if the cycle is already used
//     cycle_index_t cycle_index = cycle_indices[i];
//     if (cycle_index <= current_start_cycle) {
//       continue;
//     }
//     if (used_cycles[cycle_index]) {
//       continue;
//     }

//     cycle_length_t cycle_length;
//     vertex_t* cycle =
//         cycle_get(cycles, max_cycle_length, cycle_index, &cycle_length);

//     // cycle is only usable if all edges are available
//     bool can_use = true;
//     for (cycle_length_t j = 0; j < cycle_length; j++) {
//       if (!adj_has_edge(adjacency_list, cycle[j], cycle[j + 1])) {
//         can_use = false;
//         break;
//       }
//     }
//     if (!can_use) {
//       continue;
//     }

//     // make sure the cycle satisfies the ijk condition
//     if (VERTEX_DEGREE > 2 && !is_ijk_good(used_cycles, cycles,
//     max_cycle_length,
//                                           num_cycles, cycle_index)) {
//       continue;
//     }

//     // use the cycle
//     used_cycles[cycle_index] = true;
//     for (cycle_length_t j = 0; j < cycle_length; j++) {
//       adj_remove_edge(adjacency_list, cycle[j], cycle[j + 1]);

//       // mark cycle vertices as used
//       vertex_uses[cycle[j]]++;
//       assert(vertex_uses[cycle[j]] <= VERTEX_USE_LIMIT,
//              "Vertex %" PRIvertex_t " used too many times\n", cycle[j]);
//     }

//     // if this is the final cycle needed to cover all edges, we're done
//     if (cycles_to_use == 1 ||
//         implied_max_genus_for_fit(max_used_cycles - cycles_to_use + 1,
//                                   num_vertices, num_edges) ==
//             implied_max_genus_for_fit(max_used_cycles, num_vertices,
//                                       num_edges)) {
//       return true;
//     }
//     // otherwise, continue adding cycles
//     if (search(cycles_to_use - 1, max_used_cycles, used_cycles, vertex_uses,
//                max_fit, num_search_calls, num_vertices, num_edges,
//                adjacency_list, max_cycle_length, num_cycles, cycles,
//                max_cycles_per_vertex, cycles_by_vertex, current_start_cycle))
//                {
//       return true;  // as soon as we succeed, we're done
//     }

//     // un-use the cycle
//     used_cycles[cycle_index] = false;
//     for (uint8_t j = 0; j < cycle_length; j++) {
//       adj_undo_remove_edge(adjacency_list, cycle[j], cycle[j + 1]);

//       // un-use the cycle vertices
//       vertex_uses[cycle[j]]--;
//     }
//   }

//   // if we haven't returned true by now, we've failed
//   return false;
// }

adj_t adj_load(char* filename, vertex_t* num_vertices, edge_t* num_edges) {
  FILE* fp = fopen(filename, "r");
  assert(fp != NULL, "Error opening file %s\n", filename);

  // number of vertices and edges are the two first numbers
  assert(fscanf(fp, "%" SCNvertex_t " %" SCNedge_t "", num_vertices,
                num_edges) == 2,
         "Error reading the first line of %s\n", filename);

  adj_t adjacency_list =
      (adj_t)malloc(*num_vertices * VERTEX_DEGREE * sizeof(vertex_t));
  assert(adjacency_list != NULL,
         "Error allocating memory for the adjacency list\n");
  for (vertex_t i = 0; i < *num_vertices * VERTEX_DEGREE; i++) {
    assert(fscanf(fp, "%" SCNvertex_t, &adjacency_list[i]) == 1,
           "Error reading the adjacency list from %s\n", filename);
    adjacency_list[i] -= ADJACENCY_LIST_START;
  }

  fclose(fp);

  if (PRINT_PROGRESS) {
    fprintf(stderr, "Read the adjacency list from %s\n", filename);
    fprintf(stderr, "\tNumber of vertices: %" PRIvertex_t " \n", *num_vertices);
    fprintf(stderr,
            "\tNumber of edges: %" PRIedge_t " (%" PRIedge_t " directed)\n",
            *num_edges, 2 * *num_edges);
    fprintf(stderr, "\tFirst 5 vertices (with neighbors): ");
    for (vertex_t v = 0; v < 5; v++) {
      fprintf(stderr,
              "%" PRIvertex_t "(%" PRIvertex_t " %" PRIvertex_t " %" PRIvertex_t
              ") ",
              v, adj_get_neighbors(adjacency_list, v)[0] + ADJACENCY_LIST_START,
              adj_get_neighbors(adjacency_list, v)[1] + ADJACENCY_LIST_START,
              adj_get_neighbors(adjacency_list, v)[2] + ADJACENCY_LIST_START);
    }
    fprintf(stderr, "\n");
  }

  return adjacency_list;
}

vertex_t* adj_get_neighbors(adj_t adjacency_list, vertex_t vertex) {
  return &adjacency_list[vertex * VERTEX_DEGREE];
}

void adj_remove_edge(adj_t adjacency_list, vertex_t start_vertex,
                     vertex_t end_vertex) {
  vertex_t* neighbors = adj_get_neighbors(adjacency_list, start_vertex);
  for (degree_t i = 0; i < VERTEX_DEGREE; i++) {
    if (neighbors[i] == end_vertex) {
      neighbors[i] = MAX_VERTICES;
      return;
    }
  }
}

// must have been previously removed, otherwise undefined behavior
void adj_undo_remove_edge(adj_t adjacency_list, vertex_t start_vertex,
                          vertex_t end_vertex) {
  vertex_t* neighbors = adj_get_neighbors(adjacency_list, start_vertex);
  for (degree_t i = 0; i < VERTEX_DEGREE; i++) {
    if (neighbors[i] == MAX_VERTICES) {
      neighbors[i] = end_vertex;
      return;
    }
  }
}

bool adj_has_edge(adj_t adjacency_list, vertex_t start_vertex,
                  vertex_t end_vertex) {
  vertex_t* neighbors = adj_get_neighbors(adjacency_list, start_vertex);
  for (degree_t i = 0; i < VERTEX_DEGREE; i++) {
    if (neighbors[i] == end_vertex) {
      return true;
    }
  }
  return false;
}

void fifo_init(struct fifo* fifo, cycle_index_t initial_capacity,
               cycle_length_t path_length) {
  fifo->data =
      (vertex_t*)malloc(initial_capacity * path_length * sizeof(vertex_t));
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
    vertex_t* new_data = (vertex_t*)malloc(
        2 * fifo->capacity * fifo->path_length * sizeof(vertex_t));
    assert(new_data != NULL, "Error allocating memory for the fifo\n");
    for (cycle_index_t i = 0; i < fifo->capacity; i++) {
      for (cycle_length_t j = 0; j < fifo->path_length; j++) {
        new_data[i * fifo->path_length + j] =
            fifo->data[((fifo->head + i) % fifo->capacity) * fifo->path_length +
                       j];
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
vertex_t* fifo_peek(struct fifo* fifo, cycle_index_t ix) {
  return &fifo->data[((fifo->head + ix) % fifo->capacity) * fifo->path_length];
}
cycle_index_t fifo_size(struct fifo* fifo) {
  return (fifo->tail - fifo->head + fifo->capacity) % fifo->capacity;
}
void fifo_free(struct fifo* fifo) {
  free(fifo->data);
  fifo->data = NULL;
}

cycles_t cycle_generate(adj_t adjacency_list, vertex_t num_vertices,
                        cycle_length_t cycle_length,
                        cycle_index_t* num_cycles) {
  vertex_t* buffer = (vertex_t*)malloc((cycle_length + 2) * sizeof(vertex_t));

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
    vertex_t* neighbors =
        adj_get_neighbors(adjacency_list, path[path_length - 1]);
    if (path_length == cycle_length) {
      for (degree_t i = 0; i < VERTEX_DEGREE; i++) {
        if (neighbors[i] == path[0]) {
          buffer[cycle_length + 1] = path[0];
          fifo_push(&cycle_list, buffer);
          break;
        }
      }
    } else {
      for (degree_t i = 0; i < VERTEX_DEGREE; i++) {
        vertex_t neighbor = neighbors[i];
        if (neighbor <= path[0]) {
          continue;
        }
        bool neighbor_in_path = false;
        for (cycle_length_t j = 0; j < path_length; j++) {
          if (path[j] == neighbor) {
            neighbor_in_path = true;
            break;
          }
        }
        if (!neighbor_in_path) {
          buffer[0] = path_length + 1;
          path[path_length] = neighbor;
          fifo_push(&queue, buffer);
        }
      }
    }
  }

  fifo_free(&queue);
  free(buffer);
  *num_cycles = fifo_size(&cycle_list);
  vertex_t* cycles = (vertex_t*)realloc(
      cycle_list.data, *num_cycles * (cycle_length + 2) * sizeof(vertex_t));
  assert(cycles != NULL, "Error reallocating memory for the cycles\n");
  cycle_list.data = NULL;
  fifo_free(&cycle_list);

  if (DEBUG) {
    fprintf(stderr, "Generated cycles of length: %" PRIcycle_length_t "\n",
            cycle_length);
    fprintf(stderr, "\tNumber of cycles: %" PRIcycle_index_t "\n", *num_cycles);
    fprintf(stderr, "\tFirst 5 cycles:\n");
    for (cycle_index_t i = 0; i < 5; i++) {
      fprintf(stderr, "\t\t%d: ", i);
      for (cycle_length_t j = 0; j < cycle_length + 1; j++) {
        fprintf(stderr, "%02" PRIvertex_t " ",
                cycle_get(cycles, cycle_length, i, NULL)[j]);
      }
      fprintf(stderr, "\n");
    }
  }

  return cycles;
}

vertex_t* cycle_get(cycles_t cycles, cycle_length_t max_cycle_length,
                    cycle_index_t cycle_index, cycle_length_t* cycle_length) {
  vertex_t* row = &cycles[cycle_index * (max_cycle_length + 2)];
  if (cycle_length != NULL) {
    *cycle_length = row[0];
  }
  return &row[1];
}

cycle_index_t* cbv_generate(vertex_t num_vertices, cycles_t cycles,
                            cycle_index_t num_cycles,
                            cycle_length_t max_cycle_length,
                            cycle_index_t* max_cycles_per_vertex) {
  // find the number of cycles per vertex
  cycle_index_t* cycles_per_vertex =
      (cycle_index_t*)malloc(num_vertices * sizeof(cycle_index_t));
  assert(cycles_per_vertex != NULL,
         "Error allocating memory for the cycles per vertex\n");
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

  cbv_t cycles_by_vertex = (cbv_t)malloc(
      num_vertices * (*max_cycles_per_vertex + 1) * sizeof(cycle_index_t));
  assert(cycles_by_vertex != NULL,
         "Error allocating memory for the cycles by vertex\n");

  // fill in the cycles by vertex
  for (vertex_t i = 0; i < num_vertices; i++) {
    cycles_by_vertex[i * (*max_cycles_per_vertex + 1)] = cycles_per_vertex[i];
    cycle_index_t num_cycles_for_vertex = 0;
    for (cycle_index_t j = 0;
         j < num_cycles && num_cycles_for_vertex < cycles_per_vertex[i]; j++) {
      bool cycle_contains_vertex = false;
      vertex_t* cycle = cycle_get(cycles, max_cycle_length, j, &cycle_length);
      for (cycle_length_t k = 0; k < cycle_length; k++) {
        if (cycle[k] == i) {
          cycle_contains_vertex = true;
          break;
        }
      }
      if (cycle_contains_vertex) {
        cycles_by_vertex[i * (*max_cycles_per_vertex + 1) +
                         num_cycles_for_vertex + 1] = j;
        num_cycles_for_vertex++;
      }
    }
    assert(num_cycles_for_vertex == cycles_per_vertex[i],
           "Error filling in the cycles by vertex %" PRIvertex_t "\n", i);
  }

  if (DEBUG) {
    fprintf(stderr, "Organized cycles by vertex\n");
    fprintf(stderr, "\tMax cycles per vertex: %" PRIcycle_index_t "\n",
            *max_cycles_per_vertex);
    fprintf(stderr, "\tLast 2 cycles of vertex 0 and 1:\n");
    for (uint8_t i = num_vertices - 2; i < num_vertices; i++) {
      cycle_index_t num_cycles;
      cycle_index_t* cycle_indices = cbv_get_cycle_indices(
          cycles_by_vertex, *max_cycles_per_vertex, i, &num_cycles);
      fprintf(stderr, "\t\t%d:\n", i);
      for (cycle_index_t j = 0; j < num_cycles && j < 2; j++) {
        fprintf(stderr, "\t\t\t%" PRIcycle_index_t " / %" PRIcycle_index_t ": ",
                j, num_cycles);
        vertex_t* cycle = cycle_get(cycles, max_cycle_length, cycle_indices[j],
                                    &cycle_length);
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

cycle_index_t* cbv_get_cycle_indices(cbv_t cycles_by_vertex,
                                     cycle_index_t max_cycles_per_vertex,
                                     vertex_t vertex,
                                     cycle_index_t* num_cycles) {
  cycle_index_t* row = &cycles_by_vertex[vertex * (max_cycles_per_vertex + 1)];
  *num_cycles = row[0];
  return &row[1];
}
