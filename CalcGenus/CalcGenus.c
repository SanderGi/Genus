// Narrows down the genus of a 3 regular graph given its adjacency list.
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
#define ADJACENCY_LIST_FILENAME "adjacency_lists/balaban11.txt"  // input file
#define ADJACENCY_LIST_START 0  // change if vertex numbering doesn't start at 0
#define OUTPUT_FILENAME "CalcGenus.out"  // output file

// assumptions of the program (don't change these):
#define VERTEX_DEGREE 3
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

void show_progress(double fraction);

bool is_ijk_good(bool* used_cycles, cycles_t cycles,
                 cycle_length_t max_cycle_length, cycle_index_t num_cycles,
                 cycle_index_t cycle_to_check);
bool search(cycle_index_t cycles_to_use,                    // state
            cycle_index_t max_used_cycles,                  // state
            bool* used_cycles,                              // state
            degree_t* vertex_uses, cycle_index_t* max_fit,  // state
            uint64_t* num_search_calls,                     // state
            vertex_t num_vertices, edge_t num_edges, adj_t adjacency_list,
            cycle_length_t max_cycle_length, cycle_index_t num_cycles,
            cycles_t cycles, cycle_index_t max_cycles_per_vertex,
            cbv_t cycles_by_vertex);

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

int main(void) {
  if (PRINT_PROGRESS) {
    fprintf(stderr, "Loading adjacency list...\n");
  }

  vertex_t num_vertices;
  edge_t num_edges;
  adj_t adjacency_list =
      adj_load(ADJACENCY_LIST_FILENAME, &num_vertices, &num_edges);

  output_file = fopen(OUTPUT_FILENAME, "w");

  cycle_index_t genus_lower_bound = implied_max_genus_for_fit(
      2 * num_edges / START_CYCLE_LENGTH, num_vertices, num_edges);
  cycle_index_t genus_lower_bound_implied_fit =
      implied_max_fit_for_genus(genus_lower_bound, num_vertices, num_edges);
  cycle_index_t genus_upper_bound =
      implied_max_genus_for_fit(0, num_vertices, num_edges);

  if (PRINT_PROGRESS) {
    fprintf(
        stderr,
        "Beginning to narrow down genus (currently between %" PRIcycle_index_t
        " and %" PRIcycle_index_t " with implied fit %" PRIcycle_index_t
        ")...\n",
        genus_lower_bound, genus_upper_bound, genus_lower_bound_implied_fit);
  }

  cycle_index_t max_fit = 0;
  uint64_t num_search_calls = 0;
  cycle_length_t smallest_cycle_length = num_vertices;
  cycles_t cycles = NULL;
  cycle_index_t num_cycles = 0;
  cycle_length_t cycles_max_cycle_length = 0;
  for (cycle_length_t cur_max_cycle_length = START_CYCLE_LENGTH;
       cur_max_cycle_length <= num_vertices; cur_max_cycle_length++) {
    if (PRINT_PROGRESS) {
      fprintf(stderr,
              "Loading auxiliary data structures for cycles of length "
              "%" PRIcycle_length_t "... ",
              cur_max_cycle_length);
    }

    cycle_index_t num_new_cycles;
    cycles_t new_cycles = cycle_generate(adjacency_list, num_vertices,
                                         cur_max_cycle_length, &num_new_cycles);
    num_cycles += num_new_cycles;

    // no cycles of this length, skip to the next length
    if (num_new_cycles == 0) {
      free(new_cycles);
      if (PRINT_PROGRESS) {
        fprintf(stderr,
                "No cycles of length %" PRIcycle_length_t " found. Skipping.\n",
                cur_max_cycle_length);
      }
      continue;
    }
    if (PRINT_PROGRESS) {
      fprintf(stderr,
              "Found %" PRIcycle_index_t " cycles of length %" PRIcycle_length_t
              ".\n",
              num_new_cycles, cur_max_cycle_length);
    }

    // keep the smallest cycle length up to date
    if (cur_max_cycle_length < smallest_cycle_length) {
      smallest_cycle_length = cur_max_cycle_length;
    }

    // the smallest cycle length limits how many cycles we can fit and hence the
    // genus
    cycle_index_t genus_lower_bound_from_smallest_cycle_length =
        implied_max_genus_for_fit(2 * num_edges / smallest_cycle_length,
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
      cycles_t combined = (cycles_t)malloc(
          num_cycles * (cur_max_cycle_length + 2) * sizeof(vertex_t));
      assert(combined != NULL,
             "Error allocating memory for the combined cycles\n");
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
                   j] = new_cycles[i * (cur_max_cycle_length + 2) + j];
        }
      }
      cycles_max_cycle_length = cur_max_cycle_length;
      free(cycles);
      free(new_cycles);
      cycles = combined;
    }

    // if (cur_max_cycle_length == 12) {
    //   continue;
    // }  // TODO

    cycle_index_t max_cycles_per_vertex;
    cbv_t cycles_by_vertex =
        cbv_generate(num_vertices, cycles, num_cycles, cur_max_cycle_length,
                     &max_cycles_per_vertex);

    if (PRINT_PROGRESS) {
      fprintf(
          stderr,
          "Starting search for fit with %" PRIcycle_index_t
          " cycles or proof it doesn't exist (genus between %" PRIcycle_index_t
          " and %" PRIcycle_index_t ")...\n",
          genus_lower_bound_implied_fit, genus_lower_bound, genus_upper_bound);
    }
    show_progress(0.0);

    // keep track of used cycles and vertices
    bool* used_cycles = (bool*)malloc(num_cycles * sizeof(bool));
    assert(used_cycles != NULL,
           "Error allocating memory for the used cycles\n");
    for (cycle_index_t i = 0; i < num_cycles; i++) {
      used_cycles[i] = false;
    }
    // vertices should be used exactly VERTEX_USE_LIMIT times
    // so we keep track of the number of times each vertex has been used.
    // this allows us to fail early if a vertex can't be used enough times
    // and to prioritize vertices exploring vertices that have been used more
    // since they constrain the number of possible cycles containing them more
    degree_t* vertex_uses = (degree_t*)malloc(num_vertices * sizeof(degree_t));
    assert(vertex_uses != NULL,
           "Error allocating memory for the vertices most used order\n");

    // search for a solution that starts with one of the cycles
    for (cycle_index_t c = 0; c < num_cycles; c++) {
      // default all vertices to 0 uses
      for (vertex_t i = 0; i < num_vertices; i++) {
        vertex_uses[i] = 0;
      }

      // mark start cycle as used
      used_cycles[c] = true;
      cycle_length_t cycle_length;
      cycles_t cycle =
          cycle_get(cycles, cur_max_cycle_length, c, &cycle_length);
      for (cycle_length_t i = 0; i < cycle_length; i++) {
        adj_remove_edge(adjacency_list, cycle[i], cycle[i + 1]);

        // mark cycle vertices as used once
        vertex_uses[cycle[i]] = 1;
      }

      if (search(genus_lower_bound_implied_fit - 1,
                 genus_lower_bound_implied_fit, used_cycles, vertex_uses,
                 &max_fit, &num_search_calls, num_vertices, num_edges,
                 adjacency_list, cur_max_cycle_length, num_cycles, cycles,
                 max_cycles_per_vertex, cycles_by_vertex)) {
        // Success!
        show_progress(1.0);
        if (PRINT_PROGRESS) {
          fprintf(stderr,
                  "\nFound a solution! The genus is %" PRIcycle_index_t
                  ". Check the output for the %" PRIcycle_index_t " cycles. \n",
                  genus_lower_bound, genus_lower_bound_implied_fit);
        }
        fprintf(output_file,
                "Solution with %" PRIcycle_index_t " cycles found in %" PRId64
                " iterations:\n",
                genus_lower_bound_implied_fit, num_search_calls);
        for (cycle_index_t i = 0; i < num_cycles; i++) {
          if (used_cycles[i]) {
            cycles_t cycle =
                cycle_get(cycles, cur_max_cycle_length, i, &cycle_length);
            for (cycle_length_t j = 0; j < cycle_length + 1; j++) {
              fprintf(output_file, "%" PRIvertex_t " ",
                      cycle[j] + ADJACENCY_LIST_START);
            }
            fprintf(output_file, "\n");
          }
        }
        free(adjacency_list);
        free(vertex_uses);
        free(cycles);
        free(cycles_by_vertex);
        free(used_cycles);
        fclose(output_file);
        return 0;
      }

      // mark start cycle as unused
      used_cycles[c] = false;
      for (cycle_length_t i = 0; i < cycle_length; i++) {
        adj_undo_remove_edge(adjacency_list, cycle[i], cycle[i + 1]);
      }

      show_progress(c / (double)num_cycles);
    }

    show_progress(1.0);

    // we weren't able to find the implied fit, so the bounds need adjusting
    if ((2 * num_edges - cur_max_cycle_length - 1) / smallest_cycle_length <
        genus_lower_bound_implied_fit - 1) {
      genus_lower_bound++;
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
    genus_upper_bound =
        implied_max_genus_for_fit(max_fit, num_vertices, num_edges);

    if (genus_lower_bound == genus_upper_bound) {
      // we've found the genus!
      if (PRINT_PROGRESS) {
        fprintf(stderr,
                "\nFound the genus! It is %" PRIcycle_index_t
                ". Check the "
                "output for the %" PRIcycle_index_t " cycles. \n",
                genus_lower_bound, max_fit);
      }
      fprintf(output_file,
              "Genus found: %" PRIcycle_index_t " in %" PRId64 " iterations:\n",
              genus_lower_bound, num_search_calls);
      for (cycle_index_t i = 0; i < num_cycles; i++) {
        if (used_cycles[i]) {
          cycle_length_t cycle_length;
          cycles_t cycle =
              cycle_get(cycles, cur_max_cycle_length, i, &cycle_length);
          for (cycle_length_t j = 0; j < cycle_length + 1; j++) {
            fprintf(output_file, "%" PRIvertex_t " ",
                    cycle[j] + ADJACENCY_LIST_START);
          }
          fprintf(output_file, "\n");
        }
      }
      free(used_cycles);
      free(vertex_uses);
      free(adjacency_list);
      free(cycles);
      free(cycles_by_vertex);
      fclose(output_file);
      return 0;
    }
    assert(genus_lower_bound < genus_upper_bound,
           "Error: genus lower bound is greater than upper bound\n");

    if (PRINT_PROGRESS) {
      fprintf(stderr,
              "Narrowing down the genus to "
              "between %" PRIcycle_index_t " and %" PRIcycle_index_t
              ". Used %" PRId64 " iterations so far.\n",
              genus_lower_bound, genus_upper_bound, num_search_calls);
    }

    free(used_cycles);
    free(vertex_uses);
    free(cycles_by_vertex);
  }

  fprintf(stderr,
          "Was not able to fit any cycles. Double check the settings "
          "and adjacency list.\n");

  free(adjacency_list);
  fclose(output_file);
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

bool search(cycle_index_t cycles_to_use,                    // state
            cycle_index_t max_used_cycles,                  // state
            bool* used_cycles,                              // state
            degree_t* vertex_uses, cycle_index_t* max_fit,  // state
            uint64_t* num_search_calls,                     // state
            vertex_t num_vertices, edge_t num_edges, adj_t adjacency_list,
            cycle_length_t max_cycle_length, cycle_index_t num_cycles,
            cycles_t cycles, cycle_index_t max_cycles_per_vertex,
            cbv_t cycles_by_vertex) {
  (*num_search_calls)++;

  // pick a vertex to explore
  // we pick the most used vertex that hasn't reached the limit since it
  // constrains the search space of possible cycles more
  vertex_t vertex = 0;
  degree_t max_uses = 0;
  for (vertex_t i = 0; i < num_vertices; i++) {
    if (vertex_uses[i] < VERTEX_USE_LIMIT && vertex_uses[i] > max_uses) {
      vertex = i;
      max_uses = vertex_uses[i];

      if (max_uses == VERTEX_USE_LIMIT - 1) {
        break;  // we can't do better than this
      }
    }
  }
  // if we've explored all vertices fully, this cannot be extended further
  if (max_uses == VERTEX_USE_LIMIT) {
    return false;
  }

  // if we've reached a new maximum fit, print it
  if (max_used_cycles - cycles_to_use > *max_fit) {
    *max_fit = max_used_cycles - cycles_to_use;
    fprintf(output_file,
            "New max fit: %" PRIcycle_index_t
            " (about to try vertex %" PRIvertex_t ")\n",
            *max_fit, vertex);
    for (cycle_index_t i = 0; i < num_cycles; i++) {
      if (used_cycles[i]) {
        cycle_length_t cycle_length;
        vertex_t* cycle = cycle_get(cycles, max_cycle_length, i, &cycle_length);
        for (cycle_length_t j = 0; j < cycle_length + 1; j++) {
          fprintf(output_file, "%" PRIvertex_t " ",
                  cycle[j] + ADJACENCY_LIST_START);
        }
        fprintf(output_file, "\n");
      }
    }
    fprintf(output_file, "\n");
    fflush(output_file);
  }

  // look through the possible cycles that contain this vertex
  // if none can be used, this is a failed end and we backtrack
  // otherwise, we have our solution
  // TODO: skip the previously explored cycles
  cycle_index_t num_cycles_for_vertex;
  cbv_t cycle_indices = cbv_get_cycle_indices(
      cycles_by_vertex, max_cycles_per_vertex, vertex, &num_cycles_for_vertex);
  for (cycle_index_t i = 0; i < num_cycles_for_vertex; i++) {
    // skip if the cycle is already used
    cycle_index_t cycle_index = cycle_indices[i];
    if (used_cycles[cycle_index]) {
      continue;
    }

    cycle_length_t cycle_length;
    vertex_t* cycle =
        cycle_get(cycles, max_cycle_length, cycle_index, &cycle_length);

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
    if (!is_ijk_good(used_cycles, cycles, max_cycle_length, num_cycles,
                     cycle_index)) {
      continue;
    }

    // use the cycle
    used_cycles[cycle_index] = true;
    for (cycle_length_t j = 0; j < cycle_length; j++) {
      adj_remove_edge(adjacency_list, cycle[j], cycle[j + 1]);

      // mark cycle vertices as used
      vertex_uses[cycle[j]]++;
      assert(vertex_uses[cycle[j]] <= VERTEX_USE_LIMIT,
             "Vertex %" PRIvertex_t " used too many times\n", cycle[j]);
    }

    // if this is the final cycle needed to cover all edges, we're done
    if (cycles_to_use == 1) {
      return true;
    }
    // otherwise, continue adding cycles
    if (search(cycles_to_use - 1, max_used_cycles, used_cycles, vertex_uses,
               max_fit, num_search_calls, num_vertices, num_edges,
               adjacency_list, max_cycle_length, num_cycles, cycles,
               max_cycles_per_vertex, cycles_by_vertex)) {
      return true;  // as soon as we succeed, we're done
    }

    // un-use the cycle
    used_cycles[cycle_index] = false;
    for (uint8_t j = 0; j < cycle_length; j++) {
      adj_undo_remove_edge(adjacency_list, cycle[j], cycle[j + 1]);

      // un-use the cycle vertices
      vertex_uses[cycle[j]]--;
    }
  }

  // if we haven't returned true by now, we've failed
  return false;
}

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

struct fifo {
  vertex_t* data;
  cycle_index_t head;
  cycle_index_t tail;
  cycle_index_t capacity;
  cycle_length_t path_length;
};
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
           "Error filling in the cycles by vertex\n")
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
