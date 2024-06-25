// Attempts to fit the given cycles onto the given graph.
// A fitting must use each directed edge exactly once.
// Outputs a list of fitting cycles if they exist, or an error message if they
// don't. Optionally prints progress messages to stderr.
// Run with `make run`

#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

// configuration options:
#define PRINT_PROGRESS 1         // whether to print progress messages
#define DEBUG 0                  // whether to print debug messages
#define VERTEX_LIMIT_LENIENCY 0  // how many unused edge pairs to allow a vertex

// generated by generate.ipynb:
#define ADJACENCY_LIST_FILENAME "adjacency_list.txt"
#define CYCLES_FILENAME "cycles.txt"
#define CYCLES_BY_VERTEX_FILENAME "cycles_by_vertex.txt"

// assumptions of the program (don't change these):
#define VERTEX_DEGREE 3
#define VERTEX_USE_LIMIT VERTEX_DEGREE
#define MAX_VERTICES 255
#define MAX_EDGES 65535
#define MAX_CYCLE_LENGTH 255
#define MAX_CYCLES 4294967295

// constants for the program:
#define bool uint8_t
#define true 1
#define false 0

uint8_t* adj_load(char* filename, uint16_t* num_vertices, uint16_t* num_edges);
uint8_t* adj_get_neighbors(uint8_t* adjacency_list, uint8_t vertex);
void adj_remove_edge(uint8_t* adjacency_list, uint8_t start_vertex,
                     uint8_t end_vertex);
void adj_undo_remove_edge(uint8_t* adjacency_list, uint8_t start_vertex,
                          uint8_t end_vertex);
bool adj_has_edge(uint8_t* adjacency_list, uint8_t start_vertex,
                  uint8_t end_vertex);

uint8_t* cycle_load(char* filename, uint8_t* cycle_length,
                    uint32_t* num_cycles);
uint8_t* cycle_get(uint8_t* cycles, uint8_t cycle_length, uint32_t cycle_index);

uint32_t* cbv_load(char* filename, uint16_t num_vertices, uint8_t* cycles,
                   uint8_t cycle_length, uint32_t* max_cycles_per_vertex);
uint32_t* cbv_get_cycle_indices(uint32_t* cycles_by_vertex,
                                uint32_t max_cycles_per_vertex, uint16_t vertex,
                                uint32_t* num_cycles);

void show_progress(double fraction);

bool is_ijk_good(bool* used_cycles, uint8_t* cycles, uint8_t cycle_length,
                 uint32_t num_cycles, uint32_t cycle_to_check);
bool search(uint32_t cycles_to_use, bool* used_cycles,  // state
            uint8_t* vertex_uses, uint8_t* max_fit,     // state
            uint64_t* num_search_calls,                 // state
            uint16_t num_vertices, uint16_t num_edges, uint8_t* adjacency_list,
            uint8_t cycle_length, uint32_t num_cycles, uint8_t* cycles,
            uint32_t max_cycles_per_vertex, uint32_t* cycles_by_vertex);

int main(void) {
  if (PRINT_PROGRESS) {
    fprintf(stderr, "Loading data...\n");
  }

  uint16_t num_vertices, num_edges;
  uint8_t* adjacency_list =
      adj_load(ADJACENCY_LIST_FILENAME, &num_vertices, &num_edges);

  uint8_t cycle_length;
  uint32_t num_cycles;
  uint8_t* cycles = cycle_load(CYCLES_FILENAME, &cycle_length, &num_cycles);

  if (cycle_length > num_vertices) {
    fprintf(stderr,
            "Cycle length (%d) must be less than or equal to the number of "
            "vertices (%d)\n",
            cycle_length, num_vertices);
    exit(1);
  }

  uint32_t max_cycles_per_vertex;
  uint32_t* cycles_by_vertex =
      cbv_load(CYCLES_BY_VERTEX_FILENAME, num_vertices, cycles, cycle_length,
               &max_cycles_per_vertex);

  if (PRINT_PROGRESS) {
    fprintf(stderr, "Starting search...\n");
  }
  show_progress(0.0);

  // keep track of used cycles and vertices
  uint32_t edges_to_remove = 2 * num_edges;
  uint32_t cycles_to_use = edges_to_remove / cycle_length;
  bool* used_cycles = (bool*)malloc(num_cycles * sizeof(bool));
  if (used_cycles == NULL) {
    fprintf(stderr, "Error allocating memory for the used cycles\n");
    exit(1);
  }
  for (uint32_t i = 0; i < num_cycles; i++) {
    used_cycles[i] = false;
  }
  // vertices should be used exactly VERTEX_USE_LIMIT times
  // so we keep track of the number of times each vertex has been used.
  // this allows us to fail early if a vertex can't be used enough times
  // and to prioritize vertices exploring vertices that have been used more
  // since they constrain the number of possible cycles containing them more
  uint8_t* vertex_uses = (uint8_t*)malloc(num_vertices * sizeof(uint8_t));
  if (vertex_uses == NULL) {
    fprintf(stderr,
            "Error allocating memory for the vertices most used order\n");
    exit(1);
  }

  // search for a solution that starts with one of the cycles in this work part
  uint8_t max_fit = 0;
  uint64_t num_search_calls = 0;
  for (uint32_t c = 0; c < num_cycles; c++) {
    if (DEBUG) fprintf(stderr, "\nTrying cycle %d\n", c);

    // default all vertices to 0 uses
    for (uint16_t i = 0; i < num_vertices; i++) {
      vertex_uses[i] = 0;
    }

    // mark start cycle as used
    used_cycles[c] = true;
    cycles_to_use--;
    uint8_t* cycle = cycle_get(cycles, cycle_length, c);
    for (uint8_t i = 0; i < cycle_length; i++) {
      adj_remove_edge(adjacency_list, cycle[i], cycle[i + 1]);

      // mark cycle vertices as used once
      vertex_uses[cycle[i]] = 1;
    }

    if (search(cycles_to_use, used_cycles, vertex_uses, &max_fit,
               &num_search_calls, num_vertices, num_edges, adjacency_list,
               cycle_length, num_cycles, cycles, max_cycles_per_vertex,
               cycles_by_vertex)) {
      // Success!
      show_progress(1.0);
      if (PRINT_PROGRESS) {
        fprintf(stderr, "\nFound a solution! Check the output to see it.\n");
      }
      printf("Solution found in %lld iterations:\n", num_search_calls);
      for (uint32_t i = 0; i < num_cycles; i++) {
        if (used_cycles[i]) {
          uint8_t* cycle = cycle_get(cycles, cycle_length, i);
          for (uint8_t j = 0; j < cycle_length + 1; j++) {
            printf("%d ", cycle[j]);
          }
          printf("\n");
        }
      }
      free(adjacency_list);
      free(cycles);
      free(cycles_by_vertex);
      free(used_cycles);
      free(vertex_uses);
      return 0;
    }

    // mark start cycle as unused
    cycles_to_use++;
    used_cycles[c] = false;
    for (uint8_t i = 0; i < cycle_length; i++) {
      adj_undo_remove_edge(adjacency_list, cycle[i], cycle[i + 1]);
    }

    show_progress(c / (double)num_cycles);
  }

  show_progress(1.0);
  if (PRINT_PROGRESS) {
    fprintf(stderr,
            "\nDone. Did not find any solutions. Was only able to fit %d "
            "cycles. Used %lld iterations.\n",
            max_fit, num_search_calls);
  }
  free(adjacency_list);
  free(cycles);
  free(cycles_by_vertex);
  free(used_cycles);
  free(vertex_uses);
  return 0;
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
bool is_ijk_good(bool* used_cycles, uint8_t* cycles, uint8_t cycle_length,
                 uint32_t num_cycles, uint32_t cycle_to_check) {
  uint8_t* cycle = cycle_get(cycles, cycle_length, cycle_to_check);

  uint8_t* padded_cycle =
      (uint8_t*)malloc((cycle_length + 2) * sizeof(uint8_t));
  if (padded_cycle == NULL) {
    fprintf(stderr, "Error allocating memory for the padded cycle\n");
    exit(1);
  }
  for (uint8_t i = 0; i < cycle_length; i++) {
    padded_cycle[i] = cycle[i];
  }
  padded_cycle[cycle_length] = cycle[0];
  padded_cycle[cycle_length + 1] = cycle[1];

  for (uint32_t c = 0; c < num_cycles; c++) {
    if (used_cycles[c]) {
      uint8_t* other_cycle = cycle_get(cycles, cycle_length, c);

      uint8_t* padded_other_cycle =
          (uint8_t*)malloc((cycle_length + 2) * sizeof(uint8_t));
      if (padded_other_cycle == NULL) {
        fprintf(stderr, "Error allocating memory for the padded other cycle\n");
        exit(1);
      }
      for (uint8_t i = 0; i < cycle_length; i++) {
        padded_other_cycle[i] = other_cycle[i];
      }
      padded_other_cycle[cycle_length] = other_cycle[0];
      padded_other_cycle[cycle_length + 1] = other_cycle[1];

      for (uint8_t i = 0; i < cycle_length; i++) {
        for (uint8_t j = 0; j < cycle_length; j++) {
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

bool search(uint32_t cycles_to_use, bool* used_cycles,  // state
            uint8_t* vertex_uses, uint8_t* max_fit,     // state
            uint64_t* num_search_calls,                 // state
            uint16_t num_vertices, uint16_t num_edges, uint8_t* adjacency_list,
            uint8_t cycle_length, uint32_t num_cycles, uint8_t* cycles,
            uint32_t max_cycles_per_vertex, uint32_t* cycles_by_vertex) {
  (*num_search_calls)++;

  int8_t leniency = -1;
  uint8_t
      ignored_vertices[VERTEX_LIMIT_LENIENCY + 1];  // plus one to avoid zero
  uint8_t num_ignored_vertices = 0;
  while (leniency < VERTEX_LIMIT_LENIENCY) {
    // pick a vertex to explore
    // we pick the most used vertex that hasn't reached the limit since it
    // constrains the search space of possible cycles more
    uint8_t vertex;
    int16_t max_uses = -1;
    for (uint16_t i = 0; i < num_vertices; i++) {
      bool ignore = false;
      for (uint8_t j = 0; j < num_ignored_vertices; j++) {
        if (ignored_vertices[j] == i) {
          ignore = true;
          break;
        }
      }
      if (ignore) {
        continue;
      }

      if (vertex_uses[i] < VERTEX_USE_LIMIT && vertex_uses[i] > max_uses) {
        vertex = i;
        max_uses = vertex_uses[i];

        if (max_uses == VERTEX_USE_LIMIT - 1) {
          break;  // we can't do better than this
        }
      }
    }
    // assert we don't reach a bad state
    if (max_uses == -1) {
      fprintf(stderr, "\nNo vertex to explore\n");
      for (uint16_t i = 0; i < num_vertices; i++) {
        fprintf(stderr, "%d ", vertex_uses[i]);
      }
      fprintf(stderr, "\n");
      exit(1);
    }
    leniency += VERTEX_USE_LIMIT - vertex_uses[vertex];
    ignored_vertices[num_ignored_vertices++] = vertex;

    // if we've reached a new maximum fit, print it
    if (2 * num_edges / cycle_length - cycles_to_use > *max_fit) {
      *max_fit = 2 * num_edges / cycle_length - cycles_to_use;
      printf("New max fit: %d (about to try vertex %" PRId8 ")\n", *max_fit,
             vertex);
      for (uint32_t i = 0; i < num_cycles; i++) {
        if (used_cycles[i]) {
          uint8_t* cycle = cycle_get(cycles, cycle_length, i);
          for (uint8_t j = 0; j < cycle_length + 1; j++) {
            printf("%d ", cycle[j]);
          }
          printf("\n");
        }
      }
      printf("\n");
    }

    // look through the possible cycles that contain this vertex
    // if none can be used, this is a failed end and we backtrack
    // otherwise, we have our solution
    uint32_t num_cycles_for_vertex;
    uint32_t* cycle_indices =
        cbv_get_cycle_indices(cycles_by_vertex, max_cycles_per_vertex, vertex,
                              &num_cycles_for_vertex);
    for (uint32_t i = 0; i < num_cycles_for_vertex; i++) {
      // skip if the cycle is already used
      uint32_t cycle_index = cycle_indices[i];
      if (used_cycles[cycle_index]) {
        continue;
      }

      uint8_t* cycle = cycle_get(cycles, cycle_length, cycle_index);

      // cycle is only usable if all edges are available
      bool can_use = true;
      for (uint8_t j = 0; j < cycle_length; j++) {
        if (!adj_has_edge(adjacency_list, cycle[j], cycle[j + 1])) {
          can_use = false;
          break;
        }
      }
      if (!can_use) {
        continue;
      }

      // make sure the cycle satisfies the ijk condition
      if (!is_ijk_good(used_cycles, cycles, cycle_length, num_cycles,
                       cycle_index)) {
        continue;
      }

      // use the cycle
      if (DEBUG) fprintf(stderr, "Using cycle %d\n", cycle_index);
      used_cycles[cycle_index] = true;
      for (uint8_t j = 0; j < cycle_length; j++) {
        adj_remove_edge(adjacency_list, cycle[j], cycle[j + 1]);

        // mark cycle vertices as used
        vertex_uses[cycle[j]]++;

        // assert that we don't reach a bad state
        if (vertex_uses[cycle[j]] > VERTEX_USE_LIMIT) {
          fprintf(stderr, "\nVertex %d used too many times (exploring %d)\n",
                  cycle[j], vertex);
          for (uint16_t i = 0; i < num_vertices; i++) {
            fprintf(stderr, "%d ", vertex_uses[i]);
          }
          fprintf(stderr, "\n");
          for (uint16_t i = 0; i < num_vertices; i++) {
            fprintf(stderr, "%d: ", i);
            for (uint8_t j = 0; j < VERTEX_DEGREE; j++) {
              fprintf(stderr, "%d ", adj_get_neighbors(adjacency_list, i)[j]);
            }
            fprintf(stderr, "\n");
          }
          exit(1);
        }
      }

      // if this is the final cycle needed to cover all edges, we're done
      if (cycles_to_use == 1) {
        return true;
      }
      // otherwise, continue adding cycles
      if (search(cycles_to_use - 1, used_cycles, vertex_uses, max_fit,
                 num_search_calls, num_vertices, num_edges, adjacency_list,
                 cycle_length, num_cycles, cycles, max_cycles_per_vertex,
                 cycles_by_vertex)) {
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
  }

  // if we haven't returned true by now, we've failed
  return false;
}

uint8_t* adj_load(char* filename, uint16_t* num_vertices, uint16_t* num_edges) {
  FILE* fp = fopen(filename, "r");
  if (fp == NULL) {
    fprintf(stderr, "Error opening file %s\n", filename);
    exit(1);
  }

  // number of vertices and edges are the two first numbers
  if (fscanf(fp, "%hd %hd", num_vertices, num_edges) != 2) {
    fprintf(stderr, "Error reading the first line of %s\n", filename);
    exit(1);
  }

  uint8_t* adjacency_list =
      (uint8_t*)malloc(*num_vertices * VERTEX_DEGREE * sizeof(uint8_t));
  if (adjacency_list == NULL) {
    fprintf(stderr, "Error allocating memory for the adjacency list\n");
    exit(1);
  }
  for (uint16_t i = 0; i < *num_vertices * VERTEX_DEGREE; i++) {
    if (fscanf(fp, "%" SCNu8, &adjacency_list[i]) != 1) {
      fprintf(stderr, "Error reading the adjacency list from %s\n", filename);
      exit(1);
    }
  }

  fclose(fp);

  if (PRINT_PROGRESS) {
    fprintf(stderr, "Read the adjacency list from %s\n", filename);
    fprintf(stderr, "\tNumber of vertices: %d\n", *num_vertices);
    fprintf(stderr, "\tNumber of edges: %d (%d directed)\n", *num_edges,
            2 * *num_edges);
    fprintf(stderr, "\tFirst 5 vertices (with neighbors): ");
    for (uint8_t v = 0; v < 5; v++) {
      fprintf(stderr, "%d(%d %d %d) ", v,
              adj_get_neighbors(adjacency_list, v)[0],
              adj_get_neighbors(adjacency_list, v)[1],
              adj_get_neighbors(adjacency_list, v)[2]);
    }
    fprintf(stderr, "\n");
  }

  return adjacency_list;
}

uint8_t* adj_get_neighbors(uint8_t* adjacency_list, uint8_t vertex) {
  return &adjacency_list[vertex * VERTEX_DEGREE];
}

void adj_remove_edge(uint8_t* adjacency_list, uint8_t start_vertex,
                     uint8_t end_vertex) {
  uint8_t* neighbors = adj_get_neighbors(adjacency_list, start_vertex);
  for (uint8_t i = 0; i < VERTEX_DEGREE; i++) {
    if (neighbors[i] == end_vertex) {
      neighbors[i] = MAX_VERTICES;
      return;
    }
  }
}

// must have been previously removed, otherwise undefined behavior
void adj_undo_remove_edge(uint8_t* adjacency_list, uint8_t start_vertex,
                          uint8_t end_vertex) {
  uint8_t* neighbors = adj_get_neighbors(adjacency_list, start_vertex);
  for (uint8_t i = 0; i < VERTEX_DEGREE; i++) {
    if (neighbors[i] == MAX_VERTICES) {
      neighbors[i] = end_vertex;
      return;
    }
  }
}

bool adj_has_edge(uint8_t* adjacency_list, uint8_t start_vertex,
                  uint8_t end_vertex) {
  uint8_t* neighbors = adj_get_neighbors(adjacency_list, start_vertex);
  for (uint8_t i = 0; i < VERTEX_DEGREE; i++) {
    if (neighbors[i] == end_vertex) {
      return true;
    }
  }
  return false;
}

uint8_t* cycle_load(char* filename, uint8_t* cycle_length,
                    uint32_t* num_cycles) {
  FILE* fp = fopen(filename, "r");
  if (fp == NULL) {
    fprintf(stderr, "Error opening file %s\n", filename);
    exit(1);
  }

  // cycle length and number of cycles are the two first numbers
  if (fscanf(fp, "%" SCNu8 " %d", cycle_length, num_cycles) != 2) {
    fprintf(stderr, "Error reading the first line of %s\n", filename);
    exit(1);
  }

  uint8_t* cycles =
      (uint8_t*)malloc(*num_cycles * (*cycle_length + 1) * sizeof(uint8_t));
  if (cycles == NULL) {
    fprintf(stderr, "Error allocating memory for the cycles\n");
    exit(1);
  }
  for (uint64_t i = 0; i < *num_cycles * (*cycle_length + 1); i++) {
    if (fscanf(fp, "%" SCNu8, &cycles[i]) != 1) {
      fprintf(stderr, "Error reading the cycles from %s\n", filename);
      exit(1);
    }
  }

  fclose(fp);

  if (PRINT_PROGRESS) {
    fprintf(stderr, "Read the cycles from %s\n", filename);
    fprintf(stderr, "\tCycle length: %d\n", *cycle_length);
    fprintf(stderr, "\tNumber of cycles: %d\n", *num_cycles);
    fprintf(stderr, "\tFirst 5 cycles:\n");
    for (uint16_t i = 0; i < 5; i++) {
      fprintf(stderr, "\t\t%d: ", i);
      for (uint16_t j = 0; j < *cycle_length + 1; j++) {
        fprintf(stderr, "%02d ", cycle_get(cycles, *cycle_length, i)[j]);
      }
      fprintf(stderr, "\n");
    }
  }

  return cycles;
}

uint8_t* cycle_get(uint8_t* cycles, uint8_t cycle_length,
                   uint32_t cycle_index) {
  return &cycles[cycle_index * (cycle_length + 1)];
}

uint32_t* cbv_load(char* filename, uint16_t num_vertices, uint8_t* cycles,
                   uint8_t cycle_length, uint32_t* max_cycles_per_vertex) {
  FILE* fp = fopen(filename, "r");
  if (fp == NULL) {
    fprintf(stderr, "Error opening file %s\n", filename);
    exit(1);
  }

  // number of cycles per vertex is the first number
  if (fscanf(fp, "%d", max_cycles_per_vertex) != 1) {
    fprintf(stderr, "Error reading the first line of %s\n", filename);
    exit(1);
  }

  uint32_t* cycles_by_vertex = (uint32_t*)malloc(
      num_vertices * (*max_cycles_per_vertex + 1) * sizeof(uint32_t));
  if (cycles_by_vertex == NULL) {
    fprintf(stderr, "Error allocating memory for the cycles by vertex\n");
    exit(1);
  }
  for (uint16_t i = 0; i < num_vertices; i++) {
    if (fscanf(fp, "%d", &cycles_by_vertex[i * (*max_cycles_per_vertex + 1)]) !=
        1) {
      fprintf(stderr, "Error reading the number of cycles for vertex from %s\n",
              filename);
      exit(1);
    }
    for (uint32_t j = 0; j < cycles_by_vertex[i * (*max_cycles_per_vertex + 1)];
         j++) {
      if (fscanf(fp, "%d",
                 &cycles_by_vertex[i * (*max_cycles_per_vertex + 1) + j + 1]) !=
          1) {
        fprintf(stderr, "Error reading the cycles by vertex from %s\n",
                filename);
        exit(1);
      }
    }
  }

  fclose(fp);

  if (PRINT_PROGRESS) {
    fprintf(stderr, "Read the cycles by vertex from %s\n", filename);
    fprintf(stderr, "\tMax cycles per vertex: %d\n", *max_cycles_per_vertex);
    fprintf(stderr, "\tFirst 2 cycles of vertex 0 and 1:\n");
    for (uint16_t i = 0; i < 2; i++) {
      uint32_t num_cycles;
      uint32_t* cycle_indices = cbv_get_cycle_indices(
          cycles_by_vertex, *max_cycles_per_vertex, i, &num_cycles);
      fprintf(stderr, "\t\t%d:\n", i);
      for (uint32_t j = 0; j < num_cycles && j < 2; j++) {
        fprintf(stderr, "\t\t\t%d / %d: ", j, num_cycles);
        for (uint16_t h = 0; h < cycle_length + 1; h++) {
          fprintf(stderr, "%02d ",
                  cycle_get(cycles, cycle_length, cycle_indices[j])[h]);
        }
        fprintf(stderr, "\n");
      }
    }
  }

  return cycles_by_vertex;
}

uint32_t* cbv_get_cycle_indices(uint32_t* cycles_by_vertex,
                                uint32_t max_cycles_per_vertex, uint16_t vertex,
                                uint32_t* num_cycles) {
  uint32_t* row = &cycles_by_vertex[vertex * (max_cycles_per_vertex + 1)];
  *num_cycles = row[0];
  return &row[1];
}
