// Internal checks for the reductions and the face bound used by both solvers.
#include <assert.h>

#define main solver_main
#ifdef PARALLEL_SOLVER
#include "../multi_genus_parallel.c"
#else
#include "../multi_genus.c"
#endif
#undef main

int main(void) {
  GRAPH graph = {{0}};
  ADJAZENZ adj = {0};
  int genus;

  graph[0][0] = 2;
  einfugen(graph, adj, 1, 2);
  get_initial_embedding(graph, adj, &genus);
  KANTE *original = firstedge[2];
  red_edges[0].invers = &red_edges[1];
  red_edges[1].invers = &red_edges[0];
  subdivide(3, 1, 2, 0);
  unsubdivide(3, 1, 2);
  assert(firstedge[2] == original);
  assert(original->prev == original && original->next == original);
  assert(original->name == 1 && original->invers == firstedge[1]);

  // The pendant dart requires length five. The other three darts outside
  // that face have length at least three, giving 5/5 + 3/3 = 2 faces.
  graph[0][0] = 4;
  einfugen(graph, adj, 2, 3);
  einfugen(graph, adj, 3, 1);
  einfugen(graph, adj, 1, 4);
  assert(scaled_face_bound(graph, adj) == 2 * FACE_SCALE);
  return 0;
}
