// Calculate the minimum genus of an arbitrary connected undirected graph.
// Copyright (C) 2026 Gunnar Brinkmann

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

/* Aufruf: cat Codes | multi_genus_parallel
                              or
               cat Codes | multi_genus_parallel_64
compile

gcc -O3 -DLONG -march=native -pthread -o multi_genus_parallel \
    multi_genus_parallel.c -lm

or

gcc -O3 -march=native -pthread -o multi_genus_parallel_64 \
    multi_genus_parallel.c -lm

depending on the definition of longtype

This version keeps the original algorithm, but parallelizes the bounded
genus searches by splitting the recursion tree. Each worker repeats the cheap
work down to a chosen split depth and then explores every n-th split node. The
thread count is controlled by MULTI_GENUS_THREADS, MG_THREADS, or THREADS; if
none are set, the number of online processors is used. MULTI_GENUS_SPLIT_DEPTH
can override the adaptive default split-depth selection.

9.9. LONGTYPE eingefuehrt um auch mit unsigned_int__128 arbeiten zu koennen.
Auch Makros veraendert.

24.7.2019: Makro bit(i)  von ((1UL)<<(i)) zu  ((1UL)<<((i)-1)) veraendert um 64
knoten Graphen zu testen. Nicht alle Tests wiederholt, aber einige und geschaut
ob bits auch anders als mit dem bit() Makro benutzt werden.

Default: Berechnet eine Einbettung mit minimalem Geschlecht und gibt am Ende
eine Statistik der Geschlechter der gefundenen Einbettungen.

Die Einbettungen werden nur geschrieben, wenn das durch eine Option gewaehlt
wird.

Der Graph muss einfach (keine Multikanten oder loops)
und zusammenhaengend sein und mindestens 2 Knoten haben -- das wird nicht
getestet (ausser wenn Option b benutzt wird!

Fuer die Optionen und Funktionalitaet starten mit Option "h" oder "?"

Bei output von Einbettungen wird nicht auf Isomorphie ueberprueft, es koennen
also mehrere isomorphe Einbettungen ausgegeben werden. Aus jeder
Isomorphieklasse ist aber mindestens eine Einbettung dabei. Spiegelbilder werden
durch Festlegung von 3 Kanten an einem Knoten mit Grad mindestens 3 (falls
vorhanden) vermieden.


Tests -- allesamt natuerlich ohne einen Unterschied festzustellen:

Die Genusberechnung wurde mit einem unabhaengigen Javaprogramm (Autor: Jasper
Souffriau) verglichen. Dabei wurden nicht Statistiken von Mengen von Grafen
verglichen, sondern das Ergebnis fuer jeden einzelnen Graphen in den volgenden
Mengen von zusammenhaengenden Graphen:

Alle Graphen mit bis zu 11 Knoten.
Alle 3-regulaeren Graphen mit bis zu 24 Knoten.
Alle 4-regulaeren Graphen mit bis zu 16 Knoten.
Alle 5-regulaeren Graphen mit bis zu 14 Knoten.
Alle 3-regulaeren Graphen mit Taillenweite mindestens 5 und bis zu 26 Knoten.
Alle 3-regulaeren Graphen mit Taillenweite mindestens 6 und bis zu 28 Knoten.
Alle 3-regulaeren Graphen mit Taillenweite mindestens 7 und bis zu 34 Knoten.
Alle 3-regulaeren Graphen mit Taillenweite mindestens 8 und bis zu 44 Knoten.
Alle 3-regulaeren Graphen mit Taillenweite 9 und 58 Knoten.
Alle 4-regulaeren Graphen mit Taillenweite mindestens 5 und bis zu 24 Knoten.
Alle Graphen mit Gradsequenz 2_2_3_3_3

The function "all embeddings" was tested by writing a stupid program producing
all permutations of orders around the vertices and filtering them for the proper
genus. Then for each graph tested the range of possible genera was computed by
the Euler formula and for each graph and each possble genus the embeddings of
this genus were independently generated and the number of embeddings as well as
the number of non-isomorphic embeddings (computed by an isomorphism checking
program using lists) were compared. Due to the enormous number of embeddings
already for small graphs, not too many graphs and no large graphs could be
tested. Tested:

All 3-regular graphs on up to 18 vertices.
All graphs on 7 vertices with 6 to 17 edges.
All graphs on 8 vertices with 14 and with 15 edges.
All graphs with valence vector 1 1 1 5
All graphs with valence vector 1 1 1 2 2
All graphs with valence vector 0 1 1 2 3
All graphs with valence vector 0 2 3 2 3 and girth at least 4

As a (comparatively small) test for the use of unsigned __int128, all cubic
graphs with 24 vertices and girth 5 and all graphs with valence vector 0 0 10 7
2 and girth 5 were tested for the genus and then minimum genus embeddings were
truncated (giving graphs with the same genus and 72 resp. 68 vertices),
reembedded in genus 5, and then transformed to multicode and tested for the
genus again.

 */
#include <ctype.h>
#include <limits.h>
#include <errno.h>
#include <string.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#ifdef _WIN32
#define WIN32_LEAN_AND_MEAN
#ifdef LONG
#define MULTI_RESTORE_LONG_FEATURE
#undef LONG
#endif
#include <windows.h>
#ifdef MULTI_RESTORE_LONG_FEATURE
#define LONG
#endif
#ifdef __GNUC__
#define MULTI_THREAD_LOCAL __thread
#else
#define MULTI_THREAD_LOCAL __declspec(thread)
#endif
#else
#include <pthread.h>
#include <unistd.h>
#define MULTI_THREAD_LOCAL _Thread_local
#endif

#ifdef _WIN32
#include <fcntl.h>
#include <io.h>
#endif

#define leer 255

#ifdef LONG
#define knoten 128
#define d_kanten 1024  // maximum number of directed edges
#define LONGTYPE unsigned __int128
#else
#define knoten 64
#define LONGTYPE unsigned long long
#define d_kanten 512  // maximum number of directed edges
#endif

typedef unsigned char GRAPH[knoten + 1][knoten];
typedef unsigned char ADJAZENZ[knoten + 1];
// LONGTYPE original[knoten+1]; // the graph as bitvector

typedef struct K {
  unsigned short ursprung; /* bei welchem knoten startet die kante */
  unsigned short name;     /* Identifikation des Knotens, mit
                         dem Verbindung besteht */
#ifdef TEST
  long dummy; /* fuer alle moeglichen zwecke */
#endif
  unsigned char is_embedded;
  LONGTYPE *faceleft;
  struct K *prev;   /* vorige Kante im Uhrzeigersinn */
  struct K *next;   /* naechste Kante im Uhrzeigersinn */
  struct K *invers; /* die inverse Kante (in der Liste von "name") */
} KANTE;

#ifdef TEST
unsigned char shortpatharray[knoten + 1][knoten + 1];
#endif

static MULTI_THREAD_LOCAL KANTE edges[d_kanten];  // een lijst van bogen die toegevoegd worden
// de bogen in de array worden voogeinitialiseerd
// int em_edges=0; // embedded oriented edges -- so 2*(embedded edges)
KANTE red_edges[4 * knoten];  // bogen die bij de inverse operatie van de
                              // reductie gebruikt worden
static MULTI_THREAD_LOCAL KANTE *last_edge;
static MULTI_THREAD_LOCAL int em_vertices = 0, em_faces = 0;
static MULTI_THREAD_LOCAL int knotenzahl;
static MULTI_THREAD_LOCAL KANTE *firstedge[knoten + 1];
static MULTI_THREAD_LOCAL ADJAZENZ adj_embedded;
static MULTI_THREAD_LOCAL LONGTYPE faces[d_kanten / 3];
static MULTI_THREAD_LOCAL LONGTYPE *face_pointer[d_kanten / 3];
/* faces is een reservoir voor vlakken als bitsets. face_pointer[em_faces] is
altijd het volgende vlak dat toegekend kan worden. Als een vlak terug vrijkomt
wordt het dus aan het begin van de lijst gezet. */
static MULTI_THREAD_LOCAL LONGTYPE rememberfaces[d_kanten];
// when edge number k is inserted between right1 and right2, the face on the
// left of right1 (before adding the edge) is stored in rememberfaces[2k] and
// that on the left of right2 in  rememberfaces[2k+1]
int globalnv, globalne, write_embedding = 0, filter = -1, filter2 = -1, filterl = -1,
                        all = 0;
static MULTI_THREAD_LOCAL int edgelimit;
int filterlarge = 0, compute_lower_bound = 1, do_bfs = 1;
unsigned long long written = 0UL;

int reduce2 = 1;  // May vertices of degree 1 and 2 be reduced ?
int reconstruct[knoten + 1][4], number_reconstruct;
/* The reconstruct operations have to be performed in reverse order -- so
   starting with number_reconstruct-1 and going to 0. The triple
   reconstruct[i][] gives details about reconstruct operation number i. The int
   reconstruct[i][0] gives the type of construction: 0: add a vertex with
   degree 1. Name it reconstruct[i][1] and attach it to reconstruct[i][2]. 1:
   subdivide an edge with a vertex of degree 2. Name it reconstruct[i][1] and
   subdivide the edge {reconstruct[i][2], reconstruct[i][3]}. 2: add a vertex
   with degree 2. Name it reconstruct[i][1] and connect it parallel to the
   existing edge {reconstruct[i][2], reconstruct[i][3]} to the same vertices.
*/

int bfsnummer[knoten + 1], invbfsnummer[knoten + 1];
/* Euler's formula with at least one face gives g <= (E - V + 1) / 2. */
#define MAX_GENUS (d_kanten / 4)
static unsigned long long good_approx[MAX_GENUS + 1];

#ifdef _WIN32
typedef HANDLE multi_thread_t;
typedef DWORD (WINAPI *multi_thread_start_t)(LPVOID);
#define MULTI_THREAD_RETURN DWORD WINAPI
#define MULTI_THREAD_RESULT 0
#else
typedef pthread_t multi_thread_t;
typedef void *(*multi_thread_start_t)(void *);
#define MULTI_THREAD_RETURN void *
#define MULTI_THREAD_RESULT NULL
#endif

typedef struct {
  GRAPH graph;
  ADJAZENZ adj;
  int max_genus;
  int worker_id;
  int worker_count;
  int split_depth;
  int found;
} MULTI_WORKER;

static atomic_int multi_parallel_stop = 0;
static MULTI_THREAD_LOCAL int multi_worker_id = 0;
static MULTI_THREAD_LOCAL int multi_worker_count = 1;
static MULTI_THREAD_LOCAL int multi_split_depth = -1;
static MULTI_THREAD_LOCAL int multi_split_counter = 0;
static MULTI_THREAD_LOCAL int multi_count_split_nodes = 0;
static MULTI_THREAD_LOCAL unsigned long long multi_split_node_count = 0;
static MULTI_THREAD_LOCAL unsigned long long multi_split_node_limit = 0;
static atomic_int multi_output_claimed = 0;

int multi_thread_create(multi_thread_t *thread, multi_thread_start_t start,
                        void *arg) {
#ifdef _WIN32
  *thread = CreateThread(NULL, 0, start, arg, 0, NULL);
  return *thread == NULL ? -1 : 0;
#else
  return pthread_create(thread, NULL, start, arg);
#endif
}

int multi_thread_join(multi_thread_t thread) {
#ifdef _WIN32
  DWORD wait_result = WaitForSingleObject(thread, INFINITE);
  CloseHandle(thread);
  return wait_result == WAIT_OBJECT_0 ? 0 : -1;
#else
  return pthread_join(thread, NULL);
#endif
}

unsigned multi_online_processor_count(void) {
#ifdef _WIN32
  SYSTEM_INFO info;
  GetSystemInfo(&info);
  return info.dwNumberOfProcessors > 0 ? (unsigned)info.dwNumberOfProcessors
                                       : 1U;
#else
  long online_processors = sysconf(_SC_NPROCESSORS_ONLN);
  return online_processors > 0 ? (unsigned)online_processors : 1U;
#endif
}

int multi_getenv_positive(char *name, int fallback) {
  char *value = getenv(name);
  char *end = NULL;
  long parsed;
  if ((value == NULL) || (value[0] == '\0')) return fallback;
  parsed = strtol(value, &end, 10);
  if ((end == value) || (parsed <= 0) || (parsed > INT_MAX)) return fallback;
  return (int)parsed;
}

int multi_thread_count(void) {
  // Thread count is controlled by MULTI_GENUS_THREADS, MG_THREADS, or THREADS.
  // If none are set, use the number of online processors.
  int threads = multi_getenv_positive("MULTI_GENUS_THREADS", 0);
  if (threads <= 0) threads = multi_getenv_positive("MG_THREADS", 0);
  if (threads <= 0) threads = multi_getenv_positive("THREADS", 0);
  if (threads <= 0) threads = (int)multi_online_processor_count();
  if (threads < 1) threads = 1;
  if (threads > 64) threads = 64;
  return threads;
}

int multi_split_depth_override(void) {
  int depth = multi_getenv_positive("MULTI_GENUS_SPLIT_DEPTH", -1);
  return depth;
}

int multi_parallel_take_node(int depth) {
  if (multi_count_split_nodes && atomic_load(&multi_parallel_stop)) return 0;
  if ((multi_split_depth < 0) || (depth != multi_split_depth)) return 1;
  if (multi_count_split_nodes) {
    multi_split_node_count++;
    if ((multi_split_node_limit > 0) &&
        (multi_split_node_count >= multi_split_node_limit))
      atomic_store(&multi_parallel_stop, 1);
    return 0;
  }
  if (multi_worker_count <= 1)
    return 1;
  if (atomic_load(&multi_parallel_stop)) return 0;
  if (multi_split_counter == 0) {
    multi_split_counter = multi_worker_count - 1;
    return 1;
  }
  multi_split_counter--;
  return 0;
}

int multi_should_write_code(int genus) {
  int expected = 0;
  if (!((write_embedding) || (genus == filter) || (genus == filter2))) return 0;
  if (multi_count_split_nodes) return 0;
  if (multi_worker_count <= 1) return 1;
  if (!write_embedding) return 0;
  return atomic_compare_exchange_strong(&multi_output_claimed, &expected, 1);
}

#define bit(i) (((LONGTYPE)1) << ((i) - 1))
#define DELBIT(a, i) ((a) &= (~bit(i)))
#define SETBIT(a, i) ((a) |= (bit(i)))
#define IS_SET(a, i) ((a) & (bit(i)))

#define ULBIT(i) ((1ULL) << ((i) - 1))
#define FFSL(x) (__builtin_ffsll(x))

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

void writemap(unsigned char maxtop) {
  int i;
  KANTE *run;
  fprintf(stderr,
          "------------------------------------------------------------\n");
  for (i = 1; i <= maxtop; i++)
    if (firstedge[i] != NULL) {
      fprintf(stderr, "%d: %d", i, firstedge[i]->name);
      for (run = firstedge[i]->next; run != firstedge[i]; run = run->next)
        fprintf(stderr, " %d", run->name);
      fprintf(stderr, "\n");
    }
  fprintf(stderr,
          "------------------------------------------------------------\n");
}

void writeset(char name[], LONGTYPE s) {
  int i;

  fprintf(stderr, "%s:", name);

#ifdef LONG
  for (i = 1; i <= 128; i++)
    if (s & bit(i)) fprintf(stderr, " %d", i);
#else
  for (i = 1; i <= 64; i++)
    if (s & bit(i)) fprintf(stderr, " %d", i);
#endif

  fprintf(stderr, "\n");
}

#ifdef TEST
void testmap(int maxtop, int genus) {
  int i, counter, search;
  KANTE *run, *run2;
  LONGTYPE localface, *localfacep;
  int nv = 0, ne = 0, nf;

  // writemap(maxtop);

  for (i = 1; i <= maxtop; i++)
    if (firstedge[i] != NULL) {
      // ne+=adj_embedded[i];
      nv++;
      if (firstedge[i] == NULL) {
        fprintf(stderr, "PROBLEM 1\n");
        exit(1);
      }
      run = firstedge[i];
      counter = 0;
      do {
        ne++;
        if (run->ursprung != i) {
          fprintf(stderr, "PROBLEM 2\n");
          exit(2);
        }
        if (run->prev->next != run) {
          fprintf(stderr, "PROBLEM 3\n");
          exit(3);
        }
        if (run->next->prev != run) {
          fprintf(stderr, "PROBLEM 4\n");
          exit(4);
        }
        if (run->invers->invers != run) {
          fprintf(stderr, "PROBLEM 5\n");
          exit(5);
        }
        if (run->invers->ursprung != run->name) {
          fprintf(stderr, "PROBLEM 6\n");
          exit(6);
        }
        counter++;
        // deze test wordt meer dan 1 keer gedaan -- maar efficientie is hier
        // niet belangrijk
        run2 = run;
        localface = ((LONGTYPE)0);
        localfacep = run->faceleft;
        for (search = 0; (search < em_faces); search++)
          if (localfacep == face_pointer[search]) search = em_faces + 10;
        if (search < em_faces + 10) {
          fprintf(stderr, "PROBLEM 7a\n");
          exit(7);
        }
        do {
          SETBIT(localface, run2->ursprung);
          if (run2->faceleft != localfacep) {
            fprintf(stderr, "PROBLEM 7\n");
            exit(7);
          }
          run2 = run2->invers->next;
        } while (run2 != run);
        if (localface != *(run->faceleft)) {
          fprintf(stderr, "PROBLEM 8\n");
          writeset("localface", localface);
          writeset("*(run->faceleft)", *(run->faceleft));
          exit(8);
        }
        run = run->next;
      } while (run != firstedge[i]);
      // if (counter != adj_embedded[i]) { fprintf(stderr,"PROBLEM 9\n");
      // exit(9); }
    }
  ne = ne / 2;

  // nu nog het aantal vlakken berekenen:

  for (i = 1; i <= maxtop; i++)
    if (firstedge[i] != NULL) {
      run = firstedge[i];
      do {
        run->dummy = 0;
        run = run->next;
      } while (run != firstedge[i]);
    }

  nf = 0;
  for (i = 1; i <= maxtop; i++)
    if (firstedge[i] != NULL) {
      run = firstedge[i];
      do {
        if (run->dummy == 0) {
          nf++;
          run2 = run;
          do {
            run2->dummy = 1;
            run2 = run2->invers->next;
          } while (run2 != run);
        }
        run = run->next;
      } while (run != firstedge[i]);
    }

  if (nv - ne + nf != 2 - (2 * genus)) {
    fprintf(stderr, "PROBLEM 10 -- %d %d (%d,%d,%d)\n", genus, nv - ne + nf, nv,
            ne, nf);
    exit(10);
  }
}

#endif

void schreibegraph(GRAPH g, ADJAZENZ adj) {
  int x, y, unten, oben, maxvalence;
  fprintf(stderr, "\n\n ");

  for (x = 1, maxvalence = 0; x <= g[0][0]; x++)
    if (adj[x] > maxvalence) maxvalence = adj[x];

  fprintf(stderr, "|%2d", g[0][0]);

  for (x = 1; (x <= g[0][0]) && (x <= 24); x++) fprintf(stderr, "|%2d", x);
  fprintf(stderr, "|\n");

  fprintf(stderr, " ");

  for (x = 0; (x <= g[0][0]) && (x <= 24); x++) fprintf(stderr, "|==");
  fprintf(stderr, "|\n");

  for (x = 0; x < maxvalence; x++) {
    fprintf(stderr, " |  ");
    for (y = 1; (y <= g[0][0]) && (y <= 24); y++) {
      if (x >= adj[y])
        fprintf(stderr, "|  ");
      else
        fprintf(stderr, "|%2d", g[y][x]);
    }
    fprintf(stderr, "|\n");
  }

  unten = 25;
  oben = 48;

  while (g[0][0] >= unten) {
    fprintf(stderr, "\n");

    fprintf(stderr, "    ");

    for (x = unten; (x <= g[0][0]) && (x <= oben); x++)
      fprintf(stderr, "|%2d", x);
    fprintf(stderr, "|\n");

    fprintf(stderr, "    ");

    for (x = unten; (x <= g[0][0]) && (x <= oben); x++) fprintf(stderr, "|==");
    fprintf(stderr, "|\n");

    for (y = 0; y < maxvalence; y++) {
      fprintf(stderr, "    ");
      for (x = unten; (x <= g[0][0]) && (x <= oben); x++) {
        if (y >= adj[x])
          fprintf(stderr, "|  ");
        else
          fprintf(stderr, "|%2d", g[x][y]);
      }
      fprintf(stderr, "|\n");
    }
    unten += 24;
    oben += 24;
  }
}

void einfugen(GRAPH graph, ADJAZENZ adj, int v, int w)
/* Fuegt die Kante (v,w) in den Graphen graph ein. Dabei wird aber davon */
/* ausgegangen, dass in adj die wirklich aktuellen werte fuer die */
/* Adjazenzen stehen. Die adjazenzen werden dann aktualisiert. */

{
  graph[v][adj[v]] = w;
  graph[w][adj[w]] = v;
  adj[v]++;
  adj[w]++;
}

/* A complete single-byte record has one order byte, n-1 row terminators
   and one byte per undirected edge. */
#define MULTICODE_CAPACITY (knoten + d_kanten / 2)

static void input_error(const char *message) {
  fprintf(stderr, "Multicode input: %s\n", message);
  exit(EXIT_FAILURE);
}

static int stream_byte(FILE *input) {
  int byte = getc(input);
  if (byte == EOF && ferror(input)) input_error("read error");
  return byte;
}

static int required_byte(FILE *input, const char *context) {
  int byte = stream_byte(input);
  if (byte == EOF) input_error(context);
  return byte;
}

/* A header begins with ">>m", which cannot begin a graph of order 62:
   the neighbor 'm' would be out of range. Preserve both lookahead bytes
   when the first '>' is the order of a graph. */
static int read_graph(FILE *input, unsigned char code[MULTICODE_CAPACITY],
                      GRAPH graph, ADJAZENZ adj) {
  int order, prefix[2], prefix_count = 0;
  for (;;) {
    order = stream_byte(input);
    if (order == EOF) return 0;
    if (order != '>') break;
    prefix[0] = required_byte(input, "incomplete header or order-62 graph");
    prefix[1] = required_byte(input, "incomplete header or order-62 graph");
    if (prefix[0] != '>' || prefix[1] != 'm') {
      prefix_count = 2;
      break;
    }
    while (required_byte(input, "incomplete header") != '<') {}
    if (required_byte(input, "incomplete header") != '<')
      input_error("expected closing << in header");
  }

  if (order == 0) input_error("only single-byte multicode is supported");
  if (order > knoten) input_error("vertex count exceeds this build's limit");

  int length = 1, edge_count = 0, prefix_pos = 0;
  code[0] = (unsigned char)order;
  for (int row = 1; row < order; row++) {
    LONGTYPE seen = 0;
    for (;;) {
      int v = prefix_pos < prefix_count ? prefix[prefix_pos++]
                                        : required_byte(input, "incomplete graph record");
      if (v != 0) {
        if (v <= row || v > order)
          input_error("neighbor must be above the row vertex and within the graph");
        if (IS_SET(seen, v)) input_error("duplicate neighbor in a row");
        SETBIT(seen, v);
        if (++edge_count > d_kanten / 2) input_error("edge count exceeds this build's limit");
      }
      code[length++] = (unsigned char)v;
      if (v == 0) break;
    }
  }

  /* Unique, strictly upper-triangle incidences give degree <= order-1
     at both endpoints. Only now populate the solver's adjacency arrays. */
  globalnv = graph[0][0] = order;
  globalne = edge_count;
  memset(adj, 0, sizeof(ADJAZENZ));
  int row = 1;
  for (int i = 1; i < length; i++) {
    if (code[i] == 0)
      row++;
    else
      einfugen(graph, adj, row, code[i]);
  }
  return length;
}

/****************************add_edge***************************/

void add_edge_face(KANTE *right1, KANTE *right2, KANTE *e1)
// adds an edge between right1->ursprung and right2->ursprung
// the edge is added in the rotational order left (previous) of the two
// given edges
// This function is only called when it has been tested before that it is inside
// a face
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
      right1->faceleft;  // the others in this face are already OK
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

/****************************add_edge***************************/

KANTE *add_edge(KANTE *right1, KANTE *right2, KANTE *e1, int *genus,
                int max_genus)
// adds an edge between right1->ursprung and right2->ursprung
// the edge is added in the rotational order left (previous) of the two
// given edges
{
  LONGTYPE *face, *newface;
  int search, k;
  KANTE *run, *e2;

  if (((*genus) == max_genus) && (right1->faceleft != right2->faceleft))
    return NULL;
  // here the pointers are compared, not the sets of vertices

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

  if (right1->faceleft == right2->faceleft)  // here the pointers are compared
                                             // one face becomes two
  {
    face = e2->faceleft =
        right1->faceleft;  // the others in this face are already OK
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
  } else  // two faces become one
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

/****************************add_new***************************/

KANTE *add_new(KANTE *right, KANTE *e1)
// adds an edge to a new vertex "e1->name" -- that is: a vertex which is not yet
// embedded the edge is added left of the edge "right"
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
// Greedily constructs a tree with a root of degree 3 and all other vertices
// degree 1 or 2. This fixes the orientation of the embedding. If no vertex with
// degree at least 3 exists, the graph is a cycle or a path and this cycle or
// path is constructed. returns the number of embedded eges
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

  if (starttop == 0)  // cycle or path
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

  if (path && (adj[y] == 1))  // the graph with just one edge
    return 2;

  if (path || cycle) {
    // now first build a long path: always from vertex x and edge e2
    for (doorgaan = 1; doorgaan;) {
      for (i = 0; (i < adj[x]) && adj_embedded[graph[x][i]]; i++) {
      };
      // zoek eerste nog niet ingebedde buur
      if (i >= adj[x])
        doorgaan = 0;
      else  // boog x->graph[x][i] inbedden
      {
        e1 = e2;
        new1 = edges + em_edges;
        em_edges++;
        new2 = edges + em_edges;
        em_edges++;
        y = x;
        x = graph[y][i];  // x is now the new end
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
    // else

    // now x has degree 1 in the embedded graph and one can add one more
    // edge to form a cycle. x is already connected with y

    if (graph[x][0] == y)
      i = 1;
    else
      i = 0;
    // there are no degree 1 vertices -- all degree 2

    new1 = edges + em_edges;
    em_edges++;
    new2 = edges + em_edges;
    em_edges++;
    y = graph[x][i];  // y is now the end
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
  }  // end path or cycle

  // otherwise embed 2 more edges of starttop in arbitrary order to fix an
  // orientation

  new1 = edges + em_edges;
  em_edges++;
  new2 = edges + em_edges;
  em_edges++;
  y = graph[x][1];  // y is now the end
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
  y = graph[x][2];  // y is now the end
  new1->invers = new2;
  new2->invers = new1;
  new1->ursprung = x;
  new1->name = y;
  new2->ursprung = y;
  new2->name = x;
  adj_embedded[x]++;
  adj_embedded[y]++;
  add_new(firstedge[x]->next, new1);

  // now enlarge the three edges to paths

  for (j = 0, fedge = firstedge[starttop]; j < 3; j++) {
    x = fedge->name;
    e2 = fedge->invers;
    for (doorgaan = 1; doorgaan;) {
      for (i = 0; (i < adj[x]) && adj_embedded[graph[x][i]]; i++) {
      };
      // zoek eerste nog niet ingebedde buur
      if (i >= adj[x])
        doorgaan = 0;
      else  // boog x->graph[x][i] inbedden
      {
        e1 = e2;
        new1 = edges + em_edges;
        em_edges++;
        new2 = edges + em_edges;
        em_edges++;
        y = x;
        x = graph[y][i];  // x is now the new end
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

#ifdef TEST
  testmap(graph[0][0], *genus);
#endif
  // writemap(graph[0][0]);
  return em_edges;
}

void remove_e(GRAPH g, ADJAZENZ adj, int v, int w)
// remove edge {v,w}
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
/*************************preprocess****************/

void preprocess(GRAPH old, ADJAZENZ a_old, GRAPH new, ADJAZENZ a_new)
// Recursively removes all vertices with degree 1 or 2.
// old isn't modified -- the modified graph is in new
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
      if (a_new[v2] > 1)  // don't remove the last edge
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
    } else if (a_new[v1] == 2)  // test necessary -- can be 0 in the last step
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
    }  // end if (a_new[v1]==2)
  }  // end for
}

/************************remove_edge*****************/

void remove_edge(KANTE *edge, int *genus) {
  int end, search, k;
  KANTE *invedge, *run, *endedge;
  LONGTYPE *face;

  k = (int)(edge - edges);

  // if (adj_embedded[edge->ursprung]==1) { edge=edge->invers; }
  // by construction never the case

  end = edge->name;
  invedge = edge->invers;
  edge->is_embedded = invedge->is_embedded = 0;

  if (invedge->next ==
      invedge)  // degree 1 -- startvertex will be deleted after removal
  {
    // adj_embedded[end]=0;
    firstedge[end] = NULL;
    // adj_embedded[top]--;
    DELBIT(*(edge->faceleft), end);
    edge->prev->next = edge->next;
    edge->next->prev = edge->prev;
    em_vertices--;
  } else {
    if (edge->faceleft ==
        invedge->faceleft)  // 1 vlak wordt 2 vlakken -- het genus daalt
    {
      edge->prev->next = edge->next;
      edge->next->prev = edge->prev;
      invedge->prev->next = invedge->next;
      invedge->next->prev = invedge->prev;
      // in dit vlak houden we de oude variabele
      *(edge->next->faceleft) = rememberfaces[k];

      run = endedge =
          invedge->next;  // in dit vlak gebruiken wij een nieuwe vlak-variabele
      face = face_pointer[em_faces];
      *face = rememberfaces[k + 1];
      em_faces++;
      do {
        run->faceleft = face;
        run = run->invers->next;
      } while (run != endedge);

      (*genus)--;
    } else  // 2 vlakken worden 1 vlak  -- het genus blijft
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

void add_new_vertex(int new, int old, int numberop) {
  KANTE *e1, *e2;
  // ->inverse already fixed

  e1 = firstedge[new] = red_edges + (numberop * 4);
  e2 = e1 + 1;

  e1->ursprung = e2->name = new;
  e2->ursprung = e1->name = old;

  e1->next = e1->prev = e1;
  e2->prev = firstedge[old];
  e2->next = firstedge[old]->next;
  e2->prev->next = e2->next->prev = e2;

  return;
}

void remove_new_vertex(int new) {
  KANTE *e1;

  e1 = firstedge[new]->invers;
  firstedge[new] = NULL;

  e1->next->prev = e1->prev;
  e1->prev->next = e1->next;

  return;
}

void subdivide(int new, int old1, int old2, int numberop) {
  KANTE *e1, *e2;
  KANTE *run;
  // ->inverse already fixed

  e1 = firstedge[new] = red_edges + (numberop * 4);
  e2 = e1 + 1;

  for (run = firstedge[old1]; run->name != old2; run = run->next);

  run->name = run->invers->ursprung = new;
  e1->ursprung = e2->name = new;
  e1->name = e2->ursprung = old2;

  run = run->invers;
  if (firstedge[old2] == run) firstedge[old2] = e2;
  if (run->next != run) {
    e2->prev = run->prev;
    e2->next = run->next;
    e2->prev->next = e2->next->prev = e2;
  } else {
    e2->prev = e2->next = e2;
  }  // just one edge
  run->next = run->prev = e1;
  e1->next = e1->prev = run;

  return;
}

void unsubdivide(int new, int old1, int old2) {
  KANTE *e1, *e2;
  // the edges to old1 are the original ones

  e1 = firstedge[new];
  firstedge[new] = NULL;
  if ((e1->name) == old1) {
    e2 = e1->next;
  } else {
    e2 = e1;
    e1 = e2->next;
  }

  e1 = e1->invers;  // old edge start at old1
  e2 = e2->invers;  // new edge

  if (firstedge[old2] == e2) firstedge[old2] = e1->invers;

  e1->name = e1->invers->ursprung = old2;
  e1 = e1->invers;

  if (e2->next == e2) {
    e1->prev = e1->next = e1;
  } else {
    e1->prev = e2->prev;
    e1->next = e2->next;
    e1->prev->next = e1->next->prev = e1;
  }

  return;
}

void add_parallel(int new, int old1, int old2, int numberop)
// adds a path of length 2 with central new vertex new directly next to the edge
// {old1,old2}
{
  KANTE *e1, *e2, *e3, *e4;
  KANTE *run;
  // ->inverse already fixed

  e1 = firstedge[new] = red_edges + (numberop * 4);
  e2 = e1 + 1;
  e3 = e2 + 1;
  e4 = e3 + 1;

  for (run = firstedge[old1]; run->name != old2; run = run->next);

  e1->ursprung = e2->name = e3->ursprung = e4->name = new;
  e1->name = e2->ursprung = old1;
  e3->name = e4->ursprung = old2;

  // add in clockwise direction of run

  e2->prev = run;
  e2->next = run->next;
  e2->prev->next = e2->next->prev = e2;

  e1->next = e1->prev = e3;
  e3->next = e3->prev = e1;

  // add in counterclockwise direction of run->invers
  run = run->invers;
  e4->next = run;
  e4->prev = run->prev;
  e4->prev->next = e4->next->prev = e4;

  return;
}

void remove_parallel(int new)
// removes a path of length 2 with central new vertex new directly next to the
// edge {old1,old2}
{
  KANTE *e1, *e2;
  // ->inverse already fixed

  e1 = firstedge[new];
  e2 = e1->next->invers;
  e1 = e1->invers;
  firstedge[new] = NULL;

  e1->next->prev = e1->prev;
  e1->prev->next = e1->next;

  e2->next->prev = e2->prev;
  e2->prev->next = e2->next;

  return;
}

/**************************************CODE*********************************/
void code()
// writes the map on stdout in case all vertices 1...globalnv are present
{
  int i;
  KANTE *run, *end;

  // Reconstruct the original map for output, then restore the search state.
  for (i = number_reconstruct; i;) {
    i--;
    if (reconstruct[i][0] == 0)
      add_new_vertex(reconstruct[i][1], reconstruct[i][2], i);
    else if (reconstruct[i][0] == 1)
      subdivide(reconstruct[i][1], reconstruct[i][2], reconstruct[i][3], i);
    else if (reconstruct[i][0] == 2)
      add_parallel(reconstruct[i][1], reconstruct[i][2], reconstruct[i][3], i);
    else {
      fprintf(stderr, "Serious problem in coding... Exit(2).\n");
      exit(2);
    }
  }

  // for (i=1; i<=globalnv;i++)
  //   if (firstedge[i]==NULL) { fprintf(stderr,"gap in vertex numbers --
  //   exit.\n"); exit(1); }

  putchar(globalnv);
  if (do_bfs) {
    for (i = 1; i <= globalnv; i++) {
      run = end = firstedge[bfsnummer[i]];
      do {
        putchar(invbfsnummer[run->name]);
        run = run->next;
      } while (run != end);
      putchar(0);
    }
  } else {
    for (i = 1; i <= globalnv; i++) {
      run = end = firstedge[i];
      do {
        putchar(run->name);
        run = run->next;
      } while (run != end);
      putchar(0);
    }
  }
  // en opkuisen

  for (i = 0; i < number_reconstruct; i++) {
    if (reconstruct[i][0] == 0)
      remove_new_vertex(reconstruct[i][1]);
    else if (reconstruct[i][0] == 1)
      unsubdivide(reconstruct[i][1], reconstruct[i][2], reconstruct[i][3]);
    else if (reconstruct[i][0] == 2)
      remove_parallel(reconstruct[i][1]);
    else {
      fprintf(stderr, "Serious problem in coding... Exit(2).\n");
      exit(2);
    }
  }

  written++;
}

/*************************make_edgelist*****************/
void make_edgelist(GRAPH graph, ADJAZENZ adj, KANTE edgelist[],
                   LONGTYPE bit_edgelist[], int *ell) {
  // in increasing order of product of already embedded end-degrees
  // -- well ... with some restrictions

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
  // edgelimit gives the distance to the leaves so that only cheap tests are
  // done as ell is two times the number of edges, this is half the depth that
  // expensive test are done

#define ways(x) ((x) == 0 ? 1 : ((x) << 7))
  // this way edges to a new vertex have always priority. The product will be
  // smaller than INT_MAX for |V|<=128 The recursion uses that first a spanning
  // tree is built

  // can be done smarter and faster, but it is not crucial -- check profiler
  *ell = 0;
  while (lell) {
    best = bestdist = INT_MAX;
    // besti need not be initialized
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

    if (local_adj_embedded[localedgelist[besti][0]])  // the first vertex must
                                                      // always already be
                                                      // embedded
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
                   LONGTYPE lastsub2, int depth)
// here we know that genus=max_genus
// here we always have a spanning tree and an edge forming a cycle
// In the first call the last edge lies on a cycle in the plane
// lastsub1 and lastsub2 are always the two parts of the last face split --
// without the common vertices
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
    atomic_store(&multi_parallel_stop, 1);
    if (multi_should_write_code(genus)) code();
    return;
  }

  if (!multi_parallel_take_node(depth)) return;

  ell2 = ell - 2;
  edgelist2 = edgelist + 2;
  bit_edgelist2 = bit_edgelist + 2;

  /* When maxgenus is reached we only check for edges that cannot be embedded:
   */

  if (last->faceleft == last->invers->faceleft)
    i = MIN0(last - edgelist + 2);
  else
    i = 0;
  // if the genus has just been increased, there is no forced genus increasing
  // edge earlier
  for (; i < ell; i += 2)
    if ((bit_edgelist[i] & lastsub1) && (bit_edgelist[i] & lastsub2) &&
        (!((edgelist + i)->is_embedded)))
    // only test edges that could be affected by the last edge inserted
    {
      {
        found2 = 0;  // so far no face where it can be embedded
        for (j = 0; j < em_faces; j++) {
          if (ATLEAST2BIT(bit_edgelist[i] & (*(face_pointer[j])))) {
            found2 = 1;
            j = em_faces;
          }
        }
        if (!found2) return;
      }
    }

  // an edge between two already embedded vertices is added in a common face
  // we already know that there is at least one such face

  run = end = firstedge[edgelist->ursprung];
  do {
    run2 = end2 = firstedge[edgelist->name];
    do {
      if (run2->faceleft == run->faceleft) {
        add_edge_face(run, run2, edgelist);
#ifdef TEST
        testmap(knotenzahl, genus);
#endif
        rec_genus_max(
            edgelist2, bit_edgelist2, ell2, genus, found, edgelist,
            (*(edgelist->faceleft)) & (~(*(edgelist->invers->faceleft))),
            (*(edgelist->invers->faceleft) & (~(*(edgelist->faceleft)))),
            depth + 1);
        remove_edge(edgelist, &genus);
      }
#ifdef TEST
      testmap(knotenzahl, genus);
#endif
      run2 = run2->next;
    } while ((run2 != end2) && ((!(*found)) || all));
    run = run->next;
  } while ((run != end) && ((!(*found)) || all));

#ifdef TEST
  testmap(knotenzahl, genus);
#endif
}

void rec_genus(KANTE edgelist[], LONGTYPE bit_edgelist[], int ell, int genus,
               int max_genus, int *found, KANTE *last, LONGTYPE lastsub1,
               LONGTYPE lastsub2, int depth)
// here we always have a spanning tree and an edge forming a cycle
// In the first call the last edge lies on a cycle in the plane
// lastsub1 and lastsub2 are always the two parts of the last face split --
// without the common vertices
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
      atomic_store(&multi_parallel_stop, 1);
      if (multi_should_write_code(genus)) code();
    }
    return;
  }

  if (!multi_parallel_take_node(depth)) return;

  ell2 = ell - 2;
  edgelist2 = edgelist + 2;
  bit_edgelist2 = bit_edgelist + 2;

  // the default is to insert the edge "*edgelist" in this iteration and
  // "*edgelist+2" in the next one, but it is possible that another -- later --
  // edge is found more suitable. In that case this later edge is inserted first
  // and "*edgelist" is again tried in the next iteration. The variables with an
  // extra 2 at the end -- edgelist2, bit_edgelist2 -- are always the ones that
  // contain the values for the next iteration. At this moment they contain the
  // default: next in the list

  /* now we check whether we should first insert another edge -- if yes,
     the pointer "edgelist" is updated to this new edge and edgelist2 to the old
     edgelist to try it in the next iteration. */

  if (ell < edgelimit)  // that is: "close" to the leaves
  {
    if (last->faceleft == last->invers->faceleft)
      i = MIN0(last - edgelist + 2);
    else
      i = 0;
    // if the genus has just been increased, there is no forced genus increasing
    // edge earlier
    for (; i < ell; i += 2)
      if ((bit_edgelist[i] & lastsub1) && (bit_edgelist[i] & lastsub2) &&
          (!((edgelist + i)->is_embedded)))
      // only test edges that could be affected by the last edge inserted
      {
        {
          found2 = 0;  // so far no face where it can be embedded
          for (j = 0; j < em_faces; j++) {
            if (ATLEAST2BIT(bit_edgelist[i] & (*(face_pointer[j])))) {
              found2 = 1;
              j = em_faces;
            }
          }
          if (!found2) {
            if (genus == max_genus) return;
            // first choose this edge to add and increase the genus
            ell2 = ell;
            edgelist2 = edgelist;
            bit_edgelist2 =
                bit_edgelist;  // try the first edge in the next iteration
            edgelist = edgelist + i;
            i = ell;
          }
        }
      }
  } else {  // ell >= edgelimit -- that is: close to the root -- search for
            // minimum number of embeddable faces
    // without increasing the genus
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
          found2 = 0;  // so far no face where it can be embedded
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
              // first choose this edge to add and increase the genus
              ell2 = ell;
              edgelist2 = edgelist;
              bit_edgelist2 =
                  bit_edgelist;  // try the first edge in the next iteration
              edgelist = edgelist + i;
              changed = 1;
            } else
              edgelist = old_edgelist + i;
          }
        }  // end for over ell
    }
  }  // end ell>=edgelimit

  // now it is decided which edge must be inserted and edgelist points to it

  // an edge between two already embedded vertices is added

  old_genus = genus;

  run = end = firstedge[edgelist->ursprung];
  do {
    run2 = end2 = firstedge[edgelist->name];
    do {
      if (add_edge(run, run2, edgelist, &genus, max_genus) != NULL) {
#ifdef TEST
        testmap(knotenzahl, genus);
#endif
        if (old_genus != genus) {
          if (genus < max_genus)
            rec_genus(edgelist2, bit_edgelist2, ell2, genus, max_genus, found,
                      edgelist, lastsub1, lastsub2, depth + 1);
          else
            rec_genus_max(edgelist2, bit_edgelist2, ell2, genus, found,
                          edgelist, lastsub1, lastsub2, depth + 1);
        } else  // genus not increased, so there is no edge always increasing
                // the genus and we do not yet have max_genus
        {
          rec_genus(
              edgelist2, bit_edgelist2, ell2, genus, max_genus, found, edgelist,
              (*(edgelist->faceleft)) & (~(*(edgelist->invers->faceleft))),
              (*(edgelist->invers->faceleft) & (~(*(edgelist->faceleft)))),
              depth + 1);
        }
        remove_edge(edgelist, &genus);
      }
#ifdef TEST
      testmap(knotenzahl, genus);
#endif
      run2 = run2->next;
    } while ((run2 != end2) && ((!(*found)) || all));
    run = run->next;
  } while ((run != end) && ((!(*found)) || all));

#ifdef TEST
  testmap(knotenzahl, genus);
#endif
}

void pre_rec_genus(KANTE edgelist[], LONGTYPE bit_edgelist[], int ell,
                   int genus, int max_genus, int *found, KANTE *last,
                   int depth)
// in this function the embedded graph is completed to a spanning tree
// and the first cycle is formed
{
  KANTE *run, *end, *run2, *end2;

  if (ell == 0) {
    if (max_genus == genus) {
      *found = 1;
      atomic_store(&multi_parallel_stop, 1);
      if (multi_should_write_code(genus)) code();
    }
    return;
  }

  if (!multi_parallel_take_node(depth)) return;

  // if (firstedge[edgelist->name]!=NULL)
  //  { rec_genus(edgelist, bit_edgelist, ell, genus, max_genus, found, last);
  //    return;
  //   }

  if (firstedge[edgelist->name] == NULL) {
    run = end = firstedge[edgelist->ursprung];
    do {
      add_new(run, edgelist);
#ifdef TEST
      testmap(knotenzahl, genus);
#endif
      pre_rec_genus(edgelist + 2, bit_edgelist + 2, ell - 2, genus, max_genus,
                    found, edgelist, depth + 1);
      remove_edge(edgelist, &genus);
#ifdef TEST
      testmap(knotenzahl, genus);
#endif
      run = run->next;
    } while ((run != end) && ((!(*found)) || all));
  } else  // the first cycle will be formed
  {
    run = end = firstedge[edgelist->ursprung];
    do {
      run2 = end2 = firstedge[edgelist->name];
      do {
        if (add_edge(run, run2, edgelist, &genus, max_genus) != NULL) {
#ifdef TEST
          testmap(knotenzahl, genus);
#endif
          if (max_genus > 0)
            rec_genus(
                edgelist + 2, bit_edgelist + 2, ell - 2, genus, max_genus,
                found, edgelist,
                (*(edgelist->faceleft)) & (~(*(edgelist->invers->faceleft))),
                (*(edgelist->invers->faceleft) & (~(*(edgelist->faceleft)))),
                depth + 1);
          else  // max_genus=0
            rec_genus_max(
                edgelist + 2, bit_edgelist + 2, ell - 2, genus, found, edgelist,
                (*(edgelist->faceleft)) & (~(*(edgelist->invers->faceleft))),
                (*(edgelist->invers->faceleft) & (~(*(edgelist->faceleft)))),
                depth + 1);
          remove_edge(edgelist, &genus);
        }
#ifdef TEST
        testmap(knotenzahl, genus);
#endif
        run2 = run2->next;
      } while ((run2 != end2) && ((!(*found)) || all));
      run = run->next;
    } while ((run != end) && ((!(*found)) || all));
  }

  return;
}

/****************getshortestdpath**************************/

int getshortestdpath(GRAPH graph, ADJAZENZ adj, int start, int ziel)
// computes the length of the shortest directed cyclic walk
// through the edge {start,ziel}
// where an edge is followed by its inverse if and only if the walk
// passes a vertex of degree 1.

{
  int list[d_kanten], previous[d_kanten], length[d_kanten], run, ll;
  int top, new, i;

  if ((adj[start] == 1) && (adj[ziel] == 1)) return 2;

  RESET_EDGEMARKS;

  // BFS

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
        }  // end new != previous[run]
      }  // end for
    }
    run++;
  }  // end while (1)
  return 0;  // just for the compiler -- the routine will always return from
             // inside the while loop
}

#ifdef TEST
int dfs_verder(GRAPH graph, ADJAZENZ adj, int start, int end, int previous,
               int top, int restlengte) {
  int i;

  if (restlengte == 0) {
    if ((top == start) && ((adj[start] == 1) || (previous != end)))
      return 1;
    else
      return 0;
  }

  for (i = 0; i < adj[top]; i++)
    if ((adj[top] == 1) || (graph[top][i] != previous)) {
      if (dfs_verder(graph, adj, start, end, top, graph[top][i],
                     restlengte - 1))
        return 1;
    }

  return 0;
}

int dfs_found(GRAPH graph, ADJAZENZ adj, int start, int end, int restlengte) {
  int i;

  for (i = 0; i < adj[end]; i++)
    if ((adj[end] == 1) || (graph[end][i] != start)) {
      if (dfs_verder(graph, adj, start, end, end, graph[end][i],
                     restlengte - 1))
        return 1;
    }

  return 0;
}

void stupidtestfractions(GRAPH graph, ADJAZENZ adj) {
  int i, j, end, run, limit;

  for (i = 1; i <= graph[0][0]; i++)
    for (j = 0; j < adj[i]; j++) {
      end = graph[i][j];
      limit = shortpatharray[i][end];
      for (run = 2; run < limit; run++)
        if (dfs_found(graph, adj, i, end, run - 1)) {
          fprintf(stderr, "Problem 1 with shortpatharray. Exit.\n");
          exit(13);
        }
      if (!dfs_found(graph, adj, i, end, limit - 1)) {
        fprintf(stderr,
                "Problem 2 with shortpatharray. %d->%d limit %d Exit.\n", i,
                end, limit);
        exit(13);
      }
    }
}
#endif

/****************compute_fractions**************************/

/* Round each reciprocal upward. At most d_kanten terms are accumulated.
   The scale is divisible by common small face lengths. */
#define FACE_SCALE 3603600000000LL

static long long face_weight(int length) {
  return (FACE_SCALE + length - 1) / length;
}

static long long scaled_face_bound(GRAPH graph, ADJAZENZ adj)
// computes an upper bound for the number of faces via fractions 1/k for edges
// which require a face of length at least k
{
  int knotenzahl, i, j, k, start, end, buffer;
  long long facebound1, facebound2;
  int lengtharray[d_kanten], sizes[d_kanten + 1], max, ll;
  int sizes_aroundvertex[knoten + 1][d_kanten + 1], max_a[knoten + 1];

  knotenzahl = graph[0][0];
  for (i = 1; i <= knotenzahl; i++) {
    max_a[i] = 1;
  }
  max = 1;

  for (start = 1; start < knotenzahl; start++)
    for (j = 0; j < adj[start]; j++)
      if ((end = graph[start][j]) > start) {
        buffer = getshortestdpath(graph, adj, start, end);
#ifdef TEST
        shortpatharray[start][end] = shortpatharray[end][start] = buffer;
#endif
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

  // At least max darts lie in a face of length >= max. Raising the
  // largest entries gives the most conservative assignment.

  for (j = 1; j <= max; j++) lengtharray[ll - j] = max;

  for (j = 0, facebound1 = 0; j < ll; j++)
    facebound1 += face_weight(lengtharray[j]);

  // Now a criterion using the angles around the vertices:
  // Assume that not all edges at a vertex k have the same bound for the face
  // length. If there are k undirected edges at v so that both directed edges
  // lie in a face of size max_a[v], then at least k+1 angles belong to faces of
  // size at least max_a[v] On the other hand: If there are k undirected edges
  // at v so that both directed edges lie in a face with minimal (for v) lower
  // bound, then at most k-1 angles can have this lower bound. We get a valid
  // series of bounds for the angle if we replace one minimal lower bound with a
  // maximal lower bound -- see proof paper!

  facebound2 = 0;
  for (start = 1; start <= knotenzahl; start++)
    if (adj[start]) {
      for (j = 2; sizes_aroundvertex[start][j] == 0; j++) {}
      if (j == max_a[start])
        facebound2 += sizes_aroundvertex[start][j] * face_weight(j);
      else {
        facebound2 += (sizes_aroundvertex[start][j] - 1) * face_weight(j);
        for (j++; j < max_a[start]; j++)
          facebound2 += sizes_aroundvertex[start][j] * face_weight(j);
        facebound2 += (sizes_aroundvertex[start][j] + 1) * face_weight(j);
      }
    }

#ifdef TEST
  stupidtestfractions(graph, adj);
#endif

  if (facebound2 > facebound1)
    return facebound1;
  else
    return facebound2;
}

/*************************get_genus*****************/

void multi_search_bound(GRAPH graph, ADJAZENZ adj, int max_genus, int *found,
                        int split_depth) {
  int genus, ell;
  LONGTYPE bit_edgelist[d_kanten];
  KANTE *edgelist;

  multi_split_depth = split_depth;
  multi_split_counter = multi_worker_id;
  knotenzahl = graph[0][0];
  edgelist = edges + get_initial_embedding(graph, adj, &genus);
  make_edgelist(graph, adj, edgelist, bit_edgelist, &ell);
  pre_rec_genus(edgelist, bit_edgelist, ell, genus, max_genus, found,
                edgelist - 2, 0);
}

unsigned long long multi_count_bound_split_nodes(GRAPH graph, ADJAZENZ adj,
                                                 int max_genus,
                                                 int split_depth,
                                                 unsigned long long limit) {
  int found = 0;
  multi_worker_id = 0;
  multi_worker_count = 1;
  multi_count_split_nodes = 1;
  multi_split_node_count = 0;
  multi_split_node_limit = limit;
  atomic_store(&multi_parallel_stop, 0);
  multi_search_bound(graph, adj, max_genus, &found, split_depth);
  multi_count_split_nodes = 0;
  multi_split_node_limit = 0;
  atomic_store(&multi_parallel_stop, 0);
  return multi_split_node_count;
}

int multi_choose_split_depth(GRAPH graph, ADJAZENZ adj, int max_genus, int ell,
                             int threads) {
  int depth, max_depth, best_depth = 1;
  unsigned long long count, best_count = 0;
  unsigned long long target = 1000ULL;
  int override = multi_split_depth_override();
  if (override > 0) return override;
  if ((unsigned long long)threads * 128ULL > target)
    target = (unsigned long long)threads * 128ULL;
  max_depth = ell / 2;
  if (max_depth < 1) max_depth = 1;
  if (max_depth > 24) max_depth = 24;
  for (depth = 1; depth <= max_depth; depth++) {
    count = multi_count_bound_split_nodes(graph, adj, max_genus, depth, target);
    if (count > best_count) {
      best_count = count;
      best_depth = depth;
    }
    if (count >= target) return depth;
  }
  if (best_count < (unsigned long long)threads * 4ULL) return -1;
  return best_depth;
}

MULTI_THREAD_RETURN multi_bound_worker(void *arg) {
  MULTI_WORKER *worker = (MULTI_WORKER *)arg;
  int found = 0;
  multi_worker_id = worker->worker_id;
  multi_worker_count = worker->worker_count;
  multi_search_bound(worker->graph, worker->adj, worker->max_genus, &found,
                     worker->split_depth);
  worker->found = found;
  if (found) atomic_store(&multi_parallel_stop, 1);
  return MULTI_THREAD_RESULT;
}

int multi_search_bound_parallel(GRAPH graph, ADJAZENZ adj, int max_genus,
                                int ell, int threads) {
  int i, found = 0;
  int split_depth = multi_choose_split_depth(graph, adj, max_genus, ell, threads);
  MULTI_WORKER *workers;
  multi_thread_t *thread_handles;

  if (split_depth < 0) {
    multi_worker_id = 0;
    multi_worker_count = 1;
    multi_search_bound(graph, adj, max_genus, &found, -1);
    return found;
  }

  workers = (MULTI_WORKER *)calloc((size_t)threads, sizeof(MULTI_WORKER));
  thread_handles =
      (multi_thread_t *)calloc((size_t)threads, sizeof(multi_thread_t));
  if ((workers == NULL) || (thread_handles == NULL)) {
    fprintf(stderr, "Error allocating worker threads.\n");
    exit(1);
  }

  atomic_store(&multi_parallel_stop, 0);
  atomic_store(&multi_output_claimed, 0);
  for (i = 0; i < threads; i++) {
    memcpy(workers[i].graph, graph, sizeof(GRAPH));
    memcpy(workers[i].adj, adj, sizeof(ADJAZENZ));
    workers[i].max_genus = max_genus;
    workers[i].worker_id = i;
    workers[i].worker_count = threads;
    workers[i].split_depth = split_depth;
    workers[i].found = 0;
    if (multi_thread_create(thread_handles + i, multi_bound_worker,
                            workers + i) != 0) {
      fprintf(stderr, "Error creating worker thread.\n");
      exit(1);
    }
  }
  for (i = 0; i < threads; i++) {
    if (multi_thread_join(thread_handles[i]) != 0) {
      fprintf(stderr, "Error joining worker thread.\n");
      exit(1);
    }
    if (workers[i].found) found = 1;
  }
  free(thread_handles);
  free(workers);
  return found;
}

int get_genus(GRAPH graph, ADJAZENZ adj) {
  int i, genus;   // genus: genus van de gedeeltelijk ingebedde graaf
  int max_genus;  // max_genus: altijd bovengrens voor genus -- op het einde:
                  // genus
  int do_reduce2, parallel_threads, use_parallel;
  GRAPH newgraph;
  GRAPH parallel_graph;
  ADJAZENZ newadj;
  ADJAZENZ parallel_adj;
  int ell, found, min_genus, restvertices, restedges;
  LONGTYPE bit_edgelist[d_kanten];
  KANTE *edgelist;

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
    // fprintf(stderr,"before %d restvertices %d\n",graph[0][0],
    // graph[0][0]-number_reconstruct);

    restvertices =
        graph[0][0] - number_reconstruct;  // the number of remaining vertices

    if (restvertices == 2)  // reduced to a single edge, so the graph is plane
    {
      if ((write_embedding) || (filter == 0) || (filter2 == 0)) {
        get_initial_embedding(newgraph, newadj, &genus);
        code();
      }
      return 0;
    }
    for (i = 1, restedges = 0; i <= knotenzahl; i++) restedges += newadj[i];
    restedges = restedges / 2;
    edgelist = edges + get_initial_embedding(newgraph, newadj, &genus);
    make_edgelist(newgraph, newadj, edgelist, bit_edgelist, &ell);
    memcpy(parallel_graph, newgraph, sizeof(GRAPH));
    memcpy(parallel_adj, newadj, sizeof(ADJAZENZ));
  } else {
    restvertices = globalnv;
    restedges = globalne;
    edgelist = edges + get_initial_embedding(graph, adj, &genus);
    // now make a list of edges that must still be embedded
    make_edgelist(graph, adj, edgelist, bit_edgelist, &ell);
    memcpy(parallel_graph, graph, sizeof(GRAPH));
    memcpy(parallel_adj, adj, sizeof(ADJAZENZ));
  }

  // Even a one-face embedding has genus at most half the cycle rank.
  if (filter > (restedges - restvertices + 1) / 2) return -1;
  // Triangular faces give g >= ceil((E - 3V + 6) / 6).
  min_genus = MIN0((restedges - 3 * restvertices + 6 + 5) / 6);

  if ((filter2 >= 0) && (min_genus > filter2)) return -1;
  if ((filterl >= 0) && (min_genus > filterl)) return -1;
  if ((filter >= 0) && (min_genus > filter)) return -1;

  if (compute_lower_bound) {
    long long bound = do_reduce2 ? scaled_face_bound(newgraph, newadj)
                                 : scaled_face_bound(graph, adj);
    // F is integral, so F <= floor(bound / FACE_SCALE).
    int max_faces = (int)(bound / FACE_SCALE);
    int lower = (3 + restedges - restvertices - max_faces) / 2;
    if (lower > min_genus) min_genus = lower;
  }

  parallel_threads = multi_thread_count();
  use_parallel = (parallel_threads > 1) && !all && (filter < 0) &&
                 (filter2 < 0) && !filterlarge;

  if (filter >= 0) {
    found = 0;
    if (min_genus > filter) return -1;
    pre_rec_genus(edgelist, bit_edgelist, ell, genus, filter, &found,
                  edgelist - 2, 0);
    if (found)
      return filter;
    else
      return -1;
  }

  // else

  for (found = 0, max_genus = min_genus; !found; max_genus++) {
    if ((filter2 >= 0) && (max_genus > filter2)) return -1;
    if ((filterl >= 0) && (max_genus > filterl)) return -1;
    if (use_parallel) {
      found = multi_search_bound_parallel(parallel_graph, parallel_adj,
                                          max_genus, ell, parallel_threads);
    } else {
      multi_worker_count = 1;
      multi_split_depth = -1;
      pre_rec_genus(edgelist, bit_edgelist, ell, genus, max_genus, &found,
                    edgelist - 2, 0);
    }
  }

  if (max_genus - 1 == min_genus) good_approx[min_genus]++;

  return max_genus - 1;
}

static void usage(const char *name, int status) {
  fprintf(stderr,
          "Input: simple connected graphs in single-byte multicode (up to "
          "%d vertices and %d edges).\n", knoten, d_kanten / 2);
  fprintf(stderr,
          "Usage: \t %s [lx] [nb] [w] [wa] [fx] [fmx] [fax] [F] [o] [L]\n",
          name);
  fprintf(stderr, "\t x is a decimal integer from 0 to %d (e.g. l2).\n", INT_MAX);
  fprintf(stderr,
          "lx: \t use x as an upper limit for the genus -- don't compute a "
          "genus larger than x.\n");
  fprintf(stderr,
          "nb: \t Do not compute a nontrivial lower bound for any graph\n");
  fprintf(stderr,
          " \t  -- just use the trivial bound assuming that all faces are "
          "triangles.\n");
  fprintf(stderr, "w: \t write a minimum genus embedding.\n");
  fprintf(stderr, "wa: \t write all minimum genus embeddings.\n");
  fprintf(stderr, "fx: \t write an embedding of genus x.\n");
  fprintf(stderr,
          "fmx: \t write an embedding of genus x if x is the minimum genus for "
          "the graph.\n");
  fprintf(stderr, "fax: \t write all embeddings of genus x.\n");
  fprintf(stderr,
          "F: \t  only together with lx: Write all graphs with a genus larger "
          "than x  \n");
  fprintf(stderr,
          "\t as multicode to stdout. Do not combine with options also writing "
          "embeddings to stdout.\n");
  fprintf(stderr, "\t No two options for writing can be used together!\n");
  fprintf(stderr,
          "o: \t use the original labelling in the computation. The default is "
          "to use a \n");
  fprintf(stderr,
          "\t BFS labelling in the computation and restore the original for "
          "output.\n");
  fprintf(stderr,
          "L: \t write an unsigned char 255 on stdout each time work on a new "
          "graph is started.\n");
  fprintf(stderr,
          "\t In combination with the output of codes this can be used to "
          "decide when codes\n");
  fprintf(stderr, "\t for a new graph are output.\n");
  fprintf(stderr, "No two of lx, fx, fax, fmx can be used simultaneously.\n");
  fprintf(stderr, "Embeddings are orientable cellular rotations. All-output "
                  "modes fix one orientation when a vertex has degree >= 3.\n");
  exit(status);
}

static int genus_option(const char *digits, const char *name) {
  char *end;
  errno = 0;
  long value = strtol(digits, &end, 10);
  if (!isdigit((unsigned char)*digits) || *end || errno == ERANGE ||
      value > INT_MAX)
    usage(name, EXIT_FAILURE);
  return (int)value;
}

int smallgenus(int nv) {
  if (filter > 0) return -1;
  if (write_embedding || (filter == 0) || (filter2 == 0)) {
    if (nv == 1) {
      putchar(1);
      putchar(0);
    } else {
      putchar(2);
      putchar(2);
      putchar(0);
      putchar(1);
      putchar(0);
    }
    written++;
  }
  return 0;
}

void sort(unsigned char list[], int length)
// FFSL should be a processor instruction and fast
{
  int i;
  unsigned long long small = 0UL, large = 0UL;

  for (i = 0; i < length; i++) {
    if (list[i] <= 64)
      small |= ULBIT(list[i]);
    else
      large |= ULBIT(list[i] - 64);
  }

  for (i = 0; small; i++) {
    list[i] = FFSL(small);
    small &= (small - 1);
  }
  for (; large; i++) {
    list[i] = FFSL(large) + 64;
    large &= (large - 1);
  }
}

/**********************************************************************/

int bfsnum(GRAPH gr, ADJAZENZ adj, GRAPH newgr, ADJAZENZ newadj)
// the returnvalue is 1 if the graph is connected, 0 otherwise.
// disconnected graphs are not relabelled
{
  int i, j, ll, start, best, run, top;
  int list[knoten];

  // start is a vertex with smallest valency -- seems to work best sometimes,
  // but far from always... Sometimes largest valency works better...

  for (start = i = 1, best = adj[1]; i <= gr[0][0]; i++) {
    bfsnummer[i] = 0;
    if (adj[i] < best) {
      best = adj[i];
      start = i;
    }
  }

  bfsnummer[start] = 1;
  invbfsnummer[1] = start;

  list[0] = start;
  ll = 1;
  for (run = 0; (ll < gr[0][0]) && (run < ll); run++) {
    i = list[run];
    for (j = 0; j < adj[i]; j++) {
      if (!bfsnummer[(top = gr[i][j])]) {
        list[ll] = top;
        ll++;
        bfsnummer[top] = ll;
        invbfsnummer[ll] = top;
      }
    }
  }

  if (ll != gr[0][0]) {
    fprintf(stderr, "Skipping disconnected graph!\n");
    return 0;
  }

  if (!do_bfs) return 1;
  newgr[0][0] = gr[0][0];
  for (i = 1; i <= gr[0][0]; i++) {
    top = invbfsnummer[i];
    newadj[i] = adj[top];
    for (j = 0; j < newadj[i]; j++) newgr[i][j] = bfsnummer[gr[top][j]];
    newgr[i][j] = 0;
    sort(newgr[i], newadj[i]);
  }

  return 1;
}

/**************MAIN****************************/

int main(int argc, char *argv[]) {
  GRAPH graph, newgraph;
  ADJAZENZ adj, newadj;
  unsigned char code[MULTICODE_CAPACITY];
  int i, codelaenge, write_separator = 0;
  int genus, limits = 0, outputs = 0;
  unsigned long long larger = 0, list[MAX_GENUS + 1] = {0};

#ifdef _WIN32
  _setmode(_fileno(stdin), _O_BINARY);
  _setmode(_fileno(stdout), _O_BINARY);
#endif

  if (sizeof(unsigned long long) != 8) {
    fprintf(stderr, "Expected 64 bit for unsigned long long -- exit!\n");
    exit(1);
  }

  for (i = 1; i < argc; i++) {
    const char *arg = argv[i];
    if (!strcmp(arg, "h") || !strcmp(arg, "?") || !strcmp(arg, "--help")) {
      usage(argv[0], EXIT_SUCCESS);
    } else if (arg[0] == 'l') {
      filterl = genus_option(arg + 1, argv[0]);
      limits++;
    } else if (!strcmp(arg, "nb")) {
      compute_lower_bound = 0;
    } else if (!strcmp(arg, "o")) {
      do_bfs = 0;
    } else if (!strcmp(arg, "L")) {
      write_separator = 1;
    } else if (!strcmp(arg, "w") || !strcmp(arg, "wa")) {
      write_embedding = 1;
      all = arg[1] == 'a';
      reduce2 = !all;
      outputs++;
    } else if (arg[0] == 'f') {
      if (arg[1] == 'm') {
        filter2 = genus_option(arg + 2, argv[0]);
      } else {
        all = arg[1] == 'a';
        filter = genus_option(arg + (all ? 2 : 1), argv[0]);
        reduce2 = 0;
      }
      limits++;
      outputs++;
    } else if (!strcmp(arg, "F")) {
      filterlarge = 1;
      outputs++;
    } else {
      usage(argv[0], EXIT_FAILURE);
    }
  }
  if (limits > 1 || outputs > 1 || (filterlarge && filterl < 0))
    usage(argv[0], EXIT_FAILURE);

  if (reduce2) {
    for (i = 0; i < 2 * knoten; i++) {
      red_edges[2 * i].invers = red_edges + (2 * i + 1);
      red_edges[2 * i + 1].invers = red_edges + (2 * i);
    }
  }

  while ((codelaenge = read_graph(stdin, code, graph, adj)) != 0) {
    if (write_separator) putchar(255);
    if (!bfsnum(graph, adj, newgraph, newadj)) continue;
    if (globalnv < 3)
      genus = smallgenus(globalnv);
    else if (do_bfs)
      genus = get_genus(newgraph, newadj);
    else
      genus = get_genus(graph, adj);

    if (genus >= 0) {
      list[genus]++;
    } else {
      larger++;
      if (filterlarge) fwrite(code, sizeof(unsigned char), codelaenge, stdout);
    }
  }

  if (filter < 0) {
    for (i = 0; i <= MAX_GENUS; i++)
      if (list[i]) fprintf(stderr, "graphs with genus %d: %llu\n", i, list[i]);
    int limit = filter2 >= 0 ? filter2 : filterl;
    if (limit >= 0)
      fprintf(stderr, "With genus larger than %d: %llu\n", limit, larger);
  }

  if ((filter < 0) && (filter2 < 0) && (filterl < 0) && compute_lower_bound) {
    for (i = 1; i <= MAX_GENUS; i++)
      if (list[i])
        fprintf(stderr,
                "Among the graphs with genus %d the lower bound was sharp for "
                "%2.2lf percent.\n",
                i, (((double)good_approx[i]) * 100.0) / ((double)list[i]));
  }

  if (write_embedding || (filter >= 0) || (filter2 >= 0))
    fprintf(stderr, "Wrote %llu embeddings.\n", written);

  return (0);
}
