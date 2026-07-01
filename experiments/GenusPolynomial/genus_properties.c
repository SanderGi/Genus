// Fast exact orientable genus-polynomial and invariant collector for simple
// connected cubic graph6 inputs.

#define _DARWIN_C_SOURCE
#define _DEFAULT_SOURCE
#define _POSIX_C_SOURCE 200809L
#ifndef MAXN
#define MAXN 64
#endif

#include <ctype.h>
#include <errno.h>
#include <inttypes.h>
#include <math.h>
#include <pthread.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#ifdef __APPLE__
#include <sys/sysctl.h>
#endif
#include <unistd.h>

#include <nauty/nauty.h>

#define GP_MAX_N 64
#define GP_MAX_EDGES ((GP_MAX_N * 3) / 2)
#define GP_MAX_DARTS (GP_MAX_EDGES * 2)
#define GP_MAX_GENUS (GP_MAX_N + 2)
#define GP_FIELD_CAP 4096
#define GP_ROW_CAP 16384
#define GP_ERROR_CAP 512

typedef struct {
    size_t index;
    const char *graph6;
    int n;
    int m;
    uint64_t adj[GP_MAX_N];
    uint8_t degree[GP_MAX_N];
    uint8_t neigh[GP_MAX_N][3];
    uint8_t edge_u[GP_MAX_EDGES];
    uint8_t edge_v[GP_MAX_EDGES];
} Graph;

typedef struct {
    bool input_stdin;
    const char *input_path;
    int generate_cubic_n;
    const char *geng_path;
    const char *out_path;
    int threads;
    size_t limit;
    size_t progress_every;
    bool skip_invalid;
    bool compute_automorphisms;
    bool compute_matrix_spectra;
    bool compute_spanning_trees;
} Options;

typedef struct {
    char **items;
    size_t count;
    size_t capacity;
} StringVec;

typedef struct {
    char *row;
    char error[GP_ERROR_CAP];
    bool ok;
    bool skipped;
} Result;

typedef struct {
    const Options *options;
    char **lines;
    size_t count;
    size_t next_index;
    size_t processed;
    bool stop_requested;
    pthread_mutex_t mutex;
    Result *results;
} WorkQueue;

typedef struct {
    size_t index;
    char *line;
} StreamJob;

typedef enum {
    STREAM_RESULT_EMPTY = 0,
    STREAM_RESULT_OK,
    STREAM_RESULT_SKIPPED,
    STREAM_RESULT_ERROR,
} StreamResultKind;

typedef struct {
    StreamResultKind kind;
    bool ready;
    char *row;
    char error[GP_ERROR_CAP];
} StreamResult;

typedef struct {
    const Options *options;
    FILE *out;
    StreamJob *jobs;
    size_t job_capacity;
    size_t job_head;
    size_t job_tail;
    size_t job_count;
    StreamResult *results;
    size_t result_capacity;
    size_t next_to_emit;
    size_t enqueued;
    size_t processed;
    size_t written;
    size_t skipped;
    size_t errors;
    bool producer_done;
    bool stop_requested;
    pthread_mutex_t mutex;
    pthread_cond_t not_empty;
    pthread_cond_t not_full;
} StreamQueue;

typedef struct {
    uint64_t counts[GP_MAX_GENUS];
    int gamma;
    int g_max;
    double expected;
    double variance;
    double r;
    double r1;
    double r2;
    uint64_t total_rotation_systems;
    char spectrum[GP_FIELD_CAP];
} GenusStats;

typedef struct {
    uint8_t dart_count;
    uint8_t head[GP_MAX_DARTS];
    uint8_t next0[GP_MAX_DARTS];
    uint8_t next1[GP_MAX_DARTS];
    uint64_t head_bit[GP_MAX_DARTS];
} RotationData;

static void die(const char *message) {
    fprintf(stderr, "error: %s\n", message);
    exit(1);
}

static void die_errno(const char *message) {
    fprintf(stderr, "error: %s: %s\n", message, strerror(errno));
    exit(1);
}

static char *xstrdup(const char *s) {
    size_t len = strlen(s);
    char *copy = malloc(len + 1);
    if (!copy) die_errno("malloc");
    memcpy(copy, s, len + 1);
    return copy;
}

static void string_vec_push(StringVec *vec, char *item) {
    if (vec->count == vec->capacity) {
        size_t new_capacity = vec->capacity ? vec->capacity * 2 : 1024;
        char **new_items = realloc(vec->items, new_capacity * sizeof(*new_items));
        if (!new_items) die_errno("realloc");
        vec->items = new_items;
        vec->capacity = new_capacity;
    }
    vec->items[vec->count++] = item;
}

static void string_vec_free(StringVec *vec) {
    for (size_t i = 0; i < vec->count; ++i) free(vec->items[i]);
    free(vec->items);
    vec->items = NULL;
    vec->count = 0;
    vec->capacity = 0;
}

static char *trim_graph6_line(char *line) {
    while (*line && isspace((unsigned char)*line)) ++line;
    size_t len = strlen(line);
    while (len > 0 && isspace((unsigned char)line[len - 1])) line[--len] = '\0';

    const char *header = ">>graph6<<";
    size_t header_len = strlen(header);
    if (strncmp(line, header, header_len) == 0) line += header_len;
    return line;
}

static void read_lines_from_stream(FILE *stream, StringVec *lines, size_t limit) {
    char *buffer = NULL;
    size_t cap = 0;
    ssize_t len;

    while ((len = getline(&buffer, &cap, stream)) != -1) {
        (void)len;
        char *trimmed = trim_graph6_line(buffer);
        if (*trimmed == '\0') continue;
        string_vec_push(lines, xstrdup(trimmed));
        if (limit > 0 && lines->count >= limit) break;
    }
    free(buffer);
}

static void read_graph6_file(const char *path, StringVec *lines, size_t limit) {
    FILE *stream = fopen(path, "r");
    if (!stream) die_errno(path);
    read_lines_from_stream(stream, lines, limit);
    fclose(stream);
}

static bool add_edge(Graph *g, int u, int v, char *err, size_t err_len) {
    if (u < 0 || v < 0 || u >= g->n || v >= g->n || u == v) {
        snprintf(err, err_len, "invalid edge (%d,%d)", u, v);
        return false;
    }
    if ((g->adj[u] >> v) & 1ULL) {
        snprintf(err, err_len, "duplicate edge (%d,%d)", u, v);
        return false;
    }
    g->adj[u] |= 1ULL << v;
    g->adj[v] |= 1ULL << u;
    return true;
}

static int graph6_size(const unsigned char *s, size_t len, size_t *pos, char *err,
                       size_t err_len) {
    if (len == 0) {
        snprintf(err, err_len, "empty graph6 record");
        return -1;
    }
    if (s[0] != '~') {
        if (s[0] < 63 || s[0] > 126) {
            snprintf(err, err_len, "invalid graph6 size byte");
            return -1;
        }
        *pos = 1;
        return (int)s[0] - 63;
    }
    if (len < 4) {
        snprintf(err, err_len, "truncated graph6 size");
        return -1;
    }
    if (s[1] != '~') {
        int n = 0;
        for (int i = 1; i <= 3; ++i) {
            if (s[i] < 63 || s[i] > 126) {
                snprintf(err, err_len, "invalid graph6 extended size byte");
                return -1;
            }
            n = (n << 6) | ((int)s[i] - 63);
        }
        *pos = 4;
        return n;
    }
    if (len < 8) {
        snprintf(err, err_len, "truncated graph6 large size");
        return -1;
    }
    uint64_t n = 0;
    for (int i = 2; i <= 7; ++i) {
        if (s[i] < 63 || s[i] > 126) {
            snprintf(err, err_len, "invalid graph6 large size byte");
            return -1;
        }
        n = (n << 6) | ((uint64_t)s[i] - 63);
    }
    if (n > INT32_MAX) {
        snprintf(err, err_len, "graph6 size is too large");
        return -1;
    }
    *pos = 8;
    return (int)n;
}

static bool parse_graph6(const char *record, size_t index, Graph *g, char *err,
                         size_t err_len) {
    memset(g, 0, sizeof(*g));
    g->index = index;
    g->graph6 = record;

    const unsigned char *s = (const unsigned char *)record;
    size_t len = strlen(record);
    size_t pos = 0;
    int n = graph6_size(s, len, &pos, err, err_len);
    if (n < 0) return false;
    if (n > GP_MAX_N) {
        snprintf(err, err_len, "graph has %d vertices; max supported is %d", n, GP_MAX_N);
        return false;
    }
    g->n = n;

    size_t bit_count = (size_t)n * (size_t)(n - 1) / 2;
    size_t body_len = (bit_count + 5) / 6;
    if (len < pos + body_len) {
        snprintf(err, err_len, "graph6 record is truncated");
        return false;
    }

    size_t bit_index = 0;
    for (size_t byte_index = 0; byte_index < body_len; ++byte_index) {
        unsigned char c = s[pos + byte_index];
        if (c < 63 || c > 126) {
            snprintf(err, err_len, "invalid graph6 data byte");
            return false;
        }
        int value = (int)c - 63;
        for (int bit = 5; bit >= 0 && bit_index < bit_count; --bit, ++bit_index) {
            if ((value >> bit) & 1) {
                int v = 1;
                size_t before = 0;
                while (before + (size_t)v <= bit_index) {
                    before += (size_t)v;
                    ++v;
                }
                int u = (int)(bit_index - before);
                if (!add_edge(g, u, v, err, err_len)) return false;
                ++g->m;
            }
        }
    }

    if (n == 0) {
        snprintf(err, err_len, "graph has no vertices");
        return false;
    }
    if (n % 2 != 0) {
        snprintf(err, err_len, "graph has %d vertices; cubic graphs need even order", n);
        return false;
    }
    if (g->m != (3 * n) / 2) {
        snprintf(err, err_len, "graph has %d edges; expected 3n/2=%d", g->m,
                 (3 * n) / 2);
        return false;
    }

    int edge_index = 0;
    for (int u = 0; u < n; ++u) {
        uint64_t bits = g->adj[u];
        while (bits) {
            int v = __builtin_ctzll(bits);
            bits &= bits - 1;
            if (g->degree[u] < 3) g->neigh[u][g->degree[u]] = (uint8_t)v;
            ++g->degree[u];
            if (u < v) {
                if (edge_index >= GP_MAX_EDGES) {
                    snprintf(err, err_len, "too many edges");
                    return false;
                }
                g->edge_u[edge_index] = (uint8_t)u;
                g->edge_v[edge_index] = (uint8_t)v;
                ++edge_index;
            }
        }
        if (g->degree[u] != 3) {
            snprintf(err, err_len, "vertex %d has degree %u; expected 3", u,
                     (unsigned)g->degree[u]);
            return false;
        }
    }

    uint64_t visited = 1ULL;
    int queue[GP_MAX_N];
    int head = 0, tail = 0;
    queue[tail++] = 0;
    while (head < tail) {
        int u = queue[head++];
        uint64_t unseen = g->adj[u] & ~visited;
        while (unseen) {
            int v = __builtin_ctzll(unseen);
            unseen &= unseen - 1;
            visited |= 1ULL << v;
            queue[tail++] = v;
        }
    }
    if (tail != n) {
        snprintf(err, err_len, "graph is disconnected");
        return false;
    }

    return true;
}

static int bfs_distances(const Graph *g, int source, uint64_t blocked_vertices,
                         int blocked_edge_a, int blocked_edge_b, int *dist) {
    for (int i = 0; i < g->n; ++i) dist[i] = -1;
    if ((blocked_vertices >> source) & 1ULL) return 0;

    int queue[GP_MAX_N];
    int head = 0, tail = 0;
    dist[source] = 0;
    queue[tail++] = source;

    while (head < tail) {
        int u = queue[head++];
        for (int i = 0; i < 3; ++i) {
            int v = g->neigh[u][i];
            if ((blocked_vertices >> v) & 1ULL) continue;
            bool blocked = false;
            if (blocked_edge_a >= 0) {
                int a = g->edge_u[blocked_edge_a], b = g->edge_v[blocked_edge_a];
                blocked = (u == a && v == b) || (u == b && v == a);
            }
            if (!blocked && blocked_edge_b >= 0) {
                int a = g->edge_u[blocked_edge_b], b = g->edge_v[blocked_edge_b];
                blocked = (u == a && v == b) || (u == b && v == a);
            }
            if (blocked || dist[v] >= 0) continue;
            dist[v] = dist[u] + 1;
            queue[tail++] = v;
        }
    }
    return tail;
}

static bool connected_after_blocks(const Graph *g, uint64_t blocked_vertices,
                                   int blocked_edge_a, int blocked_edge_b) {
    int start = -1;
    int remaining = 0;
    for (int i = 0; i < g->n; ++i) {
        if (((blocked_vertices >> i) & 1ULL) == 0) {
            if (start < 0) start = i;
            ++remaining;
        }
    }
    if (remaining <= 1) return true;
    int dist[GP_MAX_N];
    int reached = bfs_distances(g, start, blocked_vertices, blocked_edge_a,
                                blocked_edge_b, dist);
    return reached == remaining;
}

static int compute_diameter(const Graph *g) {
    int best = 0;
    int dist[GP_MAX_N];
    for (int source = 0; source < g->n; ++source) {
        bfs_distances(g, source, 0, -1, -1, dist);
        for (int v = 0; v < g->n; ++v) {
            if (dist[v] < 0) return -1;
            if (dist[v] > best) best = dist[v];
        }
    }
    return best;
}

static int compute_girth(const Graph *g) {
    int best = GP_MAX_N + 1;
    int dist[GP_MAX_N], parent[GP_MAX_N], queue[GP_MAX_N];

    for (int source = 0; source < g->n; ++source) {
        for (int i = 0; i < g->n; ++i) {
            dist[i] = -1;
            parent[i] = -1;
        }
        int head = 0, tail = 0;
        dist[source] = 0;
        queue[tail++] = source;
        while (head < tail) {
            int u = queue[head++];
            for (int i = 0; i < 3; ++i) {
                int v = g->neigh[u][i];
                if (dist[v] < 0) {
                    dist[v] = dist[u] + 1;
                    parent[v] = u;
                    queue[tail++] = v;
                } else if (parent[u] != v && parent[v] != u) {
                    int cycle_len = dist[u] + dist[v] + 1;
                    if (cycle_len < best) best = cycle_len;
                }
            }
        }
    }
    return best == GP_MAX_N + 1 ? -1 : best;
}

static bool is_bipartite(const Graph *g) {
    int color[GP_MAX_N];
    for (int i = 0; i < g->n; ++i) color[i] = -1;
    int queue[GP_MAX_N];

    for (int start = 0; start < g->n; ++start) {
        if (color[start] >= 0) continue;
        int head = 0, tail = 0;
        color[start] = 0;
        queue[tail++] = start;
        while (head < tail) {
            int u = queue[head++];
            for (int i = 0; i < 3; ++i) {
                int v = g->neigh[u][i];
                if (color[v] < 0) {
                    color[v] = 1 - color[u];
                    queue[tail++] = v;
                } else if (color[v] == color[u]) {
                    return false;
                }
            }
        }
    }
    return true;
}

static int vertex_connectivity(const Graph *g) {
    if (g->n <= 1) return 0;
    for (int v = 0; v < g->n; ++v) {
        if (!connected_after_blocks(g, 1ULL << v, -1, -1)) return 1;
    }
    for (int a = 0; a < g->n; ++a) {
        for (int b = a + 1; b < g->n; ++b) {
            uint64_t blocked = (1ULL << a) | (1ULL << b);
            if (!connected_after_blocks(g, blocked, -1, -1)) return 2;
        }
    }
    return 3;
}

static int edge_connectivity(const Graph *g) {
    for (int e = 0; e < g->m; ++e) {
        if (!connected_after_blocks(g, 0, e, -1)) return 1;
    }
    for (int a = 0; a < g->m; ++a) {
        for (int b = a + 1; b < g->m; ++b) {
            if (!connected_after_blocks(g, 0, a, b)) return 2;
        }
    }
    return 3;
}

static void cycle_dfs(const Graph *g, int start, int current, int depth, int length,
                      uint64_t visited, uint64_t *oriented_count) {
    if (depth == length - 1) {
        if ((g->adj[current] >> start) & 1ULL) ++(*oriented_count);
        return;
    }
    for (int i = 0; i < 3; ++i) {
        int v = g->neigh[current][i];
        if (v == start) continue;
        if ((visited >> v) & 1ULL) continue;
        if (v < start) continue;
        cycle_dfs(g, start, v, depth + 1, length, visited | (1ULL << v),
                  oriented_count);
    }
}

static uint64_t count_cycles_length(const Graph *g, int length) {
    uint64_t oriented_count = 0;
    for (int start = 0; start < g->n; ++start) {
        cycle_dfs(g, start, start, 0, length, 1ULL << start, &oriented_count);
    }
    return oriented_count / 2;
}

static int cmp_double(const void *a, const void *b) {
    double da = *(const double *)a;
    double db = *(const double *)b;
    return (da > db) - (da < db);
}

static void jacobi_eigenvalues(int n, double matrix[GP_MAX_N][GP_MAX_N],
                               double *eigenvalues) {
    if (n == 0) return;
    const double tolerance = 1e-13;
    int max_iterations = n > 1 ? 80 * n * n : 1;
    if (max_iterations < 100) max_iterations = 100;

    for (int iter = 0; iter < max_iterations; ++iter) {
        int p = 0, q = 1;
        double max_offdiag = n > 1 ? fabs(matrix[0][1]) : 0.0;
        for (int i = 0; i < n; ++i) {
            for (int j = i + 1; j < n; ++j) {
                double value = fabs(matrix[i][j]);
                if (value > max_offdiag) {
                    max_offdiag = value;
                    p = i;
                    q = j;
                }
            }
        }
        if (max_offdiag < tolerance) break;

        double app = matrix[p][p];
        double aqq = matrix[q][q];
        double apq = matrix[p][q];
        double tau = (aqq - app) / (2.0 * apq);
        double sign = tau >= 0.0 ? 1.0 : -1.0;
        double t = sign / (fabs(tau) + sqrt(1.0 + tau * tau));
        double c = 1.0 / sqrt(1.0 + t * t);
        double s = t * c;

        for (int k = 0; k < n; ++k) {
            if (k == p || k == q) continue;
            double akp = matrix[k][p];
            double akq = matrix[k][q];
            matrix[k][p] = matrix[p][k] = c * akp - s * akq;
            matrix[k][q] = matrix[q][k] = s * akp + c * akq;
        }
        matrix[p][p] = app - t * apq;
        matrix[q][q] = aqq + t * apq;
        matrix[p][q] = matrix[q][p] = 0.0;
    }

    for (int i = 0; i < n; ++i) eigenvalues[i] = matrix[i][i];
    qsort(eigenvalues, (size_t)n, sizeof(double), cmp_double);
}

static void append_formatted_double(char *out, size_t out_cap, double value) {
    double rounded = nearbyint(value * 1e10) / 1e10;
    if (fabs(rounded) < 1e-8) rounded = 0.0;

    char tmp[64];
    snprintf(tmp, sizeof(tmp), "%.10f", rounded);
    size_t len = strlen(tmp);
    while (len > 0 && tmp[len - 1] == '0') tmp[--len] = '\0';
    if (len > 0 && tmp[len - 1] == '.') tmp[--len] = '\0';
    if (strcmp(tmp, "-0") == 0 || tmp[0] == '\0') strcpy(tmp, "0");
    strncat(out, tmp, out_cap - strlen(out) - 1);
}

static void compute_spectrum_string(const Graph *g, bool laplacian, char *out,
                                    size_t out_cap) {
    double matrix[GP_MAX_N][GP_MAX_N] = {{0.0}};
    double eigenvalues[GP_MAX_N];
    int n = g->n;

    if (laplacian) {
        for (int i = 0; i < n; ++i) matrix[i][i] = (double)g->degree[i];
    }
    for (int e = 0; e < g->m; ++e) {
        int u = g->edge_u[e], v = g->edge_v[e];
        if (laplacian) {
            matrix[u][v] = -1.0;
            matrix[v][u] = -1.0;
        } else {
            matrix[u][v] = 1.0;
            matrix[v][u] = 1.0;
        }
    }

    jacobi_eigenvalues(n, matrix, eigenvalues);
    out[0] = '\0';
    for (int i = 0; i < n; ++i) {
        if (i > 0) strncat(out, ";", out_cap - strlen(out) - 1);
        append_formatted_double(out, out_cap, eigenvalues[i]);
    }
}

static __int128 bareiss_determinant(int n, __int128 matrix[GP_MAX_N][GP_MAX_N]) {
    if (n == 0) return 1;
    if (n == 1) return matrix[0][0];

    int sign = 1;
    __int128 previous_pivot = 1;
    for (int k = 0; k < n - 1; ++k) {
        if (matrix[k][k] == 0) {
            int swap_row = -1;
            for (int r = k + 1; r < n; ++r) {
                if (matrix[r][k] != 0) {
                    swap_row = r;
                    break;
                }
            }
            if (swap_row < 0) return 0;
            for (int c = 0; c < n; ++c) {
                __int128 tmp = matrix[k][c];
                matrix[k][c] = matrix[swap_row][c];
                matrix[swap_row][c] = tmp;
            }
            sign *= -1;
        }
        __int128 pivot = matrix[k][k];
        for (int i = k + 1; i < n; ++i) {
            for (int j = k + 1; j < n; ++j) {
                matrix[i][j] =
                    (matrix[i][j] * pivot - matrix[i][k] * matrix[k][j]) /
                    previous_pivot;
            }
        }
        previous_pivot = pivot;
        for (int i = k + 1; i < n; ++i) matrix[i][k] = 0;
        for (int j = k + 1; j < n; ++j) matrix[k][j] = 0;
    }
    return sign > 0 ? matrix[n - 1][n - 1] : -matrix[n - 1][n - 1];
}

static void int128_to_string(__int128 value, char *out, size_t out_cap) {
    if (out_cap == 0) return;
    if (value == 0) {
        snprintf(out, out_cap, "0");
        return;
    }
    bool negative = value < 0;
    unsigned __int128 u = negative ? (unsigned __int128)(-value) : (unsigned __int128)value;
    char tmp[128];
    size_t len = 0;
    while (u > 0 && len < sizeof(tmp) - 1) {
        tmp[len++] = (char)('0' + (u % 10));
        u /= 10;
    }
    size_t pos = 0;
    if (negative && pos + 1 < out_cap) out[pos++] = '-';
    while (len > 0 && pos + 1 < out_cap) out[pos++] = tmp[--len];
    out[pos] = '\0';
}

static void compute_spanning_tree_count(const Graph *g, char *out, size_t out_cap) {
    int n = g->n;
    if (n <= 1) {
        snprintf(out, out_cap, "1");
        return;
    }

    __int128 lap[GP_MAX_N][GP_MAX_N] = {{0}};
    for (int v = 0; v < n; ++v) lap[v][v] = g->degree[v];
    for (int e = 0; e < g->m; ++e) {
        int u = g->edge_u[e], v = g->edge_v[e];
        lap[u][v] -= 1;
        lap[v][u] -= 1;
    }

    __int128 cofactor[GP_MAX_N][GP_MAX_N] = {{0}};
    for (int i = 0; i < n - 1; ++i)
        for (int j = 0; j < n - 1; ++j) cofactor[i][j] = lap[i][j];
    __int128 det = bareiss_determinant(n - 1, cofactor);
    if (det < 0) det = -det;
    int128_to_string(det, out, out_cap);
}

static void compute_automorphism_order(const Graph *g, char *out, size_t out_cap) {
    int n = g->n;
    int m = SETWORDSNEEDED(n);
    graph ng[MAXN * MAXM];
    int lab[GP_MAX_N], ptn[GP_MAX_N], orbits[GP_MAX_N];
    DEFAULTOPTIONS_GRAPH(options);
    statsblk stats;

    nauty_check(WORDSIZE, m, n, NAUTYVERSIONID);
    EMPTYGRAPH(ng, m, n);
    for (int e = 0; e < g->m; ++e) {
        ADDONEEDGE(ng, g->edge_u[e], g->edge_v[e], m);
    }

    options.getcanon = FALSE;
    densenauty(ng, lab, ptn, orbits, &options, &stats, m, n, NULL);
    if (stats.errstatus != 0) {
        snprintf(out, out_cap, "NA");
        return;
    }

    if (stats.grpsize2 == 0) {
        snprintf(out, out_cap, "%.0f", stats.grpsize1);
    } else {
        snprintf(out, out_cap, "%.12ge%d", stats.grpsize1, stats.grpsize2);
    }
}

static bool prepare_rotation_data(const Graph *g, RotationData *data, char *err,
                                  size_t err_len) {
    memset(data, 0, sizeof(*data));
    int dart_index[GP_MAX_N][GP_MAX_N];
    for (int i = 0; i < GP_MAX_N; ++i)
        for (int j = 0; j < GP_MAX_N; ++j) dart_index[i][j] = -1;

    int dart = 0;
    for (int e = 0; e < g->m; ++e) {
        int u = g->edge_u[e], v = g->edge_v[e];
        dart_index[u][v] = dart;
        data->head[dart] = (uint8_t)v;
        ++dart;
        dart_index[v][u] = dart;
        data->head[dart] = (uint8_t)u;
        ++dart;
    }
    data->dart_count = (uint8_t)dart;

    for (int tail = 0; tail < g->n; ++tail) {
        for (int ni = 0; ni < 3; ++ni) {
            int head = g->neigh[tail][ni];
            int d = dart_index[tail][head];
            if (d < 0) {
                snprintf(err, err_len, "internal dart-index error");
                return false;
            }

            int pos = -1;
            for (int k = 0; k < 3; ++k) {
                if (g->neigh[head][k] == tail) {
                    pos = k;
                    break;
                }
            }
            if (pos < 0) {
                snprintf(err, err_len, "internal neighbor-order error");
                return false;
            }

            int next0_neighbor = g->neigh[head][(pos + 1) % 3];
            int next1_neighbor = g->neigh[head][(pos + 2) % 3];
            data->next0[d] = (uint8_t)dart_index[head][next0_neighbor];
            data->next1[d] = (uint8_t)dart_index[head][next1_neighbor];
            data->head_bit[d] = 1ULL << head;
        }
    }
    return true;
}

static int count_faces_fast(const RotationData *data, uint64_t mask, uint32_t *seen,
                            uint32_t stamp) {
    int faces = 0;
    int dart_count = data->dart_count;
    for (int start = 0; start < dart_count; ++start) {
        if (seen[start] == stamp) continue;
        ++faces;
        int current = start;
        while (seen[current] != stamp) {
            seen[current] = stamp;
            current = (mask & data->head_bit[current]) ? data->next1[current]
                                                       : data->next0[current];
        }
    }
    return faces;
}

static bool compute_genus_stats(const Graph *g, GenusStats *stats, char *err,
                                size_t err_len) {
    memset(stats, 0, sizeof(*stats));
    if (g->n <= 0 || g->n >= 64) {
        snprintf(err, err_len, "exact rotation spectrum needs 1 <= n < 64");
        return false;
    }

    RotationData data;
    if (!prepare_rotation_data(g, &data, err, err_len)) return false;

    uint64_t masks_to_enumerate = 1ULL << (g->n - 1);
    uint64_t total = 1ULL << g->n;
    uint32_t seen[GP_MAX_DARTS] = {0};
    uint32_t stamp = 0;

    for (uint64_t mask = 0; mask < masks_to_enumerate; ++mask) {
        ++stamp;
        if (stamp == 0) {
            memset(seen, 0, sizeof(seen));
            stamp = 1;
        }
        int faces = count_faces_fast(&data, mask, seen, stamp);
        int two_g = 2 - g->n + g->m - faces;
        if (two_g < 0 || (two_g & 1)) {
            snprintf(err, err_len,
                     "invalid genus from n=%d m=%d faces=%d two_g=%d", g->n,
                     g->m, faces, two_g);
            return false;
        }
        int genus = two_g / 2;
        if (genus < 0 || genus >= GP_MAX_GENUS) {
            snprintf(err, err_len, "computed genus %d out of range", genus);
            return false;
        }
        stats->counts[genus] += 2;
    }

    uint64_t actual_total = 0;
    stats->gamma = -1;
    stats->g_max = -1;
    double first_moment = 0.0;
    double second_moment = 0.0;
    for (int genus = 0; genus < GP_MAX_GENUS; ++genus) {
        uint64_t count = stats->counts[genus];
        if (!count) continue;
        actual_total += count;
        if (stats->gamma < 0) stats->gamma = genus;
        stats->g_max = genus;
        first_moment += (double)genus * (double)count;
        second_moment += (double)genus * (double)genus * (double)count;
    }
    if (actual_total != total) {
        snprintf(err, err_len, "spectrum total is %" PRIu64 "; expected %" PRIu64,
                 actual_total, total);
        return false;
    }
    stats->total_rotation_systems = total;
    stats->expected = first_moment / (double)total;
    double second = second_moment / (double)total;
    stats->variance = second - stats->expected * stats->expected;
    if (stats->variance < 0.0 && stats->variance > -1e-12) stats->variance = 0.0;
    stats->r = (double)stats->counts[stats->gamma] / (double)total;
    uint64_t r1_count = 0, r2_count = 0;
    for (int genus = 0; genus < GP_MAX_GENUS; ++genus) {
        if (genus <= stats->gamma + 1) r1_count += stats->counts[genus];
        if (genus <= stats->gamma + 2) r2_count += stats->counts[genus];
    }
    stats->r1 = (double)r1_count / (double)total;
    stats->r2 = (double)r2_count / (double)total;

    stats->spectrum[0] = '\0';
    for (int genus = 0; genus < GP_MAX_GENUS; ++genus) {
        if (!stats->counts[genus]) continue;
        char part[64];
        snprintf(part, sizeof(part), "%s%d:%" PRIu64,
                 stats->spectrum[0] ? ";" : "", genus, stats->counts[genus]);
        strncat(stats->spectrum, part, sizeof(stats->spectrum) - strlen(stats->spectrum) - 1);
    }
    return true;
}

static char *analyze_graph_to_csv(const Graph *g, const Options *options, char *err,
                                  size_t err_len) {
    int girth = compute_girth(g);
    int diameter = compute_diameter(g);
    bool bipartite = is_bipartite(g);
    int vconn = vertex_connectivity(g);
    int econn = edge_connectivity(g);
    uint64_t triangle_count = count_cycles_length(g, 3);
    uint64_t four_cycle_count = count_cycles_length(g, 4);
    uint64_t five_cycle_count = count_cycles_length(g, 5);
    uint64_t six_cycle_count = count_cycles_length(g, 6);

    char automorphism_order[128] = "NA";
    char adjacency_spectrum[GP_FIELD_CAP] = "NA";
    char laplacian_spectrum[GP_FIELD_CAP] = "NA";
    char spanning_trees[128] = "NA";

    if (options->compute_automorphisms) {
        compute_automorphism_order(g, automorphism_order, sizeof(automorphism_order));
    }
    if (options->compute_matrix_spectra) {
        compute_spectrum_string(g, false, adjacency_spectrum, sizeof(adjacency_spectrum));
        compute_spectrum_string(g, true, laplacian_spectrum, sizeof(laplacian_spectrum));
    }
    if (options->compute_spanning_trees) {
        compute_spanning_tree_count(g, spanning_trees, sizeof(spanning_trees));
    }

    GenusStats genus_stats;
    if (!compute_genus_stats(g, &genus_stats, err, err_len)) return NULL;

    char *row = malloc(GP_ROW_CAP);
    if (!row) die_errno("malloc row");
    int written = snprintf(
        row, GP_ROW_CAP,
        "%zu,%s,%d,%d,%d,%d,%s,%d,%d,%s,%" PRIu64 ",%" PRIu64 ",%" PRIu64
        ",%" PRIu64 ",%s,%s,%s,%s,%d,%d,%.12g,%.12g,%.12g,%.12g,%.12g,%" PRIu64,
        g->index, g->graph6, g->n, g->m, girth, diameter,
        bipartite ? "True" : "False", vconn, econn, automorphism_order,
        triangle_count, four_cycle_count, five_cycle_count, six_cycle_count,
        adjacency_spectrum, laplacian_spectrum, spanning_trees, genus_stats.spectrum,
        genus_stats.gamma, genus_stats.g_max, genus_stats.expected, genus_stats.variance,
        genus_stats.r, genus_stats.r1, genus_stats.r2,
        genus_stats.total_rotation_systems);
    if (written < 0 || written >= GP_ROW_CAP) {
        free(row);
        snprintf(err, err_len, "CSV row exceeded internal buffer");
        return NULL;
    }
    return row;
}

static void *worker_main(void *arg) {
    WorkQueue *work = (WorkQueue *)arg;

    for (;;) {
        pthread_mutex_lock(&work->mutex);
        if (work->stop_requested || work->next_index >= work->count) {
            pthread_mutex_unlock(&work->mutex);
            break;
        }
        size_t index = work->next_index++;
        pthread_mutex_unlock(&work->mutex);

        Result *result = &work->results[index];
        Graph graph;
        char err[GP_ERROR_CAP] = "";

        if (!parse_graph6(work->lines[index], index, &graph, err, sizeof(err))) {
            snprintf(result->error, sizeof(result->error), "%s", err);
            result->skipped = work->options->skip_invalid;
            if (!work->options->skip_invalid) {
                pthread_mutex_lock(&work->mutex);
                work->stop_requested = true;
                pthread_mutex_unlock(&work->mutex);
            }
        } else {
            char *row = analyze_graph_to_csv(&graph, work->options, err, sizeof(err));
            if (!row) {
                snprintf(result->error, sizeof(result->error), "%s", err);
                result->skipped = work->options->skip_invalid;
                if (!work->options->skip_invalid) {
                    pthread_mutex_lock(&work->mutex);
                    work->stop_requested = true;
                    pthread_mutex_unlock(&work->mutex);
                }
            } else {
                result->row = row;
                result->ok = true;
            }
        }

        pthread_mutex_lock(&work->mutex);
        ++work->processed;
        if (work->options->progress_every > 0 &&
            work->processed % work->options->progress_every == 0) {
            fprintf(stderr, "Processed %zu/%zu graphs\n", work->processed, work->count);
        }
        pthread_mutex_unlock(&work->mutex);
    }
    return NULL;
}

static bool stream_queue_stopped(StreamQueue *queue) {
    bool stopped;
    pthread_mutex_lock(&queue->mutex);
    stopped = queue->stop_requested;
    pthread_mutex_unlock(&queue->mutex);
    return stopped;
}

static void stream_queue_init(StreamQueue *queue, const Options *options, FILE *out) {
    memset(queue, 0, sizeof(*queue));
    queue->options = options;
    queue->out = out;
    queue->job_capacity = (size_t)options->threads * 8;
    if (queue->job_capacity < 128) queue->job_capacity = 128;
    if (queue->job_capacity > 8192) queue->job_capacity = 8192;
    queue->jobs = calloc(queue->job_capacity, sizeof(*queue->jobs));
    if (!queue->jobs) die_errno("calloc stream jobs");
    pthread_mutex_init(&queue->mutex, NULL);
    pthread_cond_init(&queue->not_empty, NULL);
    pthread_cond_init(&queue->not_full, NULL);
}

static void stream_queue_destroy(StreamQueue *queue) {
    for (size_t i = 0; i < queue->job_count; ++i) {
        size_t pos = (queue->job_head + i) % queue->job_capacity;
        free(queue->jobs[pos].line);
    }
    for (size_t i = 0; i < queue->result_capacity; ++i) {
        free(queue->results[i].row);
    }
    free(queue->jobs);
    free(queue->results);
    pthread_cond_destroy(&queue->not_empty);
    pthread_cond_destroy(&queue->not_full);
    pthread_mutex_destroy(&queue->mutex);
}

static void stream_queue_finish_producer(StreamQueue *queue) {
    pthread_mutex_lock(&queue->mutex);
    queue->producer_done = true;
    pthread_cond_broadcast(&queue->not_empty);
    pthread_mutex_unlock(&queue->mutex);
}

static bool stream_queue_enqueue(StreamQueue *queue, char *line, size_t index) {
    pthread_mutex_lock(&queue->mutex);
    while (queue->job_count == queue->job_capacity && !queue->stop_requested) {
        pthread_cond_wait(&queue->not_full, &queue->mutex);
    }
    if (queue->stop_requested) {
        pthread_mutex_unlock(&queue->mutex);
        return false;
    }

    queue->jobs[queue->job_tail].index = index;
    queue->jobs[queue->job_tail].line = line;
    queue->job_tail = (queue->job_tail + 1) % queue->job_capacity;
    ++queue->job_count;
    ++queue->enqueued;
    pthread_cond_signal(&queue->not_empty);
    pthread_mutex_unlock(&queue->mutex);
    return true;
}

static void stream_queue_ensure_result_capacity_locked(StreamQueue *queue,
                                                       size_t index) {
    if (index < queue->result_capacity) return;

    size_t new_capacity = queue->result_capacity ? queue->result_capacity * 2 : 1024;
    while (new_capacity <= index) new_capacity *= 2;
    StreamResult *new_results =
        realloc(queue->results, new_capacity * sizeof(*queue->results));
    if (!new_results) die_errno("realloc stream results");
    memset(new_results + queue->result_capacity, 0,
           (new_capacity - queue->result_capacity) * sizeof(*new_results));
    queue->results = new_results;
    queue->result_capacity = new_capacity;
}

static void stream_queue_flush_ready_locked(StreamQueue *queue) {
    while (queue->next_to_emit < queue->result_capacity) {
        StreamResult *result = &queue->results[queue->next_to_emit];
        if (!result->ready) break;

        if (result->kind == STREAM_RESULT_OK) {
            fprintf(queue->out, "%s\n", result->row);
            free(result->row);
            result->row = NULL;
            ++queue->written;
        } else if (result->kind == STREAM_RESULT_SKIPPED) {
            fprintf(stderr, "skipped graph %zu: %s\n", queue->next_to_emit,
                    result->error);
            ++queue->skipped;
        } else if (result->kind == STREAM_RESULT_ERROR) {
            fprintf(stderr, "failed graph %zu: %s\n", queue->next_to_emit,
                    result->error);
            ++queue->errors;
        }

        result->ready = false;
        result->kind = STREAM_RESULT_EMPTY;
        ++queue->next_to_emit;
    }
}

static void *stream_worker_main(void *arg) {
    StreamQueue *queue = (StreamQueue *)arg;

    for (;;) {
        pthread_mutex_lock(&queue->mutex);
        while (queue->job_count == 0 && !queue->producer_done &&
               !queue->stop_requested) {
            pthread_cond_wait(&queue->not_empty, &queue->mutex);
        }
        if (queue->job_count == 0 && (queue->producer_done || queue->stop_requested)) {
            pthread_mutex_unlock(&queue->mutex);
            break;
        }

        StreamJob job = queue->jobs[queue->job_head];
        queue->jobs[queue->job_head].line = NULL;
        queue->job_head = (queue->job_head + 1) % queue->job_capacity;
        --queue->job_count;
        pthread_cond_signal(&queue->not_full);
        pthread_mutex_unlock(&queue->mutex);

        Graph graph;
        char err[GP_ERROR_CAP] = "";
        StreamResultKind kind = STREAM_RESULT_EMPTY;
        char *row = NULL;

        if (!parse_graph6(job.line, job.index, &graph, err, sizeof(err))) {
            kind = queue->options->skip_invalid ? STREAM_RESULT_SKIPPED
                                                : STREAM_RESULT_ERROR;
        } else {
            row = analyze_graph_to_csv(&graph, queue->options, err, sizeof(err));
            if (row) {
                kind = STREAM_RESULT_OK;
            } else {
                kind = queue->options->skip_invalid ? STREAM_RESULT_SKIPPED
                                                    : STREAM_RESULT_ERROR;
            }
        }
        free(job.line);

        pthread_mutex_lock(&queue->mutex);
        stream_queue_ensure_result_capacity_locked(queue, job.index);
        StreamResult *result = &queue->results[job.index];
        result->kind = kind;
        result->row = row;
        if (kind == STREAM_RESULT_SKIPPED || kind == STREAM_RESULT_ERROR) {
            snprintf(result->error, sizeof(result->error), "%s", err);
        }
        result->ready = true;
        if (kind == STREAM_RESULT_ERROR) {
            queue->stop_requested = true;
            pthread_cond_broadcast(&queue->not_full);
            pthread_cond_broadcast(&queue->not_empty);
        }

        ++queue->processed;
        stream_queue_flush_ready_locked(queue);
        if (queue->options->progress_every > 0 &&
            queue->processed % queue->options->progress_every == 0) {
            fprintf(stderr, "Processed %zu graphs\n", queue->processed);
            fflush(stderr);
            fflush(queue->out);
        }
        pthread_mutex_unlock(&queue->mutex);
    }
    return NULL;
}

static size_t stream_graph6_records(FILE *stream, StreamQueue *queue,
                                    bool *hit_limit) {
    char *buffer = NULL;
    size_t cap = 0;
    ssize_t len;
    size_t produced = 0;

    while ((len = getline(&buffer, &cap, stream)) != -1) {
        (void)len;
        char *trimmed = trim_graph6_line(buffer);
        if (*trimmed == '\0') continue;

        if (queue->options->limit > 0 && produced >= queue->options->limit) {
            *hit_limit = true;
            break;
        }

        char *line = xstrdup(trimmed);
        if (!stream_queue_enqueue(queue, line, produced)) {
            free(line);
            break;
        }
        ++produced;

        if (queue->options->limit > 0 && produced >= queue->options->limit) {
            *hit_limit = true;
            break;
        }
    }

    free(buffer);
    return produced;
}

static int stream_graph6_from_geng(const Options *options, StreamQueue *queue) {
    char command[256];
    if (options->generate_cubic_n <= 0 || options->generate_cubic_n > GP_MAX_N) {
        die("--generate-cubic N needs 1 <= N <= 64");
    }
    int written = snprintf(command, sizeof(command), "%s -cd3D3 -q %d",
                           options->geng_path, options->generate_cubic_n);
    if (written < 0 || written >= (int)sizeof(command)) {
        die("geng command is too long");
    }

    FILE *stream = popen(command, "r");
    if (!stream) die_errno("popen(geng)");
    bool hit_limit = false;
    stream_graph6_records(stream, queue, &hit_limit);
    stream_queue_finish_producer(queue);
    int status = pclose(stream);
    if (status != 0 && !hit_limit && !stream_queue_stopped(queue)) {
        fprintf(stderr, "warning: geng command exited with status %d\n", status);
    }
    return status;
}

static int default_thread_count(void) {
#ifdef _SC_NPROCESSORS_ONLN
    long ncpu = sysconf(_SC_NPROCESSORS_ONLN);
    if (ncpu < 1) return 1;
    if (ncpu > 64) return 64;
    return (int)ncpu;
#elif defined(__APPLE__)
    int ncpu = 1;
    size_t len = sizeof(ncpu);
    if (sysctlbyname("hw.ncpu", &ncpu, &len, NULL, 0) == 0 && ncpu > 0) {
        return ncpu > 64 ? 64 : ncpu;
    }
    return 1;
#else
    return 1;
#endif
}

static void print_usage(FILE *stream) {
    fprintf(stream,
            "Usage: genus_properties [--graph6 FILE | --stdin | --generate-cubic N] [options]\n"
            "\n"
            "Inputs:\n"
            "  --graph6 FILE          Read one graph6 cubic graph per line.\n"
            "  --stdin                Read graph6 records from stdin.\n"
            "  --generate-cubic N     Stream connected non-isomorphic cubic graphs from nauty geng.\n"
            "\n"
            "Options:\n"
            "  --out FILE             Write CSV to FILE instead of stdout.\n"
            "  --threads N            Worker threads (default: online CPU count).\n"
            "  --limit N              Stop after N graph6 records.\n"
            "  --progress-every N     Print progress every N processed graphs (default: 1000).\n"
            "  --skip-invalid         Skip invalid records instead of failing.\n"
            "  --geng PATH            geng executable path/name (default: geng).\n"
            "  --no-automorphisms     Write NA for automorphism_group_order.\n"
            "  --no-matrix-spectra    Write NA for adjacency/laplacian spectra.\n"
            "  --no-spanning-trees    Write NA for spanning_tree_count.\n"
            "  --help                 Show this help.\n");
}

static bool parse_positive_int(const char *text, int *out) {
    char *end = NULL;
    errno = 0;
    long value = strtol(text, &end, 10);
    if (errno || end == text || *end != '\0' || value <= 0 || value > INT32_MAX) {
        return false;
    }
    *out = (int)value;
    return true;
}

static bool parse_size(const char *text, size_t *out) {
    char *end = NULL;
    errno = 0;
    unsigned long long value = strtoull(text, &end, 10);
    if (errno || end == text || *end != '\0') return false;
    *out = (size_t)value;
    return true;
}

static Options parse_options(int argc, char **argv) {
    Options options = {
        .input_stdin = false,
        .input_path = NULL,
        .generate_cubic_n = 0,
        .geng_path = "geng",
        .out_path = NULL,
        .threads = default_thread_count(),
        .limit = 0,
        .progress_every = 1000,
        .skip_invalid = false,
        .compute_automorphisms = true,
        .compute_matrix_spectra = true,
        .compute_spanning_trees = true,
    };

    for (int i = 1; i < argc; ++i) {
        const char *arg = argv[i];
        if (strcmp(arg, "--help") == 0 || strcmp(arg, "-h") == 0) {
            print_usage(stdout);
            exit(0);
        } else if (strcmp(arg, "--stdin") == 0) {
            options.input_stdin = true;
        } else if (strcmp(arg, "--graph6") == 0 || strcmp(arg, "-i") == 0) {
            if (++i >= argc) die("--graph6 needs a path");
            options.input_path = argv[i];
        } else if (strcmp(arg, "--generate-cubic") == 0) {
            if (++i >= argc || !parse_positive_int(argv[i], &options.generate_cubic_n)) {
                die("--generate-cubic needs a positive integer");
            }
        } else if (strcmp(arg, "--geng") == 0) {
            if (++i >= argc) die("--geng needs a path");
            options.geng_path = argv[i];
        } else if (strcmp(arg, "--out") == 0 || strcmp(arg, "-o") == 0) {
            if (++i >= argc) die("--out needs a path");
            options.out_path = argv[i];
        } else if (strcmp(arg, "--threads") == 0 || strcmp(arg, "-j") == 0) {
            if (++i >= argc || !parse_positive_int(argv[i], &options.threads)) {
                die("--threads needs a positive integer");
            }
        } else if (strcmp(arg, "--limit") == 0) {
            if (++i >= argc || !parse_size(argv[i], &options.limit)) {
                die("--limit needs a nonnegative integer");
            }
        } else if (strcmp(arg, "--progress-every") == 0) {
            if (++i >= argc || !parse_size(argv[i], &options.progress_every)) {
                die("--progress-every needs a nonnegative integer");
            }
        } else if (strcmp(arg, "--skip-invalid") == 0) {
            options.skip_invalid = true;
        } else if (strcmp(arg, "--no-automorphisms") == 0) {
            options.compute_automorphisms = false;
        } else if (strcmp(arg, "--no-matrix-spectra") == 0) {
            options.compute_matrix_spectra = false;
        } else if (strcmp(arg, "--no-spanning-trees") == 0) {
            options.compute_spanning_trees = false;
        } else {
            fprintf(stderr, "unknown option: %s\n", arg);
            print_usage(stderr);
            exit(2);
        }
    }

    int input_modes = (options.input_stdin ? 1 : 0) + (options.input_path ? 1 : 0) +
                      (options.generate_cubic_n > 0 ? 1 : 0);
    if (input_modes != 1) {
        die("choose exactly one input mode: --graph6, --stdin, or --generate-cubic");
    }
    if (options.threads < 1) options.threads = 1;
    return options;
}

static void write_csv_header(FILE *out) {
    fprintf(out,
            "index,graph6,n,m,girth,diameter,bipartite,vertex_connectivity,"
            "edge_connectivity,automorphism_group_order,triangle_count,"
            "four_cycle_count,five_cycle_count,six_cycle_count,adjacency_spectrum,"
            "laplacian_spectrum,spanning_tree_count,spectrum,gamma,g_max,"
            "expected_genus,variance,R,R_1,R_2,total_rotation_systems\n");
}

static FILE *open_output(const Options *options) {
    if (!options->out_path) return stdout;
    FILE *out = fopen(options->out_path, "w");
    if (!out) die_errno(options->out_path);
    return out;
}

int main(int argc, char **argv) {
    Options options = parse_options(argc, argv);
    StringVec lines = {0};

    if (options.generate_cubic_n > 0) {
        FILE *out = open_output(&options);
        write_csv_header(out);
        fflush(out);

        StreamQueue queue;
        stream_queue_init(&queue, &options, out);
        pthread_t *threads = calloc((size_t)options.threads, sizeof(*threads));
        if (!threads) die_errno("calloc stream threads");

        for (int i = 0; i < options.threads; ++i) {
            int rc = pthread_create(&threads[i], NULL, stream_worker_main, &queue);
            if (rc != 0) {
                errno = rc;
                die_errno("pthread_create");
            }
        }

        stream_graph6_from_geng(&options, &queue);

        for (int i = 0; i < options.threads; ++i) pthread_join(threads[i], NULL);
        free(threads);

        pthread_mutex_lock(&queue.mutex);
        stream_queue_flush_ready_locked(&queue);
        fflush(queue.out);
        size_t enqueued = queue.enqueued;
        size_t written = queue.written;
        size_t skipped = queue.skipped;
        size_t errors = queue.errors;
        pthread_mutex_unlock(&queue.mutex);

        if (out != stdout) fclose(out);
        stream_queue_destroy(&queue);

        if (enqueued == 0) {
            fprintf(stderr, "error: no graph6 records found\n");
            return 1;
        }
        if (skipped > 0) {
            fprintf(stderr, "Skipped %zu invalid graph%s\n", skipped,
                    skipped == 1 ? "" : "s");
        }
        fprintf(stderr, "Wrote %zu graph row%s\n", written,
                written == 1 ? "" : "s");
        return errors > 0 ? 1 : 0;
    }

    if (options.input_stdin) {
        read_lines_from_stream(stdin, &lines, options.limit);
    } else {
        read_graph6_file(options.input_path, &lines, options.limit);
    }

    if (lines.count == 0) die("no graph6 records found");
    if ((size_t)options.threads > lines.count) options.threads = (int)lines.count;

    Result *results = calloc(lines.count, sizeof(*results));
    pthread_t *threads = calloc((size_t)options.threads, sizeof(*threads));
    if (!results || !threads) die_errno("calloc");

    WorkQueue work = {
        .options = &options,
        .lines = lines.items,
        .count = lines.count,
        .next_index = 0,
        .processed = 0,
        .stop_requested = false,
        .mutex = PTHREAD_MUTEX_INITIALIZER,
        .results = results,
    };

    for (int i = 0; i < options.threads; ++i) {
        int rc = pthread_create(&threads[i], NULL, worker_main, &work);
        if (rc != 0) {
            errno = rc;
            die_errno("pthread_create");
        }
    }
    for (int i = 0; i < options.threads; ++i) pthread_join(threads[i], NULL);

    FILE *out = open_output(&options);
    write_csv_header(out);

    size_t ok_count = 0, skipped_count = 0, error_count = 0;
    for (size_t i = 0; i < lines.count; ++i) {
        if (results[i].ok) {
            fprintf(out, "%s\n", results[i].row);
            ++ok_count;
        } else if (results[i].skipped) {
            ++skipped_count;
            fprintf(stderr, "skipped graph %zu: %s\n", i, results[i].error);
        } else if (results[i].error[0]) {
            ++error_count;
            fprintf(stderr, "failed graph %zu: %s\n", i, results[i].error);
        }
    }
    if (out != stdout) fclose(out);

    for (size_t i = 0; i < lines.count; ++i) free(results[i].row);
    free(results);
    free(threads);
    string_vec_free(&lines);

    if (skipped_count > 0) {
        fprintf(stderr, "Skipped %zu invalid graph%s\n", skipped_count,
                skipped_count == 1 ? "" : "s");
    }
    if (error_count > 0) return 1;
    fprintf(stderr, "Wrote %zu graph row%s\n", ok_count, ok_count == 1 ? "" : "s");
    return 0;
}
