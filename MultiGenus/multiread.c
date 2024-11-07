/* Aufruf: cat Codes | multilies ------- oder
           cat Codes | multilies welchergraph */

#include <limits.h>
#include <memory.h>
#include <stdio.h>
#include <stdlib.h>

#define leer USHRT_MAX

#define KNOTEN 4000
#define MAXVALENCE 100

typedef unsigned short ENTRYTYPE;
typedef ENTRYTYPE GRAPH[KNOTEN + 1][MAXVALENCE + 1];
typedef ENTRYTYPE ADJAZENZ[KNOTEN + 1];

int kantenzahl, maxvalence, welchergraph, codelaenge;
ENTRYTYPE knotenzahl;

schreibegraph(g) GRAPH g;
{
  int x, y, unten, oben;
  fprintf(stdout, "\n\n ");

  if (g[0][0] < 100) {
    fprintf(stdout, "|%2d", g[0][0]);

    for (x = 1; (x <= g[0][0]) && (x <= 24); x++) fprintf(stdout, "|%2d", x);
    fprintf(stdout, "|\n");

    fprintf(stdout, " ");

    for (x = 0; (x <= g[0][0]) && (x <= 24); x++) fprintf(stdout, "|==");
    fprintf(stdout, "|\n");

    for (x = 0; x < maxvalence; x++) {
      fprintf(stdout, " |  ");
      for (y = 1; (y <= g[0][0]) && (y <= 24); y++)
        if (g[y][x] == leer)
          fprintf(stdout, "|  ");
        else
          fprintf(stdout, "|%2d", g[y][x]);
      fprintf(stdout, "|\n");
    }

    unten = 25;
    oben = 48;

    while (g[0][0] >= unten) {
      fprintf(stdout, "\n");

      fprintf(stdout, "    ");

      for (x = unten; (x <= g[0][0]) && (x <= oben); x++)
        fprintf(stdout, "|%2d", x);
      fprintf(stdout, "|\n");

      fprintf(stdout, "    ");

      for (x = unten; (x <= g[0][0]) && (x <= oben); x++)
        fprintf(stdout, "|==");
      fprintf(stdout, "|\n");

      for (y = 0; y < maxvalence; y++) {
        fprintf(stdout, "    ");
        for (x = unten; (x <= g[0][0]) && (x <= oben); x++)
          if (g[x][y] == leer)
            fprintf(stdout, "|  ");
          else
            fprintf(stdout, "|%2d", g[x][y]);
        fprintf(stdout, "|\n");
      }
      unten += 24;
      oben += 24;
    }
  } else if (g[0][0] < 1000) {
    fprintf(stdout, "|%3d", g[0][0]);

    for (x = 1; (x <= g[0][0]) && (x <= 24); x++) fprintf(stdout, "|%3d", x);
    fprintf(stdout, "|\n");

    fprintf(stdout, " ");

    for (x = 0; (x <= g[0][0]) && (x <= 24); x++) fprintf(stdout, "|===");
    fprintf(stdout, "|\n");

    for (x = 0; x < maxvalence; x++) {
      fprintf(stdout, " |   ");
      for (y = 1; (y <= g[0][0]) && (y <= 24); y++)
        if (g[y][x] == leer)
          fprintf(stdout, "|   ");
        else
          fprintf(stdout, "|%3d", g[y][x]);
      fprintf(stdout, "|\n");
    }

    unten = 25;
    oben = 48;

    while (g[0][0] >= unten) {
      fprintf(stdout, "\n");

      fprintf(stdout, "     ");

      for (x = unten; (x <= g[0][0]) && (x <= oben); x++)
        fprintf(stdout, "|%3d", x);
      fprintf(stdout, "|\n");

      fprintf(stdout, "     ");

      for (x = unten; (x <= g[0][0]) && (x <= oben); x++)
        fprintf(stdout, "|===");
      fprintf(stdout, "|\n");

      for (y = 0; y < maxvalence; y++) {
        fprintf(stdout, "     ");
        for (x = unten; (x <= g[0][0]) && (x <= oben); x++)
          if (g[x][y] == leer)
            fprintf(stdout, "|   ");
          else
            fprintf(stdout, "|%3d", g[x][y]);
        fprintf(stdout, "|\n");
      }
      unten += 24;
      oben += 24;
    }
  } else /*if (g[0][0] < 10000)*/
  {
    fprintf(stdout, "|%4d", g[0][0]);

    for (x = 1; (x <= g[0][0]) && (x <= 19); x++) fprintf(stdout, "|%4d", x);
    fprintf(stdout, "|\n");

    fprintf(stdout, " ");

    for (x = 0; (x <= g[0][0]) && (x <= 19); x++) fprintf(stdout, "|====");
    fprintf(stdout, "|\n");

    for (x = 0; x < maxvalence; x++) {
      fprintf(stdout, " |    ");
      for (y = 1; (y <= g[0][0]) && (y <= 19); y++)
        if (g[y][x] == leer)
          fprintf(stdout, "|    ");
        else
          fprintf(stdout, "|%4d", g[y][x]);
      fprintf(stdout, "|\n");
    }

    unten = 20;
    oben = 38;

    while (g[0][0] >= unten) {
      fprintf(stdout, "\n");

      fprintf(stdout, "      ");

      for (x = unten; (x <= g[0][0]) && (x <= oben); x++)
        fprintf(stdout, "|%4d", x);
      fprintf(stdout, "|\n");

      fprintf(stdout, "      ");

      for (x = unten; (x <= g[0][0]) && (x <= oben); x++)
        fprintf(stdout, "|====");
      fprintf(stdout, "|\n");

      for (y = 0; y < maxvalence; y++) {
        fprintf(stdout, "      ");
        for (x = unten; (x <= g[0][0]) && (x <= oben); x++)
          if (g[x][y] == leer)
            fprintf(stdout, "|    ");
          else
            fprintf(stdout, "|%4d", g[x][y]);
        fprintf(stdout, "|\n");
      }
      unten += 19;
      oben += 19;
    }
  }
}

einfugen(graph, adj, v, w) GRAPH graph;
ADJAZENZ adj;
int v, w;
/* Fuegt die Kante (v,w) in den Graphen graph ein. Dabei wird aber davon */
/* ausgegangen, dass in adj die wirklich aktuellen werte fuer die */
/* Adjazenzen stehen. Die adjazenzen werden dann aktualisiert. */

{
  graph[v][adj[v]] = w;
  graph[w][adj[w]] = v;
  adj[v]++;
  adj[w]++;
}

decodiere(code, graph, adj, codelaenge)

    ENTRYTYPE *code;
GRAPH graph;
ADJAZENZ adj;
int codelaenge;

{
  int i, j;
  ENTRYTYPE knotenzahl;

  /*for(i=0;i<codelaenge;i++) printf(" %d ",code[i]); printf("\n");*/

  graph[0][0] = knotenzahl = code[0];

  for (i = 1; i <= knotenzahl; i++) {
    adj[i] = 0;
    for (j = 0; j <= MAXVALENCE; j++) graph[i][j] = leer;
  }
  for (j = 1; j <= MAXVALENCE; j++) graph[0][j] = 0;

  j = 1;

  for (i = 1; i < codelaenge; i++) {
    if (code[i] == 0)
      j++;
    else
      einfugen(graph, adj, j, (int)code[i]);
    if ((adj[code[i]] > MAXVALENCE) || (adj[j] > MAXVALENCE)) {
      fprintf(stderr, "MAXVALENCE too small (%d)!\n", MAXVALENCE);
      exit(0);
    }
  }
}

main(argc, argv)

    int argc;
char *argv[];

{
  GRAPH graph;
  ADJAZENZ adj;
  int zaehlen, i, nuller;
  ENTRYTYPE code[KNOTEN * MAXVALENCE + KNOTEN];
  unsigned char dummy;

  welchergraph = 0;

  if (argc >= 2) sscanf(argv[1], "%d", &welchergraph);

  zaehlen = 0;

  for (; fread(&dummy, sizeof(unsigned char), 1, stdin);) {
    if (dummy != 0) {
      knotenzahl = code[0] = dummy;
      nuller = 0;
      codelaenge = 1;
      while (nuller < knotenzahl - 1) {
        code[codelaenge] = getc(stdin);
        if (code[codelaenge] == 0) nuller++;
        codelaenge++;
      }
    } else {
      fread(code, sizeof(ENTRYTYPE), 1, stdin);
      knotenzahl = code[0];
      nuller = 0;
      codelaenge = 1;
      while (nuller < knotenzahl - 1) {
        fread(code + codelaenge, sizeof(ENTRYTYPE), 1, stdin);
        if (code[codelaenge] == 0) nuller++;
        codelaenge++;
      }
    }

    zaehlen++;
    if ((!welchergraph) || (welchergraph == zaehlen)) {
      decodiere(code, graph, adj, codelaenge);
      for (i = 1, maxvalence = 0; i <= knotenzahl; i++)
        if (adj[i] > maxvalence) maxvalence = adj[i];
      printf("\n\n\n Graph Nr: %d \n\n", zaehlen);
      schreibegraph(graph);
    }
    /*    if (welchergraph == zaehlen) break;*/
  }

  return (0);
}
