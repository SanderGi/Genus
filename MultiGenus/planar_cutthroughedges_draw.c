// compile cc -O4 -o planar_cutthroughedges_draw  planar_cutthroughedges_draw.c -lm
// for options start it with e.g. option h or ?

#include<unistd.h>
#include<stdlib.h>
#include<stdio.h>
#include<ctype.h>
#include<limits.h>
#include <time.h>
#include <string.h>
#include <sys/times.h>
#include <math.h>

#define N 2048
#define SMALLN 150
#define MAXVAL 50  /* maximale valenz */
#define MAXFACE 50 /* maximale Flaechengroesse 255 */
#define MAXCYC 40 // maximum number of cycles looked for
#define MAXCOLOURGENUS 5 // for larger genus, keep labels and generate additional colours programmatically
#define MAXGENUS 20
#define TEXTURESIZE 2048
#define NOTINGRAPH ((-5)*MAXGENUS)
#define RADIUS (100.0)
#define MAXEDGES (N<<5)
#define MAXITERATIONS (INT_MAX/2)
// for the iterations of spring embedder

#define aussen   (N+2) /* so werden kanten nach aussen markiert */

#define infty    LONG_MAX
#define FL_MAX   UCHAR_MAX
#define KN_MAX   USHRT_MAX
#define unbelegt FL_MAX
#define leer     KN_MAX-1
#define f_leer    FL_MAX-1
#define False    0
#define True     1
#define nil      0
#define reg      3


/* Typ-Deklarationen: */

typedef  char BOOL; /* von 0 verschieden entspricht True */


/* Element der Adjazenztabelle: */


typedef struct K {
                   unsigned int ursprung; /* bei welchem knoten startet die kante */
                   unsigned int name;  /* Identifikation des Knotens, mit
                                       dem Verbindung besteht */
                   int cyclenumber; // 0: an edge of the original graph -- possibly subdivided, NOTINGRAPH if only present for the triangulation, otherwise: number of the cutting cycle 
                   int facesize_left; /* die Flaechengroesse links der
					       Kante */
                   unsigned int mark, mark2;
                   int ends[2]; /* in the beginning ursprung and name, but when an original edge is subdivided the ends are copied to the parts */
                   struct K *prev;  /* vorige Kante im Uhrzeigersinn */
                   struct K *next;  /* naechste Kante im Uhrzeigersinn */
		   struct K *invers; /* die inverse Kante (in der Liste von "name") */
                   double wantlength;
                   int edgenumber;
                  } KANTE;

/* "Ueberschrift" der Adjazenztabelle (Array of Pointers): */
typedef KANTE *PLANMAP[N+1];
                  /* Jeweils N KANTEn */
                  /* ACHTUNG: 1. Zeile der Adjazenztabelle hat Index 0 -
                     wird fast nicht benutzt, N Zeilen auch ausreichend
		     In [0][0].name wird aber die knotenzahl gespeichert 
		     und in [0][1].name die Zahl der gerichteten Kanten */

// nv, map, adj, type, startedge, numcycles used everywhere -- as the parameter list grew so long: global!

int globalgenus;
int nv, maxoriginal;// er zullen meer toppen aangemaakt worden dan voor de originele graaf en de nummers zullen ook veranderen,
// maar de originele toppen zullen altijd 1,...,maxoriginal zijn
PLANMAP map={NULL};
int adj[N], type[N]; // type 0: original vertex, 1: subdivision vertex, 2: the center of the cycles, 3: a vertex when triangulated -- just used for placing the others
int is_tree, numberpaths;
int *paths[N/2]={NULL}, pathlength[N/2];
int rememberadj[N]; // remember the degree of the original vertices
char *vertexcolour[N];
char defaultcolour[8]="black";
KANTE *startedge=NULL;
int starttop_t0=0; // will remain 0 if cut with a central vertex in a face, so that comparing a vertex to it is always false
// in case an original vertex is the center it is startedge->ursprung
int nullvertices, numcycles;
// nullvertices=number of vertices of the original graph -- they also have the lowest numbers

int available_edges, used_edges;
KANTE *edgebuffer;
KANTE *edgelist[MAXEDGES];
int maxcross=0, blackwhite=0, forceblackwhite=0, drawvertexnumbers=1, labels=0, straight=0, text=0;
int chosenvertex=0, chosenedge[2]={0};
int firstpage=1;
char *objprefix=NULL;
int objdrawings=0;
int boundary_side[N+1], boundary_cyc[N+1];
double boundary_t[N+1];
char allowedcut[SMALLN][SMALLN];
#define CANBECUT(a,b) (((a)>=SMALLN) || (((b)>=SMALLN)) || allowedcut[a][b])

int cutnext();

static unsigned int markvalue = UINT_MAX, numbermarks=0;
#define RESETMARKS {int mki; numbermarks=0; if (markvalue== UINT_MAX) \
			       { markvalue = 1; for (mki=0;mki<MAXEDGES;mki++) \
			  edgebuffer[mki].mark=0;} else markvalue++;}
#define MARK(e) {(e)->mark = markvalue; numbermarks++; }
#define UNMARK(e) {(e)->mark = 0; numbermarks--; }
#define ISMARKED(e) ((e)->mark == markvalue)
#define UNMARKED(e) ((e)->mark != markvalue)
#define ALLMARKED (numbermarks==used_edges)

static unsigned int markvalue2 = UINT_MAX;
#define RESETMARKS2 {int mki; if (markvalue2== UINT_MAX) \
			       { markvalue2 = 1; for (mki=0;mki<MAXEDGES;mki++) \
			  edgebuffer[mki].mark2=0;} else markvalue2++;}
#define MARK2(e) {(e)->mark2 = markvalue2;}
#define UNMARK2(e) {(e)->mark2 = 0; }
#define ISMARKED2(e) ((e)->mark2 == markvalue2)
#define UNMARKED2(e) ((e)->mark2 != markvalue2)

int dubbel=0;


static unsigned int vmarks[N+1];
#define RESETMARKSV {int mki;  for (mki=1;mki<=N;++mki) vmarks[mki]=0; } 
#define VMARK(a) vmarks[a]=1;
#define VUNMARK(a) vmarks[a]=0;
#define VISMARKED(a) (vmarks[a])
#define VUNMARKED(a) (!(vmarks[a]))
#define VISMARKEDL(a) (vmarks[a]==1)
#define VUNMARKEDL(a) (vmarks[a]!=1)
#define VISMARKEDH(a) (vmarks[a]>1)
#define VUNMARKEDH(a) (vmarks[a]<2)
#define VINCREASEMARK(a) (++vmarks[a])
#define VDECREASEMARK(a) ((vmarks[a]>0)?(--vmarks[a]):0)

#define minf(a) ((a)->edgenumber<(a)->invers->edgenumber?(a)->edgenumber:(a)->invers->edgenumber)

#define vec(v,a,b) { (v)[0]=(b)[0]-(a)[0]; (v)[1]=(b)[1]-(a)[1]; }
#define len(a) (sqrt(((a)[0]*(a)[0])+((a)[1]*(a)[1])))
#define area(a,b,c) (0.5*abs(((a)[0]*(((b)[1]-(c)[1]))) + ((b)[0]*(((c)[1]-(a)[1]))) + ((c)[0]*(((a)[1]-(b)[1])))))
#define area_t(t)  (0.5*abs((coordinates[t[0]][0]*((coordinates[t[1]][1]-coordinates[t[2]][1]))) + (coordinates[t[1]][0]*((coordinates[t[2]][1]-coordinates[t[0]][1]))) \
			    + (coordinates[t[2]][0]*((coordinates[t[0]][1]-coordinates[t[1]][1])))))
#define setcenter_t(x,t) (x)[0]=(coordinates[(t)[0]][0]+coordinates[(t)[1]][0]+coordinates[(t)[2]][0])/3.0; \
  (x)[1]=(coordinates[(t)[0]][1]+coordinates[(t)[1]][1]+coordinates[(t)[2]][1])/3.0;
#define FACTOR (0.25)
#define FACEFACTOR (1.0)


int dbcycle[100],dbcyclelength;

char colours[11][16]={"black","blue","red","green","orange","olive","gray","pink","yellow","lime","cyan"};

char *cyclecolour(int cyclenumber)
{
  static char generated[8][64];
  static int slot=0;
  int n, red, green, blue;

  n=abs(cyclenumber);
  if (forceblackwhite) return "gray";
  if (n<11) return colours[n];

  slot=(slot+1)%8;
  red=(53*n+97)%206+50;
  green=(97*n+53)%206+50;
  blue=(149*n+29)%206+50;
  snprintf(generated[slot],64,"color={rgb,255:red,%d;green,%d;blue,%d}",red,green,blue);
  return generated[slot];
}

char *cyclelabel(int cyclenumber)
{
  static char labels[8][16];
  static int slot=0;
  int n;

  n=abs(cyclenumber);
  slot=(slot+1)%8;
  if (n<=26) snprintf(labels[slot],16,"%c",'A'-1+n);
  else snprintf(labels[slot],16,"%d",n);
  return labels[slot];
}

/***************************SCHREIBEEDGE********************************/

void schreibeedge(char st[], KANTE *edge)
{
  fprintf(stderr,"%s: ",st);
  fprintf(stderr,"%d->%d number %d cyclenumber %d mark %u \n",edge->ursprung, edge->name, edge->edgenumber,edge->cyclenumber, ISMARKED(edge));

}

/**************************SCHREIBEFACES***********************************/

void schreibefaces(char str[])
{
  int i,j,counter;
  KANTE *run, *start;
  RESETMARKS2;
  fprintf(stderr,"-----------------------%s-----------------------------------------\n",str);
  if (nv==0) fprintf(stderr,"Empty graph!\n");
  for (i=counter=1;i<=nv; i++)
    { start=map[i];
      for (j=0; j<adj[i]; j++, start=start->next)
	{
	  if (UNMARKED2(start))
	    { fprintf(stderr,"Face number %d:  %d --(%d,%d,%d) -- ",counter++,start->ursprung,start->cyclenumber,start->edgenumber,start->invers->edgenumber);
	      MARK2(start);
	      for (run=start->invers->next; run!=start; run=run->invers->next)
		{ fprintf(stderr,"%d --(%d,%d,%d) -- ",run->ursprung,run->cyclenumber,run->edgenumber,run->invers->edgenumber);  MARK2(run); }
	      fprintf(stderr,"\n");
	    }
	}
    }
 fprintf(stderr,"----------------------------------------------------------------\n");
}


/**************************SCHREIBEMAP***********************************/

void schreibemap(char str[])
{
  int i;
  KANTE *run, *start;
  fprintf(stderr,"-----------------------%s-----------------------------------------\n",str);
  if (nv==0) fprintf(stderr,"Empty graph!\n");
  for (i=1;i<=nv; i++)
    { start=map[i]; 
      if (adj[i])
	{ fprintf(stderr,"%d (deg: %d, type: %d): %d(%d, %d, %d [%d])",i,adj[i],type[i],start->name,start->cyclenumber,start->edgenumber,start->invers->edgenumber,ISMARKED(start));
	  for (run=start->next; run!=start; run=run->next) fprintf(stderr," %d(%d, %d, %d)[%d]",run->name,run->cyclenumber, run->edgenumber,run->invers->edgenumber, ISMARKED(run));
	  fprintf(stderr,"\n");
	}
      else  fprintf(stderr,"%d (0): \n",i);
    }
 fprintf(stderr,"----------------------------------------------------------------\n");
 schreibefaces("the faces:\n");
}

void getgenustest(char str[])
{
  int i,j,counter,edges;
  KANTE *run, *start;

   if (nv==0) fprintf(stderr,"Empty graph!\n");
   
  RESETMARKS2;
  for (i=1, edges=0;i<=nv; i++)
    {if (adj[i])
      { edges++;
	for (run=map[i]->next; run!=map[i]; run=run->next) edges++;
	}
    }

  if (edges&1) { fprintf(stderr,"odd number of oriented edges...\n"); exit(1); }

  edges=edges/2;

  for (counter=0, i=1; i<=nv; i++)
    { start=map[i];
      for (j=0; j<adj[i]; j++, start=start->next)
	{
	  if (UNMARKED2(start))
	    { counter++; 
	      MARK2(start);
	      for (run=start->invers->next; run!=start; run=run->invers->next)
		{ MARK2(run); }
	    }
	}
    }
  fprintf(stderr,"%s",str);
  fprintf(stderr,"Euler characteristic %d\n",nv-edges+counter);
}

void testgraph(char str[])
{
  int i,j;
  KANTE *run,*remember;

  for (i=1; i<=nv; i++)
    {
      if ((run=map[i])==NULL) { fprintf(stderr,"NULL pointer in map: nv=%d map[%d]=NULL  ---- %s \n",nv,i,str); exit(1); }
      for (remember=run, j=0; j<adj[i]; j++, run=run->next)
	{ if (run->next->prev!=run) { fprintf(stderr,"A ---- %s \n",str); exit(1); }
	  if (run->prev->next!=run) { fprintf(stderr,"B ---- %s \n",str); exit(1); }
	  if (run->invers->invers!=run)  { fprintf(stderr,"C ---- %s \n",str); exit(1); }
	  if (run->ursprung != i) { fprintf(stderr,"D ---- %s \n",str); exit(1); }
	  if ((run->name < 1) || (run->name>nv)) { fprintf(stderr,"F vertex %d (nv=%d) boog %d->%d ---- %s \n",i,nv,run->ursprung,run->name,str); exit(1); }
	}
      if (run!=remember) { fprintf(stderr,"H ---- %s \n",str); exit(1); }
    }
}

KANTE *getedge()
{
  if (available_edges==0) { fprintf(stderr,"Not enough edges -- increase MAXEDGES\n"); exit(0); }
  available_edges--; used_edges++;
  return edgelist[available_edges];
}

void returnedge(KANTE *edge)
{
  edgelist[available_edges]=edge;
  available_edges++; used_edges--;
}

void cleargraph()
{
  int i,j;
  KANTE *run;
  
  for (i=1;i<=nv;i++)
    { run=map[i];
      for (j=0;j<adj[i];j++) { returnedge(run); run=run->next; }
      map[i]=NULL;
    }
  nv=0;
  startedge=NULL;
  for (i=0;i<=N;i++)
    {
      boundary_side[i]=(-1);
      boundary_cyc[i]=0;
      boundary_t[i]=0.0;
    }

}

void remove_edge(KANTE *edge)
// removes the edge and its inverse from the graph
{ int start;

  start=edge->ursprung;
   if (adj[start]==1)
    { map[start]=NULL;
      adj[start]=0;
    }
  else
    {
      if (map[start]==edge) map[start]=edge->next;
      edge->next->prev=edge->prev;
      edge->prev->next=edge->next;
      adj[start]--;
    }

   edge=edge->invers;

   start=edge->ursprung;
   if (adj[start]==1)
     { map[start]=NULL;
       adj[start]=0;
     }
   else
     {
       if (map[start]==edge) map[start]=edge->next;
       edge->next->prev=edge->prev;
       edge->prev->next=edge->next;
       adj[start]--;
     }

   returnedge(edge->invers); returnedge(edge);
}

/************************COUNT_FACES*******************/

int count_faces_and_get_facesizes( )

{
  KANTE *run, *run2;
  int i, j, k;
  int faces=0, size;

  RESETMARKS;

  for (i=1;i<=nv;i++)
    {run2=map[i];
      for (j=0; j<adj[i];j++)
	{ run=run2; run2=run2->next;
	  if (UNMARKED(run))
	    { 
	      faces++;
	      for (size=0; UNMARKED(run); run=run->invers->next) { size++; MARK(run); }
	      for (k=0; k<size; k++, run=run->invers->next) run->facesize_left=size;
	    }
	}
    }

  return faces;
}

/*************************DECODIEREPLANAR******************************/

void decodiereplanar(unsigned short* code, int *nv, PLANMAP map, int adj[N], int type[])
{
  int i,j,k,puffer,zaehler, bufferzaehler, lnv, ne=0, marks[N];
  KANTE *buffer[N], *run, *run2;

*nv = lnv= nullvertices = maxoriginal = code[0];

 if (*nv>=SMALLN) { fprintf(stderr,"Constant SMALLN too small. Increase to at least %d and recompile.\n",(*nv)+1); exit(1); }

zaehler=1;

for(i=1;i<=lnv; i++)
  { adj[i]=type[i]=0;
    for(j=0, bufferzaehler=zaehler; code[bufferzaehler]; j++, bufferzaehler++)
      buffer[j]=getedge();
    if (j) map[i]=buffer[0]; else map[i]=NULL;
      for(j=0; code[zaehler]; j++, zaehler++) 
	{
	  buffer[j]->name=(buffer[j]->ends)[0]=code[zaehler];
	  buffer[j]->ursprung=(buffer[j]->ends)[1]=i;
	  buffer[j]->cyclenumber=0;
	  buffer[j]->facesize_left=0;
	  //if (code[zaehler]>i) { kantenzaehler++; buffer[j]->kantennummer=kantenzaehler; }
	}
      adj[i]=j;
      ne+=j;
      for(j=1, k=0; j<adj[i]; j++, k++)     
	{ buffer[j]->prev=buffer[k]; buffer[k]->next=buffer[j]; }
      buffer[0]->prev=buffer[adj[i]-1]; buffer[adj[i]-1]->next=buffer[0];
      zaehler++; /* 0 weglesen */
    }

/* Die folgende Methode ist prinzipiell zwar leider quadratisch, hat aber den Vorteil,
   keinen zusaetzlichen Speicher zu verbrauchen und in der Praxis trotzdem schnell zu
   sein: */

for(i=1;i<= lnv;i++)
  { 
    for(j=0, run=map[i]; j<adj[i]; j++, run=run->next) if (run->name > i)
	{ puffer=run->name;
	  for ( run2=map[puffer]; run2->name != i; run2=run2->next);
	  run->invers=run2;
	  run2->invers=run;
	  //map[puffer][k].kantennummer = -(map[i][j].kantennummer);
	}
    }

 if (ne!=((lnv-1)<<1)) is_tree=0;
 else
   {
     int length;
     is_tree=1;
     for(i=1;i<= lnv;i++) marks[i]=0;
     numberpaths=0;
     for(i=1;i<= lnv;i++)
       if ((adj[i]==2) && (marks[i]==0))
	 {
	   if (paths[numberpaths]==NULL) paths[numberpaths]=malloc(sizeof(int)*N);
	   if (paths[numberpaths]==NULL) { fprintf(stderr,"Can't get memory -- exit()\n"); exit(1); }
	   marks[i]=1;
	   run=map[i];
	   while ((marks[run->name]==0) && (adj[run->name]==2)) { run=run->invers->next; }
	   // marks worden getest om bij onsamenhangende grafen met cykel geen oneindige lus te hebben
	   run=run->invers;
	   paths[numberpaths][0]=run->ursprung;
	   length=0;
	   while (adj[run->name]==2)
	     { marks[run->name]=1; length++; paths[numberpaths][length]=run->name; run=run->invers->next; }
	   length++; paths[numberpaths][length]=run->name; 
	   pathlength[numberpaths]=length;
	   numberpaths++;
	 }
   }
 return;
}

/**************************LESECODE_TEXT*******************************/

int lesecode_text(unsigned short code[], int *laenge)
{
  int j, nullenzaehler,lauf;
  unsigned short sh; 

  if (((lauf=scanf("%d",&j))==0) || (lauf==EOF)) return 0; 
  code[0]=(unsigned short)j; 
  lauf=1;
  for (nullenzaehler=0; nullenzaehler<j; lauf++)
    { if (scanf("%hd",code+lauf)==0) { fprintf(stderr,"Incorrect code -- early end!\n"); exit(0); }
	if (code[lauf]==0) nullenzaehler++;
      }

  *laenge=lauf;

  return 1;
  }


/**************************LESECODE*******************************/

int lesecode(unsigned short code[], int *laenge, FILE *file)
/* gibt 1 zurueck, wenn ein code gelesen wurde und 0 sonst */
{

unsigned char ucharpuffer;
int lauf, nullenzaehler;

 if (text) return lesecode_text(code, laenge);

if (fread(&ucharpuffer,sizeof(unsigned char),1,file)==0) return(0);

if (ucharpuffer=='>') /* koennte ein header sein -- oder 'ne 62, also ausreichend fuer
			     unsigned char */
  { code[0]=ucharpuffer;
    lauf=1; nullenzaehler=0;
    code[1]=(unsigned short)getc(file);
    if(code[1]==0) nullenzaehler++; 
    code[2]=(unsigned short)getc(file);
    if(code[2]==0) nullenzaehler++; 
    lauf=3;
    /* jetzt wurden 3 Zeichen gelesen */
    if ((code[1]=='>') && ((code[2]=='p') || (code[2]=='e')) ) /*garantiert header*/
      { while ((ucharpuffer=getc(file)) != '<');
	/* noch zweimal: */ ucharpuffer=getc(file); 
	if (ucharpuffer!='<') { fprintf(stderr,"Problems with header -- single '<'\n"); exit(1); }
	if (!fread(&ucharpuffer,sizeof(unsigned char),1,file)) return(0);
	/* kein graph drin */
	lauf=1; nullenzaehler=0; }
    /* else kein header */
  }
else { lauf=1; nullenzaehler=0; }

if (ucharpuffer!=0) /* kann noch in unsigned char codiert werden ... */
  {
    code[0]=ucharpuffer;
    if (code[0]>N) { fprintf(stderr,"Constant N too small %d > %d \n",code[0],N); exit(1); }
    while(nullenzaehler<code[0])
      { code[lauf]=(unsigned short)getc(file);
	if(code[lauf]==0) nullenzaehler++;
	lauf++; }
  }
else  {
  if (!fread(code,sizeof(unsigned short),1,file)) { fprintf(stderr,"Problem reading -- exit.\n"); exit(1); }
	if (code[0]>N) { fprintf(stderr,"Constant N too small %d > %d \n",code[0],N); exit(1); }
	lauf=1; nullenzaehler=0;
	while(nullenzaehler<code[0])
	  { if (!fread(code+lauf,sizeof(unsigned short),1,file)) { fprintf(stderr,"Problem reading -- exit.\n"); exit(1); }
	    if(code[lauf]==0) nullenzaehler++;
	    lauf++; }
      }

*laenge=lauf;
return(1);
}

/******************codiere_und_schreibe********************/

void codiere_und_schreibe(int nv, PLANMAP map, int adj[])
{
unsigned char code[7*N+2];
unsigned short scode[7*N+2];
 int i,j,codelaenge;
 KANTE *run;
 
  if (nv<=UCHAR_MAX)
    {
      code[0]=nv;
      codelaenge=1;
      for (i=1;i<=nv;i++)
	{ run=map[i];
	  for (j=0;j<adj[i];j++)
	    { code[codelaenge]=run->name;
	      codelaenge++;
	      run=run->next;
	    }
	  code[codelaenge]=0;   codelaenge++;
	}
      fwrite(code,sizeof(unsigned char),codelaenge,stdout);
    }
  else
    {
      if (nv<=USHRT_MAX)
	{putchar(0);
	  scode[0]=nv;
	  codelaenge=1;
	  for (i=1;i<=nv;i++)
	    { run=map[i];
	      for (j=0;j<adj[i];j++)
		{ scode[codelaenge]=run->name;
		  codelaenge++;
		  run=run->next;
		}
	      scode[codelaenge]=0;   codelaenge++;
	    }
	  fwrite(scode,sizeof(unsigned short),codelaenge,stdout);
	}
      else { fprintf(stderr,"More than %d vertices? Get serious... Exit.\n",USHRT_MAX); exit(1); }
    }
}


/***********************CHECK_CON********************/


int search_on(KANTE *edge)
// runs around a face and switches face when graph edge is found
{
  KANTE *run;

 
  for (run=edge->invers->next; (run!=edge) ; run=run->invers->next) // run has already been marked
    {
      if (ISMARKED(run)) return 0;
      else
	{ MARK(run); 
	  if (ALLMARKED) { return 1; }
	  if (run->cyclenumber==0)
	    {
	      MARK(run->invers); 
	      if (ALLMARKED) { return 1; }
	      if (search_on(run->invers)) return 1;
	    }
	}
    }
  return 0;
}

int check_con(KANTE *edge)
// checks whether one can go through all faces without ever crossing an edge with cyclenumber!=0
{
  KANTE *run;

  RESETMARKS;
  run=edge;

  do
    {
      if (ISMARKED(run)) return 0; // the following edges were evaluated by the iteration marking that edge -- and still not all are marked...
      else
	{
	  MARK(run); 
	  if (ALLMARKED) return 1;
	  if (run->cyclenumber==0)
	    {
	      MARK(run->invers); 
	      if (ALLMARKED) return 1;
	      if (search_on(run->invers)) return 1;
	    }
	}
      run=run->invers->next;
    }
  while (run!=edge);

      return 0;
}

void undo_subdiv_edge(KANTE *edge)
// must be called for the edge returned by subdiv_edge(). The subdivided vertex must have only the neighbours it had after subdividing
 {
   KANTE *run;

   run=edge->next;
   edge->invers->name=run->name;
   run->invers->name=edge->name;
   edge->invers->invers=run->invers;
   run->invers->invers=edge->invers;
   map[edge->ursprung]=NULL; adj[edge->ursprung]=0;
   returnedge(run); returnedge(edge);
   nv--;
   //testgraph("undo subdiv");
}

KANTE *subdiv_edge(KANTE *edge)
// subdivides the original edge and returns the edge starting at the new vertex and in the same direction as edge
// the addresses of the edges leaving the two end vertices are not changed!
{
  KANTE *first, *second;
  int nextone;

  nv++; if (nv>N) { fprintf(stderr,"Too many vertices (including the extra vertices used for the construction) for constant N=%d -- exit.\n",N); exit(1); }
  type[nv]=1;
  nextone=nv;
  adj[nextone]=2;
  first=map[nextone]=getedge(); second=getedge();
  first->ursprung=second->ursprung=nextone;
  first->name=edge->ursprung; second->name=edge->name;
  (first->ends)[0]= (second->ends)[0]=(edge->ends)[0];
  (first->ends)[1]= (second->ends)[1]=(edge->ends)[1];
  first->next=first->prev=second;  second->next=second->prev=first;
  first->cyclenumber=second->cyclenumber=edge->cyclenumber;
  first->facesize_left=second->facesize_left=0; // in fact undefined
  first->invers=edge; second->invers=edge->invers;
  edge->invers=first; edge->name=nextone;
  second->invers->invers=second; second->invers->name=nextone;
  return second;
}

void undo_newvertex(KANTE *edge)
// the graph must be in the state as just after adding the vertex that is to be deleted. edge must be the edge returned by newvertex
{

  map[nv]=NULL; adj[nv]=0; nv--;
  adj[edge->name]--;
  edge=edge->invers;
  edge->next->prev=edge->prev;
  edge->prev->next=edge->next;
  returnedge(edge->invers); returnedge(edge);
  undo_subdiv_edge(edge->next);
}


KANTE *newvertex(KANTE *edge, int cycnum)
// subdivides edge and adds a new vertex in the face left of edge and connects it to the center of the edge
// returns the edge starting at the new vertex;
{
  KANTE *new, *newe, *neweinv;
  int nextone;

  new=subdiv_edge(edge);

  nv++; if (nv>N) { fprintf(stderr,"Too many vertices (including the extra vertices used for the construction) for constant N=%d -- exit.\n",N); exit(1); }
  type[nv]=2;
  nextone=nv;
  newe=getedge(); neweinv=getedge();
  adj[nextone]=1; map[nextone]=newe;
  newe->invers=neweinv; neweinv->invers=newe;
  newe->ursprung=neweinv->name=nextone;
  neweinv->ursprung=newe->name=new->ursprung;
  newe->next=newe->prev=newe;
  neweinv->next=new; neweinv->prev=new->prev; 
  new->prev->next=neweinv;  new->prev=neweinv;
  newe->cyclenumber=neweinv->cyclenumber=cycnum;
  newe->facesize_left=neweinv->facesize_left=0;
  adj[newe->name]++;
  return newe; 
}


void undo_connect(KANTE *e)
// removes the new edge e, which must have endpoints of degree more than 1
{
  e->next->prev=e->prev;
  e->prev->next=e->next;
  adj[e->ursprung]--;
  e=e->invers;
  e->next->prev=e->prev;
  e->prev->next=e->next;
  adj[e->ursprung]--;
 
  returnedge(e->invers); returnedge(e);
}


KANTE *connect(KANTE *e1, KANTE *e2, int cyclenumber)
// connects the end of e1 with the end of e2. In the rotational order the new edge is added in next direction of
// the inverse of these edges
// returns the new edge starting at e1->name
{
  KANTE *newe, *neweinv, *e1next, *e2next;

  newe=getedge(); neweinv=getedge();
  newe->cyclenumber=neweinv->cyclenumber=cyclenumber;
  e1=e1->invers; e2=e2->invers;
  e1next=e1->next; e2next=e2->next;

  newe->invers=neweinv; neweinv->invers=newe;
  newe->name=neweinv->ursprung=e2->ursprung;
  neweinv->name=newe->ursprung=e1->ursprung;

  newe->next=e1next; newe->prev=e1;
  e1next->prev=e1->next=newe;
  adj[e1->ursprung]++;

   neweinv->next=e2next; neweinv->prev=e2;
  e2next->prev=e2->next=neweinv;
  adj[e2->ursprung]++;

  return newe;
  
}


int makecycle(KANTE *edge, int startpoint, int length, int maxlength, int cyclenumber, int multicross)
// edge points to an original edge that must be crossed. This function iterates over all possibilities to cross the
// face on the other side, resp. 
{
  KANTE *run, *end, *newedge, *subdivedge;

  if (adj[edge->name]!=3)
    {
    fprintf(stderr,"Degree should be 3... exit(1);\n");
    schreibeedge("edge",edge);
    schreibemap("problem");
    exit(1); }

  edge=edge->invers;
  run=edge->prev->invers->next;
  end=edge->next->invers;

    
  if (length==maxlength) // then startpoint must be in this face or one can return 0
    { 
      for ( ; run!=end; run=run->invers->next)
	{
	  if (run->name==startpoint)
	    {
	      newedge=connect(end,run,cyclenumber);
	      if (check_con(run))
		{
		  if (cyclenumber==numcycles) return 1;
		  //else
		  if (cutnext(cyclenumber+1,maxlength,multicross)) return 1;
		}
	      undo_connect(newedge);
	    }
	}
      return 0;
    }
  // else if startpoint is in the face it can not be the aim, as that was tested before

 
  while (run!=end)
    {
      if (CANBECUT(run->ursprung,run->name) && (run->cyclenumber==0) // don't cross cutedges
	  &&  (type[run->ursprung]==0) && (type[run->name]==0)) // first try edges that were not subdivided before
	{
	  subdivedge=subdiv_edge(run);
	  newedge=connect(edge->next->invers,subdivedge->prev->invers,cyclenumber);
	  if (makecycle(newedge,startpoint,length+1,maxlength,cyclenumber,multicross)) return 1;
	  undo_connect(newedge);
	  undo_subdiv_edge(subdivedge);
	}
      run=run->invers->next;
    }

  if (multicross)
    {
      run=edge->prev->invers->next;
      while (run!=end)
	{
	  if (	CANBECUT(run->ursprung,run->name) && (run->cyclenumber==0) // don't cross cutedges
	      &&  ((type[run->ursprung]!=0) || (type[run->name]!=0)))  // then try edges that were subdivided before -- that is: the rest
	    {
	      subdivedge=subdiv_edge(run);
	      newedge=connect(edge->next->invers,subdivedge->prev->invers,cyclenumber);
	      if (makecycle(newedge,startpoint,length+1,maxlength,cyclenumber,1)) return 1;
	      undo_connect(newedge);
	      undo_subdiv_edge(subdivedge);
	    }
	  run=run->invers->next;
	}
    }

  return 0;
}

#define MAX(a,b) ((a)>(b)?(a):(b))
#define MIN(a,b) ((a)>(b)?(b):(a))

int  cutnext(int cycnum, int minlength, int multicross)
 // returns one if a way to cut it properly is found -- otherwise 0
// tries to start in each angle around startedge->ursprung
// the length of the cycles increases -- if there was a shorter one it would have been found before
 {
   int maxlength;
   int found=0,k;
   KANTE *run, *start, *startbuf, *subdivedge, *newedge, *endedge;


   if (cycnum>numcycles) { fprintf(stderr,"Problem -- cycnum too large -- exit.\n"); exit(1); }

   if (minlength==0)
     {
       // first check whether there is a way to cut it without crossing a single edge
       startbuf=startedge;
       for (k=0;k<adj[starttop_t0];k++, startbuf=startbuf->next)
	 { start=startbuf->invers->next; endedge=startbuf->prev->invers;
	   for ( ; start != endedge; start=start->invers->next)
	     if (start->name==starttop_t0) 
	       {
		 run=connect(endedge,start,cycnum);
		 // startedge is the global variable remembering the start
		 if (check_con(run))
		   {
		     if (cycnum==numcycles) return 1;
		     // else
		     if (cutnext(cycnum+1, 0, multicross)) return 1;
		   }
		 undo_connect(run);
	       }
	 }
     }
 
   for (maxlength=MAX(minlength,1); !found && (multicross || (maxlength<=maxcross)); maxlength++)
     {
       startbuf=startedge; endedge=startedge->prev->invers;
       do // first test edges that haven't been subdivided before -- for the same number of crossings prefer fewer crossing per edge
	 // -- but of course it is some local decision -- no global optimum guaranteed
	 {
	   for (run=startbuf->invers->next; !found && (run!=endedge); run=run->invers->next)
	     if ( CANBECUT(run->ursprung,run->name) && (type[run->ursprung]==0) && (type[run->name]==0))  // in case of starttop_t0 it has type 2
	       {
	       subdivedge=subdiv_edge(run);
	       newedge=connect(startbuf->prev->invers,subdivedge->prev->invers,cycnum);
	       if (makecycle(newedge,startedge->ursprung,1,maxlength,cycnum,multicross)) return 1;
	       undo_connect(newedge);
	       undo_subdiv_edge(subdivedge);
	     }
	   endedge=startbuf->invers; startbuf=startbuf->next; 
	 }
       while (startbuf!=startedge);

       // then those that have been subdivided before
       if (multicross)
	 {
	   startbuf=startedge; endedge=startedge->prev->invers;
	   do 
	     {
	       for (run=startbuf->invers->next; !found && (run!=endedge); run=run->invers->next)
		 if (CANBECUT(run->ursprung,run->name) && (run->ursprung!=starttop_t0) && (run->name!=starttop_t0)
		     &&  ((type[run->ursprung]!=0) || (type[run->name]!=0))) // to make sure they were not tested before  
		   {
		     subdivedge=subdiv_edge(run);
		     newedge=connect(startbuf->prev->invers,subdivedge->prev->invers,cycnum);
		     if (makecycle(newedge,startedge->ursprung,1,maxlength,cycnum,1)) return 1;
		     undo_connect(newedge);
		     undo_subdiv_edge(subdivedge);
		   }
	       endedge=startbuf->invers; startbuf=startbuf->next;
	     }
	   while (startbuf!=startedge);
	 }
     }
  
   return found;
 }


int bfsdist_face(KANTE *start)
// computes the maximum distance of a vertex from the closest vertex in the face left of run
{
  int i, j, list[N+1], ll, dist[N+1], top, top2;
  KANTE *run;

  RESETMARKSV;

  for (i=ll=0; i<(start->facesize_left); i++, start=start->invers->next)
    { top=start->ursprung;
      if (VUNMARKED(top)) // in case of not simple faces
	{ VMARK(top);
	  list[ll]=top; dist[ll]=0; ll++;
	}
    }

  for (i=0; i<ll; i++)
    { top=list[i];
       run=map[top];
       for (j=0;j<adj[top]; j++, run=run->next)
	 if (VUNMARKED(run->name))
	   {
	     if (ll==(nv-1)) return (dist[i]+1); // this would be the last vertex in the list
	     top2=run->name;
	     VMARK(top2);
	     list[ll]=top2; dist[ll]= (dist[i]+1); ll++;
	   }
    }

  // should never get here, but:

  return (dist[ll-1]);
}


int bfsdist_vertex(int starttop)
{
  int i, j, list[N+1], ll, dist[N+1], top, top2;
  KANTE *run;

  RESETMARKSV;

  list[0]=starttop; ll=1;
  VMARK(starttop);
  dist[0]=0;

  for (i=0; i<ll; i++)
    { top=list[i];
       run=map[top];
       for (j=0;j<adj[top]; j++, run=run->next)
	 if (VUNMARKED(run->name))
	   {
	     if (ll==(nv-1)) return (dist[i]+1); // this would be the last vertex in the list
	     top2=run->name;
	     VMARK(top2);
	     list[ll]=top2; dist[ll]= (dist[i]+1); ll++;
	   }
    }

  // should never get here, but:

  return (dist[ll-1]);
}

int faceOK(KANTE *start)
// checks whether the face contains an edge that can be cut
{
  KANTE *run;
  
  if (CANBECUT(start->ursprung,start->name)) return 1;

  for (run=start->invers->next; run!=start; run=run->invers->next)  if (CANBECUT(run->ursprung,run->name)) return 1;

  return 0;

}

int  cutit()
 // returns one if a way to cut it properly is found -- otherwise 0
 {
   int i,j,maxlength,buffer;
   int found=0, maxdist,maxface;
   KANTE *run, *run2, *startbuf, *start; // the cycles will start at start->ursprung -- a new vertex in the center of the largest face

   startbuf=NULL;
    if ((chosenedge[0]>=1) && (chosenedge[0]<=nv) &&  (chosenedge[1]>=1) && (chosenedge[1]<=nv))
      {
	run=map[chosenedge[0]];
	for (i=0; i<adj[chosenedge[0]]; i++, run=run->next)
	  if (run->name==chosenedge[1]) { startbuf=run; i=N; }
	if (startbuf && !faceOK(startbuf)) { fprintf(stderr,"All edges of chosen face must not be cut. Exit.\n");   exit(1); }
      }

    if (startbuf==NULL)
      {
	for (i=1;i<=nv;i++)
	  { run=map[i];
	    for (j=0; j<adj[i];j++, run=run->next)
	      { if (faceOK(run) && ((startbuf==NULL) || (startbuf->facesize_left<run->facesize_left))) startbuf=run; }
	  }

	if (startbuf==NULL)  { fprintf(stderr,"Can't find a face with edges that are allowed to be cut. \n");   exit(1); }
	maxface=startbuf->facesize_left;
	RESETMARKS;
	MARK(startbuf);
	maxdist=bfsdist_face(startbuf);
	for (run=startbuf->invers->next; run!=startbuf; run=run->invers->next) MARK(run);
	
	for (i=1;i<=nv;i++)
	  { run=map[i];
	    for (j=0; j<adj[i];j++, run=run->next)
	      { if (faceOK(run) && (run->facesize_left==maxface) && UNMARKED(run))
		  {
		    MARK(run);
		    for (run2=run->invers->next; run2!=run; run2=run2->invers->next) MARK(run2);
		    if ((buffer=bfsdist_face(run))>maxdist)
		      {
			maxdist=buffer; startbuf=run;
		      }
		  }
	      }
	  }
      }

 
   // first try not to cut through the same edge twice -- and give a maximum number of edges that a cycle crosses -- defined as maxcross
   if (startbuf->facesize_left>=2*numcycles)
     {
       // omdat einde en begin van de cykel er niet toedoet, 1 boog overslaan -- maar meer niet omdat de cykels met stijgende lengte gezocht worden
       for (maxlength=1; maxlength<=maxcross; maxlength++)
	 for (start=startbuf->invers->next; start != startbuf; start=start->invers->next)
	   if (CANBECUT(start->ursprung,start->name))
	   {
	     run=startedge=newvertex(start,1);
	     if (makecycle(run,run->ursprung,1,maxlength,1,0)) return 1;
	     undo_newvertex(run);
	   }
     }

   // then try everything
   for (maxlength=1; 1 ; maxlength++)
     for (start=startbuf->invers->next; !found && (start != startbuf); start=start->invers->next) // omdat einde en begin  van de cykel er niet toedoet, 1 boog overslaan
        if (CANBECUT(start->ursprung,start->name))
	  {
	    run=startedge=newvertex(start,1);
	    if (makecycle(run,run->ursprung,1,maxlength,1,1)) return 1;
	    undo_newvertex(run);
	  }

   return 0; // should never be reached
 }

/***************************************************************************************************/

void rek_mark(int dfsnummer[], int kb[], int is_cut[], int *nextnummer, int top, int from)
{
  int i, top2;
  KANTE *run;

  dfsnummer[top]=kb[top]=*nextnummer;
  (*nextnummer)++;

  for (i=0,run=map[top]; i<adj[top]; i++, run=run->next)
    {
      top2=run->name;
      if (top2!=from)
	{
	  if (dfsnummer[top2]==0)
	    {
	      rek_mark(dfsnummer, kb, is_cut, nextnummer, top2, top);
	      if (kb[top2]>=dfsnummer[top]) is_cut[top]=1;
	    }
	  if (kb[top2]<kb[top]) kb[top]=kb[top2];
	}
    }
}

void mark_cutvertices(int is_cut[])
{
  int i, nextnummer;
  int dfsnummer[N+1], kb[N+1];
  KANTE *run;

  for (i=1;i<=nv;i++) { is_cut[i]=dfsnummer[i]=0; kb[i]=INT_MAX; }

  dfsnummer[1]=kb[1]=1;
  nextnummer=2;

  run=map[1]; 
  rek_mark(dfsnummer, kb, is_cut, &nextnummer, run->name,1);
      
  for (i=1, run=run->next; i<adj[1]; run=run->next, i++)
    if (dfsnummer[run->name]==0)
      { is_cut[1]=1; 
	rek_mark(dfsnummer, kb, is_cut, &nextnummer, run->name,1);
      }
 }



/******************************************CUTIT_V***************************************/

int  cutit_v()
// returns one if a way to cut it properly is found -- otherwise 0
// cuts with a central vertex from the graph -- not a center of a face -- but always through edges
{
  int i,j,k, maxlength,buffer, counter, starttop, edgestocut;
   int maxdist=0;
   KANTE *run, *run2, *startbuf, *start, *end; // the cycles will start at start->ursprung -- a new vertex in the center of the largest face
   int is_cut[N+1];

   // Search for the non-cutvertex so that the sum of the face sizes around is maximum -- this way there are many edges to cut through.
   // The choice for a non-cutvertex is not necessary -- just a choice. In the rare case that all vertices are cutvertices, this condition is dropped.
   // If faces are not simple, edges are counted twice -- once for every direction.
   // Among equal ones, one with smallest maximum distance of other vertices is chosen.

   if ((chosenvertex>=1) && (chosenvertex<=nv))
     {
       starttop_t0=starttop=chosenvertex;
       counter= (-2*adj[starttop]);
       run=map[starttop];
       for (j=0;j<adj[starttop];j++, run=run->next) counter+=run->facesize_left;
       edgestocut=counter; 
     }
   else
     {
       mark_cutvertices(is_cut);
       
       for (i=1, starttop=0, edgestocut=0; i<=nv; i++)
	 if (!is_cut[i])
	   { run=map[i];
	     counter= (-2*adj[i]);
	     for (j=0;j<adj[i];j++, run=run->next) counter+=run->facesize_left;
	     if (counter>edgestocut) { edgestocut=counter; starttop=i; maxdist=bfsdist_vertex(i); }
	     else if ((counter==edgestocut) && ((buffer=bfsdist_vertex(i))>maxdist))
	       { starttop=i; maxdist=buffer; }
	   }
       
       if (starttop==0)
	 for (i=1, starttop=0, edgestocut=0; i<=nv; i++)
	   { run=map[i];
	     counter= (-2*adj[i]);
	     for (j=0;j<adj[i];j++, run=run->next) counter+=run->facesize_left;
	     if (counter>edgestocut) { edgestocut=counter; starttop=i; maxdist=bfsdist_vertex(i); }
	     else if ((counter==edgestocut) && ((buffer=bfsdist_vertex(i))>maxdist))
	       { starttop=i; maxdist=buffer; }
	   }
       starttop_t0=starttop;
     }


   // Now we know one starttop with the maximum number of edges to subdivide (in a meaningful way)
   type[starttop]=2;

   // first check whether there is a way to cut it without crossing a single edge
   startbuf=map[starttop];
   for (k=0;k<adj[starttop];k++, startbuf=startbuf->next)
     { start=startbuf->invers->next; end=startbuf->prev->invers;
       for ( ; start != end; start=start->invers->next)
	 if (start->name==starttop) 
	 {
	   run2=startedge=connect(end,start,1);
	   // startedge is the global variable remembering the start
	   if (check_con(run2))
	     {
	       if (cutnext(2, 0, 0)) return 1;
	     }
	   undo_connect(run2);
	 }
     }


   // first try not to cut through the same edge twice -- and give a maximum number of edges that a cycle crosses -- defined as maxcross
   if (edgestocut>=2*numcycles)
     {
       // omdat de cykels met stijgende lengte gezocht worden ook voor de eerste cykel al alle bogen toetsen -- 1 boog zou overgeslagen kunnen worden.
       for (maxlength=1; maxlength<=maxcross; maxlength++)
	 {
	   startbuf=map[starttop];
	   for (k=0;k<adj[starttop];k++, startbuf=startbuf->next)
	     { start=startbuf->invers->next; end=startbuf->prev->invers;
	       for ( ; start != end; start=start->invers->next)
		 if (CANBECUT(start->ursprung,start->name))
		 {
		   run=subdiv_edge(start);
		   // the end vertex of "end" can change, so recompute the previous one
		   run2=startedge=connect(startbuf->prev->invers,run->prev->invers,1);
		   // startedge is the global variable remembering the start
		   if (makecycle(run2,starttop,1,maxlength,1,0)) return 1;
		   undo_connect(run2);
		   undo_subdiv_edge(run);
		 }
	     }
	 }
     }

   // then try everything

   // first also a cycle not crossing, but allowing multiple crossings later
 startbuf=map[starttop];
   for (k=0;k<adj[starttop];k++, startbuf=startbuf->next)
     { start=startbuf->invers->next; end=startbuf->prev->invers;
       for ( ; start != end; start=start->invers->next)
	 if (start->name==starttop) 
	 {
	   run2=startedge=connect(end,start,1);
	   // startedge is the global variable remembering the start
	   if (check_con(run2))
	     {
	       if (cutnext(2, 0, 1)) return 1;
	     }
	   undo_connect(run2);
	 }
     }
   
   for (maxlength=1; 1 ; maxlength++)
     {
       startbuf=map[starttop];
       for (k=0;k<adj[starttop];k++, startbuf=startbuf->next)
	 { start=startbuf->invers->next; end=startbuf->prev->invers;
	   for ( ; start != end; start=start->invers->next)
	     if (CANBECUT(start->ursprung,start->name))
	     {
	       run=subdiv_edge(start);
	       // the end vertex of "end" can change, so recompute the previous one
	       run2=startedge=connect(startbuf->prev->invers,run->prev->invers,1);
	       if (makecycle(run2,starttop,1,maxlength,1,1)) return 1;
	       undo_connect(run2);
	       undo_subdiv_edge(run);
	     }
	 }
     }
       
   return 0; // should never be reached
 }



// just the prev and next operations to make b right of a which is already in the rotational order -- b not
#define RIGHT(a,b) {(b)->prev=(a); (b)->next=(a)->next; (a)->next->prev=(b); (a)->next=(b); }
// just the prev and next operations to make b left of a 
#define LEFT(a,b) {(b)->next=(a); (b)->prev=(a)->prev; (a)->prev->next=(b); (a)->prev=(b); }


KANTE *split_end(KANTE *first)
 // splits further after the first split. Right of first there is already the future outer face
 {
   KANTE *second, *firstright, *firstrightinv, *secondright, *secondrightinv, *otherright;
   
   if (adj[first->name]!=5) { fprintf(stderr,"problem splitend  -- %d->%d   (%d) -- deg %d exit\n",first->ursprung,first->name, first->edgenumber, adj[first->name]); exit(24); }
   second=first->invers->next->next;
   otherright=second->next;
   if (first->cyclenumber != second->cyclenumber) { fprintf(stderr,"problem splitend 2 -- exit\n"); exit(25); }
   
    nv++; if (nv>N) { fprintf(stderr,"Too many vertices (including the extra vertices used for the construction) for constant N=%d -- exit.\n",N); exit(1); }
    type[nv]=type[first->name];
    firstright=first->invers->prev->invers; firstrightinv=firstright->invers;
    map[nv]=secondright=getedge(); secondrightinv=getedge();
    map[second->ursprung]=second;
 
    secondright->invers=secondrightinv; secondrightinv->invers=secondright;
    firstrightinv->ursprung=firstright->name=nv;
    
    secondright->ursprung=secondrightinv->name=otherright->ursprung=otherright->invers->name=nv;
    secondrightinv->ursprung=secondright->name=second->name;
    
    secondright->cyclenumber=secondrightinv->cyclenumber= (- (first->cyclenumber));
    
    adj[first->name]=adj[nv]=3;
    adj[second->name]++;
    
    LEFT(second->invers,secondrightinv);
    first->invers->prev=second; second->next=first->invers;
    secondright->prev=firstrightinv; firstrightinv->next=secondright;
    otherright->prev=secondright; 
    secondright->next=otherright; 

    return second;
    
 }

KANTE *firstsplit(KANTE *first)
{
  KANTE *second, *firstright, *firstrightinv, *secondright, *secondrightinv, *otherright;

  if ((first->ursprung==starttop_t0) && (first->name==starttop_t0))
    {
      firstright=getedge();
      firstrightinv=getedge();
      firstright->name=firstright->ursprung= firstrightinv->name=firstrightinv->ursprung=starttop_t0;
      firstright->cyclenumber=firstrightinv->cyclenumber= (-(first->cyclenumber));
      firstright->invers=firstrightinv;  firstrightinv->invers=firstright;
      firstright->next=first->next; firstright->prev=first;
      firstright->next->prev=first->next=firstright; 
      firstrightinv->next=first->invers; firstrightinv->prev=first->invers->prev;
      first->invers->prev=firstrightinv->prev->next=firstrightinv; 
      adj[starttop_t0]+=2;
      return first;
    }

  // else


  if (adj[first->name]!=4) { fprintf(stderr,"problem firstsplit -- %d->%d   (%d) -- deg %d exit\n",first->ursprung,first->name, first->edgenumber, adj[first->name]);
    schreibemap("problem when splitting:"); exit(14); }
  second=first->invers->next->next;
  otherright=second->next;
  if (first->cyclenumber != second->cyclenumber) { fprintf(stderr,"problem firstsplit 2 -- exit\n"); exit(15); }

  nv++; if (nv>N) { fprintf(stderr,"Too many vertices (including the extra vertices used for the construction) for constant N=%d -- exit.\n",N); exit(1); }
  type[nv]=type[first->name];
  firstright=getedge(); firstrightinv=getedge(); map[nv]=secondright=getedge(); secondrightinv=getedge();
  map[second->ursprung]=second;
 
  firstright->invers=firstrightinv; firstrightinv->invers=firstright;
  secondright->invers=secondrightinv; secondrightinv->invers=secondright;
  firstright->ursprung=firstrightinv->name=first->ursprung;
  firstrightinv->ursprung=firstright->name=nv;

  secondright->ursprung=secondrightinv->name=otherright->ursprung=otherright->invers->name=nv;
  secondrightinv->ursprung=secondright->name=second->name;

  firstright->cyclenumber=firstrightinv->cyclenumber=secondright->cyclenumber=secondrightinv->cyclenumber= (- (first->cyclenumber));

  adj[first->name]=adj[nv]=3;
  adj[first->ursprung]++; adj[second->name]++;

  RIGHT(first,firstright);
  LEFT(second->invers,secondrightinv);

  first->invers->prev=second; second->next=first->invers;
  secondright->prev=firstrightinv; firstrightinv->next=secondright;
  otherright->prev=secondright; otherright->next=firstrightinv;
  firstrightinv->prev=secondright->next=otherright; 

  return second;
}

void detach(KANTE *start)
 {
   KANTE *prev;

   map[start->ursprung]=start->next;
   prev=start->prev;
   adj[start->ursprung]-=2;
   start->next->prev=prev->prev;
   prev->prev->next=start->next;

   nv++; if (nv>N) { fprintf(stderr,"Too many vertices (including the extra vertices used for the construction) for constant N=%d -- exit.\n",N); exit(1); }
   type[nv]=type[start->ursprung];
   map[nv]=start;
   adj[nv]=2;
   start->ursprung=start->invers->name=prev->ursprung=prev->invers->name=nv;
   start->next=prev; prev->prev=start;
   
 }

void detach_v(KANTE *start)
 {
   KANTE *prev, *run;
   int deg;

   map[start->ursprung]=start->next;
   for (deg=2, prev=start->prev; (prev->cyclenumber)==0; prev=prev->prev, deg++);
   adj[start->ursprung]-=deg;
   start->next->prev=prev->prev;
   prev->prev->next=start->next;

   nv++; if (nv>N) { fprintf(stderr,"Too many vertices (including the extra vertices used for the construction) for constant N=%d -- exit.\n",N); exit(1); }
   type[nv]=type[start->ursprung];
   map[nv]=start;
   adj[nv]=deg;
   for (run=start; deg ; deg--, run=run->prev)
     {   run->ursprung=run->invers->name=nv; }
   start->next=prev; prev->prev=start;
   
 }

void cut_open()
// cuts along the cycles -- doubling the vertices to get a planar graph
{
  KANTE *run, *nextedge;
  int start;

  
  start=startedge->ursprung;
  run=firstsplit(startedge);
  //first cut all the cycles, keeping the common vertex
  for ( ; run!=startedge->prev->invers;   )
    {
      if (run->name==start)
	{
	  run=run->invers->next;
	  if (run->cyclenumber<0) // already split
	    { for (run=run->invers->prev; run->name!=start; run=run->invers->prev); }
	  else
	    { 	  
	      run=firstsplit(run);
	    }
	}
      else // that is: run->name is not the startvertex
	{ 
	  run=split_end(run);
	}
    }

  // Finally open up the central vertex:

 
  while (adj[start]>2)
    {  nextedge=startedge->next->next;
      detach(startedge);
      startedge=nextedge;
    }

}

void cut_open_v()
// cuts along the cycles -- doubling the vertices to get a planar graph
{
  KANTE *run, *nextedge;
  int start, stop, i, count;

  start=startedge->ursprung;
   
  run=firstsplit(startedge);


   //first cut all the cycles, keeping the common vertex
  for ( stop=0; !stop;   )
    {
      if (run->name==start)
	{
	  run=run->invers->next;
	  while (run->cyclenumber==0) {  run=run->next; }
	  if (run==startedge) stop=1;
	  else
	    {
	      if (run->cyclenumber<0) // already split
		{ for ( ; run->name!=start; run=run->invers->prev); }
	      else
		{ 	  
		  run=firstsplit(run);
		}
	    }
	}
      else // that is: run->name is not the startvertex
	{ 
	  run=split_end(run);
	}
    }

  // Finally open up the central vertex:

  for (i=0, count=(-2), run=map[start]; i<adj[start];i++,run=run->next) if (run->cyclenumber) count++;

  for ( ; count; count-=2)
    {  
      for (nextedge=startedge->next->next; nextedge->cyclenumber==0; nextedge=nextedge->next);
      detach_v(startedge);
      startedge=nextedge;
    }

  
}

void rotate_clockwise_to(double c[2], double coordinates[2], double angle)
{
  c[0]=(coordinates[0]*cos(angle))+(coordinates[1]*sin(angle));
  c[1]=(coordinates[1]*cos(angle))-(coordinates[0]*sin(angle));
}


#define abs(a) ((a)>0?(a):(-(a)))

int uf_find(int parent[], int x)
{
  while (parent[x]!=x)
    {
      parent[x]=parent[parent[x]];
      x=parent[x];
    }
  return x;
}

void uf_union(int parent[], int a, int b)
{
  int ra, rb;
  if ((a<0) || (b<0)) return;
  ra=uf_find(parent,a);
  rb=uf_find(parent,b);
  if (ra!=rb) parent[rb]=ra;
}

void texture_bounds(double coord[][2], double *minx, double *maxx, double *miny, double *maxy)
{
  int i, first=1;
  double padx, pady;

  for (i=1;i<=nv;i++)
    if (adj[i]>0)
      {
	if (first)
	  { *minx=*maxx=coord[i][0]; *miny=*maxy=coord[i][1]; first=0; }
	else
	  {
	    if (coord[i][0]<*minx) *minx=coord[i][0];
	    if (coord[i][0]>*maxx) *maxx=coord[i][0];
	    if (coord[i][1]<*miny) *miny=coord[i][1];
	    if (coord[i][1]>*maxy) *maxy=coord[i][1];
	  }
      }
  if (first) { *minx=*miny=-RADIUS; *maxx=*maxy=RADIUS; }
  padx=0.08*((*maxx)-(*minx));
  pady=0.08*((*maxy)-(*miny));
  if (padx<1.0) padx=1.0;
  if (pady<1.0) pady=1.0;
  *minx-=padx; *maxx+=padx; *miny-=pady; *maxy+=pady;
}

void coord_to_uv(double coord[][2], int v, double minx, double maxx, double miny, double maxy, double *u, double *vv)
{
  *u=(coord[v][0]-minx)/(maxx-minx);
  *vv=(coord[v][1]-miny)/(maxy-miny);
  if (*u<0.0) *u=0.0; if (*u>1.0) *u=1.0;
  if (*vv<0.0) *vv=0.0; if (*vv>1.0) *vv=1.0;
}

void canonical_point(double x, double y, int genus, double out[3])
{
  double theta, rho, t, local, major, minor, spacing, u, v, scale, r2;
  int handle;

  if (genus<=0)
    {
      scale=RADIUS;
      x/=scale; y/=scale;
      r2=x*x+y*y;
      out[0]=1.45*(2.0*x/(1.0+r2));
      out[1]=1.45*(2.0*y/(1.0+r2));
      out[2]=1.45*((1.0-r2)/(1.0+r2));
      return;
    }

  theta=atan2(y,x);
  if (theta<0.0) theta += 2.0*M_PI;
  rho=sqrt(x*x+y*y)/RADIUS;
  if (rho>1.0) rho=1.0;
  t=theta/(2.0*M_PI);
  handle=(int)floor(t*((double)genus));
  if (handle>=genus) handle=genus-1;
  local=(t*((double)genus))-((double)handle);
  u=2.0*M_PI*local;
  v=2.0*M_PI*rho;
  major=1.25;
  minor=0.38;
  spacing=3.0;
  out[0]=(((double)handle)-(((double)genus)-1.0)/2.0)*spacing + (major+minor*cos(v))*cos(u);
  out[1]=(major+minor*cos(v))*sin(u);
  out[2]=minor*sin(v);
}

void texture_set(unsigned char *img, int x, int y, int r, int g, int b)
{
  int p;
  if ((x<0) || (x>=TEXTURESIZE) || (y<0) || (y>=TEXTURESIZE)) return;
  p=3*((TEXTURESIZE-1-y)*TEXTURESIZE+x);
  img[p]=r; img[p+1]=g; img[p+2]=b;
}

void texture_line(unsigned char *img, int x0, int y0, int x1, int y1, int r, int g, int b, int width)
{
  int dx, dy, sx, sy, err, e2, wx, wy;

  dx=abs(x1-x0); dy=abs(y1-y0);
  sx=(x0<x1)?1:-1; sy=(y0<y1)?1:-1;
  err=dx-dy;
  for (;;)
    {
      for (wx=-width; wx<=width; wx++)
	for (wy=-width; wy<=width; wy++)
	  if ((wx*wx+wy*wy)<=width*width) texture_set(img,x0+wx,y0+wy,r,g,b);
      if ((x0==x1) && (y0==y1)) break;
      e2=2*err;
      if (e2>-dy) { err-=dy; x0+=sx; }
      if (e2<dx) { err+=dx; y0+=sy; }
    }
}

void texture_circle(unsigned char *img, int cx, int cy, int radius, int r, int g, int b)
{
  int x,y;
  for (x=-radius; x<=radius; x++)
    for (y=-radius; y<=radius; y++)
      if (x*x+y*y<=radius*radius) texture_set(img,cx+x,cy+y,r,g,b);
}

void write_texture(char *filename, double coord[][2], double minx, double maxx, double miny, double maxy)
{
  FILE *file;
  unsigned char *img;
  int i,j,x0,y0,x1,y1;
  double u,vv;
  KANTE *run;

  img=malloc(3*TEXTURESIZE*TEXTURESIZE);
  if (img==NULL) { fprintf(stderr,"Can't allocate texture image -- exit.\n"); exit(1); }
  memset(img,255,3*TEXTURESIZE*TEXTURESIZE);

  for (i=1;i<=nv;i++)
    {
      run=map[i];
      for (j=0;j<adj[i];j++, run=run->next)
	if ((run->ursprung<run->name) && (run->cyclenumber==0) && (type[run->ursprung]!=3) && (type[run->name]!=3))
	  {
	    coord_to_uv(coord,run->ursprung,minx,maxx,miny,maxy,&u,&vv);
	    x0=(int)(u*(TEXTURESIZE-1)); y0=(int)(vv*(TEXTURESIZE-1));
	    coord_to_uv(coord,run->name,minx,maxx,miny,maxy,&u,&vv);
	    x1=(int)(u*(TEXTURESIZE-1)); y1=(int)(vv*(TEXTURESIZE-1));
	    texture_line(img,x0,y0,x1,y1,20,25,30,4);
	  }
    }

  for (i=1;i<=nv;i++)
    if (type[i]==0)
      {
	coord_to_uv(coord,i,minx,maxx,miny,maxy,&u,&vv);
	x0=(int)(u*(TEXTURESIZE-1)); y0=(int)(vv*(TEXTURESIZE-1));
	texture_circle(img,x0,y0,9,10,10,10);
	texture_circle(img,x0,y0,5,245,245,245);
      }

  file=fopen(filename,"wb");
  if (file==NULL) { fprintf(stderr,"Can't open texture file %s -- exit.\n",filename); exit(1); }
  fprintf(file,"P6\n%d %d\n255\n",TEXTURESIZE,TEXTURESIZE);
  fwrite(img,3,TEXTURESIZE*TEXTURESIZE,file);
  fclose(file);
  free(img);
}

int canonical_mesh_id(int ring, int sector, int sectors)
{
  if (ring==0) return 0;
  while (sector<0) sector+=sectors;
  sector%=sectors;
  return 1+(ring-1)*sectors+sector;
}

void canonical_mesh_point(int genus, int side_segments, int rings, int ring, int sector, double out[3])
{
  double rho, theta, local, ub, vb, u, v, major, minor, spacing;
  int sectors, side, handle, q;

  if (genus<=0)
    {
      theta=(2.0*M_PI*((double)sector))/64.0;
      rho=((double)ring)/((double)rings);
      canonical_point(RADIUS*rho*cos(theta),RADIUS*rho*sin(theta),0,out);
      return;
    }

  sectors=4*genus*side_segments;
  theta=(2.0*M_PI*((double)sector))/((double)sectors);
  rho=((double)ring)/((double)rings);
  side=sector/side_segments;
  handle=side/4;
  q=side%4;
  local=((double)(sector%side_segments))/((double)side_segments);

  if (q==0) { ub=local; vb=0.0; }
  else if (q==1) { ub=1.0; vb=local; }
  else if (q==2) { ub=1.0-local; vb=1.0; }
  else { ub=0.0; vb=1.0-local; }

  u=0.5*(1.0-rho)+rho*ub;
  v=0.5*(1.0-rho)+rho*vb;
  major=1.25;
  minor=0.38;
  spacing=3.0;

  out[0]=(((double)handle)-(((double)genus)-1.0)/2.0)*spacing + (major+minor*cos(2.0*M_PI*v))*cos(2.0*M_PI*u);
  out[1]=(major+minor*cos(2.0*M_PI*v))*sin(2.0*M_PI*u);
  out[2]=minor*sin(2.0*M_PI*v) + 0.10*(1.0-rho)*sin(theta*((double)genus));
}

void clamp_unit(double *x)
{
  if (*x<0.0) *x=0.0;
  if (*x>1.0) *x=1.0;
}

void projected_uv(double x, double y, double minx, double maxx, double miny, double maxy, double *u, double *v)
{
  *u=(x-minx)/(maxx-minx);
  *v=(y-miny)/(maxy-miny);
  clamp_unit(u);
  clamp_unit(v);
}

typedef struct
{
  long long x;
  long long y;
  long long z;
  long long u;
  long long v;
  int index;
  unsigned char used;
} OBJVERTEXCACHEENTRY;

typedef struct
{
  OBJVERTEXCACHEENTRY *entries;
  unsigned int capacity;
} OBJVERTEXCACHE;

long long quantize_obj_value(double x)
{
  if (x>=0.0) return (long long)(x*1000000.0+0.5);
  return (long long)(x*1000000.0-0.5);
}

unsigned int obj_vertex_hash(long long x, long long y, long long z, long long u, long long v)
{
  unsigned long long h;
  h=1469598103934665603ULL;
  h=(h^(unsigned long long)x)*1099511628211ULL;
  h=(h^(unsigned long long)y)*1099511628211ULL;
  h=(h^(unsigned long long)z)*1099511628211ULL;
  h=(h^(unsigned long long)u)*1099511628211ULL;
  h=(h^(unsigned long long)v)*1099511628211ULL;
  return (unsigned int)(h^(h>>32));
}

void obj_cache_init(OBJVERTEXCACHE *cache, unsigned int capacity)
{
  cache->capacity=capacity;
  cache->entries=calloc(capacity,sizeof(OBJVERTEXCACHEENTRY));
  if (cache->entries==NULL) { fprintf(stderr,"Can't allocate OBJ vertex cache -- exit.\n"); exit(1); }
}

void obj_cache_free(OBJVERTEXCACHE *cache)
{
  free(cache->entries);
  cache->entries=NULL;
  cache->capacity=0;
}

int obj_emit_vertex(FILE *obj, OBJVERTEXCACHE *cache, double x, double y, double z, double u, double v, int *vcount)
{
  long long qx,qy,qz,qu,qv;
  unsigned int slot, start;

  clamp_unit(&u);
  clamp_unit(&v);
  qx=quantize_obj_value(x);
  qy=quantize_obj_value(y);
  qz=quantize_obj_value(z);
  qu=0;
  qv=0;
  slot=obj_vertex_hash(qx,qy,qz,qu,qv)&(cache->capacity-1);
  start=slot;
  while (cache->entries[slot].used)
    {
      if ((cache->entries[slot].x==qx) && (cache->entries[slot].y==qy) &&
	  (cache->entries[slot].z==qz) && (cache->entries[slot].u==qu) &&
	  (cache->entries[slot].v==qv))
	return cache->entries[slot].index;
      slot=(slot+1)&(cache->capacity-1);
      if (slot==start) { fprintf(stderr,"OBJ vertex cache is full -- exit.\n"); exit(1); }
    }
  (*vcount)++;
  cache->entries[slot].used=1;
  cache->entries[slot].x=qx;
  cache->entries[slot].y=qy;
  cache->entries[slot].z=qz;
  cache->entries[slot].u=qu;
  cache->entries[slot].v=qv;
  cache->entries[slot].index=*vcount;
  fprintf(obj,"v %.8f %.8f %.8f\n",x,y,z);
  fprintf(obj,"vt %.8f %.8f\n",u,v);
  return *vcount;
}

void obj_emit_triangle(FILE *obj, OBJVERTEXCACHE *cache, double a[3], double b[3], double c[3], double au, double av, double bu, double bv, double cu, double cv, int *vcount, int *faces)
{
  int ia, ib, ic;
  ia=obj_emit_vertex(obj,cache,a[0],a[1],a[2],au,av,vcount);
  ib=obj_emit_vertex(obj,cache,b[0],b[1],b[2],bu,bv,vcount);
  ic=obj_emit_vertex(obj,cache,c[0],c[1],c[2],cu,cv,vcount);
  fprintf(obj,"f %d/%d %d/%d %d/%d\n",ia,ia,ib,ib,ic,ic);
  (*faces)++;
}

void sphere_point(double theta, double phi, double out[3])
{
  double r;
  r=1.45;
  out[0]=r*sin(phi)*cos(theta);
  out[1]=r*sin(phi)*sin(theta);
  out[2]=r*cos(phi);
}

void sphere_uv(double p[3], double *u, double *v)
{
  *u=0.5 + p[0]/3.2;
  *v=0.5 + p[1]/3.2;
  clamp_unit(u);
  clamp_unit(v);
}

void write_sphere_mesh(FILE *obj, OBJVERTEXCACHE *cache, int *vcount, int *faces)
{
  int lat, lon, i, j;
  double p00[3], p01[3], p10[3], p11[3], u00,v00,u01,v01,u10,v10,u11,v11;
  double phi0, phi1, th0, th1;

  lat=56;
  lon=112;
  for (i=0;i<lat;i++)
    {
      phi0=M_PI*((double)i)/((double)lat);
      phi1=M_PI*((double)(i+1))/((double)lat);
      for (j=0;j<lon;j++)
	{
	  th0=2.0*M_PI*((double)j)/((double)lon);
	  th1=2.0*M_PI*((double)(j+1))/((double)lon);
	  sphere_point(th0,phi0,p00);
	  sphere_point(th1,phi0,p01);
	  sphere_point(th0,phi1,p10);
	  sphere_point(th1,phi1,p11);
	  sphere_uv(p00,&u00,&v00);
	  sphere_uv(p01,&u01,&v01);
	  sphere_uv(p10,&u10,&v10);
	  sphere_uv(p11,&u11,&v11);
	  if (i==0)
	    obj_emit_triangle(obj,cache,p00,p10,p11,u00,v00,u10,v10,u11,v11,vcount,faces);
	  else if (i==lat-1)
	    obj_emit_triangle(obj,cache,p00,p10,p01,u00,v00,u10,v10,u01,v01,vcount,faces);
	  else
	    {
	      obj_emit_triangle(obj,cache,p00,p10,p11,u00,v00,u10,v10,u11,v11,vcount,faces);
	      obj_emit_triangle(obj,cache,p00,p11,p01,u00,v00,u11,v11,u01,v01,vcount,faces);
	    }
	}
    }
}

void torus_point(double centerx, double major, double minor, double u, double v, double out[3])
{
  out[0]=centerx+(major+minor*cos(v))*cos(u);
  out[1]=(major+minor*cos(v))*sin(u);
  out[2]=minor*sin(v);
}

void write_torus_mesh(FILE *obj, int genus, OBJVERTEXCACHE *cache, int *vcount, int *faces)
{
  int seg_u, seg_v, i, j;
  double centerx, major, minor, u0, u1, v0, v1;
  double p00[3], p01[3], p10[3], p11[3];
  double tu0, tu1, tv0, tv1;

  seg_u=144;
  seg_v=56;
  centerx=0.0;
  major=1.25;
  minor=0.38;
  for (i=0;i<seg_u;i++)
    {
      u0=2.0*M_PI*((double)i)/((double)seg_u);
      u1=2.0*M_PI*((double)(i+1))/((double)seg_u);
      tu0=((double)i)/((double)seg_u);
      tu1=((double)(i+1))/((double)seg_u);
      for (j=0;j<seg_v;j++)
	{
	  v0=2.0*M_PI*((double)j)/((double)seg_v);
	  v1=2.0*M_PI*((double)(j+1))/((double)seg_v);
	  tv0=((double)j)/((double)seg_v);
	  tv1=((double)(j+1))/((double)seg_v);
	  torus_point(centerx,major,minor,u0,v0,p00);
	  torus_point(centerx,major,minor,u1,v0,p01);
	  torus_point(centerx,major,minor,u0,v1,p10);
	  torus_point(centerx,major,minor,u1,v1,p11);
	  obj_emit_triangle(obj,cache,p00,p10,p11,tu0,tv0,tu0,tv1,tu1,tv1,vcount,faces);
	  obj_emit_triangle(obj,cache,p00,p11,p01,tu0,tv0,tu1,tv1,tu1,tv0,vcount,faces);
	}
    }
}

double distance_to_segment(double x, double y, double z, double ax, double ay, double az, double bx, double by, double bz)
{
  double vx,vy,vz,wx,wy,wz,len2,t,px,py,pz,dx,dy,dz;
  vx=bx-ax; vy=by-ay; vz=bz-az;
  wx=x-ax; wy=y-ay; wz=z-az;
  len2=vx*vx+vy*vy+vz*vz;
  if (len2<=0.0) return sqrt(wx*wx+wy*wy+wz*wz);
  t=(wx*vx+wy*vy+wz*vz)/len2;
  if (t<0.0) t=0.0;
  if (t>1.0) t=1.0;
  px=ax+t*vx; py=ay+t*vy; pz=az+t*vz;
  dx=x-px; dy=y-py; dz=z-pz;
  return sqrt(dx*dx+dy*dy+dz*dz);
}

double smooth_min(double a, double b, double k)
{
  double h, m;
  if (a>900.0) return b;
  m=(a<b)?a:b;
  h=k-abs(a-b);
  if (h<=0.0) return m;
  return m - (h*h)/(4.0*k);
}

double handle_chain_sdf(double x, double y, double z, int genus)
{
  double major, minor, spacing, blend, d, cx, cx2, q, tor, seg, a, b;
  int h;

  major=1.18;
  minor=0.34;
  spacing=2.55;
  blend=0.26;
  d=1000.0;
  for (h=0;h<genus;h++)
    {
      cx=(((double)h)-(((double)genus)-1.0)/2.0)*spacing;
      q=sqrt((x-cx)*(x-cx)+y*y)-major;
      tor=sqrt(q*q+z*z)-minor;
      d=smooth_min(d,tor,blend);
      if (h<genus-1)
	{
	  cx2=(((double)(h+1))-(((double)genus)-1.0)/2.0)*spacing;
	  a=cx+major;
	  b=cx2-major;
	  seg=distance_to_segment(x,y,z,a,0.0,0.0,b,0.0,0.0)-minor;
	  d=smooth_min(d,seg,blend);
	}
    }
  return d;
}

void interp_zero(double a[3], double b[3], double va, double vb, double out[3])
{
  double t;
  if (abs(va-vb)<1e-12) t=0.5;
  else t=va/(va-vb);
  if (t<0.0) t=0.0;
  if (t>1.0) t=1.0;
  out[0]=a[0]+t*(b[0]-a[0]);
  out[1]=a[1]+t*(b[1]-a[1]);
  out[2]=a[2]+t*(b[2]-a[2]);
}

void handle_uv(double p[3], double minx, double maxx, double miny, double maxy, double *u, double *v)
{
  projected_uv(p[0],p[1],minx,maxx,miny,maxy,u,v);
}

void normalize3(double v[3])
{
  double len;
  len=sqrt(v[0]*v[0]+v[1]*v[1]+v[2]*v[2]);
  if (len<1e-12) { v[0]=0.0; v[1]=0.0; v[2]=1.0; return; }
  v[0]/=len; v[1]/=len; v[2]/=len;
}

void handle_chain_gradient(double p[3], int genus, double grad[3])
{
  double eps;
  eps=0.0001;
  grad[0]=handle_chain_sdf(p[0]+eps,p[1],p[2],genus)-handle_chain_sdf(p[0]-eps,p[1],p[2],genus);
  grad[1]=handle_chain_sdf(p[0],p[1]+eps,p[2],genus)-handle_chain_sdf(p[0],p[1]-eps,p[2],genus);
  grad[2]=handle_chain_sdf(p[0],p[1],p[2]+eps,genus)-handle_chain_sdf(p[0],p[1],p[2]-eps,genus);
  normalize3(grad);
}

void obj_emit_oriented_handle_triangle(FILE *obj, OBJVERTEXCACHE *cache, int genus, double a[3], double b[3], double c[3], double au, double av, double bu, double bv, double cu, double cv, int *vcount, int *faces)
{
  double ab[3], ac[3], n[3], mid[3], grad[3], dot;
  ab[0]=b[0]-a[0]; ab[1]=b[1]-a[1]; ab[2]=b[2]-a[2];
  ac[0]=c[0]-a[0]; ac[1]=c[1]-a[1]; ac[2]=c[2]-a[2];
  n[0]=ab[1]*ac[2]-ab[2]*ac[1];
  n[1]=ab[2]*ac[0]-ab[0]*ac[2];
  n[2]=ab[0]*ac[1]-ab[1]*ac[0];
  mid[0]=(a[0]+b[0]+c[0])/3.0;
  mid[1]=(a[1]+b[1]+c[1])/3.0;
  mid[2]=(a[2]+b[2]+c[2])/3.0;
  handle_chain_gradient(mid,genus,grad);
  dot=n[0]*grad[0]+n[1]*grad[1]+n[2]*grad[2];
  if (dot<0.0) obj_emit_triangle(obj,cache,a,c,b,au,av,cu,cv,bu,bv,vcount,faces);
  else obj_emit_triangle(obj,cache,a,b,c,au,av,bu,bv,cu,cv,vcount,faces);
}

void emit_tetra_surface(FILE *obj, OBJVERTEXCACHE *cache, int genus, double p[4][3], double val[4], double minx, double maxx, double miny, double maxy, int *vcount, int *faces)
{
  int inside[4], outside[4], ni, no, i;
  double q0[3], q1[3], q2[3], q3[3], u0,v0,u1,v1,u2,v2,u3,v3;

  ni=0; no=0;
  for (i=0;i<4;i++)
    if (val[i]<0.0) { inside[ni]=i; ni++; }
    else { outside[no]=i; no++; }

  if ((ni==0) || (ni==4)) return;

  if (ni==1)
    {
      interp_zero(p[inside[0]],p[outside[0]],val[inside[0]],val[outside[0]],q0);
      interp_zero(p[inside[0]],p[outside[1]],val[inside[0]],val[outside[1]],q1);
      interp_zero(p[inside[0]],p[outside[2]],val[inside[0]],val[outside[2]],q2);
      handle_uv(q0,minx,maxx,miny,maxy,&u0,&v0);
      handle_uv(q1,minx,maxx,miny,maxy,&u1,&v1);
      handle_uv(q2,minx,maxx,miny,maxy,&u2,&v2);
      obj_emit_oriented_handle_triangle(obj,cache,genus,q0,q1,q2,u0,v0,u1,v1,u2,v2,vcount,faces);
    }
  else if (ni==3)
    {
      interp_zero(p[outside[0]],p[inside[0]],val[outside[0]],val[inside[0]],q0);
      interp_zero(p[outside[0]],p[inside[1]],val[outside[0]],val[inside[1]],q1);
      interp_zero(p[outside[0]],p[inside[2]],val[outside[0]],val[inside[2]],q2);
      handle_uv(q0,minx,maxx,miny,maxy,&u0,&v0);
      handle_uv(q1,minx,maxx,miny,maxy,&u1,&v1);
      handle_uv(q2,minx,maxx,miny,maxy,&u2,&v2);
      obj_emit_oriented_handle_triangle(obj,cache,genus,q0,q2,q1,u0,v0,u2,v2,u1,v1,vcount,faces);
    }
  else
    {
      interp_zero(p[inside[0]],p[outside[0]],val[inside[0]],val[outside[0]],q0);
      interp_zero(p[inside[1]],p[outside[0]],val[inside[1]],val[outside[0]],q1);
      interp_zero(p[inside[1]],p[outside[1]],val[inside[1]],val[outside[1]],q2);
      interp_zero(p[inside[0]],p[outside[1]],val[inside[0]],val[outside[1]],q3);
      handle_uv(q0,minx,maxx,miny,maxy,&u0,&v0);
      handle_uv(q1,minx,maxx,miny,maxy,&u1,&v1);
      handle_uv(q2,minx,maxx,miny,maxy,&u2,&v2);
      handle_uv(q3,minx,maxx,miny,maxy,&u3,&v3);
      obj_emit_oriented_handle_triangle(obj,cache,genus,q0,q1,q2,u0,v0,u1,v1,u2,v2,vcount,faces);
      obj_emit_oriented_handle_triangle(obj,cache,genus,q0,q2,q3,u0,v0,u2,v2,u3,v3,vcount,faces);
    }
}

void write_handle_chain_mesh(FILE *obj, int genus, OBJVERTEXCACHE *cache, int *vcount, int *faces)
{
  int nx, ny, nz, i, j, k, c, t, m;
  int tet[6][4]={{0,5,1,6},{0,1,2,6},{0,2,3,6},{0,3,7,6},{0,7,4,6},{0,4,5,6}};
  int ox[8]={0,1,1,0,0,1,1,0};
  int oy[8]={0,0,1,1,0,0,1,1};
  int oz[8]={0,0,0,0,1,1,1,1};
  double major, minor, spacing, margin, minx, maxx, miny, maxy, minz, maxz, dx, dy, dz;
  double cube_p[8][3], cube_val[8], tp[4][3], tv[4];

  major=1.18;
  minor=0.34;
  spacing=2.55;
  margin=0.22;
  minx=-(((double)genus)-1.0)*spacing/2.0 - major - minor - margin;
  maxx= (((double)genus)-1.0)*spacing/2.0 + major + minor + margin;
  miny=-(major+minor+margin);
  maxy= (major+minor+margin);
  minz=-(minor+margin);
  maxz= (minor+margin);

  nx=56+18*genus;
  if (nx>176) nx=176;
  ny=44;
  nz=28;
  dx=(maxx-minx)/((double)nx);
  dy=(maxy-miny)/((double)ny);
  dz=(maxz-minz)/((double)nz);

  for (i=0;i<nx;i++)
    for (j=0;j<ny;j++)
      for (k=0;k<nz;k++)
	{
	  for (c=0;c<8;c++)
	    {
	      cube_p[c][0]=minx+dx*((double)(i+ox[c]));
	      cube_p[c][1]=miny+dy*((double)(j+oy[c]));
	      cube_p[c][2]=minz+dz*((double)(k+oz[c]));
	      cube_val[c]=handle_chain_sdf(cube_p[c][0],cube_p[c][1],cube_p[c][2],genus);
	    }
	  for (t=0;t<6;t++)
	    {
	      for (m=0;m<4;m++)
		{
		  tp[m][0]=cube_p[tet[t][m]][0];
		  tp[m][1]=cube_p[tet[t][m]][1];
		  tp[m][2]=cube_p[tet[t][m]][2];
		  tv[m]=cube_val[tet[t][m]];
		}
	      emit_tetra_surface(obj,cache,genus,tp,tv,minx,maxx,miny,maxy,vcount,faces);
	    }
	}
}

void graph_chain_point(double x, double y, int genus, double out[3])
{
  double theta, rho, t, local, u, v, major, minor, spacing, center;
  int handle;

  theta=atan2(y,x);
  if (theta<0.0) theta += 2.0*M_PI;
  rho=sqrt(x*x+y*y)/RADIUS;
  if (rho>1.0) rho=1.0;
  t=theta/(2.0*M_PI);
  handle=(int)floor(t*((double)genus));
  if (handle<0) handle=0;
  if (handle>=genus) handle=genus-1;
  local=(t*((double)genus))-((double)handle);
  u=2.0*M_PI*local;
  v=2.0*M_PI*rho;
  major=1.18;
  minor=0.34;
  spacing=2.55;
  center=(((double)handle)-(((double)genus)-1.0)/2.0)*spacing;
  torus_point(center,major,minor,u,v,out);
}

void project_handle_chain_point(double start[3], int genus, double lift, double out[3]);

void graph_chain_surface_point(double x, double y, int genus, double lift, double out[3])
{
  double theta, rho, major, minor, spacing, bridge, half, s, seg, corner, q, alpha, center;
  double spx, spy, nx, ny, v, tube, angle;
  int h, placed;

  theta=atan2(y,x);
  if (theta<0.0) theta += 2.0*M_PI;
  rho=sqrt(x*x+y*y)/RADIUS;
  if (rho<0.0) rho=0.0;
  if (rho>1.0) rho=1.0;
  if (rho>0.985) rho=0.985;

  major=1.18;
  minor=0.34;
  spacing=2.55;
  bridge=spacing-2.0*major;
  if (bridge<0.05) bridge=0.05;
  seg=M_PI*major;
  corner=0.5*M_PI*minor;
  half=((double)genus)*seg + ((double)(genus-1))*(bridge+2.0*corner);
  s=(theta/(2.0*M_PI))*(2.0*half);
  placed=0;

  if (s<=half)
    {
      for (h=0;h<genus;h++)
	{
	  center=(((double)h)-(((double)genus)-1.0)/2.0)*spacing;
	  if ((s<=seg) || (h==genus-1))
	    {
	      q=s/seg;
	      if (q<0.0) q=0.0; if (q>1.0) q=1.0;
	      alpha=M_PI*(1.0-q);
	      spx=center+major*cos(alpha);
	      spy=major*sin(alpha);
	      nx=cos(alpha);
	      ny=sin(alpha);
	      placed=1;
	      break;
	    }
	  s-=seg;
	  if (h<genus-1)
	    {
	      if (s<=corner)
		{
		  q=s/corner;
		  if (q<0.0) q=0.0; if (q>1.0) q=1.0;
		  angle=0.5*M_PI*q;
		  spx=center+major;
		  spy=0.0;
		  nx=cos(angle);
		  ny=sin(angle);
		  placed=1;
		  break;
		}
	      s-=corner;
	      if (s<=bridge)
		{
		  q=s/bridge;
		  if (q<0.0) q=0.0; if (q>1.0) q=1.0;
		  spx=center+major+q*bridge;
		  spy=0.0;
		  nx=0.0;
		  ny=1.0;
		  placed=1;
		  break;
		}
	      s-=bridge;
	      if (s<=corner)
		{
		  q=s/corner;
		  if (q<0.0) q=0.0; if (q>1.0) q=1.0;
		  angle=0.5*M_PI+0.5*M_PI*q;
		  spx=center+major+bridge;
		  spy=0.0;
		  nx=cos(angle);
		  ny=sin(angle);
		  placed=1;
		  break;
		}
	      s-=corner;
	    }
	}
    }
  else
    {
      s-=half;
      for (h=genus-1;h>=0;h--)
	{
	  center=(((double)h)-(((double)genus)-1.0)/2.0)*spacing;
	  if ((s<=seg) || (h==0))
	    {
	      q=s/seg;
	      if (q<0.0) q=0.0; if (q>1.0) q=1.0;
	      alpha=(-M_PI)*q;
	      spx=center+major*cos(alpha);
	      spy=major*sin(alpha);
	      nx=cos(alpha);
	      ny=sin(alpha);
	      placed=1;
	      break;
	    }
	  s-=seg;
	  if (h>0)
	    {
	      if (s<=corner)
		{
		  q=s/corner;
		  if (q<0.0) q=0.0; if (q>1.0) q=1.0;
		  angle=M_PI+0.5*M_PI*q;
		  spx=center-major;
		  spy=0.0;
		  nx=cos(angle);
		  ny=sin(angle);
		  placed=1;
		  break;
		}
	      s-=corner;
	      if (s<=bridge)
		{
		  q=s/bridge;
		  if (q<0.0) q=0.0; if (q>1.0) q=1.0;
		  spx=center-major-q*bridge;
		  spy=0.0;
		  nx=0.0;
		  ny=-1.0;
		  placed=1;
		  break;
		}
	      s-=bridge;
	      if (s<=corner)
		{
		  q=s/corner;
		  if (q<0.0) q=0.0; if (q>1.0) q=1.0;
		  angle=1.5*M_PI+0.5*M_PI*q;
		  spx=center-major-bridge;
		  spy=0.0;
		  nx=cos(angle);
		  ny=sin(angle);
		  placed=1;
		  break;
		}
	      s-=corner;
	    }
	}
    }

  if (!placed)
    {
      center=-(((double)genus)-1.0)*spacing/2.0;
      spx=center-major;
      spy=0.0;
      nx=-1.0;
      ny=0.0;
    }

  v=2.0*M_PI*rho;
  tube=minor+lift;
  out[0]=spx+tube*cos(v)*nx;
  out[1]=spy+tube*cos(v)*ny;
  out[2]=tube*sin(v);
}

double positive_angle(double angle)
{
  while (angle<0.0) angle += 2.0*M_PI;
  while (angle>=2.0*M_PI) angle -= 2.0*M_PI;
  return angle;
}

double smoothstep01(double edge0, double edge1, double x)
{
  double t;
  if (edge0==edge1) return (x>=edge1) ? 1.0 : 0.0;
  t=(x-edge0)/(edge1-edge0);
  if (t<0.0) t=0.0;
  if (t>1.0) t=1.0;
  return t*t*(3.0-2.0*t);
}

void polygon_side_uv(int side, double local, int genus, int *handle, double *u, double *vv)
{
  int q;

  if (genus<1) genus=1;
  if (side<0) side=0;
  if (side>=4*genus) side=(4*genus)-1;
  if (local<0.0) local=0.0;
  if (local>1.0) local=1.0;

  *handle=side/4;
  q=side%4;
  if (q==0) { *u=local; *vv=0.0; }
  else if (q==1) { *u=1.0; *vv=local; }
  else if (q==2) { *u=1.0-local; *vv=1.0; }
  else { *u=0.0; *vv=1.0-local; }
}

void polygon_params_from_coord(double x, double y, int genus, int *side, double *local, double *rho)
{
  int sides;
  double alpha, shifted, angle, rawside;

  sides=numberpaths;
  if (sides<=0) sides=4*genus;
  if (sides<=0) sides=4;

  alpha=positive_angle(-atan2(y,x)-(M_PI/2.0));
  angle=(2.0*M_PI)/((double)sides);
  shifted=positive_angle(alpha-(angle/2.0));
  rawside=shifted/angle;
  *side=(int)floor(rawside);
  if (*side>=sides) *side=sides-1;
  if (*side<0) *side=0;
  *local=rawside-((double)(*side));
  if (*local<0.0) *local=0.0;
  if (*local>1.0) *local=1.0;
  *rho=sqrt(x*x+y*y)/RADIUS;
  if (*rho<0.0) *rho=0.0;
  if (*rho>1.0) *rho=1.0;
}

void polygon_params_for_vertex(int vertex, double x, double y, int genus, int *side, double *local, double *rho)
{
  if ((genus>0) && (vertex>0) && (vertex<=N) && (boundary_side[vertex]>=0))
    {
      *side=boundary_side[vertex];
      *local=boundary_t[vertex];
      if (*local<0.0) *local=0.0;
      if (*local>1.0) *local=1.0;
      *rho=1.0;
      return;
    }
  polygon_params_from_coord(x,y,genus,side,local,rho);
}

void polygon_surface_point(int side, double local, double rho, int genus, double lift, double out[3])
{
  double ub, vb, u, vv, major, minor, spacing, center, start[3], grad[3];
  double chain[3], centerpoint[3], paired[3], blend[3], alpha, angle, corner, weight, center_weight, radial_weight, corner_weight, x, y;
  int sides;
  int handle;

  if (rho<0.0) rho=0.0;
  if (rho>1.0) rho=1.0;
  polygon_side_uv(side,local,genus,&handle,&ub,&vb);
  u=0.5*(1.0-rho)+rho*ub;
  vv=0.5*(1.0-rho)+rho*vb;

  if (genus<=1)
    {
      major=1.25;
      minor=0.38;
      center=0.0;
      torus_point(center,major,minor,2.0*M_PI*u,2.0*M_PI*vv,out);
      grad[0]=cos(2.0*M_PI*vv)*cos(2.0*M_PI*u);
      grad[1]=cos(2.0*M_PI*vv)*sin(2.0*M_PI*u);
      grad[2]=sin(2.0*M_PI*vv);
      normalize3(grad);
      out[0]+=lift*grad[0]; out[1]+=lift*grad[1]; out[2]+=lift*grad[2];
      return;
    }

  if (handle<0) handle=0;
  if (handle>=genus) handle=genus-1;
  major=1.18;
  minor=0.34;
  spacing=2.55;
  center=(((double)handle)-(((double)genus)-1.0)/2.0)*spacing;
  torus_point(center,major,minor,2.0*M_PI*u,2.0*M_PI*vv,start);
  project_handle_chain_point(start,genus,lift,paired);

  sides=numberpaths;
  if (sides<=0) sides=4*genus;
  if (sides<=0) sides=4;
  angle=(2.0*M_PI)/((double)sides);
  alpha=angle/2.0 + (((double)side)+local)*angle;
  x=(-RADIUS*rho*sin(alpha));
  y=(-RADIUS*rho*cos(alpha));
  graph_chain_surface_point(x,y,genus,lift,chain);
  graph_chain_surface_point(RADIUS*0.001,0.0,genus,lift,centerpoint);
  center_weight=1.0-smoothstep01(0.05,0.22,rho);
  chain[0]=centerpoint[0]*center_weight+chain[0]*(1.0-center_weight);
  chain[1]=centerpoint[1]*center_weight+chain[1]*(1.0-center_weight);
  chain[2]=centerpoint[2]*center_weight+chain[2]*(1.0-center_weight);

  corner=local;
  if ((1.0-local)<corner) corner=1.0-local;
  radial_weight=smoothstep01(0.82,0.985,rho);
  corner_weight=smoothstep01(0.04,0.18,corner);
  weight=radial_weight*corner_weight;
  blend[0]=chain[0]*(1.0-weight)+paired[0]*weight;
  blend[1]=chain[1]*(1.0-weight)+paired[1]*weight;
  blend[2]=chain[2]*(1.0-weight)+paired[2]*weight;
  out[0]=blend[0]; out[1]=blend[1]; out[2]=blend[2];
}

void graph_surface_vertex_point(int vertex, double x, double y, int genus, double lift, double out[3])
{
  double scale, r2, rho, local;
  double grad[3];
  int side;

  if (genus<=0)
    {
      scale=RADIUS;
      x/=scale; y/=scale;
      r2=x*x+y*y;
      out[0]=1.45*(2.0*x/(1.0+r2));
      out[1]=1.45*(2.0*y/(1.0+r2));
      out[2]=1.45*((1.0-r2)/(1.0+r2));
      grad[0]=out[0]; grad[1]=out[1]; grad[2]=out[2];
      normalize3(grad);
      out[0]+=lift*grad[0]; out[1]+=lift*grad[1]; out[2]+=lift*grad[2];
      return;
    }

  polygon_params_for_vertex(vertex,x,y,genus,&side,&local,&rho);
  polygon_surface_point(side,local,rho,genus,lift,out);
}

void project_handle_chain_point(double start[3], int genus, double lift, double out[3])
{
  double grad[3], d;
  int iter;

  out[0]=start[0]; out[1]=start[1]; out[2]=start[2];
  for (iter=0;iter<10;iter++)
    {
      handle_chain_gradient(out,genus,grad);
      d=handle_chain_sdf(out[0],out[1],out[2],genus);
      out[0]-=d*grad[0];
      out[1]-=d*grad[1];
      out[2]-=d*grad[2];
    }
  handle_chain_gradient(out,genus,grad);
  out[0]+=lift*grad[0]; out[1]+=lift*grad[1]; out[2]+=lift*grad[2];
}

void graph_surface_point(double x, double y, int genus, double lift, double out[3])
{
  double scale, r2, rho, local;
  double grad[3];
  int side;

  if (genus<=0)
    {
      scale=RADIUS;
      x/=scale; y/=scale;
      r2=x*x+y*y;
      out[0]=1.45*(2.0*x/(1.0+r2));
      out[1]=1.45*(2.0*y/(1.0+r2));
      out[2]=1.45*((1.0-r2)/(1.0+r2));
      grad[0]=out[0]; grad[1]=out[1]; grad[2]=out[2];
      normalize3(grad);
      out[0]+=lift*grad[0]; out[1]+=lift*grad[1]; out[2]+=lift*grad[2];
      return;
    }

  polygon_params_from_coord(x,y,genus,&side,&local,&rho);
  polygon_surface_point(side,local,rho,genus,lift,out);
}

int obj_emit_line_vertex(FILE *obj, double p[3], int *vcount)
{
  (*vcount)++;
  fprintf(obj,"v %.8f %.8f %.8f\n",p[0],p[1],p[2]);
  return *vcount;
}

double normalized_delta(double a, double b)
{
  double d;
  d=b-a;
  while (d<0.0) d+=2.0*M_PI;
  while (d>=2.0*M_PI) d-=2.0*M_PI;
  return d;
}

int circle_through_points(double ax, double ay, double bx, double by, double cx, double cy, double *ox, double *oy)
{
  double d, aa, bb, cc;
  d=2.0*(ax*(by-cy)+bx*(cy-ay)+cx*(ay-by));
  if (fabs(d)<1e-9) return 0;
  aa=ax*ax+ay*ay;
  bb=bx*bx+by*by;
  cc=cx*cx+cy*cy;
  *ox=(aa*(by-cy)+bb*(cy-ay)+cc*(ay-by))/d;
  *oy=(aa*(cx-bx)+bb*(ax-cx)+cc*(bx-ax))/d;
  return 1;
}

void emit_graph_segment(FILE *obj, double coord[][2], int v, int w, int genus, double lift, int *vcount, int *linecount)
{
  int s, samples, idx, emit_count, lineindices[20000], use_arc;
  double x0,y0,x1,y1,dx,dy,length,t,p[3],px,py,mx,my,ox,oy,r,a0,am,a1,delta,dm;

  x0=coord[v][0]; y0=coord[v][1];
  x1=coord[w][0]; y1=coord[w][1];
  dx=x1-x0; dy=y1-y0;
  length=sqrt(dx*dx+dy*dy);
  samples=(int)(length/1.25)+24;
  if (genus>=2) samples*=8;
  if (samples<48) samples=48;
  if (samples>16384) samples=16384;

  use_arc=0;
  if ((type[v]==1) && (type[w]==1) && (length<=(RADIUS/1.5)))
    {
      mx=(x0+x1)*0.47;
      my=(y0+y1)*0.47;
      if (circle_through_points(x0,y0,mx,my,x1,y1,&ox,&oy))
	{
	  r=sqrt((x0-ox)*(x0-ox)+(y0-oy)*(y0-oy));
	  a0=atan2(y0-oy,x0-ox);
	  am=atan2(my-oy,mx-ox);
	  a1=atan2(y1-oy,x1-ox);
	  delta=normalized_delta(a0,a1);
	  dm=normalized_delta(a0,am);
	  if (dm>delta) delta-=2.0*M_PI;
	  use_arc=1;
	}
    }

  emit_count=0;
  for (s=0;s<=samples;s++)
    {
      t=((double)s)/((double)samples);
      if (use_arc)
	{
	  px=ox+r*cos(a0+t*delta);
	  py=oy+r*sin(a0+t*delta);
	}
      else
	{
	  px=x0+t*dx;
	  py=y0+t*dy;
	}
      if (s==0) graph_surface_vertex_point(v,px,py,genus,lift,p);
      else if (s==samples) graph_surface_vertex_point(w,px,py,genus,lift,p);
      else graph_surface_point(px,py,genus,lift,p);
      idx=obj_emit_line_vertex(obj,p,vcount);
      if (emit_count>=20000) { fprintf(stderr,"OBJ graph line too long -- exit.\n"); exit(1); }
      lineindices[emit_count++]=idx;
    }

  fprintf(obj,"l");
  for (s=0;s<emit_count;s++) fprintf(obj," %d",lineindices[s]);
  fprintf(obj,"\n");
  (*linecount)++;
}

void write_graph_overlay(FILE *obj, double coord[][2], int genus, int *vcount, int *linecount, int *pointcount)
{
  int i,j,idx,v,w;
  double p[3],labelp[3],lift,label_lift;
  KANTE *run;

  *linecount=0;
  *pointcount=0;
  lift=0.002;
  label_lift=0.055;

  fprintf(obj,"g embedded_graph_edges\n");
  for (i=1;i<=nv;i++)
    if (type[i]!=3)
      {
	run=map[i];
	for (j=0;j<adj[i];j++, run=run->next)
	  if ((run->ursprung<run->name) && (run->cyclenumber==0) &&
	      (type[run->ursprung]!=3) && (type[run->name]!=3))
	    {
	      v=run->ursprung;
	      w=run->name;
	      fprintf(obj,"# graph_edge %d %d segment %d %d type %d %d coord %.8f %.8f %.8f %.8f\n",
		      (run->ends)[0],(run->ends)[1],v,w,type[v],type[w],coord[v][0],coord[v][1],coord[w][0],coord[w][1]);
	      emit_graph_segment(obj,coord,v,w,genus,lift,vcount,linecount);
	    }
      }

  fprintf(obj,"g embedded_graph_vertices\n");
  for (i=1;i<=nv;i++)
    if ((i<=nullvertices) && (type[i]!=3))
      {
	graph_surface_vertex_point(i,coord[i][0],coord[i][1],genus,lift,p);
	graph_surface_vertex_point(i,coord[i][0],coord[i][1],genus,label_lift,labelp);
	idx=obj_emit_line_vertex(obj,p,vcount);
	fprintf(obj,"# graph_vertex_label %d %d %.8f %.8f %.8f\n",idx,i,labelp[0],labelp[1],labelp[2]);
	fprintf(obj,"p %d\n",idx);
	(*pointcount)++;
      }
}

void write_obj(double coord[][2])
{
  FILE *obj, *mtl;
  char basename[1024], objname[1100], mtlname[1100], mtlbase[1100];
  char *leaf;
  int genus, faces, vcount, linecount, pointcount;
  double minx,maxx,miny,maxy;
  OBJVERTEXCACHE cache;

  genus=globalgenus;
  texture_bounds(coord,&minx,&maxx,&miny,&maxy);

  objdrawings++;
  if (objdrawings==1) snprintf(basename,sizeof(basename),"%s",objprefix);
  else snprintf(basename,sizeof(basename),"%s_%d",objprefix,objdrawings);
  snprintf(objname,sizeof(objname),"%s.obj",basename);
  snprintf(mtlname,sizeof(mtlname),"%s.mtl",basename);
  leaf=strrchr(basename,'/');
  if (leaf) leaf++;
  else leaf=basename;
  snprintf(mtlbase,sizeof(mtlbase),"%s.mtl",leaf);

  mtl=fopen(mtlname,"w");
  if (mtl==NULL) { fprintf(stderr,"Can't open material file %s -- exit.\n",mtlname); exit(1); }
  fprintf(mtl,"newmtl graph_surface\nKd 0.780 0.790 0.780\nKa 0.180 0.180 0.180\nKs 0.080 0.080 0.080\nNs 20\n");
  fclose(mtl);

  obj=fopen(objname,"w");
  if (obj==NULL) { fprintf(stderr,"Can't open OBJ file %s -- exit.\n",objname); exit(1); }
  fprintf(obj,"# canonical handle surface generated by planar_cutthroughedges_draw\n");
  fprintf(obj,"# genus %d; genus 0 is a sphere, genus 1 is a torus, genus >=2 is a thickened canonical loop chain\n",genus);
  fprintf(obj,"mtllib %s\n",mtlbase);
  fprintf(obj,"o canonical_handles_%d\n",objdrawings);
  vcount=0;
  faces=0;
  obj_cache_init(&cache,(genus>=2) ? 524288U : 131072U);
  fprintf(obj,"usemtl graph_surface\ns 1\n");
  if (genus<=0) write_sphere_mesh(obj,&cache,&vcount,&faces);
  else if (genus==1) write_torus_mesh(obj,genus,&cache,&vcount,&faces);
  else write_handle_chain_mesh(obj,genus,&cache,&vcount,&faces);
  write_graph_overlay(obj,coord,genus,&vcount,&linecount,&pointcount);

  fclose(obj);
  obj_cache_free(&cache);
  fprintf(stderr,"Wrote OBJ surface %s with %d vertices, %d triangular faces, %d graph polylines, and %d graph points.\n",objname,vcount,faces,linecount,pointcount);
}

void output_pl(double coord[][2], KANTE *outer, int writeouterface)
// starttop_t0>0 means that a vertex of the original graph is the common point of all cutting cycles
{
  int i,j,v,w;
  KANTE *run;
  double scale0, mindistance, length, ve[2];
  int realvertices[N], numberrealvertices;

  if (objprefix) { write_obj(coord); return; }

  if (!writeouterface) for (i=1; i<=nv; i++) if (type[i]==2) type[i]=3;

  mindistance = RADIUS;

  numberrealvertices=0; // vertices on the cutting cycles are also counted
  for (i=1; i<=nv; i++) if (type[i]!=3) { realvertices[numberrealvertices]=i; numberrealvertices++; }

  mindistance = RADIUS;

  for (i=0; i<numberrealvertices-1; i++)
    for (j=i+1; j<numberrealvertices; j++)
    { 
	 vec(ve,coord[realvertices[i]],coord[realvertices[j]]);
	 length=len(ve);
	 if (length<mindistance) { mindistance=length; }
    }

  scale0=0.9;
  mindistance= MAX(5,mindistance);
  if (mindistance<13.0) scale0 *= (mindistance/13.0);
  

  

  if (firstpage)
    {
      //fprintf(stdout,"\\documentclass[multi]{standalone}\n");
      fprintf(stdout,"\\documentclass{article}\n");
      fprintf(stdout,"\\usepackage{tikz}\n");
      fprintf(stdout,"\\usepackage{tkz-euclide}\n");
      fprintf(stdout,"\\addtolength{\\textwidth}{3cm}\n");
      fprintf(stdout,"\\addtolength{\\oddsidemargin}{-1.5cm}\n");
      fprintf(stdout,"\\addtolength{\\evensidemargin}{-1.5cm}\n");
      fprintf(stdout,"\\begin{document}\n");
      firstpage=0;
    }
  else
    fprintf(stdout,"\\newpage\n");
  fprintf(stdout,"\\begin{center}\n");
  //fprintf(stdout,"\\begin{tikzpicture}[scale=0.3]\n");
  if (writeouterface) fprintf(stdout,"\\begin{tikzpicture}[scale=0.07]\n");
  else  fprintf(stdout,"\\begin{tikzpicture}[scale=0.08]\n");
  fprintf(stdout,"\\def\\vertexscale{%1.2lf}\n",scale0);
  if (drawvertexnumbers)
    {
      for (i=1;i<=nv;i++)
	if (type[i]<3)
	  {
	    fprintf(stdout,"\\node [circle,%s,draw,scale=\\vertexscale] (%d) at (%3.5lf,%3.5lf) {%d};\n",vertexcolour[rememberadj[i]],i,coord[i][0],coord[i][1],i); // original vertex
	  }
    }
  else
    {
      for (i=1;i<=nv;i++)
	if (type[i]<3)
	  {
	    fprintf(stdout,"\\node [circle,%s,draw,scale=\\vertexscale,fill=%s] (%d) at (%3.5lf,%3.5lf) {};\n",vertexcolour[rememberadj[i]],vertexcolour[rememberadj[i]],i,coord[i][0],coord[i][1]); // original vertex
	  }
    }

  for (i=1;i<=nv;i++)
    { run=map[i];
      for (j=0;j<adj[i];j++, run=run->next)
	{ if ((run->ursprung<run->name) && (run->cyclenumber==0))
	    {
	      v=run->ursprung; w=run->name;
	      fprintf(stdout,"\\draw [black] (%d) to (%d);\n",v,w);
	    }
	  //if ((run->ursprung<run->name) && (run->cyclenumber==NOTINGRAPH))  fprintf(stdout,"\\draw [blue] (%d) to (%d);\n",run->ursprung,run->name);
	}
    }

  fprintf(stdout,"\\end{tikzpicture}\n");
  fprintf(stdout,"\\end{center}\n");
 
}

void output(double coord[][2])
// starttop_t0>0 means that a vertex of the original graph is the common point of all cutting cycles
{
  int i,j,v,w, cont, corner;
  KANTE *run, *end, *run2;
  double scale0, scale2,scale3,scale4,x,y,c[2], mindistance,length, ve[2], rot_angle;
  int realvertices[N], numberrealvertices;
  char *centercolour;
  double labelmove=1.05, hoekmove=1.0;

  if (objprefix) { write_obj(coord); return; }

  if (straight)
    { if (globalgenus==1) { if (starttop_t0) hoekmove=0.95; else hoekmove=0.97; }
      else hoekmove=0.99;
      labelmove *= 1.02;
    }

  // the original vertices are always the smallest numbers
  if (starttop_t0)
    { for (i=cont=1,corner=0 ; cont; i++) // one vertex not
	if (type[i]!=0) { if (corner) cont=0; else corner=i; }
     }

  numberrealvertices=0; // vertices on the cutting cycles are also counted
  for (i=1; i<=nv; i++) if (type[i]!=3) { realvertices[numberrealvertices]=i; numberrealvertices++; }

  mindistance = RADIUS;

  
  for (i=0; i<numberrealvertices-1; i++)
    for (j=i+1; j<numberrealvertices; j++)
    { 
	 vec(ve,coord[realvertices[i]],coord[realvertices[j]]);
	 length=len(ve);
	 if (length<mindistance) { mindistance=length; }
    }

  scale0=1;  scale2=0.75; scale3 = 1.5; scale4=1;

  mindistance= MAX(5,mindistance);

  if (mindistance<15.0) { scale0 *= (mindistance/15.0); scale2 *= (mindistance/15.0); }
  if (mindistance<13.0) scale4 *= (mindistance/13.0);

  if (starttop_t0 && drawvertexnumbers) rot_angle=0.05*scale0; else  rot_angle=0.04*scale2;

    if (firstpage)
    {
      //fprintf(stdout,"\\documentclass[multi]{standalone}\n");
      fprintf(stdout,"\\documentclass{article}\n");
      fprintf(stdout,"\\usepackage{tikz}\n");
      fprintf(stdout,"\\usepackage{tkz-euclide}\n");
      fprintf(stdout,"\\addtolength{\\textwidth}{3cm}\n");
      fprintf(stdout,"\\addtolength{\\oddsidemargin}{-1.5cm}\n");
      fprintf(stdout,"\\addtolength{\\evensidemargin}{-1.5cm}\n");
      fprintf(stdout,"\\begin{document}\n");
      firstpage=0;
    }
  else
    fprintf(stdout,"\\newpage\n");

     fprintf(stdout,"\\begin{center}\n");
  
    if (blackwhite && labels) fprintf(stdout,"\\begin{tikzpicture}[scale=0.06]\n");
    else  if (blackwhite) fprintf(stdout,"\\begin{tikzpicture}[scale=0.065]\n");
    else   if (labels) fprintf(stdout,"\\begin{tikzpicture}[scale=0.065]\n");
    else fprintf(stdout,"\\begin{tikzpicture}[scale=0.07]\n");

    fprintf(stdout,"\\def\\vertexscale{%1.2lf}\n",scale0);
    fprintf(stdout,"\\def\\labelscale{%1.2lf}\n",scale4);
      
  if (drawvertexnumbers)
    {
      for (i=1;i<=nv;i++)
	if (type[i]<3)
	  {
	    if (type[i]==0) fprintf(stdout,"\\node [circle,%s,draw,scale=\\vertexscale] (%d) at (%3.5lf,%3.5lf) {%d};\n",vertexcolour[rememberadj[i]],i,coord[i][0],coord[i][1],i); // original vertex
	    else if ((type[i]==1) || (type[i]==2)) fprintf(stdout,"\\tkzDefPoint(%3.5lf,%3.5lf){%d}\n",coord[i][0],coord[i][1],i);
	    else { fprintf(stderr,"Problem with vertex types -- exit.\n"); exit(1); }
	  }
    }
  else
  {
    for (i=1;i<=nv;i++)
      if (type[i]<3)
	{
	  if (type[i]==0) fprintf(stdout,"\\node [circle,%s,draw,scale=\\vertexscale,fill=%s] (%d) at (%3.5lf,%3.5lf) {};\n",vertexcolour[rememberadj[i]],vertexcolour[rememberadj[i]],i,coord[i][0],coord[i][1]); // original vertex
	  else if ((type[i]==1) || (type[i]==2)) fprintf(stdout,"\\tkzDefPoint(%3.5lf,%3.5lf){%d}\n",coord[i][0],coord[i][1],i);
	  else { fprintf(stderr,"Problem with vertex types -- exit.\n"); exit(1); }
	}
  }
  
  for (i=1;i<=nv;i++)
    if (type[i]!=3)
      { run=map[i];
      for (j=0;j<adj[i];j++, run=run->next)
	{ if ((run->ursprung<run->name) && (run->cyclenumber==0))
	    {v=run->ursprung; w=run->name;
	      if ((type[v]==1) && (type[w]==1))
		{ 
		  x=coord[v][0]-coord[w][0]; y=coord[v][1]-coord[w][1]; 
		  if (sqrt((x*x)+(y*y))>(RADIUS/1.5)) fprintf(stdout,"\\draw [black] (%d) to (%d);\n",v,w);
		  else
		    {
		      fprintf(stdout,"\\tkzDefPoint(%3.5lf,%3.5lf){A}\n",coord[v][0], coord[v][1] );
		      fprintf(stdout,"\\tkzDefPoint(%3.5lf,%3.5lf){B}\n",(coord[v][0]+coord[w][0])*0.47, (coord[v][1]+coord[w][1])*0.47);
		      fprintf(stdout,"\\tkzDefPoint(%3.5lf,%3.5lf){C}\n",coord[w][0], coord[w][1] );
		      fprintf(stdout,"\\tkzCircumCenter(A,B,C)\\tkzGetPoint{D}\n");
		      if (((coord[v][0]>=0) && (coord[w][0]>=0) && (coord[v][1]>=coord[w][1])) ||
			  ((coord[v][0]<=0) && (coord[w][0]>=0) && (coord[v][1]>=0)) ||
			  ((coord[v][0]<=0) && (coord[w][0]<=0) && (coord[v][1]<=coord[w][1])) ||
			  ((coord[v][0]>=0) && (coord[w][0]<=0) && (coord[v][1]<=0)))
			fprintf(stdout,"\\tkzDrawArc[black](D,A)(C)\n");
		      else
			fprintf(stdout,"\\tkzDrawArc[black](D,C)(A)\n");
		    }
		}
	      else
		{
		  fprintf(stdout,"\\draw [black] (%d) to (%d);\n",v,w);
		  if (labels)
		    {
		      if ((type[v]==0) && (type[w]==1))
			{ if ((run->ends)[0]==v)
			    fprintf(stdout,"\\node [draw=none,fill=none,scale=\\labelscale] () at (%3.5lf,%3.5lf) {%d};\n",coord[w][0]*labelmove,coord[w][1]*labelmove,(run->ends)[1]);
			  else
			    fprintf(stdout,"\\node [draw=none,fill=none,scale=\\labelscale] () at (%3.5lf,%3.5lf) {%d};\n",coord[w][0]*labelmove,coord[w][1]*labelmove,(run->ends)[0]);
			}
		      else
			if ((type[v]==1) && (type[w]==0))
			{ if ((run->ends)[0]==v)
			    fprintf(stdout,"\\node [draw=none,fill=none,scale=\\labelscale]  () at (%3.5lf,%3.5lf) {%d};\n",coord[v][0]*labelmove,coord[v][1]*labelmove,(run->ends)[1]);
			  else
			    fprintf(stdout,"\\node [draw=none,fill=none,scale=\\labelscale] () at (%3.5lf,%3.5lf) {%d};\n",coord[v][0]*labelmove,coord[v][1]*labelmove,(run->ends)[0]);
			}
		    }
		}
	    }
	}
    }

  // now run around the outer face


  if (starttop_t0)
    {
      run=NULL;
      for (i=1; (i<=nv); i++)
	if (type[i]==2)
	  { run=map[i];
	    for (j=0;j<adj[i];j++)
	      { if (run->cyclenumber==0) j=i=nv;  // some copies of starttop_t0 might have degree 2 or just triangulation edges and cut edges -- but not all
		else run=run->next;
	      }
	  }
      while ((run->cyclenumber==0) || (run->cyclenumber == NOTINGRAPH)) run=run->prev;
    }
  else
    {
      for (i=1;(type[i]!=1) && (i<=nv);i++);
      if (i>nv) { fprintf(stderr,"didn't find type 1 vertex in output function -- exit.\n"); exit(1); }
      for (run=map[i]; (run->cyclenumber==0) || (run->cyclenumber == NOTINGRAPH) || (run->cyclenumber != run->prev->cyclenumber); run=run->next);
      while(type[run->ursprung]!=2) run=run->invers->next;
     }

  end=run;

  if (blackwhite)
    {
      do
	{
	  for (run2=run; type[run2->name]!=2; run2=run2->invers->next);
	  if (run->cyclenumber>0)
	    {
	      rotate_clockwise_to(c,coord[run->ursprung],rot_angle);
	      fprintf(stdout,"\\tkzDefPoint(%3.5lf,%3.5lf){A}\n",c[0]*hoekmove, c[1]*hoekmove );
	      rotate_clockwise_to(c,coord[run2->name],-rot_angle);
	      fprintf(stdout,"\\tkzDefPoint(%3.5lf,%3.5lf){B}\n",c[0]*hoekmove, c[1]*hoekmove);
	      if (straight) fprintf(stdout,"\\draw[->,line width=0.9mm, %s](A) to (B);\n",cyclecolour(run->cyclenumber));
	      else
		{
		  fprintf(stdout,"\\tkzDefPoint(0.0,0.0){C}\n");
		  fprintf(stdout,"\\tkzDrawArc[->,line width=0.9mm, %s](C,B)(A)\n",cyclecolour(run->cyclenumber));
		}
	    }
	  else
	    if (run->cyclenumber != NOTINGRAPH)
	    {
	      rotate_clockwise_to(c,coord[run->ursprung],rot_angle);
	      fprintf(stdout,"\\tkzDefPoint(%3.5lf,%3.5lf){A}\n",c[0]*hoekmove, c[1]*hoekmove );
	      rotate_clockwise_to(c,coord[run2->name],-rot_angle);
	      fprintf(stdout,"\\tkzDefPoint(%3.5lf,%3.5lf){B}\n",c[0]*hoekmove, c[1]*hoekmove);
	      if (straight) fprintf(stdout,"\\draw[<-,line width=0.9mm, %s](A) to (B);\n",cyclecolour(run->cyclenumber));
	      else
		{
		  fprintf(stdout,"\\tkzDefPoint(0.0,0.0){C}\n");
		  fprintf(stdout,"\\tkzDrawArc[<-,line width=0.9mm, %s](C,B)(A)\n",cyclecolour(run->cyclenumber));
		}
	    }
	  if (straight)
	    {
	      rotate_clockwise_to(c,coord[run->ursprung],(M_PI)/((double)(numcycles)));
		      if (labels) fprintf(stdout,"\\node [draw=none,fill=none,scale=%1.2lf] () at (%3.5lf,%3.5lf) {%s};\n",
					  scale3,(c[0]+coord[run->ursprung][0])*0.6,(c[1]+coord[run->ursprung][1])*0.59,cyclelabel(run->cyclenumber));
		      else fprintf(stdout,"\\node [draw=none,fill=none,scale=%1.2lf] () at (%3.5lf,%3.5lf) {%s};\n",
				   scale3,(c[0]+coord[run->ursprung][0])*0.56,(c[1]+coord[run->ursprung][1])*0.55,cyclelabel(run->cyclenumber));
	    }
	  else
	    {
	      rotate_clockwise_to(c,coord[run->ursprung],(M_PI)/((double)(2*numcycles)));
		      if (labels) fprintf(stdout,"\\node [draw=none,fill=none,scale=%1.2lf] () at (%3.5lf,%3.5lf) {%s};\n",scale3,c[0]*1.15,c[1]*1.15,cyclelabel(run->cyclenumber));
		      else fprintf(stdout,"\\node [draw=none,fill=none,scale=%1.2lf] () at (%3.5lf,%3.5lf) {%s};\n",scale3,c[0]*1.06,c[1]*1.06,cyclelabel(run->cyclenumber));
	    }
	  run=run2->invers->next;
	}
      while (run!=end);
    }
  else
     {
      do
	{
	  for (run2=run; type[run2->name]!=2; run2=run2->invers->next);
	  if (run->cyclenumber>0)
	    {
	      rotate_clockwise_to(c,coord[run->ursprung],rot_angle);
	      fprintf(stdout,"\\tkzDefPoint(%3.5lf,%3.5lf){A}\n",c[0]*hoekmove, c[1]*hoekmove);
	      rotate_clockwise_to(c,coord[run2->name],-rot_angle);
	      fprintf(stdout,"\\tkzDefPoint(%3.5lf,%3.5lf){B}\n",c[0]*hoekmove, c[1]*hoekmove );
	      if (straight) fprintf(stdout,"\\draw[->,line width=0.9mm, %s](A) to (B);\n",colours[abs(run->cyclenumber)]);
	      else
		{
		  fprintf(stdout,"\\tkzDefPoint(0.0,0.0){C}\n");
		  fprintf(stdout,"\\tkzDrawArc[->,line width=0.9mm, %s](C,B)(A)\n",colours[abs(run->cyclenumber)]);
		}
	    }
	  else
	    if (run->cyclenumber != NOTINGRAPH)
	    {
	      rotate_clockwise_to(c,coord[run->ursprung],rot_angle);
	      fprintf(stdout,"\\tkzDefPoint(%3.5lf,%3.5lf){A}\n",c[0]*hoekmove, c[1]*hoekmove );
	      rotate_clockwise_to(c,coord[run2->name],-rot_angle);
	      fprintf(stdout,"\\tkzDefPoint(%3.5lf,%3.5lf){B}\n",c[0]*hoekmove, c[1]*hoekmove );
	      if (straight) fprintf(stdout,"\\draw[<-,line width=0.9mm, %s](A) to (B);\n",colours[abs(run->cyclenumber)]);
	      else
		{
		  fprintf(stdout,"\\tkzDefPoint(0.0,0.0){C}\n");
		  fprintf(stdout,"\\tkzDrawArc[<-,line width=0.9mm, %s](C,B)(A)\n",colours[abs(run->cyclenumber)]);
		}
	    }
	  run=run2->invers->next;
	  //run=end;
	}
      while (run!=end);
      }
 
  if (drawvertexnumbers)
    {
      for (i=1;i<=nv;i++)
	if (type[i]==2)
	  {
	    if (starttop_t0) fprintf(stdout,"\\node [circle,%s,draw,fill=white,scale=\\vertexscale] (%d) at (%3.5lf,%3.5lf) {%d};\n",vertexcolour[rememberadj[corner]],i,coord[i][0],coord[i][1],corner); // original vertex
		else fprintf(stdout,"\\node [black,circle,draw,fill=white,scale=%1.2lf,line width=1mm] (%d) at (%3.5lf,%3.5lf) {};\n",scale2,i,coord[i][0],coord[i][1]); // subdivision vertex
	  }
    }
  else
  {
    for (i=1;i<=nv;i++)
      if (type[i]==2)
	{
	  if (starttop_t0) fprintf(stdout,"\\node [circle,%s,draw,scale=\\vertexscale,fill=%s] (%d) at (%3.5lf,%3.5lf) {};\n",vertexcolour[rememberadj[corner]],vertexcolour[rememberadj[corner]],i,coord[i][0],coord[i][1]); // original vertex
	  else fprintf(stdout,"\\node [black,circle,draw,scale=%1.2lf,line width=0.4mm] (%d) at (%3.5lf,%3.5lf) {};\n",scale2,i,coord[i][0],coord[i][1]); // subdivision vertex
	}
  }
  
  fprintf(stdout,"\\end{tikzpicture}\n");
  fprintf(stdout,"\\end{center}\n");
  
}


void triangulate_faces(KANTE *outer)
// subdivides all faces -- except for the external one -- with a new vertex and connects them to all boundary vertices
// must only be applied to graphs constructed by the other routines -- no general purpose routine!
{
  int i,j,nextone,oldvertices;
  KANTE *center, *fromold, *run, *start, *end;

  RESETMARKS;

  if (outer==NULL)
    {
      if (starttop_t0)
	{
	  j=0;
	  for (i=1; (i<=nv); i++)
	    if ((type[i]==2) && (adj[i]>2)) { j=i; i=nv; } // in case of degree more than 2 the vertex always has an internal edge
	  for (run=map[j]; (run->cyclenumber) && (run->cyclenumber!=NOTINGRAPH); run=run->next);
	  for (run=run->prev ; (run->cyclenumber==0) ||  (run->cyclenumber==NOTINGRAPH) ; run=run->prev);
	}
      else
	{
	  for (i=1;(type[i]!=1) && (i<=nv);i++);
	  if (i>nv) { fprintf(stderr,"didn't find type 1 vertex in triangulate -- exit.\n"); exit(1); }
	  for (run=map[i]; run->cyclenumber; run=run->next);
	  for (run=run->prev ; (run->cyclenumber==0) ||  (run->cyclenumber==NOTINGRAPH) ; run=run->prev);
	  // now the outer face is left
	}
    }
  else { run=outer; }

  end=run;
  do
    { MARK(run); run=run->invers->next; } // mark the outer face
  while (run!=end);

  oldvertices=nv;

  for (i=1;i<=oldvertices;i++)
    {start=map[i];
      for (j=0;j<adj[i];j++,start=start->next)
	if (UNMARKED(start)) // new face
	{
	  nv++; type[nv]=3; if (nv>N) { fprintf(stderr,"Too many vertices (including the extra vertices used for the construction) for constant N=%d -- exit.\n",N); exit(1); }
	  nextone=nv;
	  adj[nextone]=0;
	  for (run=start; UNMARKED(run); run=run->invers->next) // ends in a new edge
	    {
	      MARK(run);
	      center=getedge(); adj[nextone]++;
	      fromold=getedge(); adj[run->ursprung]++;
	      center->cyclenumber=fromold->cyclenumber=NOTINGRAPH;
	      center->invers=fromold; fromold->invers=center;
	      center->ursprung=fromold->name=nextone;
	      center->name=fromold->ursprung=run->ursprung;
	      center->facesize_left=fromold->facesize_left=0;
	      if (adj[nextone]==1) { map[nextone]= center->next= center->prev=center; }
	      else { center->prev=map[nextone]; center->next=map[nextone]->next; 
		map[nextone]->next=center->next->prev=center; }
	      fromold->prev=run->prev; fromold->next=run;
	      fromold->prev->next=run->prev=fromold;
	      MARK(center); MARK(fromold);
	    }
	}
    }
}


void connect_deg1(KANTE *start)
// Introduces a new vertex inside the face left of start and connects it to all vertices of degree 1 in that face.
// It must be guaranteed that there are at least two such vertices.
{
  KANTE *run, *center,*fromold;

  nv++; type[nv]=3;
  if (nv>N) { fprintf(stderr,"Too many vertices (including the extra vertices used for the construction) for constant N=%d -- exit.\n",N); exit(1); }
  adj[nv]=0;
  if (adj[start->ursprung]==1) start=start->invers->next;
  run=start;
  do
    {
      if (adj[run->ursprung]==1)
	{
	  center=getedge(); adj[nv]++;
	  fromold=getedge(); adj[run->ursprung]++;
	  center->cyclenumber=fromold->cyclenumber=NOTINGRAPH;
	  center->invers=fromold; fromold->invers=center;
	  center->ursprung=fromold->name=nv;
	  center->name=fromold->ursprung=run->ursprung;
	  center->facesize_left=fromold->facesize_left=0;
	  if (adj[nv]==1)
	    { map[nv]= center->next= center->prev=center; }
	  else
	    { center->prev=map[nv]; center->next=map[nv]->next; 
	      map[nv]->next=center->next->prev=center; }
	  fromold->prev=fromold->next=run;
	  run->next=run->prev=fromold;
	}
       run=run->invers->next;	     
    }
  while (run!=start);
}




void spring(double coordinates[][2])
// as described in Olaf's paper in the DIMACS series
{
  int i, j, k, top;
  double maxverhuis, verhuis[N][2];
  KANTE *run, *run2;
  int triangles[2*N][3], numbertriangles;
  static int (*inwhichtriangles)[2*N]=NULL;
    int numinwhich[N], iteration;
  int t, move[N], numbermove; // which vertices may be moved? 0: no 1: yes
  double center_t[2*N][2], square_area_t[2*N],noemer, damping;

  
  if (*inwhichtriangles==NULL)
    { inwhichtriangles=malloc(N*N*2*sizeof(int));
      if (inwhichtriangles==NULL) { fprintf(stderr,"Can not allocate memory in spring() -- exit()\n"); exit(1); }
    }


  RESETMARKS;

  for (i=1; i<=nv; i++) numinwhich[i]=0;
  numbertriangles=0;
  
  for (i=1, numbermove=0; i<=nv; i++)
    {
       if (type[i]==3) // each triangle has a vertex of type 3
	 {
	   move[numbermove]=i; numbermove++;
	   for (j=0, run=map[i]; j<adj[i]; j++, run=run->next)
	     if (UNMARKED(run))
	       {
		 for (k=0, run2=run; k<3; k++,run2=run2->invers->next)
		   {
		     MARK(run2);
		     top=run2->ursprung; 
		     triangles[numbertriangles][k]=top; 
		     inwhichtriangles[top][numinwhich[top]]=numbertriangles;
		     numinwhich[top]++;
		   }
		 numbertriangles++;
	       }
	 }
       else
	 {
	   if (type[i]==0) { move[numbermove]=i; numbermove++; } 
	 }
     }

  // now repeat the replacements:

  maxverhuis=RADIUS;
  damping=1.0;
  for (iteration=0; (maxverhuis> (0.0005*RADIUS)) && (iteration<MAXITERATIONS); iteration++)
    {
      if ((iteration%10)==0) damping *= 1.02;
      maxverhuis=0.0;
      for (i=0;i<numbertriangles;i++)
	{
	  setcenter_t(center_t[i],triangles[i]);
	  square_area_t[i]=area_t(triangles[i]);
	  square_area_t[i]*=square_area_t[i];
	}
      
      
      for (i=0;i<numbermove;i++)
	{ top= move[i];
	  verhuis[top][0]=verhuis[top][1]=noemer=0.0;
	  for (j=0; j<numinwhich[top]; j++)
	    {t=inwhichtriangles[top][j];
	      verhuis[top][0] += square_area_t[t]*(center_t[t][0]-coordinates[top][0]);
	      verhuis[top][1] += square_area_t[t]*(center_t[t][1]-coordinates[top][1]);
	      noemer += square_area_t[t];
	    }
	  verhuis[top][0] /= (noemer * damping); if (maxverhuis<verhuis[top][0]) maxverhuis=verhuis[top][0];
	  verhuis[top][1] /= (noemer * damping);  if (maxverhuis<verhuis[top][1]) maxverhuis=verhuis[top][1];
	}
      
      for (i=0;i<numbermove;i++)
	{ top= move[i];
	  coordinates[top][0] += verhuis[top][0];
	  coordinates[top][1] += verhuis[top][1];
	}
    }
  
}


void wissel(double m[][N], double resx[], double resy[], int pos1, int pos2, int length)
{
  double bufv[N], buf;

  memcpy(bufv,m[pos1],length*sizeof(double));
  memcpy(m[pos1],m[pos2],length*sizeof(double));
  memcpy(m[pos2],bufv,length*sizeof(double));
  buf=resx[pos1]; resx[pos1]=resx[pos2]; resx[pos2]=buf;
  buf=resy[pos1]; resy[pos1]=resy[pos2]; resy[pos2]=buf;
}

void tutte_embed(double coord[][2])
{
  static double (*m)[N]=NULL;
  double resx[N], resy[N], deg, w;
  int i,j,k,top,end,postop, search;
  int vertices[N], pos[N], niv;
  KANTE *run;

  if (*m==NULL)
    { m=malloc(N*N*sizeof(double));
      if (m==NULL) { fprintf(stderr,"Can not allocate memory in titte_embed() -- exit()\n"); exit(1); }
    }

  for (i=1, niv=0; i<=nv; i++) if ((type[i]==0) || (type[i]==3)) { vertices[niv]=i; pos[i]=niv; niv++; }
  
  for (i=0; i<niv; i++)
    {
      resx[i]=resy[i]=0.0; 
      for (j=0; j<=niv; j++) m[i][j]=0.0;
    }

  // lijn 2*i is de vergelijking voor vertices[i] x-coordinate en 
  for (i=0; i<niv; i++)
    {top=vertices[i];
      run=map[top];
      deg = (double) adj[top];
      m[i][i]=1.0;
      for (j=0; j< adj[top]; j++, run=run->next)
	{
	  end=run->name; 
	  if ((type[end]!=0) && (type[end]!=3)) { resx[i] += (coord[end][0]/deg); resy[i] += (coord[end][1]/deg); }
	  else
	    {  postop=pos[end];
	      m[i][postop] = -(1.0/deg);  
	    }
	}
    }

  // Now gaussian elimination on x with also considering the two result vectors

  for (i=0;i<(niv-1);i++) // prepare colum i 
    {
      if (abs(m[i][i])< 0.00001)
	{
	  for (search=i+1; (search<niv) && (abs(m[search][i])< 0.00001); search++);
	  if (search<niv) wissel(m,resx,resy,i,search,niv);
	  if (abs(m[i][i])< 0.00001) { fprintf(stderr,"PROBLEM!!!\n");  exit(0); }
	}
      if (abs(m[i][i])> 0.00001)
	{
	  for (j=i+1; j<niv; j++) // j: line
	    {w=m[j][i]/m[i][i]; 
	      for (k=i;k<niv;k++) // over all colums
		{ m[j][k] -= (w*m[i][k]); }
	      resx[j] -= w*resx[i];
	      resy[j] -= w*resy[i];
	    }
	}
    }

  
  // Now evaluate:
  for (i=niv-1;i>=0;i--)
    { top=vertices[i];
      w=coord[top][0]=resx[i]/m[i][i];
      for (j=i-1; j>=0; j--) resx[j] -= (m[j][i]*w);
      w=coord[top][1]=resy[i]/m[i][i];
      for (j=i-1; j>=0; j--) resy[j] -= (m[j][i]*w);
    }
 }

int checksimple(KANTE *run)
// returns 1 if the face on the left of run is a simple cycle -- 0 otherwise
{
  KANTE *end;

  RESETMARKSV;

  end=run;
  do
    { if (VISMARKED(run->ursprung)) return 0;
      VMARK(run->ursprung);
      run=run->invers->next;
    }
  while (run!=end);

  return 1;
}


int checksimple_mark(KANTE *run, int *size)
// returns 1 if the face on the left of run is a simple cycle -- 0 otherwise
// always runs over the whole face and marks the edges
// in *size the length of the face is stored
{
  KANTE *end;
  int returnvalue =1, length=0;

  RESETMARKSV;

  end=run;
  do
    {
      length++;
      MARK(run);
      if (VISMARKED(run->ursprung)) returnvalue= 0;
      VMARK(run->ursprung);
      run=run->invers->next;
    }
  while (run!=end);

  *size=length;
  return returnvalue;
}


void add_ring(KANTE **startp, int size, int vertextype)
// adds a ring inside the face left of *startp and connects it to once to each vertex occurence of the face.
// *startp is changed to an edge, so that the new face formed by the ring is on the left
 {
   KANTE *start, *run, *run2;
   int i, top;

   if ((nv+size)>N) { fprintf(stderr,"Too many vertices (including the extra vertices used for the construction) for constant N=%d -- exit.\n",N); exit(1); }
   
   start=*startp;

   for (i=1;i<=size;i++)
     {
       type[nv+i]=vertextype;
       run=map[nv+i]=getedge();
       run2=getedge();
       run->ursprung=run2->ursprung=nv+i;
       run->next=run->prev=run2; run2->next=run2->prev=run;
       run->cyclenumber=run2->cyclenumber=NOTINGRAPH;
       adj[nv+i]=2;
     }

   *startp=map[nv+1];

   // make that a cycle:
     for (i=1;i<=size;i++)
     {
       run=map[nv+i];
       top= (nv+1)+(i%size);
       run->invers=map[top]->prev;
       run->name=top; run->invers->name=nv+i;
       run->invers->invers=run;
     }

     for (i=1, run=*startp;i<=size;i++, start=start->invers->next->next, run=run->invers->next)
     {
       connect(run->invers,start,NOTINGRAPH);
     }

     nv+=size;

 }

int countdeg1s(KANTE *start, int *size)
{
  KANTE *run;
  int c=0, s=0;

  run=start;
  do
    { if (adj[run->ursprung]==1) c++;
      s++;
      run=run->invers->next;
    }
  while (run!=start);

  *size=s;
  return c;
}


void remove_1cuts()
// First increases the degree of degree 1 vertices.
// Then checks every face whether it is simple. As by far most faces will be, that is faster than immediately going for bridging 1-cuts.
// If a face is not simple, for each occurence of a cutvertex x in the boundary, the non-cut  vertex before and after a path of cutvertices are connected.
// Here "cutvertex" stands for "cutvertex detected by this face" -- that is: occurs multiple times in the boundary walk of the face.

{
  int i, j, k, oldnv, vertexcount[N+1], size;
  KANTE *run, *run2, *remember;

  
  oldnv=nv;
  // First get rid of vertices of degree 1 by connecting them to the other side or by connecting several ones to a common new vertex in the common face
  for (i=1;i<=oldnv;i++)
    if (adj[i]==1)
      { if (countdeg1s(map[i],&size)>1) connect_deg1(map[i]);
	else
	  {
	    // connect to other side
	    for (run=map[i], k=(size/2)-1; k; run=run->invers->next, k--);
	    if (size%2==0)
	      {
		if (run->name != map[i]->name) connect(run,map[i]->invers,NOTINGRAPH);
		else
		  {
		    connect(run->prev->invers,map[i]->invers,NOTINGRAPH);
		    connect(run->invers->next,map[i]->invers,NOTINGRAPH);
		  }
	      }
	    else
	      {
		// keep local symmetry -- also connect to next one
		if ((run->name != map[i]->name) && (run->invers->next->name != map[i]->name))
		  {
		    connect(run,map[i]->invers,NOTINGRAPH);
		    connect(run->invers->next->next,map[i]->invers,NOTINGRAPH);
		  }
		else
		  {
		    connect(run->prev->invers,map[i]->invers,NOTINGRAPH);
		    connect(run->invers->next->invers->next,map[i]->invers,NOTINGRAPH);
		  }
	      }
	  }
      }

   // Using add_ring() would also be possible, but force the surrounding face to be large, so better do it like this:
    
    RESETMARKS;
    for (i=1;i<=oldnv;i++)
      { run=map[i];
	for (j=0;j<adj[i];j++, run=run->next)
	  if (UNMARKED(run))
	    { if (!checksimple_mark(run,&size))
		{
		  run2=run;
		  for (k=1;k<=nv;k++) vertexcount[k]=0;
		  for (k=0;k<size;k++)
		    {
		      vertexcount[run2->name]++;
		      run2=run2->invers->next;
		    }

		  while (vertexcount[run2->ursprung]>1) run2=run2->invers->next;
		  for (k=0;k<size; )
		    {
		      if (vertexcount[run2->name]>1)
			{
			  remember=run2;
			  for (run2=run2->invers->next; (vertexcount[run2->name]>1) &&  (k<size); k++, run2=run2->invers->next);
			  connect(run2,remember->prev->invers,NOTINGRAPH);
			  run2=remember->prev;
			  k++;
			}
			  else { run2=run2->invers->next; k++; }
		    }
		}
	    }
      }

    return;
}


void embed()
// embeds the outer face on a polygon placed on a cycle. The points that correspond to the one central cut vertex (recognized as the degree 2 ones on a cycle
// in case of a facial center) are distributed equally around the circle around (0,0). The radius of the circle is 100.0
{

  KANTE *run, *nextstart;
  int i, j, cycn, top, newtop;
  int lengthpath[4*MAXGENUS];
  KANTE *startsegment[4*MAXGENUS];
  double coordinates[N+1][2]={{0.0}}, angle; // angle between two corners
  double secondcoordinates[2]={0.0}, diff[2];

  for (i=0;i<=N;i++)
    {
      boundary_side[i]=(-1);
      boundary_cyc[i]=0;
      boundary_t[i]=0.0;
    }

  //first look for the boundary
  if (starttop_t0==0)
    {
      for (i=1;i<=nv;i++)
	if (adj[i]==2)
	  {run=map[i];
	    if ((run->cyclenumber) && (adj[run->name]>2))
	      { if (run->invers->next->cyclenumber==run->cyclenumber) // outer face left
		  startedge=run;
		else startedge=run->next;
		i=nv;
	      }
	  }
    }
  else
    {
      run=map[starttop_t0];
      while ((run->cyclenumber==0) || (run->prev->cyclenumber==0)) run=run->next;
      startedge=run;  // outer face left
    }


  if (startedge==NULL) { fprintf(stderr,"Can't find startedge in embed() -- exit\n"); exit(30); }

  numberpaths=0;

  nextstart=startedge;
  do
    {
      cycn=nextstart->cyclenumber;
      lengthpath[numberpaths]=1;
      startsegment[numberpaths]=nextstart;
      for (run=nextstart->invers->next; run->cyclenumber==cycn; run=run->invers->next)
	{ (lengthpath[numberpaths])++; }
      nextstart=run;
      numberpaths++;
    }
  while (nextstart!=startedge); // numberpaths is now 4*globalgenus

  remove_1cuts();

  angle=(2.0*M_PI)/((double) numberpaths);
  coordinates[0][0]=0.0;
  coordinates[0][1]= -RADIUS;

  for (i=0;i<numberpaths;i++)
    {
      run=startsegment[i];
      top=(run->ursprung);
      boundary_side[top]=i;
      boundary_cyc[top]=run->cyclenumber;
      boundary_t[top]=0.0;
      rotate_clockwise_to(coordinates[top],coordinates[0],((double)i)*angle+(angle/2.0));
      rotate_clockwise_to(secondcoordinates,coordinates[0],((double)(i+1))*angle+(angle/2.0));
      diff[0]=secondcoordinates[0]-coordinates[top][0];
      diff[1]=secondcoordinates[1]-coordinates[top][1];
      if (straight)
	  for (j=1; j<lengthpath[i]; j++, run=run->invers->next)
	    { newtop=run->name;
	      boundary_side[newtop]=i;
	      boundary_cyc[newtop]=run->cyclenumber;
	      boundary_t[newtop]=((double)j)/((double)lengthpath[i]);
	      coordinates[newtop][0]=coordinates[top][0]+((double)j/lengthpath[i])*diff[0];
	      coordinates[newtop][1]=coordinates[top][1]+((double)j/lengthpath[i])*diff[1];
	    }
      else
	  for (j=1; j<lengthpath[i]; j++, run=run->invers->next)
	    { newtop=run->name;
	      boundary_side[newtop]=i;
	      boundary_cyc[newtop]=run->cyclenumber;
	      boundary_t[newtop]=((double)j)/((double)lengthpath[i]);
	      coordinates[newtop][0]=coordinates[top][0]+((double)j/lengthpath[i])*diff[0];
	      coordinates[newtop][1]=coordinates[top][1]+((double)j/lengthpath[i])*diff[1];
	      rotate_clockwise_to(coordinates[newtop],coordinates[top],((double)j)*(angle/((double)lengthpath[i])));
	    }
    }

  triangulate_faces(NULL);
  tutte_embed(coordinates);
  spring(coordinates);
  output(coordinates);

}

void straightenpath(double coordinates[][2])
{
  int i,j,length;

  for (i=0;i<numberpaths;i++)
    { length=pathlength[i];
      for (j=1;j<length; j++)
	{
	  coordinates[paths[i][j]][0]= coordinates[paths[i][0]][0]+(coordinates[paths[i][length]][0]-coordinates[paths[i][0]][0])*((double)j/(double)length);
	  coordinates[paths[i][j]][1]= coordinates[paths[i][0]][1]+(coordinates[paths[i][length]][1]-coordinates[paths[i][0]][1])*((double)j/(double)length);
	}
    }
}

void embed_planar()
// embeds the outer face on a polygon placed on a cycle. The outer face is chosen as a face that has largest size. Among those faces one with a vertex at largest possible distance from this face is chosen.
// If the face is simple, the vertices are distributed equally around the circle around (0,0). The radius of the circle is 100.0. If it is not simple, an artifical cycle of the same length around that face is formed and later not output.
  
{

  KANTE *run;
  int i, j, top, maxsize, maxdist=0, buffer, writeouterface;
  KANTE *maxfaceleft;
  double coordinates[N+1][2]={{0.0}}, angle; // angle between two corners

  RESETMARKS;

  maxsize=0;

  if (chosenedge[0]==0)
    {
      for (i=1; i<=nv; i++)
	{ 
	  for (run=map[i], j=0;j<adj[i];j++, run=run->next)
	    if (UNMARKED(run))
	      {
		if ((run->facesize_left)>maxsize)
		  {
		    maxsize=(run->facesize_left);
		    maxdist=bfsdist_face(run);
		    maxfaceleft=run;
		  }
		else
		  if ((run->facesize_left==maxsize) && checksimple(run))
		    { buffer=bfsdist_face(run);
		      if (buffer>maxdist)
			{
			  maxdist=buffer;
			  maxfaceleft=run;
			}
		    }
	      }
	}
    }
  else // that is: outer face is chosen
    {
      i=chosenedge[0]; buffer=0;
      for (run=map[i], j=0;j<adj[i];j++, run=run->next)
	if (run->name==chosenedge[1])
	      {
		buffer=1;
		maxsize=(run->facesize_left);
		maxdist=bfsdist_face(run);
		maxfaceleft=run;
	      }
      if (buffer==0) { fprintf(stderr,"Edge describing outer face not found! Exit!\n"); exit(1); }
    }

  

  if (!checksimple(maxfaceleft)) { add_ring(&maxfaceleft,maxsize,2); writeouterface=0; }
  else writeouterface=1;

  remove_1cuts();

  angle=(2.0*M_PI)/((double) maxsize);
  coordinates[0][0]=0.0;
  coordinates[0][1]= -100.0;

  for (i=0, run=maxfaceleft; i<maxsize; i++, run=run->invers->next)
    {
      top=(run->ursprung); 
      type[top]=2;
      rotate_clockwise_to(coordinates[top],coordinates[0],((double)i)*angle+(angle/2.0));
     }

  triangulate_faces(maxfaceleft);
  tutte_embed(coordinates);
  spring(coordinates);
  if (is_tree) straightenpath(coordinates);
  output_pl(coordinates,maxfaceleft,writeouterface);
  
}



void usage(char str[])
{
  fprintf(stderr,"\nusage %s (v,f) [b] [mx] [n] [l] [mx] [cv x] [cf x y] [d x col] [N x y] [s] [t] [o prefix]\n",str);
  fprintf(stderr,"Only for connected embedded graphs numbered from 1...|V|.\n");
  fprintf(stderr,"The embedded input graph is cut (if genus>0) to form a plane representation and a drawing as tikz in a latex file is written to stdout.\n\n");
  fprintf(stderr,"In case of genus>0 at least one of the options v and f must be present. \n");
  fprintf(stderr,"Option v: take one of the original vertices as the common point of the cutting cycles.\n");
  fprintf(stderr,"Option f: take a point inside a face as the common point of the cutting cycles.\n");
  fprintf(stderr,"In case both options are given, two drawings of each input graph are produced -- one with face center, one with vertex center.\n\n");
  fprintf(stderr,"Option b: for black and white -- use labels A, B, C for the edges to be identified instead of colours (default).\n");
  fprintf(stderr," \t For genus 6 or larger labels are added automatically, but colours are still used.\n\n");
  fprintf(stderr,"Option n: Do not give vertex numbers, but just draw black dots.\n\n");
  fprintf(stderr,"Option l: Write small labels at the boundary -- indicating where edges crossing the boundary will finally go to.\n\n");
  fprintf(stderr,"Option: mx: (with x a number) first look only for cuts that never cut the same edge twice -- in the drawing no edge of the graph crosses the boundary twice.\n");
  fprintf(stderr,"\t Such a cut need not exist, so an upper bound x on the number of edges crossing a separating cycle must be given.\n");
  fprintf(stderr,"\t Furthermore the search can last very long -- and find nothing -- so don't use large x -- maybe x=3 or so.\n");
  fprintf(stderr,"\t in difficult cases. It can also lead to too many vertices during the construction. A good value for y is 2 or at most 3. \n\n");
  fprintf(stderr,"Option cv x: with x a number. Only active in combination with v: take vertex x as the center of the cutting cycles. \n");
  fprintf(stderr,"\t Without this option or if there is no vertex x in the graph, the program chooses itself.\n");
  fprintf(stderr,"Option cf x y: with x, y numbers. Only active in combination with f (or genus 0): take the face on the left from the edge x->y as the center of the cutting cycles.\n");
  fprintf(stderr,"\t In case of genus 0 the face described is taken as the outer face.\n");
  fprintf(stderr,"\t Without this option or if there is no such edge in the graph, the program chooses itself.\n");
    fprintf(stderr,"Option d x col: with x a number and col a colour known to tikz, so e.g. blue, red, green. In the output, vertices with degree x get colour col.\n");
  fprintf(stderr,"Option N x y: with x,y numbers. Do not cut through edge {x,y} if present. This option can be used for several edges. If all edges of a face are chosen, it must be made sure\n");
  fprintf(stderr,"\t that this face is not chosen as the outer face by cf or v. Note that even then it is possible that a solution is hard to find or doesn't exist.\n");
  fprintf(stderr,"Option s makes the program use straight line segments for the boundary, so the outer face will be a polygon instead of a circle.\n");
  fprintf(stderr,"Option t makes the program interpret the input not as binary input of planarcode type, but as the ASCII version of it.\n");
  fprintf(stderr,"Option o prefix writes prefix.obj, prefix.mtl, and prefix.ppm as a textured canonical-handle OBJ export instead of writing LaTeX to stdout.\n");
  exit(1);
}

int bfs_connected()
{
  int i, j, list[N+1], ll, top, top2;
  KANTE *run;

  RESETMARKSV;

  list[0]=1; ll=1; VMARK(1);

  for (i=0; i<ll; i++)
    { top=list[i];
       run=map[top];
       for (j=0;j<adj[top]; j++, run=run->next)
	 if (VUNMARKED(run->name))
	   {
	     if (ll==(nv-1)) return 1; // this would be the last vertex in the list
	     top2=run->name;
	     VMARK(top2);
	     list[ll]=top2; ll++;
	   }
    }

  // otherwise disconnected

  return 0;
}


/*******************MAIN********************************/

int main(int argc, char *argv[])

{

  int zaehlen=0, lblackwhite=0, drawings=0;
  unsigned short code[7*N+2];
  int i, j, v1, v2, lauf, edges, faces, genus;
  int progress=0, vertexstart=0, facestart=0;

  for (i=0;i<SMALLN;i++) for (j=0;j<SMALLN;j++) allowedcut[i][j]=1;
 
  for (i=0;i<N; i++) vertexcolour[i]=defaultcolour;
  
  for (i=1;i<argc; i++)
    {
      if (argv[i][0]=='m') { maxcross=atoi(argv[i]+1); }
      else if (argv[i][0]=='n') { drawvertexnumbers=0;}
      else if (argv[i][0]=='b') { lblackwhite=1; forceblackwhite=1; }
      else if (argv[i][0]=='f') facestart=1;
      else if (argv[i][0]=='v') vertexstart=1;
      else if (argv[i][0]=='p') progress=1;
      else if (argv[i][0]=='s') straight=1;
      else if (argv[i][0]=='l') labels=1;
      else if (argv[i][0]=='t') text=1;
      else if (argv[i][0]=='o') { i++; if (i>=argc) usage(argv[0]); objprefix=argv[i]; }
      else if (argv[i][0]=='c')
	{ if (argv[i][1]=='v') {i++; chosenvertex=atoi(argv[i]); }
	  else if (argv[i][1]=='f') {i++; chosenedge[0]=atoi(argv[i]); i++; chosenedge[1]=atoi(argv[i]); }
	  else usage(argv[0]);
	}
      else if (argv[i][0]=='d')
	{ 
	  if ((i>=argc-2) || (!isdigit(argv[i+1][0]))) { usage(argv[0]); }
	  vertexcolour[atoi(argv[i+1])]=argv[i+2];
	  i+=2;
	}
      else if (argv[i][0]=='N')
	{
	  i++; v1=atoi(argv[i]); i++; v2=atoi(argv[i]); 
	  allowedcut[v1][v2]=allowedcut[v2][v1]=0;
	}
      
      else usage(argv[0]);
    }

  if (labels && (!drawvertexnumbers))
    {
      fprintf(stderr,"The combination of options l and n does not make sense.\n");
      usage(argv[0]);
    }

 srand48(time(0));
 
 edgebuffer=malloc(sizeof(KANTE)*MAXEDGES);
 if (edgebuffer==NULL) { fprintf(stderr,"can't get edges -- exit!\n"); exit(1); }
 available_edges=MAXEDGES; used_edges=0;
 for (i=0;i<MAXEDGES;i++)
   { edgelist[i]=edgebuffer+i; // in the beginning they are in the normal order, but this can be mixed up later
     edgebuffer[i].edgenumber=i+1;
   }

for (;lesecode(code,&lauf,stdin);)
  {
    zaehlen++;
    if (progress) fprintf(stderr,"Number %d\n",zaehlen);
    decodiereplanar(code, &nv, map, adj, type);
    for (i=1;i<=nv;i++) rememberadj[i]=adj[i];
    if (!bfs_connected()) usage(argv[0]);
    faces=count_faces_and_get_facesizes();
    for (i=1, edges=0; i<=nv; i++) edges+=adj[i];
    edges=edges/2;
    globalgenus=genus= ((2+edges-nv-faces)/2);

    if (genus && (vertexstart==0) && (facestart==0)) usage(argv[0]);

    if (genus>MAXGENUS) { fprintf(stderr,"Genus %d larger than maximum allowed genus %d. Exit.\n",genus, MAXGENUS); exit(1); }
    if (genus>MAXCOLOURGENUS) { blackwhite=1; } else blackwhite=lblackwhite; 

    if (genus==0) { embed_planar(); drawings++; cleargraph(); }
    else 
      {
	numcycles=2*genus;
	if (vertexstart)
	  {
	    if (cutit_v())
	      {
		cut_open_v();
		embed();
		drawings++;
	      }
	    else fprintf(stderr,"No way found to cut it...\n");
	    cleargraph();
	  }
	  if (facestart)
	  {
	    starttop_t0=0;
	    if (vertexstart)
	      {
		decodiereplanar(code, &nv, map, adj, type);
		count_faces_and_get_facesizes();
	      }
	    if (cutit())
	      { 
		cut_open();
		embed();
		drawings++;
	      }
	    else fprintf(stderr,"No way found to cut it...\n");
	    cleargraph();
	  }
      }
  }
 if (!objprefix) fprintf(stdout,"\\end{document}\n");

 if (objprefix) fprintf(stderr,"%s: Wrote %d OBJ drawing(s) of %d graph(s).\n",argv[0],drawings,zaehlen);
 else fprintf(stderr,"%s: Wrote %d tikz-drawing(s) of %d graph(s) to stdout.\n",argv[0],drawings,zaehlen);
return(0);

}
