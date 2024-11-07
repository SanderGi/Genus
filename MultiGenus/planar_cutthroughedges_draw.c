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
#define MAXCOLOURGENUS 5 // otherwise the colour list must be updated -- already for genus 5 (10+1 colours) colours are sometimes difficult to distinguish
#define MAXGENUS 20
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
int maxcross=0, blackwhite=0, drawvertexnumbers=1, labels=0, straight=0, text=0;
int chosenvertex=0, chosenedge[2]={0};
int firstpage=1;
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

void output_pl(double coord[][2], KANTE *outer, int writeouterface)
// starttop_t0>0 means that a vertex of the original graph is the common point of all cutting cycles
{
  int i,j,v,w;
  KANTE *run;
  double scale0, mindistance, length, ve[2];
  int realvertices[N], numberrealvertices;

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
	      if (straight) fprintf(stdout,"\\draw[->,line width=0.9mm, gray](A) to (B);\n");
	      else
		{
		  fprintf(stdout,"\\tkzDefPoint(0.0,0.0){C}\n");
		  fprintf(stdout,"\\tkzDrawArc[->,line width=0.9mm, gray](C,B)(A)\n");
		}
	    }
	  else
	    if (run->cyclenumber != NOTINGRAPH)
	    {
	      rotate_clockwise_to(c,coord[run->ursprung],rot_angle);
	      fprintf(stdout,"\\tkzDefPoint(%3.5lf,%3.5lf){A}\n",c[0]*hoekmove, c[1]*hoekmove );
	      rotate_clockwise_to(c,coord[run2->name],-rot_angle);
	      fprintf(stdout,"\\tkzDefPoint(%3.5lf,%3.5lf){B}\n",c[0]*hoekmove, c[1]*hoekmove);
	      if (straight) fprintf(stdout,"\\draw[<-,line width=0.9mm, gray](A) to (B);\n");
	      else
		{
		  fprintf(stdout,"\\tkzDefPoint(0.0,0.0){C}\n");
		  fprintf(stdout,"\\tkzDrawArc[<-,line width=0.9mm, gray](C,B)(A)\n");
		}
	    }
	  if (straight)
	    {
	      rotate_clockwise_to(c,coord[run->ursprung],(M_PI)/((double)(numcycles)));
	      if (labels) fprintf(stdout,"\\node [draw=none,fill=none,scale=%1.2lf] () at (%3.5lf,%3.5lf) {%c};\n",
				  scale3,(c[0]+coord[run->ursprung][0])*0.6,(c[1]+coord[run->ursprung][1])*0.59,'A'-1+abs(run->cyclenumber));
	      else fprintf(stdout,"\\node [draw=none,fill=none,scale=%1.2lf] () at (%3.5lf,%3.5lf) {%c};\n",
			   scale3,(c[0]+coord[run->ursprung][0])*0.56,(c[1]+coord[run->ursprung][1])*0.55,'A'-1+abs(run->cyclenumber));
	    }
	  else
	    {
	      rotate_clockwise_to(c,coord[run->ursprung],(M_PI)/((double)(2*numcycles)));
	      if (labels) fprintf(stdout,"\\node [draw=none,fill=none,scale=%1.2lf] () at (%3.5lf,%3.5lf) {%c};\n",scale3,c[0]*1.15,c[1]*1.15,'A'-1+abs(run->cyclenumber));
	      else fprintf(stdout,"\\node [draw=none,fill=none,scale=%1.2lf] () at (%3.5lf,%3.5lf) {%c};\n",scale3,c[0]*1.06,c[1]*1.06,'A'-1+abs(run->cyclenumber));
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
  int i, j, numberpaths, cycn, top, newtop;
  int lengthpath[4*MAXGENUS];
  KANTE *startsegment[4*MAXGENUS];
  double coordinates[N+1][2]={{0.0}}, angle; // angle between two corners
  double secondcoordinates[2]={0.0}, diff[2];

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
      rotate_clockwise_to(coordinates[top],coordinates[0],((double)i)*angle+(angle/2.0));
      rotate_clockwise_to(secondcoordinates,coordinates[0],((double)(i+1))*angle+(angle/2.0));
      diff[0]=secondcoordinates[0]-coordinates[top][0];
      diff[1]=secondcoordinates[1]-coordinates[top][1];
      if (straight)
	  for (j=1; j<lengthpath[i]; j++, run=run->invers->next)
	    { newtop=run->name;
	      coordinates[newtop][0]=coordinates[top][0]+((double)j/lengthpath[i])*diff[0];
	      coordinates[newtop][1]=coordinates[top][1]+((double)j/lengthpath[i])*diff[1];
	    }
      else
	  for (j=1; j<lengthpath[i]; j++, run=run->invers->next)
	    { newtop=run->name;
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
  fprintf(stderr,"\nusage %s (v,f) [b] [mx] [n] [l] [mx] [cv x] [cf x y] [d x col] [N x y] [s] [t]\n",str);
  fprintf(stderr,"Only for connected embedded graphs numbered from 1...|V|.\n");
  fprintf(stderr,"The embedded input graph is cut (if genus>0) to form a plane representation and a drawing as tikz in a latex file is written to stdout.\n\n");
  fprintf(stderr,"In case of genus>0 at least one of the options v and f must be present. \n");
  fprintf(stderr,"Option v: take one of the original vertices as the common point of the cutting cycles.\n");
  fprintf(stderr,"Option f: take a point inside a face as the common point of the cutting cycles.\n");
  fprintf(stderr,"In case both options are given, two drawings of each input graph are produced -- one with face center, one with vertex center.\n\n");
  fprintf(stderr,"Option b: for black and white -- use labels A, B, C for the edges to be identified instead of colours (default).\n");
  fprintf(stderr," \t For genus 6 or larger this is done automatically as colours would be hard to distinguish.\n\n");
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
      else if (argv[i][0]=='b') { lblackwhite=1; }
      else if (argv[i][0]=='f') facestart=1;
      else if (argv[i][0]=='v') vertexstart=1;
      else if (argv[i][0]=='p') progress=1;
      else if (argv[i][0]=='s') straight=1;
      else if (argv[i][0]=='l') labels=1;
      else if (argv[i][0]=='t') text=1;
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
 fprintf(stdout,"\\end{document}\n");

 fprintf(stderr,"%s: Wrote %d tikz-drawing(s) of %d graph(s) to stdout.\n",argv[0],drawings,zaehlen);
return(0);

}



