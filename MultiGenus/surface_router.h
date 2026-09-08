/* SPDX-FileCopyrightText: 2026 Alexander Metzger
 * SPDX-License-Identifier: GPL-2.0-only
 * Higher-genus OBJ layout. Route on the dual of an embedded triangulation,
 * with constrained mesh edges and counterclockwise vertex ports. No polygon
 * projection or seam interpolation is involved. Included by planar_draw.c.
 */
#ifndef SURFACE_ROUTER_H
#define SURFACE_ROUTER_H

typedef struct { double p[3],u,v,axis[3]; int h,kind,sides[2]; } SRPoint;
typedef struct { int v[3], next[3], wall[3], owner,base; } SRTriangle;
typedef struct { int a,b,face,side,used; } SRHash;
typedef struct { int u,v,start,end,startbase,endbase,*path,length,*poly,plen,left,right,spinecheck; } SRRoute;
typedef struct {
  SRPoint *points,*centers,*normals;
  SRTriangle *triangles,*base_triangles;
  int nbases,base_np,compact;
  int np,nt,pcap,tcap,nu,nw,genus;
  int *walls,nwalls,wcap;
  int *removed,*vertex,*ports, *blocked;
  int *previous,*stamp,*heap,*heap_pos;
  double *repulsion,*distance,*graphdistance;
  int strategy;
  int serial,heap_size;
  unsigned int random;
} SRMesh;

static void *sr_alloc(size_t n, size_t size)
{
  void *p=calloc(n,size);
  if (!p) { fprintf(stderr,"Surface router: allocation failed.\n"); exit(1); }
  return p;
}
static unsigned int sr_random(SRMesh *m)
{ m->random ^= m->random << 13; m->random ^= m->random >> 17; m->random ^= m->random << 5; return m->random; }
static double sr_distance(SRPoint a, SRPoint b)
{
  double x=a.p[0]-b.p[0],y=a.p[1]-b.p[1],z=a.p[2]-b.p[2];
  return sqrt(x*x+y*y+z*z);
}
static SRPoint sr_lerp(SRPoint a, SRPoint b, double t)
{
  SRPoint p; int k; double du=b.u-a.u,dv=b.v-a.v;
  memset(&p,0,sizeof(p));
  for(k=0;k<3;k++) p.p[k]=a.p[k]+t*(b.p[k]-a.p[k]);
  if(du>0.5)du-=1;if(du< -0.5)du+=1;if(dv>0.5)dv-=1;if(dv< -0.5)dv+=1;
  p.h=a.h==b.h ? a.h : -1;p.u=a.u+t*du;p.v=a.v+t*dv;
  return p;
}
static int sr_point(SRMesh *m, SRPoint p)
{
  if(m->np==m->pcap) {
    m->pcap=m->pcap ? m->pcap*2 : 4096;
    m->points=realloc(m->points,m->pcap*sizeof(SRPoint));
    if(!m->points) { fprintf(stderr,"Surface router: allocation failed.\n"); exit(1); }
  }
  m->points[m->np]=p; return m->np++;
}
static void sr_triangle(SRMesh *m,int a,int b,int c,int owner)
{
  SRTriangle *t;
  if(m->nt==m->tcap) {
    m->tcap=m->tcap ? m->tcap*2 : 8192;
    m->triangles=realloc(m->triangles,m->tcap*sizeof(SRTriangle));
    if(!m->triangles) { fprintf(stderr,"Surface router: allocation failed.\n"); exit(1); }
  }
  t=&m->triangles[m->nt++];t->base=m->nt-1;
  t->v[0]=a;t->v[1]=b;t->v[2]=c;t->owner=owner;
  t->next[0]=t->next[1]=t->next[2]=-1;
  t->wall[0]=t->wall[1]=t->wall[2]=0;
}
static int sr_grid(SRMesh *m,int h,int u,int v)
{ return (h*m->nu+(u+m->nu)%m->nu)*m->nw+(v+m->nw)%m->nw; }
static void sr_remove(SRMesh *m,int h,int u,int v,int ru,int rv)
{
  int i,j;
  for(i=-ru;i<ru;i++) for(j=-rv;j<rv;j++) m->removed[sr_grid(m,h,u+i,v+j)]=1;
}
/* Counterclockwise boundary of a rectangular disk in a torus chart. */
static int sr_ring(SRMesh *m,int h,int u,int v,int ru,int rv,int *ring)
{
  int i,j,n=0;
  for(i=-ru;i<ru;i++) ring[n++]=sr_grid(m,h,u+i,v-rv);
  for(j=-rv;j<rv;j++) ring[n++]=sr_grid(m,h,u+ru,v+j);
  for(i=ru;i>-ru;i--) ring[n++]=sr_grid(m,h,u+i,v+rv);
  for(j=rv;j>-rv;j--) ring[n++]=sr_grid(m,h,u-ru,v+j);
  return n;
}
static void sr_mesh(SRMesh *m,int genus,int seed)
{
  int maxdegree=0,h,i,j,k,a,b,c,d,ring[256],other[256],prev[256],next[256],n,step,v,ru,rv,best,trial,ok;
  double u,w,score,bestscore,dist;
  SRPoint p;
  memset(&p,0,sizeof(p));
  memset(m,0,sizeof(*m)); m->genus=genus;m->nu=64;m->nw=48;m->random=seed;m->strategy=((seed-17)/7919)%3;
  for(i=1;i<=nv;i++)if(adj[i]>maxdegree)maxdegree=adj[i];
  /* Large sparse maps use normal arcs on a coarser routing triangulation.
   * Keep the established small-map layout and degree-dependent disk capacity. */
  m->compact=nv>50 && genus>=8 && nv<=10*genus && maxdegree<=4;
  if(m->compact){m->nu=24;m->nw=16;}
  if(maxdegree>24){m->nu+=8*((maxdegree+3)/4-6);m->nw+=4*((maxdegree+3)/4-6);}
  m->removed=sr_alloc(genus*m->nu*m->nw,sizeof(int));
  m->vertex=sr_alloc(nv+1,sizeof(int));
  m->ports=sr_alloc((nv+1)*MAXVAL,sizeof(int));
  for(h=0;h<genus;h++) for(i=0;i<m->nu;i++) for(j=0;j<m->nw;j++) {
    u=2*M_PI*i/m->nu;w=2*M_PI*j/m->nw;p.h=h;p.u=i/(double)m->nu;p.v=j/(double)m->nw;
    p.p[0]=(h-(genus-1)*0.5)*3.5+(1.18+0.38*cos(w))*cos(u);
    p.p[1]=(1.18+0.38*cos(w))*sin(u);p.p[2]=0.38*sin(w);
    sr_point(m,p);
  }
  /* Remove facing disks and join their boundaries with an embedded annulus.
   * This is a connected sum of tori, hence exactly the requested genus. */
  for(h=0;h<genus-1;h++) {
    sr_remove(m,h,0,0,m->compact ? 1 : 2,m->compact ? 2 : 5);sr_remove(m,h+1,m->nu/2,0,m->compact ? 1 : 2,m->compact ? 2 : 5);
    n=sr_ring(m,h,0,0,m->compact ? 1 : 2,m->compact ? 2 : 5,ring);
    for(k=0;k<n;k++) {
      a=ring[k]-h*m->nu*m->nw;i=a/m->nw;j=a%m->nw;
      other[k]=sr_grid(m,h+1,m->nu/2-i,j);prev[k]=ring[k];
    }
    for(step=1;step<=8;step++) {
      for(k=0;k<n;k++) next[k]=step==8 ? other[k] : sr_point(m,sr_lerp(m->points[ring[k]],m->points[other[k]],step/8.0));
      for(k=0;k<n;k++) {
        j=(k+1)%n;
        sr_triangle(m,prev[k],next[j],next[k],0);
        sr_triangle(m,prev[k],prev[j],next[j],0);
      }
      memcpy(prev,next,n*sizeof(int));
    }
  }
  /* Reserve mutually separated disks. Farthest candidate placement distributes
   * vertices over the whole surface; seeds vary the first placement and ports. */
  for(v=1;v<=nv;v++) {
    ru=rv=(adj[v]+3)/4;
    if(ru<1)ru=rv=1;
    if(ru>16) { fprintf(stderr,"Surface router: vertex degree exceeds disk capacity.\n"); exit(1); }
    best=-1;bestscore=-1;
    for(trial=0;trial<1200;trial++) {
      h=sr_random(m)%genus;i=sr_random(m)%m->nu;j=sr_random(m)%m->nw;
      ok=1;
      for(a=-ru-1;a<=ru;a++)for(b=-rv-1;b<=rv;b++)if(m->removed[sr_grid(m,h,i+a,j+b)])ok=0;
      if(!ok)continue;
      k=sr_grid(m,h,i,j);score=100;
      for(a=1;a<v;a++) {
        dist=sr_distance(m->points[k],m->points[m->vertex[a]]);
        if(dist<score)score=dist;
      }
      score*=0.9+0.2*(sr_random(m)%1000)/1000.0;
      if(score>bestscore){bestscore=score;best=k;}
    }
    if(best<0) { fprintf(stderr,"Surface router: surface is too crowded for vertex disks.\n"); exit(1); }
    h=best/(m->nu*m->nw);i=(best/m->nw)%m->nu;j=best%m->nw;
    sr_remove(m,h,i,j,ru,rv);n=sr_ring(m,h,i,j,ru,rv,ring);
    m->vertex[v]=sr_point(m,m->points[best]);
    a=m->nt;
    for(k=0;k<n;k++)sr_triangle(m,m->vertex[v],ring[k],ring[(k+1)%n],v);
    b=sr_random(m)%n;
    for(k=0;k<adj[v];k++)m->ports[v*MAXVAL+k]=a+(b+(k*n/adj[v]))%n;
  }
  for(h=0;h<genus;h++)for(i=0;i<m->nu;i++)for(j=0;j<m->nw;j++)if(!m->removed[sr_grid(m,h,i,j)]) {
    a=sr_grid(m,h,i,j);b=sr_grid(m,h,i+1,j);c=sr_grid(m,h,i+1,j+1);d=sr_grid(m,h,i,j+1);
    sr_triangle(m,a,b,c,0);sr_triangle(m,a,c,d,0);
  }
}
static void sr_adjacency(SRMesh *m)
{
  int cap=1,i,j,a,b,slot,k;SRHash *hash;
  while(cap<m->nt*8)cap*=2;
  hash=sr_alloc(cap,sizeof(SRHash));
  for(i=0;i<m->nt;i++)for(j=0;j<3;j++){m->triangles[i].next[j]=-1;m->triangles[i].wall[j]=0;}
  for(i=0;i<m->nt;i++)for(j=0;j<3;j++) {
    a=m->triangles[i].v[j];b=m->triangles[i].v[(j+1)%3];if(a>b){k=a;a=b;b=k;}
    slot=((unsigned int)a*73856093U^(unsigned int)b*19349663U)&(cap-1);
    while(hash[slot].used && (hash[slot].a!=a || hash[slot].b!=b))slot=(slot+1)&(cap-1);
    if(!hash[slot].used){hash[slot].a=a;hash[slot].b=b;hash[slot].face=i;hash[slot].side=j;hash[slot].used=1;}
    else {
      k=hash[slot].face;
      if(m->triangles[k].v[hash[slot].side]==m->triangles[i].v[j]){fprintf(stderr,"Surface router: inconsistent surface orientation.\n");exit(1);}
      if(m->triangles[k].next[hash[slot].side]>=0){fprintf(stderr,"Surface router: nonmanifold mesh.\n");exit(1);}
      m->triangles[i].next[j]=k;m->triangles[k].next[hash[slot].side]=i;
    }
  }
  for(i=0;i<m->nwalls;i++) {
    a=m->walls[2*i];b=m->walls[2*i+1];if(a>b){k=a;a=b;b=k;}
    slot=((unsigned int)a*73856093U^(unsigned int)b*19349663U)&(cap-1);
    while(hash[slot].used && (hash[slot].a!=a || hash[slot].b!=b))slot=(slot+1)&(cap-1);
    if(!hash[slot].used){fprintf(stderr,"Surface router: lost a constrained edge.\n");exit(1);}
    k=hash[slot].face;j=hash[slot].side;m->triangles[k].wall[j]=1;a=m->triangles[k].next[j];
    for(j=0;j<3;j++)if(m->triangles[a].next[j]==k)m->triangles[a].wall[j]=1;
  }
  free(hash);
  for(i=0;i<m->nt;i++)for(j=0;j<3;j++)if(m->triangles[i].next[j]<0){fprintf(stderr,"Surface router: open mesh.\n");exit(1);}
}
/* Small Taubin steps round connected-sum necks without collapsing the handles. */
static void sr_smooth(SRMesh *m)
{
  SRPoint *sum=sr_alloc(m->np,sizeof(SRPoint));int *degree=sr_alloc(m->np,sizeof(int));
  int iter,i,j,k,a,b;double weight;
  for(iter=0;iter<20;iter++) {
    memset(sum,0,m->np*sizeof(SRPoint));memset(degree,0,m->np*sizeof(int));
    for(i=0;i<m->nt;i++)for(j=0;j<3;j++) {
      a=m->triangles[i].v[j];b=m->triangles[i].v[(j+1)%3];
      for(k=0;k<3;k++){sum[a].p[k]+=m->points[b].p[k];sum[b].p[k]+=m->points[a].p[k];}
      degree[a]++;degree[b]++;
    }
    weight=iter%2 ? -0.36 : 0.35;
    for(i=0;i<m->np;i++)if(degree[i])for(k=0;k<3;k++)m->points[i].p[k]+=weight*(sum[i].p[k]/degree[i]-m->points[i].p[k]);
  }
  free(sum);free(degree);
}
static SRPoint sr_center(SRMesh *m,int face)
{
  SRPoint p;int j,k;memset(&p,0,sizeof(p));
  for(j=0;j<3;j++)for(k=0;k<3;k++)p.p[k]+=m->points[m->triangles[face].v[j]].p[k]/3;
  return p;
}
static void sr_heap_up(SRMesh *m,int node)
{
  int pos=m->heap_pos[node],parent,other;
  if(pos<0){pos=++m->heap_size;m->heap[pos]=node;m->heap_pos[node]=pos;}
  while(pos>1) {
    parent=pos/2;other=m->heap[parent];if(m->distance[other]<=m->distance[node])break;
    m->heap[pos]=other;m->heap_pos[other]=pos;pos=parent;
  }
  m->heap[pos]=node;m->heap_pos[node]=pos;
}
static int sr_heap_pop(SRMesh *m)
{
  int result=m->heap[1],node=m->heap[m->heap_size--],pos=1,child;
  while(pos*2<=m->heap_size) {
    child=pos*2;
    if(child<m->heap_size && m->distance[m->heap[child+1]]<m->distance[m->heap[child]])child++;
    if(m->distance[node]<=m->distance[m->heap[child]])break;
    m->heap[pos]=m->heap[child];m->heap_pos[m->heap[pos]]=pos;pos=child;
  }
  if(m->heap_size){m->heap[pos]=node;m->heap_pos[node]=pos;}
  m->heap_pos[result]=-1;return result;
}
/* Optimize the assignment of graph vertices to well-separated surface sites.
 * Distances and departure directions are intrinsic shortest paths on the mesh;
 * Euclidean chords through a handle are not useful layout estimates. */
static void sr_place_graph(SRMesh *m)
{
  int i,j,k,a,b,u,v,node,other,iter,total=nv*nv,*degree,*offset,*cursor,*neighbors,*first;
  int *perm,*best,*inverse,*oldvertex,*fanstart,*fansize;double *metric,delta,cost,bestcost,temp,initial;
  SRPoint *directions;SRMesh heap;KANTE *edge;
  degree=sr_alloc(m->np+1,sizeof(int));offset=sr_alloc(m->np+1,sizeof(int));
  for(i=0;i<m->nt;i++)for(j=0;j<3;j++){degree[m->triangles[i].v[j]]++;degree[m->triangles[i].v[(j+1)%3]]++;}
  for(i=0;i<m->np;i++)offset[i+1]=offset[i]+degree[i];
  neighbors=sr_alloc(offset[m->np],sizeof(int));cursor=sr_alloc(m->np,sizeof(int));memcpy(cursor,offset,m->np*sizeof(int));
  for(i=0;i<m->nt;i++)for(j=0;j<3;j++){
    a=m->triangles[i].v[j];b=m->triangles[i].v[(j+1)%3];neighbors[cursor[a]++]=b;neighbors[cursor[b]++]=a;
  }
  metric=sr_alloc(total,sizeof(double));directions=sr_alloc(total,sizeof(SRPoint));first=sr_alloc(m->np,sizeof(int));
  memset(&heap,0,sizeof(heap));heap.heap=sr_alloc(m->np+1,sizeof(int));heap.heap_pos=sr_alloc(m->np,sizeof(int));heap.distance=sr_alloc(m->np,sizeof(double));
  for(u=1;u<=nv;u++){
    heap.heap_size=0;for(i=0;i<m->np;i++){heap.heap_pos[i]=-1;heap.distance[i]=1e30;first[i]=-1;}
    a=m->vertex[u];heap.distance[a]=0;sr_heap_up(&heap,a);
    while(heap.heap_size){
      node=sr_heap_pop(&heap);
      for(j=offset[node];j<offset[node+1];j++){
        other=neighbors[j];cost=heap.distance[node]+sr_distance(m->points[node],m->points[other]);
        if(cost<heap.distance[other]){heap.distance[other]=cost;first[other]=node==a ? other : first[node];sr_heap_up(&heap,other);}
      }
    }
    for(v=1;v<=nv;v++)if(v!=u){
      b=m->vertex[v];metric[(u-1)*nv+v-1]=heap.distance[b];other=first[b];
      cost=sr_distance(m->points[a],m->points[other]);
      for(k=0;k<3;k++)directions[(u-1)*nv+v-1].p[k]=(m->points[other].p[k]-m->points[a].p[k])/cost;
    }
  }
  perm=sr_alloc(nv+1,sizeof(int));best=sr_alloc(nv+1,sizeof(int));inverse=sr_alloc(nv+1,sizeof(int));oldvertex=sr_alloc(nv+1,sizeof(int));
  for(u=1;u<=nv;u++)perm[u]=u;
  cost=0;for(u=1;u<=nv;u++)for(j=0,edge=map[u];j<adj[u];j++,edge=edge->next)cost+=metric[(u-1)*nv+edge->name-1]*0.5;
  initial=cost;bestcost=cost;memcpy(best,perm,(nv+1)*sizeof(int));
  /* Swapping equal-degree sites keeps vertex disks large enough for their ports. */
  for(iter=0;iter<1200*nv;iter++){
    u=1+sr_random(m)%nv;v=1+sr_random(m)%nv;if(u==v || adj[u]!=adj[v])continue;
    a=perm[u];b=perm[v];delta=0;
    for(j=0,edge=map[u];j<adj[u];j++,edge=edge->next)if(edge->name!=(unsigned int)v){k=perm[edge->name]-1;delta+=metric[(b-1)*nv+k]-metric[(a-1)*nv+k];}
    for(j=0,edge=map[v];j<adj[v];j++,edge=edge->next)if(edge->name!=(unsigned int)u){k=perm[edge->name]-1;delta+=metric[(a-1)*nv+k]-metric[(b-1)*nv+k];}
    temp=(initial/(nv+1))*0.4*pow(0.002,iter/(1200.0*nv));
    if(delta<=0 || sr_random(m)/(double)UINT_MAX<exp(-delta/temp)){
      perm[u]=b;perm[v]=a;cost+=delta;
      if(cost<bestcost){bestcost=cost;memcpy(best,perm,(nv+1)*sizeof(int));}
    }
  }
  m->graphdistance=sr_alloc(nv*nv,sizeof(double));
  for(u=1;u<=nv;u++)for(v=1;v<=nv;v++)m->graphdistance[(u-1)*nv+v-1]=metric[(best[u]-1)*nv+best[v]-1];
  memcpy(oldvertex,m->vertex,(nv+1)*sizeof(int));
  fanstart=sr_alloc(nv+1,sizeof(int));fansize=sr_alloc(nv+1,sizeof(int));
  for(i=0;i<m->nt;i++)if((u=m->triangles[i].owner)){if(!fansize[u])fanstart[u]=i;fansize[u]++;}
  for(u=1;u<=nv;u++){m->vertex[u]=oldvertex[best[u]];inverse[best[u]]=u;}
  for(i=0;i<m->nt;i++)if(m->triangles[i].owner)m->triangles[i].owner=inverse[m->triangles[i].owner];
  /* Rotate the complete star, never individual darts, to fit its neighbors. */
  for(u=1;u<=nv;u++){
    double bestangle=1e30,angle,dot,length;SRPoint ray;int start=fanstart[best[u]],size=fansize[best[u]],phase=0;
    for(a=0;a<size;a++){
      angle=0;for(j=0,edge=map[u];j<adj[u];j++,edge=edge->next){
        b=start+(a+j*size/adj[u])%size;
        ray=sr_lerp(m->points[m->triangles[b].v[1]],m->points[m->triangles[b].v[2]],0.5);
        length=sr_distance(ray,m->points[m->vertex[u]]);dot=0;
        for(k=0;k<3;k++)dot+=(ray.p[k]-m->points[m->vertex[u]].p[k])*directions[(best[u]-1)*nv+best[edge->name]-1].p[k]/length;
        angle+=1-dot;
      }
      if(angle<bestangle){bestangle=angle;phase=a;}
    }
    for(j=0;j<adj[u];j++)m->ports[u*MAXVAL+j]=start+(phase+j*size/adj[u])%size;
  }
  fprintf(stderr,"Surface placement distance %.3f -> %.3f.\n",initial,bestcost);
  free(degree);free(offset);free(cursor);free(neighbors);free(first);free(metric);free(directions);free(heap.heap);free(heap.heap_pos);free(heap.distance);
  free(perm);free(best);free(inverse);free(oldvertex);free(fanstart);free(fansize);
}
static int sr_find_path(SRMesh *m,SRRoute *r,int id)
{
  int i,j,node,next,length;double cost,d;
  m->serial++;m->heap_size=0;
  for(i=0;i<m->nt;i++)m->heap_pos[i]=-1;
  m->stamp[r->start]=m->serial;m->distance[r->start]=0;m->previous[r->start]=-1;sr_heap_up(m,r->start);
  while(m->heap_size) {
    node=sr_heap_pop(m);if(node==r->end)break;
    for(j=0;j<3;j++) {
      if(m->triangles[node].wall[j])continue;
      next=m->triangles[node].next[j];
      if(m->blocked[next] && m->blocked[next]!=id+1)continue;
      cost=(m->compact ? sr_distance(m->centers[node],m->centers[next]) : 1.0)*(1.0+m->repulsion[next]);
      d=m->distance[node]+cost;
      if(m->stamp[next]!=m->serial || d<m->distance[next]-1e-9) {
        m->stamp[next]=m->serial;m->distance[next]=d;m->previous[next]=node;sr_heap_up(m,next);
      }
    }
  }
  if(m->stamp[r->end]!=m->serial)return 0;
  for(node=r->end,length=0;node>=0;node=m->previous[node])length++;
  r->path=realloc(r->path,length*sizeof(int));
  if(!r->path){fprintf(stderr,"Surface router: allocation failed.\n");exit(1);}
  r->length=length;
  for(node=r->end,i=length-1;node>=0;node=m->previous[node]){r->path[i--]=node;}
  return 1;
}
static int sr_root(int *parent,int v)
{
  int r=v,next;while(parent[r]!=r)r=parent[r];
  while(parent[v]!=v){next=parent[v];parent[v]=r;v=next;}return r;
}
static void sr_union(int *parent,int a,int b)
{ a=sr_root(parent,a);b=sr_root(parent,b);if(a!=b)parent[a]=b; }
/* A dual corridor cuts each visited triangle into two regions. Track these
 * regions by triangle corners, joining across unconstrained sides only. This
 * tests connectivity of the actual cut surface, without a grid-width cutoff. */
static int sr_connected_complement(SRMesh *m,SRRoute *r)
{
  int *parent=sr_alloc(m->nt*3,sizeof(int)),*cut=sr_alloc(m->nt*3,sizeof(int));
  int i,j,k,a,b,root=-1,ok=1;
  for(i=0;i<m->nt*3;i++)parent[i]=i;
  for(i=1;i<r->length;i++) {
    a=r->path[i-1];b=r->path[i];
    for(j=0;j<3;j++){if(m->triangles[a].next[j]==b)cut[3*a+j]=1;if(m->triangles[b].next[j]==a)cut[3*b+j]=1;}
  }
  for(i=0;i<m->nt;i++)if(!m->triangles[i].owner)for(j=0;j<3;j++) {
    if(!cut[3*i+j])sr_union(parent,3*i+j,3*i+(j+1)%3);
    a=m->triangles[i].next[j];if(m->triangles[i].wall[j] || m->triangles[a].owner)continue;
    for(k=0;k<3;k++)if(m->triangles[a].v[k]==m->triangles[i].v[j])sr_union(parent,3*i+j,3*a+k);
    for(k=0;k<3;k++)if(m->triangles[a].v[k]==m->triangles[i].v[(j+1)%3])sr_union(parent,3*i+(j+1)%3,3*a+k);
  }
  for(i=0;i<m->nt;i++)if(!m->triangles[i].owner)for(j=0;j<3;j++) {
    a=sr_root(parent,3*i+j);if(root<0)root=a;else if(root!=a){ok=0;break;}
  }
  free(parent);free(cut);return ok;
}
static unsigned long long sr_signature(SRMesh *m,int face,int side)
{
  SRPoint a=m->points[m->triangles[face].v[side]],b=m->points[m->triangles[face].v[(side+1)%3]];
  if(a.h<0 || a.h!=b.h)return 0;
  if(fabs(a.u-0.25)<1e-9 && fabs(b.u-0.25)<1e-9)return 1ULL<<(2*a.h);
  if(fabs(a.v-0.5)<1e-9 && fabs(b.v-0.5)<1e-9)return 1ULL<<(2*a.h+1);
  return 0;
}
static void sr_clearance(SRMesh *m)
{
  int i,j,a,b;double d;
  m->heap_size=0;
  for(i=0;i<m->nt;i++) {
    m->heap_pos[i]=-1;m->distance[i]=1e20;
    if(m->triangles[i].owner){m->distance[i]=0;sr_heap_up(m,i);}
    else for(j=0;j<3;j++)if(m->triangles[i].wall[j]) {
      a=m->triangles[i].v[j];b=m->triangles[i].v[(j+1)%3];
      d=sr_distance(m->centers[i],sr_lerp(m->points[a],m->points[b],0.5));
      if(d<m->distance[i]){m->distance[i]=d;sr_heap_up(m,i);}
    }
  }
  while(m->heap_size) {
    a=sr_heap_pop(m);
    for(j=0;j<3;j++) {
      b=m->triangles[a].next[j];d=m->distance[a]+sr_distance(m->centers[a],m->centers[b]);
      if(d<m->distance[b]){m->distance[b]=d;sr_heap_up(m,b);}
    }
  }
  for(i=0;i<m->nt;i++)m->repulsion[i]=0.0064/((m->distance[i]+0.015)*(m->distance[i]+0.015));
}
static int sr_spine_path(SRMesh *m,SRRoute *r,int id,int cover,int shift)
{
  int i,j,node,next,state,face,mask,length,valid,count=m->nt*cover,result=0;
  int *previous=sr_alloc(count,sizeof(int)),*seen=sr_alloc(m->nt,sizeof(int));
  unsigned int signature;double cost,*potential=sr_alloc(m->nt,sizeof(double));SRMesh heap;
  memset(&heap,0,sizeof(heap));heap.heap=sr_alloc(count+1,sizeof(int));heap.heap_pos=sr_alloc(count,sizeof(int));heap.distance=sr_alloc(count,sizeof(double));
  for(i=0;i<count;i++){previous[i]=-2;heap.heap_pos[i]=-1;heap.distance[i]=1e30;}
  if(m->compact)for(i=0;i<m->nt;i++)potential[i]=0.99*sr_distance(m->centers[i],m->centers[r->end]);
  previous[r->start]=-1;heap.distance[r->start]=potential[r->start];sr_heap_up(&heap,r->start);
  while(heap.heap_size) {
    state=sr_heap_pop(&heap);face=state%m->nt;mask=state/m->nt;
    if(face==r->end) {
      memset(seen,0,m->nt*sizeof(int));valid=1;
      for(node=state,length=0;node>=0;node=previous[node]){i=node%m->nt;if(seen[i])valid=0;seen[i]=1;length++;}
      if(!valid)continue;
      free(r->path);r->path=sr_alloc(length,sizeof(int));r->length=length;
      for(node=state,i=length-1;node>=0;node=previous[node]){r->path[i--]=node%m->nt;}
      if(!r->spinecheck || sr_connected_complement(m,r)){result=1;break;}
      r->length=0;
      if(cover==1)break; /* No other target sheet exists in the ordinary search. */
      continue;
    }
    for(j=0;j<3;j++) {
      if(m->triangles[face].wall[j])continue;
      next=m->triangles[face].next[j];
      if(next==r->start || (m->blocked[next] && m->blocked[next]!=id+1))continue;
      signature=(sr_signature(m,face,j)>>shift)&(cover-1);node=next+(mask^signature)*m->nt;
      cost=heap.distance[state]-potential[face]+potential[next]+(m->compact ? sr_distance(m->centers[face],m->centers[next]) : 1.0)*(1+m->repulsion[next]);
      if(cost<heap.distance[node]){previous[node]=state;heap.distance[node]=cost;sr_heap_up(&heap,node);}
    }
  }
  free(heap.heap);free(heap.heap_pos);free(heap.distance);free(previous);free(seen);free(potential);return result;
}
static void sr_commit(SRMesh *m,SRRoute *r);
static void sr_compact_mesh(SRMesh *m,SRRoute *routes,int n);
static void sr_prepare(SRMesh *m,SRRoute *r,int n)
{
  int i;
  free(m->centers);m->centers=sr_alloc(m->nt,sizeof(SRPoint));for(i=0;i<m->nt;i++)m->centers[i]=sr_center(m,i);
  free(m->blocked);free(m->repulsion);free(m->distance);free(m->previous);free(m->stamp);free(m->heap);free(m->heap_pos);
  m->blocked=sr_alloc(m->nt,sizeof(int));m->repulsion=sr_alloc(m->nt,sizeof(double));
  m->distance=sr_alloc(m->nt,sizeof(double));m->previous=sr_alloc(m->nt,sizeof(int));m->stamp=sr_alloc(m->nt,sizeof(int));
  m->heap=sr_alloc(m->nt+1,sizeof(int));m->heap_pos=sr_alloc(m->nt,sizeof(int));
  for(i=0;i<m->nt;i++)if(m->triangles[i].owner)m->blocked[i]=-1;
  for(i=0;i<n;i++)if(!r[i].plen)m->blocked[r[i].start]=m->blocked[r[i].end]=i+1;
}
static int sr_routes(SRMesh *m,SRRoute **output,int *count)
{
  int i,j,k,u,v,n=0,*order,*rank,*tree,*parent,*face,*dual,nf=0,a,b,core,cover,shift,bits,found;
  SRRoute *routes;KANTE *edge,*inverse,*dart;
  for(i=1;i<=nv;i++)n+=adj[i];n/=2;
  routes=sr_alloc(n,sizeof(SRRoute));order=sr_alloc(n,sizeof(int));rank=sr_alloc(n,sizeof(int));tree=sr_alloc(n,sizeof(int));
  parent=sr_alloc(nv+1,sizeof(int));face=sr_alloc(MAXEDGES+1,sizeof(int));dual=sr_alloc(MAXEDGES+1,sizeof(int));
  for(i=0;i<=nv;i++)parent[i]=i;
  for(u=1;u<=nv;u++)for(j=0,edge=map[u];j<adj[u];j++,edge=edge->next)if(!face[edge->edgenumber]) {
    nf++;dart=edge;do{face[dart->edgenumber]=nf;dart=dart->invers->next;}while(dart!=edge);
  }
  for(i=0;i<=nf;i++)dual[i]=i;
  n=0;
  for(u=1;u<=nv;u++)for(j=0,edge=map[u];j<adj[u];j++,edge=edge->next)if(u<(int)edge->name) {
    v=edge->name;for(k=0,inverse=map[v];inverse!=edge->invers;inverse=inverse->next)k++;
    routes[n].u=u;routes[n].v=v;routes[n].start=m->ports[u*MAXVAL+j];routes[n].end=m->ports[v*MAXVAL+k];
    /* A primal tree and a disjoint dual tree leave precisely 2g handle edges. */
    routes[n].startbase=routes[n].start;routes[n].endbase=routes[n].end;
    routes[n].left=face[edge->edgenumber];routes[n].right=face[edge->invers->edgenumber];n++;
  }
  for(i=0;i<n;i++)rank[i]=i;
  for(i=0;i<n;i++)for(j=i+1;j<n;j++)
    if(m->graphdistance[(routes[rank[j]].u-1)*nv+routes[rank[j]].v-1]<m->graphdistance[(routes[rank[i]].u-1)*nv+routes[rank[i]].v-1]){k=rank[i];rank[i]=rank[j];rank[j]=k;}
  for(j=0;j<n;j++){
    i=rank[j];u=routes[i].u;v=routes[i].v;
    if(sr_root(parent,u)!=sr_root(parent,v)){tree[i]=1;sr_union(parent,u,v);}
  }
  for(j=0;j<n;j++){
    i=rank[m->strategy==1 ? j : n-1-j];if(tree[i])continue;
    a=routes[i].left;b=routes[i].right;
    if(sr_root(dual,a)!=sr_root(dual,b)){tree[i]=2;sr_union(dual,a,b);}
  }
  k=0;for(j=0;j<n;j++){i=rank[j];if(tree[i]==1)order[k++]=i;}
  for(j=0;j<n;j++){i=rank[m->strategy==2 ? n-1-j : j];if(!tree[i])order[k++]=i;}core=k;
  for(j=0;j<n;j++){i=rank[j];if(tree[i]==2)order[k++]=i;}
  for(i=0;i<n;i++){routes[i].length=0;routes[i].path=NULL;}
  *output=routes;*count=n;
  cover=1;bits=0;
  while(bits<2*m->genus && cover*m->nt<1000000){cover*=2;bits++;}
  for(k=0;k<n;k++) {
    /* A forest edge joins different boundary components; its complement
     * is connected without a separate whole-surface connectivity scan. */
    i=order[k];routes[i].spinecheck=!m->compact || tree[i]!=1;sr_prepare(m,routes,n);
    while(cover>2 && cover*m->nt>2000000){cover/=2;bits--;}
    if(k<core) {
      sr_clearance(m);found=sr_spine_path(m,&routes[i],i,1,0);
      /* A parity search has only two sheets. Try these small covers before
       * allocating the general multi-coordinate cover. */
      if(m->compact)for(shift=0;!found && shift<2*m->genus;shift++)found=sr_spine_path(m,&routes[i],i,2,shift);
      for(shift=0;!found && shift<2*m->genus;shift+=bits)found=sr_spine_path(m,&routes[i],i,cover,shift);
      if(!found)break;
    } else {sr_clearance(m);if(!sr_find_path(m,&routes[i],i))break;}
    sr_commit(m,&routes[i]);
    if(m->compact)sr_compact_mesh(m,routes,n);
  }
  fprintf(stderr,"Surface spine routing: %d/%d edges (%d spine edges).\n",k,n,core);
  free(order);free(rank);free(tree);free(parent);free(face);free(dual);return k==n;
}
static void sr_free(SRMesh *m,SRRoute *routes,int n)
{
  int i;for(i=0;i<n;i++){free(routes[i].path);free(routes[i].poly);}free(routes);free(m->walls);
  free(m->base_triangles);free(m->points);free(m->centers);free(m->normals);free(m->triangles);free(m->removed);free(m->vertex);free(m->ports);free(m->blocked);
  free(m->repulsion);free(m->distance);free(m->previous);free(m->stamp);free(m->heap);free(m->heap_pos);free(m->graphdistance);
}
/* Corridor portals are shared mesh edges. Moving a crossing only along its
 * portal keeps every segment on its supporting triangle and cannot introduce
 * crossings. Keeping a margin from corners also separates neighboring routes. */
static SRPoint *sr_path_geometry(SRMesh *m,SRRoute *r,int *a,int *b)
{
  int i,j,k,pass,n=r->length+1;double lo,hi,t1,t2,c1,c2;SRPoint *p,q1,q2;
  p=sr_alloc(n,sizeof(SRPoint));
  p[0]=m->points[m->vertex[r->u]];p[n-1]=m->points[m->vertex[r->v]];
  for(i=1;i<n-1;i++) {
    k=r->path[i-1];
    for(j=0;j<3;j++)if(m->triangles[k].next[j]==r->path[i])break;
    a[i]=m->triangles[k].v[j];b[i]=m->triangles[k].v[(j+1)%3];
    p[i]=sr_lerp(m->points[a[i]],m->points[b[i]],0.5);
  }
  for(pass=0;pass<(m->compact ? 0 : 24);pass++)for(k=1;k<n-1;k++) {
    i=pass%2 ? n-1-k : k;lo=0.15;hi=0.85;
    for(j=0;j<12;j++) {
      t1=(2*lo+hi)/3;t2=(lo+2*hi)/3;
      q1=sr_lerp(m->points[a[i]],m->points[b[i]],t1);q2=sr_lerp(m->points[a[i]],m->points[b[i]],t2);
      c1=sr_distance(p[i-1],q1)+sr_distance(q1,p[i+1]);c2=sr_distance(p[i-1],q2)+sr_distance(q2,p[i+1]);
      if(c1<c2)hi=t2;else lo=t1;
    }
    p[i]=sr_lerp(m->points[a[i]],m->points[b[i]],(lo+hi)*0.5);
  }
  return p;
}
static void sr_commit(SRMesh *m,SRRoute *r)
{
  int i,j,k,n=r->length+1,*a,*b,mid[3],first,second,third;
  SRTriangle t;double lo;
  SRPoint *p;
  a=sr_alloc(n,sizeof(int));b=sr_alloc(n,sizeof(int));p=sr_path_geometry(m,r,a,b);
  r->plen=n;r->poly=sr_alloc(n,sizeof(int));r->poly[0]=m->vertex[r->u];r->poly[n-1]=m->vertex[r->v];
  for(i=1;i<n-1;i++) {
    first=m->triangles[r->path[i-1]].base;second=m->triangles[r->path[i]].base;
    if(first==second){p[i].kind=1;for(j=0;j<3;j++)p[i].axis[j]=m->normals[first].p[j];}
    else {p[i].kind=2;p[i].sides[0]=first;p[i].sides[1]=second;lo=sr_distance(m->points[a[i]],m->points[b[i]]);for(j=0;j<3;j++)p[i].axis[j]=(m->points[b[i]].p[j]-m->points[a[i]].p[j])/lo;}
    r->poly[i]=sr_point(m,p[i]);
  }
  for(i=0;i<r->length;i++) {
    t=m->triangles[r->path[i]];
    if(t.owner) {
      first=r->poly[i==0 ? 1 : n-2];
      sr_triangle(m,t.v[0],t.v[1],first,t.owner);m->triangles[m->nt-1].base=t.base;
      m->triangles[r->path[i]]=m->triangles[--m->nt];
      sr_triangle(m,t.v[0],first,t.v[2],t.owner);m->triangles[m->nt-1].base=t.base;
    } else {
      for(j=0;j<3;j++)mid[j]=-1;
      for(j=0;j<3;j++) {
        if(t.next[j]==r->path[i-1])mid[j]=r->poly[i];
        if(t.next[j]==r->path[i+1])mid[j]=r->poly[i+1];
      }
      for(k=0;k<3;k++)if(mid[k]>=0 && mid[(k+2)%3]>=0)break;
      first=mid[k];second=mid[(k+2)%3];third=t.v[(k+2)%3];
      sr_triangle(m,t.v[k],first,second,0);m->triangles[m->nt-1].base=t.base;m->triangles[r->path[i]]=m->triangles[--m->nt];
      sr_triangle(m,first,t.v[(k+1)%3],third,0);m->triangles[m->nt-1].base=t.base;
      sr_triangle(m,first,third,second,0);m->triangles[m->nt-1].base=t.base;
    }
  }
  for(i=1;!m->compact && i<n;i++) {
    if(m->nwalls==m->wcap){m->wcap=m->wcap ? m->wcap*2 : 1024;m->walls=realloc(m->walls,2*m->wcap*sizeof(int));if(!m->walls)exit(1);}
    m->walls[2*m->nwalls]=r->poly[i-1];m->walls[2*m->nwalls+1]=r->poly[i];m->nwalls++;
  }
  free(p);free(a);free(b);if(!m->compact)sr_adjacency(m);
}
static void sr_write_route(FILE *out,SRRoute *r)
{
  int i;
  fprintf(out,"# graph_edge %d %d constrained\n",r->u,r->v);
  fprintf(out,"l");for(i=0;i<r->plen;i++)fprintf(out," %d",r->poly[i]+1);fprintf(out,"\n");
}
static double sr_area(SRPoint a,SRPoint b,SRPoint c,SRPoint normal)
{
  double x[3],y[3];int k;for(k=0;k<3;k++){x[k]=b.p[k]-a.p[k];y[k]=c.p[k]-a.p[k];}
  return (x[1]*y[2]-x[2]*y[1])*normal.p[0]+(x[2]*y[0]-x[0]*y[2])*normal.p[1]+(x[0]*y[1]-x[1]*y[0])*normal.p[2];
}
static void sr_base_normals(SRMesh *m)
{
  int i,k;double a[3],b[3],d;SRTriangle t;
  m->normals=sr_alloc(m->nt,sizeof(SRPoint));
  for(i=0;i<m->nt;i++) {
    t=m->triangles[i];for(k=0;k<3;k++){a[k]=m->points[t.v[1]].p[k]-m->points[t.v[0]].p[k];b[k]=m->points[t.v[2]].p[k]-m->points[t.v[0]].p[k];}
    m->normals[i].p[0]=a[1]*b[2]-a[2]*b[1];m->normals[i].p[1]=a[2]*b[0]-a[0]*b[2];m->normals[i].p[2]=a[0]*b[1]-a[1]*b[0];
    d=0;for(k=0;k<3;k++)d+=m->normals[i].p[k]*m->normals[i].p[k];d=sqrt(d);
    for(k=0;k<3;k++)m->normals[i].p[k]/=d;
  }
}
/* Tangential spring flow on the constrained triangulation. New vertices move
 * in their original surface triangle, or along its edge. A signed-area line
 * search keeps every triangle positive, so the flow is an isotopy: it cannot
 * cross routes, change rotations, or leave the original polyhedral surface. */
static void sr_relax(SRMesh *m,SRRoute *routes,int n)
{
  int *degree=sr_alloc(m->np+1,sizeof(int)),*offset=sr_alloc(m->np+1,sizeof(int)),*cursor,*incident;
  int *prev=sr_alloc(m->np,sizeof(int)),*next=sr_alloc(m->np,sizeof(int));
  int i,j,k,v,a,iter,trial,ok,count;double delta[3],avg[3],dot,step,oldarea,newarea,*reference=sr_alloc(m->nt,sizeof(double));
  SRPoint p,original,q[3];SRTriangle t;
  for(i=0;i<m->nt;i++){t=m->triangles[i];reference[i]=sr_area(m->points[t.v[0]],m->points[t.v[1]],m->points[t.v[2]],m->normals[t.base]);for(j=0;j<3;j++)degree[t.v[j]]++;}
  for(i=0;i<m->np;i++)offset[i+1]=offset[i]+degree[i];
  incident=sr_alloc(offset[m->np],sizeof(int));cursor=sr_alloc(m->np,sizeof(int));memcpy(cursor,offset,m->np*sizeof(int));
  for(i=0;i<m->nt;i++)for(j=0;j<3;j++)incident[cursor[m->triangles[i].v[j]]++]=i;
  for(i=0;i<m->np;i++)prev[i]=-1;
  for(i=0;i<n;i++)for(j=1;j<routes[i].plen-1;j++){v=routes[i].poly[j];prev[v]=routes[i].poly[j-1];next[v]=routes[i].poly[j+1];}
  for(iter=0;iter<350;iter++)for(i=0;i<m->np;i++) {
    v=iter%2 ? m->np-1-i : i;if(!m->points[v].kind || prev[v]<0)continue;
    original=m->points[v];for(k=0;k<3;k++)avg[k]=0;count=0;
    for(j=offset[v];j<offset[v+1];j++) {
      t=m->triangles[incident[j]];
      for(a=0;a<3;a++)if(t.v[a]!=v){for(k=0;k<3;k++)avg[k]+=m->points[t.v[a]].p[k];count++;}
    }
    for(k=0;k<3;k++)delta[k]=0.85*(m->points[prev[v]].p[k]+m->points[next[v]].p[k])*0.5+0.15*avg[k]/count-original.p[k];
    dot=0;for(k=0;k<3;k++)dot+=delta[k]*original.axis[k];
    for(k=0;k<3;k++)delta[k]=original.kind==1 ? delta[k]-dot*original.axis[k] : dot*original.axis[k];
    step=0.6;
    for(trial=0;trial<18;trial++,step*=0.5) {
      p=original;for(k=0;k<3;k++)p.p[k]+=step*delta[k];ok=1;
      for(j=offset[v];j<offset[v+1];j++) {
        t=m->triangles[incident[j]];for(a=0;a<3;a++)q[a]=m->points[t.v[a]];
        oldarea=reference[incident[j]];
        for(a=0;a<3;a++)if(t.v[a]==v)q[a]=p;
        newarea=sr_area(q[0],q[1],q[2],m->normals[t.base]);
        if(newarea<oldarea*0.2 || newarea<1e-22){ok=0;break;}
      }
      if(ok){m->points[v]=p;break;}
    }
  }
  free(degree);free(offset);free(cursor);free(incident);free(prev);free(next);free(reference);
}
static int sr_valid_geometry(SRMesh *m)
{
  int i,k;SRTriangle t;
  for(i=0;i<m->np;i++)for(k=0;k<3;k++)if(!isfinite(m->points[i].p[k]))return 0;
  for(i=0;i<m->nt;i++) {
    t=m->triangles[i];
    if(sr_area(m->points[t.v[0]],m->points[t.v[1]],m->points[t.v[2]],m->normals[t.base])<=1e-24)return 0;
  }
  return 1;
}

static void sr_route_walls(SRMesh *m,SRRoute *routes,int n,int omit)
{
  int i,j;m->nwalls=0;
  for(i=0;i<n;i++)if(i!=omit)for(j=1;j<routes[i].plen;j++){
    if(m->nwalls==m->wcap){m->wcap=m->wcap ? m->wcap*2 : 1024;m->walls=realloc(m->walls,2*m->wcap*sizeof(int));if(!m->walls)exit(1);}
    m->walls[2*m->nwalls]=routes[i].poly[j-1];m->walls[2*m->nwalls+1]=routes[i].poly[j];m->nwalls++;
  }
  sr_adjacency(m);
}
/* A route only needs its crossings of ORIGINAL surface edges. Subdivision
 * diagonals carry no topology. Remove empty bigons with an original edge,
 * straighten the remaining normal arcs inside each original triangle, and
 * rebuild their constrained cells. This bounds refinement by actual crossings
 * instead of repeatedly subdividing yesterday's subdivision diagonals. */
typedef struct { int point,a,b;double t; } SRCrossing;
typedef struct { int a,b,next; } SRChord;
typedef struct { int point;double t; } SRBoundary;
typedef struct { int a,b,next,used; } SRHalfedge;
static int sr_crossing_compare(const void *aa,const void *bb)
{
  const SRCrossing *a=aa,*b=bb;
  if(a->a!=b->a)return a->a<b->a ? -1 : 1;
  if(a->b!=b->b)return a->b<b->b ? -1 : 1;
  return a->t<b->t ? -1 : a->t>b->t;
}
static int sr_boundary_compare(const void *aa,const void *bb)
{ const SRBoundary *a=aa,*b=bb;return a->t<b->t ? -1 : a->t>b->t; }
static int sr_halfedge_compare(const void *aa,const void *bb)
{
  const SRHalfedge *a=aa,*b=bb;
  if(a->a!=b->a)return a->a<b->a ? -1 : 1;
  return a->b-b->b;
}
static double sr_edge_parameter(SRMesh *m,int point,int a,int b)
{
  int k;double numerator=0,denominator=0,x;
  for(k=0;k<3;k++){x=m->points[b].p[k]-m->points[a].p[k];numerator+=(m->points[point].p[k]-m->points[a].p[k])*x;denominator+=x*x;}
  return numerator/denominator;
}
static void sr_compact_mesh(SRMesh *m,SRRoute *routes,int n)
{
  int i,j,k,h,a,b,c,x,y,prev,next,head=0,tail=0,ncross=0,nchord=0,base,count,nh,first,face,used,owner;
  int *before=sr_alloc(m->np,sizeof(int)),*after=sr_alloc(m->np,sizeof(int)),*wireprev=sr_alloc(m->np,sizeof(int)),*wirenext=sr_alloc(m->np,sizeof(int));
  int *routeid=sr_alloc(m->np,sizeof(int)),*queue=sr_alloc(3*m->np,sizeof(int)),*active=sr_alloc(m->np,sizeof(int)),*heads=sr_alloc(m->nbases,sizeof(int));
  int *local=sr_alloc(m->np,sizeof(int)),*polygon,*offset;
  SRCrossing *cross=sr_alloc(m->np,sizeof(SRCrossing));SRChord *chords;SRBoundary *boundary;SRHalfedge *half;
  SRTriangle t;double area;
  for(i=0;i<n;i++)if(routes[i].plen){
    used=1;
    for(j=1;j<routes[i].plen-1;j++)if(m->points[routes[i].poly[j]].kind==2)routes[i].poly[used++]=routes[i].poly[j];
    routes[i].poly[used++]=routes[i].poly[routes[i].plen-1];routes[i].plen=used;
    for(j=1;j<used-1;j++){
      x=routes[i].poly[j];routeid[x]=i;wireprev[x]=routes[i].poly[j-1];wirenext[x]=routes[i].poly[j+1];active[x]=1;
      a=m->points[x].sides[0];b=m->points[x].sides[1];if(a>b){c=a;a=b;b=c;}
      t=m->base_triangles[a];
      for(k=0;k<3;k++)if(t.next[k]==b)break;
      if(k==3){fprintf(stderr,"Surface compaction lost an original portal.\n");exit(1);}
      cross[ncross].point=x;cross[ncross].a=a;cross[ncross].b=b;cross[ncross++].t=sr_edge_parameter(m,x,t.v[k],t.v[(k+1)%3]);
      queue[tail++]=x;
    }
  }
  qsort(cross,ncross,sizeof(SRCrossing),sr_crossing_compare);
  for(i=0;i<ncross;i++){
    x=cross[i].point;before[x]=after[x]=-1;
    if(i && cross[i-1].a==cross[i].a && cross[i-1].b==cross[i].b){y=cross[i-1].point;before[x]=y;after[y]=x;}
  }
  /* Only consecutive crossings in BOTH orders bound an empty bigon. Removing
   * arbitrary same-edge pairs could move a curve through another curve. */
  while(head<tail){
    x=queue[head++];if(!active[x])continue;y=wirenext[x];
    if(!active[y] || (before[x]!=y && after[x]!=y))continue;
    i=routeid[x];a=wireprev[x];b=wirenext[y];
    if(active[a])wirenext[a]=b;else routes[i].poly[1]=b;
    if(active[b])wireprev[b]=a;
    prev=before[x]==y ? before[y] : before[x];next=after[x]==y ? after[y] : after[x];
    if(prev>=0)after[prev]=next;if(next>=0)before[next]=prev;
    active[x]=active[y]=0;
    if(active[a])queue[tail++]=a;
    if(prev>=0)queue[tail++]=prev;if(next>=0)queue[tail++]=next;
  }
  for(i=0;i<n;i++)if(routes[i].plen){
    x=routes[i].poly[1];used=1;
    while(active[x]){routes[i].poly[used++]=x;x=wirenext[x];}
    routes[i].poly[used++]=x;routes[i].plen=used;
    free(routes[i].path);routes[i].path=NULL;routes[i].length=0;
  }
  /* Reclaim obsolete crossing points and cell centers as well as triangles. */
  used=m->base_np;for(i=0;i<m->base_np;i++)local[i]=i;
  for(i=m->base_np;i<m->np;i++)if(active[i]){local[i]=used;m->points[used++]=m->points[i];}
  m->np=used;
  for(i=0;i<n;i++)if(routes[i].plen)for(j=0;j<routes[i].plen;j++)routes[i].poly[j]=local[routes[i].poly[j]];
  for(i=0;i<m->nbases;i++)heads[i]=-1;
  chords=sr_alloc(ncross+n,sizeof(SRChord));
  for(i=0;i<n;i++)if(routes[i].plen){
    base=routes[i].startbase;
    for(j=1;j<routes[i].plen;j++){
      x=routes[i].poly[j-1];y=routes[i].poly[j];
      chords[nchord].a=x;chords[nchord].b=y;chords[nchord].next=heads[base];heads[base]=nchord++;
      if(j<routes[i].plen-1){a=m->points[y].sides[0];b=m->points[y].sides[1];if(base!=a && base!=b){fprintf(stderr,"Surface compaction broke a normal arc.\n");exit(1);}base=base==a ? b : a;}
    }
    if(base!=routes[i].endbase){fprintf(stderr,"Surface compaction changed an endpoint sector.\n");exit(1);}
  }
  m->nt=m->nbases;memcpy(m->triangles,m->base_triangles,m->nt*sizeof(SRTriangle));
  boundary=sr_alloc(2*ncross+2*n+3,sizeof(SRBoundary));half=sr_alloc(6*ncross+6*n+6,sizeof(SRHalfedge));
  polygon=sr_alloc(2*ncross+2*n+3,sizeof(int));offset=sr_alloc(2*ncross+2*n+4,sizeof(int));
  for(base=0;base<m->nbases;base++)if(heads[base]>=0){
    t=m->base_triangles[base];count=3;
    for(j=0;j<3;j++){boundary[j].point=t.v[j];boundary[j].t=j;local[t.v[j]]=-1;}
    for(h=heads[base];h>=0;h=chords[h].next)for(j=0;j<2;j++){
      x=j ? chords[h].b : chords[h].a;if(x<m->base_np)continue;
      a=m->points[x].sides[0];b=m->points[x].sides[1];a=a==base ? b : a;
      for(k=0;k<3;k++)if(t.next[k]==a)break;
      boundary[count].point=x;boundary[count++].t=k+sr_edge_parameter(m,x,t.v[k],t.v[(k+1)%3]);local[x]=-1;
    }
    qsort(boundary,count,sizeof(SRBoundary),sr_boundary_compare);
    used=0;for(j=0;j<count;j++)if(local[boundary[j].point]<0){boundary[used]=boundary[j];local[boundary[j].point]=used++;}count=used;
    nh=0;
    for(j=0;j<count;j++){half[nh].a=j;half[nh++].b=(j+1)%count;half[nh].a=(j+1)%count;half[nh++].b=j;}
    for(h=heads[base];h>=0;h=chords[h].next){a=local[chords[h].a];b=local[chords[h].b];half[nh].a=a;half[nh++].b=b;half[nh].a=b;half[nh++].b=a;}
    qsort(half,nh,sizeof(SRHalfedge),sr_halfedge_compare);
    for(j=0;j<=count;j++)offset[j]=0;
    for(j=0;j<nh;j++){offset[half[j].a+1]++;half[j].used=0;}
    for(j=0;j<count;j++)offset[j+1]+=offset[j];
    for(j=0;j<nh;j++){
      a=half[j].a;b=half[j].b;
      for(k=offset[b];k<offset[b+1];k++)if(half[k].b==a)break;
      half[j].next=k==offset[b] ? offset[b+1]-1 : k-1;
    }
    first=1;
    for(face=0;face<nh;face++)if(!half[face].used){
      used=0;j=face;do{polygon[used++]=boundary[half[j].a].point;half[j].used=1;j=half[j].next;}while(j!=face);
      area=0;for(j=1;j<used-1;j++)area+=sr_area(m->points[polygon[0]],m->points[polygon[j]],m->points[polygon[j+1]],m->normals[base]);
      if(area<=0)continue; /* The clockwise outer face. */
      owner=t.owner;
      if(used==3){
        if(owner){for(k=0;k<3 && polygon[0]!=m->vertex[owner];k++){x=polygon[0];polygon[0]=polygon[1];polygon[1]=polygon[2];polygon[2]=x;}if(k==3){fprintf(stderr,"Surface compaction lost a vertex.\n");exit(1);}}
        sr_triangle(m,polygon[0],polygon[1],polygon[2],owner);m->triangles[m->nt-1].base=base;
        if(first){m->triangles[base]=m->triangles[--m->nt];first=0;}
      }else{
        double ear,bestear;int tip,left,right;
        if(owner){fprintf(stderr,"Surface compaction lost a vertex fan.\n");exit(1);}
        /* A minimal triangulation avoids introducing another layer of cell
         * centers. Keep positive area in the remainder when boundary points
         * are collinear, so no zero-area ears survive at the end. */
        while(used>3){
          tip=-1;bestear=0;
          for(j=0;j<used;j++){
            ear=sr_area(m->points[polygon[(j+used-1)%used]],m->points[polygon[j]],m->points[polygon[(j+1)%used]],m->normals[base]);
            if(ear>bestear && ear<area*(1-1e-10)){bestear=ear;tip=j;}
          }
          if(tip<0){fprintf(stderr,"Surface compaction found a degenerate cell.\n");exit(1);}
          left=polygon[(tip+used-1)%used];right=polygon[(tip+1)%used];
          sr_triangle(m,left,polygon[tip],right,0);m->triangles[m->nt-1].base=base;
          if(first){m->triangles[base]=m->triangles[--m->nt];first=0;}
          memmove(polygon+tip,polygon+tip+1,(used-tip-1)*sizeof(int));used--;area-=bestear;
        }
        sr_triangle(m,polygon[0],polygon[1],polygon[2],0);m->triangles[m->nt-1].base=base;
        if(first){m->triangles[base]=m->triangles[--m->nt];first=0;}
      }
    }
  }
  for(i=0;i<n;i++)if(!routes[i].plen){routes[i].start=routes[i].startbase;routes[i].end=routes[i].endbase;}
  sr_route_walls(m,routes,n,-1);
  free(before);free(after);free(wireprev);free(wirenext);free(routeid);free(queue);free(active);free(heads);free(local);free(cross);free(chords);free(boundary);free(half);free(polygon);free(offset);
}

/* The normal arcs lie in convex original triangles. Their endpoint order on
 * each original edge is a complete noncrossing constraint, so spacing and
 * shortening need only solve coupled one-dimensional problems at portals. */
static void sr_normal_flow(SRMesh *m,SRRoute *routes,int n)
{
  SRCrossing *cross=sr_alloc(m->np,sizeof(SRCrossing));
  int *wp=sr_alloc(m->np,sizeof(int)),*wn=sr_alloc(m->np,sizeof(int));
  int *left=sr_alloc(m->np,sizeof(int)),*right=sr_alloc(m->np,sizeof(int)),*ea=sr_alloc(m->np,sizeof(int)),*eb=sr_alloc(m->np,sizeof(int));
  double *parameter=sr_alloc(m->np,sizeof(double));
  int i,j,k,a,b,x,y,count=0,start,end,iter;double lo,hi,t,grad,hess,dist,dot,len2,delta,weight;SRPoint p,q;SRTriangle face;
  for(i=0;i<n;i++)for(j=1;j<routes[i].plen-1;j++){
    x=routes[i].poly[j];wp[x]=routes[i].poly[j-1];wn[x]=routes[i].poly[j+1];
    a=m->points[x].sides[0];b=m->points[x].sides[1];if(a>b){k=a;a=b;b=k;}
    face=m->base_triangles[a];for(k=0;k<3;k++)if(face.next[k]==b)break;
    ea[x]=face.v[k];eb[x]=face.v[(k+1)%3];
    cross[count].point=x;cross[count].a=a;cross[count].b=b;
    cross[count++].t=sr_edge_parameter(m,x,ea[x],eb[x]);
  }
  qsort(cross,count,sizeof(SRCrossing),sr_crossing_compare);
  for(start=0;start<count;start=end){
    end=start+1;while(end<count && cross[end].a==cross[start].a && cross[end].b==cross[start].b)end++;
    for(i=start;i<end;i++){
      x=cross[i].point;left[x]=i>start ? cross[i-1].point : -1;right[x]=i+1<end ? cross[i+1].point : -1;
      parameter[x]=(i-start+1.0)/(end-start+1.0);
      p=sr_lerp(m->points[ea[x]],m->points[eb[x]],parameter[x]);
      for(k=0;k<3;k++)m->points[x].p[k]=p.p[k];
    }
  }
  for(iter=0;iter<48;iter++)for(i=0;i<count;i++){
    x=cross[iter%2 ? count-1-i : i].point;a=ea[x];b=eb[x];t=parameter[x];
    lo=left[x]>=0 ? parameter[left[x]] : 0;hi=right[x]>=0 ? parameter[right[x]] : 1;
    len2=0;for(k=0;k<3;k++){delta=m->points[b].p[k]-m->points[a].p[k];len2+=delta*delta;}
    grad=hess=0;p=m->points[x];
    for(j=0;j<2;j++){
      y=j ? wn[x] : wp[x];q=m->points[y];dist=sr_distance(p,q);if(dist<1e-12)continue;
      dot=0;for(k=0;k<3;k++)dot+=(p.p[k]-q.p[k])*(m->points[b].p[k]-m->points[a].p[k]);
      grad+=dot/dist;hess+=len2/dist-dot*dot/(dist*dist*dist);
    }
    weight=0.003;
    grad+=weight*(1/(hi-t)-1/(t-lo));hess+=weight*(1/((hi-t)*(hi-t))+1/((t-lo)*(t-lo)));
    delta=-grad/hess;if(delta>0.4*(hi-t))delta=0.4*(hi-t);if(delta< -0.4*(t-lo))delta=-0.4*(t-lo);
    parameter[x]=t+delta;p=sr_lerp(m->points[a],m->points[b],parameter[x]);
    for(k=0;k<3;k++)m->points[x].p[k]=p.p[k];
  }
  free(cross);free(wp);free(wn);free(left);free(right);free(ea);free(eb);free(parameter);
}

/* Reopen the entire angular sector between the two neighboring darts. This
 * lets an edge leave a vertex in a new direction without changing its order. */
static void sr_sector(SRMesh *m,int start,int *marked)
{
  int *queue=sr_alloc(m->nt,sizeof(int)),head=0,tail=0,i,a,b,owner=m->triangles[start].owner;
  queue[tail++]=start;marked[start]=1;
  while(head<tail){a=queue[head++];for(i=0;i<3;i++){
    b=m->triangles[a].next[i];if(!marked[b] && !m->triangles[a].wall[i] && m->triangles[b].owner==owner){marked[b]=1;queue[tail++]=b;}
  }}
  free(queue);
}
static int sr_reroute_path(SRMesh *m,SRRoute *r)
{
  int *source=sr_alloc(m->nt,sizeof(int)),*target=sr_alloc(m->nt,sizeof(int)),i,j,node,next,end=-1,length;double d;
  sr_sector(m,r->start,source);sr_sector(m,r->end,target);sr_clearance(m);
  m->heap_size=0;
  for(i=0;i<m->nt;i++){m->heap_pos[i]=-1;m->distance[i]=1e30;m->previous[i]=-2;if(source[i]){m->distance[i]=0;m->previous[i]=-1;sr_heap_up(m,i);}}
  while(m->heap_size){
    node=sr_heap_pop(m);if(target[node]){end=node;break;}
    for(j=0;j<3;j++){
      if(m->triangles[node].wall[j])continue;next=m->triangles[node].next[j];
      if(m->triangles[next].owner && !target[next])continue;
      d=m->distance[node]+sr_distance(m->centers[node],m->centers[next])*(1+0.5*(m->repulsion[node]+m->repulsion[next]));
      if(d<m->distance[next]){m->distance[next]=d;m->previous[next]=node;sr_heap_up(m,next);}
    }
  }
  free(source);free(target);if(end<0)return 0;
  for(node=end,length=0;node>=0;node=m->previous[node])length++;
  r->path=sr_alloc(length,sizeof(int));r->length=length;
  for(node=end,i=length-1;node>=0;node=m->previous[node])r->path[i--]=node;
  r->start=r->path[0];r->end=end;return 1;
}
static double sr_segment_distance(SRPoint p,SRPoint a,SRPoint b)
{
  double t=0,d=0,x;int k;
  for(k=0;k<3;k++){x=b.p[k]-a.p[k];d+=x*x;t+=(p.p[k]-a.p[k])*x;}
  t=d>0 ? t/d : 0;if(t<0)t=0;if(t>1)t=1;d=0;
  for(k=0;k<3;k++){x=p.p[k]-a.p[k]-t*(b.p[k]-a.p[k]);d+=x*x;}return d;
}
/* Compare actual curve length and physical clearance, independent of how
 * densely a corridor happened to be triangulated. Junctions share endpoints
 * deliberately; their small immediate neighborhoods are excluded. */
static double sr_curve_energy(SRMesh *m,SRRoute *routes,int n,int id,SRPoint *p,int count)
{
  int i,j,k,s,samples,segment=1;double length=0,travel=0,step,target,t,nearest,d,cost;SRPoint q,a,b;
  for(i=1;i<count;i++)length+=sr_distance(p[i-1],p[i]);
  samples=(int)(length/0.06)+1;if(samples>256)samples=256;step=length/samples;cost=length;
  for(s=0;s<samples;s++){
    target=(s+0.5)*step;
    while(segment<count-1 && travel+sr_distance(p[segment-1],p[segment])<target){travel+=sr_distance(p[segment-1],p[segment]);segment++;}
    d=sr_distance(p[segment-1],p[segment]);t=d>0 ? (target-travel)/d : 0;q=sr_lerp(p[segment-1],p[segment],t);
    if(sr_distance(q,p[0])<0.15 || sr_distance(q,p[count-1])<0.15)continue;
    nearest=0.01;
    for(i=0;i<n;i++)if(i!=id)for(j=1;j<routes[i].plen;j++){
      a=m->points[routes[i].poly[j-1]];b=m->points[routes[i].poly[j]];
      for(k=0;k<3;k++)if((q.p[k]<a.p[k]-0.1 && q.p[k]<b.p[k]-0.1)||(q.p[k]>a.p[k]+0.1 && q.p[k]>b.p[k]+0.1))break;
      if(k<3)continue;d=sr_segment_distance(q,a,b);if(d<nearest)nearest=d;
    }
    d=sqrt(nearest);cost+=0.2*step*(0.1-d)*(0.1-d)/((d+0.01)*(d+0.01));
  }
  return cost;
}
static int sr_endpoint_face(SRMesh *m,int a,int b,int owner)
{
  int i,j;
  for(i=0;i<m->nt;i++)if(m->triangles[i].owner==owner)for(j=0;j<3;j++)
    if((m->triangles[i].v[j]==a && m->triangles[i].v[(j+1)%3]==b)||(m->triangles[i].v[j]==b && m->triangles[i].v[(j+1)%3]==a))return i;
  fprintf(stderr,"Surface cleanup lost an endpoint edge.\n");exit(1);
}
static void sr_cleanup_routes(SRMesh *m,SRRoute *routes,int n)
{
  int pass,i,j,k,id,*order,*a,*b,changed,oldnp,oldnt;double *length,oldcost,newcost,before=0,after=0;
  SRRoute candidate;SRPoint *oldpoints,*points;SRTriangle *backup;
  order=sr_alloc(n,sizeof(int));length=sr_alloc(n,sizeof(double));
  for(i=0;i<n;i++)for(j=1;j<routes[i].plen;j++)before+=sr_distance(m->points[routes[i].poly[j-1]],m->points[routes[i].poly[j]]);
  for(pass=0;pass<6;pass++){
    for(i=0;i<n;i++){order[i]=i;length[i]=0;for(j=1;j<routes[i].plen;j++)length[i]+=sr_distance(m->points[routes[i].poly[j-1]],m->points[routes[i].poly[j]]);}
    for(i=0;i<n;i++)for(j=i+1;j<n;j++)if(length[order[j]]>length[order[i]]){k=order[i];order[i]=order[j];order[j]=k;}
    changed=0;
    for(k=0;k<n;k++){
      id=order[k];sr_route_walls(m,routes,n,id);sr_prepare(m,routes,n);
      memset(&candidate,0,sizeof(candidate));candidate.u=routes[id].u;candidate.v=routes[id].v;candidate.start=sr_endpoint_face(m,routes[id].poly[0],routes[id].poly[1],candidate.u);candidate.end=sr_endpoint_face(m,routes[id].poly[routes[id].plen-1],routes[id].poly[routes[id].plen-2],candidate.v);
      if(!sr_reroute_path(m,&candidate))continue;
      a=sr_alloc(candidate.length+1,sizeof(int));b=sr_alloc(candidate.length+1,sizeof(int));points=sr_path_geometry(m,&candidate,a,b);
      oldpoints=sr_alloc(routes[id].plen,sizeof(SRPoint));for(j=0;j<routes[id].plen;j++)oldpoints[j]=m->points[routes[id].poly[j]];
      oldcost=sr_curve_energy(m,routes,n,id,oldpoints,routes[id].plen);newcost=sr_curve_energy(m,routes,n,id,points,candidate.length+1);
      if(newcost<oldcost*0.995){
        oldnp=m->np;oldnt=m->nt;backup=sr_alloc(candidate.length,sizeof(SRTriangle));for(j=0;j<candidate.length;j++)backup[j]=m->triangles[candidate.path[j]];
        sr_commit(m,&candidate);
        if(sr_valid_geometry(m)){
          free(routes[id].path);free(routes[id].poly);routes[id]=candidate;candidate.path=NULL;candidate.poly=NULL;changed++;
        }else{
          for(j=0;j<candidate.length;j++)m->triangles[candidate.path[j]]=backup[j];m->np=oldnp;m->nt=oldnt;
        }
        free(backup);
      }
      free(candidate.path);free(candidate.poly);free(a);free(b);free(points);free(oldpoints);
    }
    fprintf(stderr,"Surface cleanup pass %d: improved %d routes.\n",pass+1,changed);if(!changed)break;
  }
  sr_route_walls(m,routes,n,-1);
  for(i=0;i<n;i++)for(j=1;j<routes[i].plen;j++)after+=sr_distance(m->points[routes[i].poly[j-1]],m->points[routes[i].poly[j]]);
  fprintf(stderr,"Surface route length %.3f -> %.3f.\n",before,after);free(order);free(length);
}
static void write_routed_surface(void)
{
  SRMesh m,bestmesh;SRRoute *routes=NULL,*bestroutes=NULL;int attempt,n=0,bestn=0,ok=0,successes=0,i,j;FILE *out,*mtl;
  double score,bestscore=1e30,normal[3],length;int k,f;
  char filename[1200],material[1200],*base;
  for(attempt=0;attempt<12;attempt++) {
    fprintf(stderr,"Routing genus %d surface (placement %d).\n",globalgenus,attempt+1);
    sr_mesh(&m,globalgenus,17+attempt*7919);sr_adjacency(&m);sr_smooth(&m);sr_base_normals(&m);sr_place_graph(&m);
    if(m.compact){m.nbases=m.nt;m.base_np=m.np;m.base_triangles=sr_alloc(m.nt,sizeof(SRTriangle));memcpy(m.base_triangles,m.triangles,m.nt*sizeof(SRTriangle));}
    ok=sr_routes(&m,&routes,&n);
    if(ok && sr_valid_geometry(&m)) {
      score=0;for(i=0;i<n;i++){score+=0.004*routes[i].plen;for(j=1;j<routes[i].plen;j++)score+=sr_distance(m.points[routes[i].poly[j-1]],m.points[routes[i].poly[j]]);}
      fprintf(stderr,"Surface layout score %.3f.\n",score);
      if(score<bestscore){if(bestroutes)sr_free(&bestmesh,bestroutes,bestn);bestmesh=m;bestroutes=routes;bestn=n;bestscore=score;}
      else sr_free(&m,routes,n);
      if(++successes==(m.compact ? 1 : (globalgenus>=8 ? 2 : 4)))break;
    } else sr_free(&m,routes,n);
  }
  if(!bestroutes){fprintf(stderr,"Surface routing could not find disjoint corridors. Try a smaller graph or a different rotation system. No invalid drawing was exported.\n");exit(1);}
  m=bestmesh;routes=bestroutes;n=bestn;
  if(m.compact)sr_normal_flow(&m,routes,n);
  else {sr_relax(&m,routes,n);sr_cleanup_routes(&m,routes,n);}
  if(!sr_valid_geometry(&m)){fprintf(stderr,"Surface router: numerical degeneration during relaxation. No drawing exported.\n");sr_free(&m,routes,n);exit(1);}
  objdrawings++;
  if(objdrawings==1)snprintf(filename,sizeof(filename),"%s.obj",objprefix);
  else snprintf(filename,sizeof(filename),"%s_%d.obj",objprefix,objdrawings);
  snprintf(material,sizeof(material),"%s.mtl",objprefix);
  mtl=fopen(material,"w");if(!mtl){fprintf(stderr,"Cannot write %s.\n",material);exit(1);}
  fprintf(mtl,"newmtl graph_surface\nKd 0.78 0.79 0.78\nKa 0.2 0.2 0.2\nKs 0.02 0.02 0.02\nNs 12\n");fclose(mtl);
  base=strrchr(material,'/');base=base ? base+1 : material;
  out=fopen(filename,"w");if(!out){fprintf(stderr,"Cannot write %s.\n",filename);exit(1);}
  fprintf(out,"# Disjoint surface corridors; genus %d; rotation-preserving vertex disks\nmtllib %s\no surface\nusemtl graph_surface\ns 1\n",globalgenus,base);
  if(m.compact)fprintf(out,"# surface_layout normal_arcs\n");
  for(i=0;i<m.np;i++)fprintf(out,"v %.15g %.15g %.15g\n",m.points[i].p[0],m.points[i].p[1],m.points[i].p[2]);
  for(i=0;i<m.nt;i++)fprintf(out,"f %d %d %d\n",m.triangles[i].v[0]+1,m.triangles[i].v[1]+1,m.triangles[i].v[2]+1);
  fprintf(out,"g embedded_graph_edges\n");
  for(i=0;i<n;i++)sr_write_route(out,&routes[i]);
  fprintf(out,"g embedded_graph_vertices\n");
  for(i=1;i<=nv;i++) {
    j=m.vertex[i]+1;for(k=0;k<3;k++)normal[k]=0;
    for(f=0;f<m.nt;f++)if(m.triangles[f].owner==i)for(k=0;k<3;k++)normal[k]+=m.normals[m.triangles[f].base].p[k];
    length=sqrt(normal[0]*normal[0]+normal[1]*normal[1]+normal[2]*normal[2]);if(length<1e-12)length=1;
    fprintf(out,"# graph_vertex_label %d %d %.15g %.15g %.15g\np %d\n",j,i,
      m.points[j-1].p[0]+0.03*normal[0]/length,m.points[j-1].p[1]+0.03*normal[1]/length,m.points[j-1].p[2]+0.03*normal[2]/length,j);
  }
  fclose(out);fprintf(stderr,"Wrote %s: %d disjoint continuous edges, %d vertices.\n",filename,n,nv);
  sr_free(&m,routes,n);
}
#endif
