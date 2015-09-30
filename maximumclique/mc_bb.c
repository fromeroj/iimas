#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define ONE 0x1ULL
#define ALL_ONES 0xFFFFFFFFFFFFFFFFULL

/*   mc_basic  -- A very simple backtracking maximum clique algorithm
 *
 *   usage:     mc_basic filename, the filename has to be on the ascii format
 *     for graphs used on DIMACS http://www.cs.hbg.psu.edu/txn131/clique.html
 *   author    -- Fabian Romero
 */

typedef struct vertex {
  int index;
  int degree;
  int nbhd_degree;
} Vertex;

/* graph is represented as an adjacency matrix.
 * As the format is 1 based (the first element is 1 not 0), to simplify
 * we keep unused the bit 0 of every adjacency list as well as the first row
 * of the table.
 * TODO: This could be a struct, but as we are not planning to manage several
 * graphs at once and for convenience, we keep as a set of global variables. */
int size=0;         /* the number of vertices of the graph */
int style=0;
int max_size=0;     /* the size of the bigger cliquer found so far */
int words=1;        /* how many uint64_t are required for a vertex's adjacency list*/
uint64_t* graph;
uint64_t* graph_n;
uint64_t* inverse_n;
struct vertex* vertices; /* 3 integers for vertex storing colour, degree, and nbhd degree*/
uint64_t* solution; /* In the same adjaceny list format */
uint64_t* all_off;  /* This is an adjacency list with all bits set */
uint64_t* all_on;   /* This is an adjacency list with all bits unset */
int nodes=0;
/*
 *  Note: clock functions are for time keeping nothing especific for MC problem
 */

/*  star_clock: returns a float, with the "wall time marker" to compare at stop */
float start_clock(){
  return (float)clock()/CLOCKS_PER_SEC;
}

/*  stop_clock: returns and print the time ellapsed in seconds from the startTime
 *  Parameters
 *  startTime -- the starting time, start_clock() will provide this parameter */
float stop_clock(float startTime){
  float endTime = (float)clock()/CLOCKS_PER_SEC;
  float elapsed = endTime - startTime;
  printf("Time elapsed: %fs\n",elapsed);
  return elapsed;
}

/*
 * Functions for managing the adjacency lists
 */

/* intersection -- returns a NEW adjacency list having
 * the intersection of bits of two adjacency lists
 *
 * Parameters
 * a,b  -- pointers to the adjacency lists.
 * Returns.
 * a pointer to a NEWLY ALLOCATED adjacency list.
 * the client is expected to clean up for this         */
uint64_t* intersection(uint64_t* a,uint64_t* b){
  int i;
  uint64_t* c=(uint64_t*)calloc(words, sizeof(uint64_t));
  for(i=0;i<words;i++){
    c[i] = a[i] & b[i];
  }
  return c;
}

/* get_bit -- returns 0 or 1 if the bit 'index'
 *            is set on the adjacency list c
 * Parameters
 * c     -- pointer to the adjacency lists.
 * index -- the elementh by index we want to know
 * Returns.
 * pointer to a *NEWLY ALLOCATED* adjacency list.  */
int get_bit(uint64_t* c,int index){
  if(index>size) return 0;
  return ((c[index/64] & ONE<<(index%64))>0)?1:0;
}

/* set_bit -- set to 0 or 1 if the bit 'index'
 *     is set on the adjacency list c
 * Parameters
 * c     -- pointer to the adjacency lists.
 * index -- the elementh by index we want to know */
void set_bit(uint64_t* c,int index,int value){
  if(index>size) return;
  uint64_t base=(value==0)?ALL_ONES:0x0ULL;
  uint64_t val=(ONE<<(index%64))^base;
  if(value==0){
    c[index/64]&=val;
  }else{
    c[index/64]|=val;
  }
}

/*
 *  Functions to manage the adjacency matrix
 */

/* add_edge -- Adds an edge to the adjacency matrix
 *             we store the FULL adjacency matrix, so, both (i,j)
 *             AND (j,i) bits are set, also note is 1 based, so the
 *             (0,x) and (x,0) bits are left zeroed in every case
 * Parameters
 * i,j     -- The indexes of the vertices to join.                   */
void add_edge(int i,int j,uint64_t* g){
  if(g==NULL)g=graph;
  if( i == j || i > size || j > size || i < 0 || j < 0)return;
  g[i*words+j/64]|=ONE<<(j%64);
  g[j*words+i/64]|=ONE<<(i%64);
}

/* has_edge -- returns 0 or 1 should the matrix contain the edge (i,j)
 *             note that (i,j) is there iff (j,i) is there
 * Parameters
 * i.j     -- The indexes of the vertices                            */
int has_edge(int i,int j,uint64_t* g){
  if(g==NULL)g=graph;
  if( i == j || i > size || j > size || i < 0 || j < 0)return 0;
  return ((g[i*words+j/64] & ONE<<(j%64)) >0 )?1:0;
}

/* nbhd -- returns the part of the matrix beind the adjacency list of the
 *         vertex v (not a copy, this is supposed to be used Read Only)
 * Parameters
 * v     -- The index of the vertex                                     */
uint64_t* nbhd(int v){
  return &graph[v*words];
}

/* print_graph -- utility function that displays on stdout the full adjacency
 *  matrix of the graph                                                    */
void print_graph(uint64_t* g){
  int i,j;
  for(i=1;i<=size;i++){
    for(j=1;j<=size;j++)printf("%d",has_edge(i,j,g));
    printf("\n");
  }
}

void save_pixmap(char* fileName,uint64_t* g){
  if(g==NULL)g=graph;
  int i,j;
  FILE *fp = fopen(fileName, "w");
  if (fp == NULL) exit(1);
  fprintf(fp, "/* XPM */\nstatic char * XFACE[] = {\n\"%d %d 3 1\",\n",size,size);
  fprintf(fp, "\n\"w c #FFFFFF\",\n\"g c #555555\",\n\"r c #FF0000\",\n");
  for(i=1;i<=size;i++){
    putc('"',fp);
    for(j=1;j<=size;j++)putc(has_edge(i,j,g)?'g':'w',fp);
    putc('"',fp);
    if(i<size)putc(',',fp);
    putc('\n',fp);
  }
    putc('}',fp);
    putc(';',fp);
  fclose(fp);
}

/* save_pixmap -- utility function that saves an image on xpm format of the
 *  matrix of adjacency the graph on the file '/tmp/sol.xpm'                    */
void save_solution_pixmap(){
  int i,j;
  char c;
  FILE *fp = fopen("/tmp/sol.xpm", "w");
  if (fp == NULL) exit(1);
  fprintf(fp, "/* XPM */\nstatic char * XFACE[] = {\n\"%d %d 3 1\",\n",size,size);
  fprintf(fp, "\n\"w c #FFFFFF\",\n\"g c #555555\",\n\"r c #FF0000\",\n");
  for(i=1;i<=size;i++){
    putc('"',fp);
    for(j=1;j<=size;j++){
      if(has_edge(i,j,NULL))
	c=(get_bit(solution,i) && get_bit(solution,j))?'r':'g';
      else
	c='w';
      putc(c,fp);
    }
    putc('"',fp);
    if(i<size)putc(',',fp);
    putc('\n',fp);
  }
    putc('}',fp);
    putc(';',fp);
  fclose(fp);
}

/* read_graph -- This function will read the graph from a file on the DIMACS format
                 and initialize all other graph wide variables
		 (size, max_size, all_on,all_off)
 *  matrix of adjacency the graph on the file '/tmp/sol.xpm'                    */
void read_graph(char* fileName){
  //  int i;
  FILE *inputfile=fopen(fileName, "r");
  size_t linesiz=0;
  char* linebuf=0;
  ssize_t linelen=0;

  while ( (linelen=getline(&linebuf, &linesiz, inputfile))>0) {
    if(linebuf[0]=='p'){
      int edges;
      char p[linesiz],edge[linesiz];
      sscanf(linebuf, "%s %s %d  %d", p, edge, &size, &edges );
      words=((size/64)+1);
      if(strcmp(edge,"edge")==0){
	printf("Initializing graph with %d rows of %d words each\n",size+1,words);
	graph=(uint64_t*)calloc((size+1)*words, sizeof(uint64_t));
	graph_n=(uint64_t*)calloc((size+1)*words, sizeof(uint64_t));
	inverse_n=(uint64_t*)calloc((size+1)*words, sizeof(uint64_t));
      }
    }

    if(linebuf[0]=='e'){
      int v1,v2;
      char p[linesiz];
      sscanf(linebuf, "%s %d  %d", p, &v1, &v2 );
      add_edge(v1,v2,NULL);
    }
  }
}

void printSet(uint64_t* c,int newLine){
  int i;
  printf("{");
  for(i=0;i<words;i++){
    printf("%"PRIx64,c[i]);
  }
  printf(":");
  for(i=1;i<=size;i++){
    if((c[i/64] & ONE<<(i%64))>0){
      printf("%d ",i);
    }
  }
  printf("}");
  if(newLine)printf("\n");
}


int popcount(uint64_t* c){
  int i,count=0;
  for(i=0; i<words; i++) count+=__builtin_popcountll(c[i]);
  return count;
}

int get_index_bit_n(uint64_t* c,int n){
  if(n>size) return -1;
  int i,j,count=0;
  for(i=0;i<words;i++){
    if(count+__builtin_popcountll(c[i])>=n){
      for(j=0;j<64;j++){
	count+=((c[i] & ONE<<j)>0)?1:0;
	if(count==n)return i*64+j;
      }
    }
    else{
      count+=__builtin_popcountll(c[i]);
    }
  }
  return -1;
}

void save_solution(uint64_t* c){
  int i,v;
  free(solution);
  solution=intersection(all_off,all_off);
  for(i=1;i<=size;i++){
    v=vertices[i].index;
    if(get_bit(c,i)){
      solution[v/64]|=ONE<<(v%64);
      printf("%d ",v);
    }
  }
  printf(" size %d\n",popcount(c));
  max_size=popcount(c);
}

int* indexes(uint64_t* p,int pp){
  int i,j=0;
  int* r;
  r=calloc(pp, sizeof(int));
  for(i=1;i<=size;i++){
    if(get_bit(p,i)){
      r[j]=i;
      j++;
      if(j==pp)break;
    }
  }
  return r;
}

void bb_colour(uint64_t* p,int* u,int* colour,int p_count){
  uint64_t* cpp=intersection(p,p);
  int colour_class=0,j,q_count,i=0,cpp_count=p_count,v;
  while(cpp_count){
    colour_class++;
    uint64_t* q=intersection(cpp,cpp);
    q_count=cpp_count;
    while(q_count){
      v=get_index_bit_n(q,1); //   use ffsll(q) to speed up.
      set_bit(cpp,v,0);cpp_count--;
      set_bit(q,v,0);
      for(j=0;j<words;j++)q[j]&=inverse_n[v*words+j];
      q_count=popcount(q);
      i++;
      u[i]=v;
      colour[i]=colour_class;
    }
    free(q);
  }
  //  for(i=0;i<=p_count;i++)printf("{%d,%d},",i,colour[i]);
  //printf("\n");
  //  printf("Colour class %d \n",colour_class);
  free(cpp);
}


void bb_max_clique(uint64_t* c,uint64_t* p,int c_count,int p_count){
  int i,j,pnp,v;
  uint64_t* new_p;
  nodes++;
  int* u=(int*)calloc(p_count+1,sizeof(int));
  int* colour=(int*)calloc(p_count+1,sizeof(int));
  bb_colour(p,u,colour,p_count);
  new_p=all_off;
  for(i=p_count;i>0;i--){
    if(colour[i]+c_count <= max_size)return;
    new_p=intersection(p,p);
    v=u[i];
    set_bit(c,v,1);c_count++;
    for(j=0;j<words;j++)new_p[j]&=graph_n[v*words+j];
    pnp=popcount(new_p);
    if( (pnp==0) && (c_count > max_size)) save_solution(c);
    if(pnp>0)bb_max_clique(c,new_p,c_count,pnp);
    set_bit(p,v,0);c_count--;
    set_bit(c,v,0);c_count--;
  }
  free(new_p);
  free(u);
  free(colour);
}

int compare_vertices (const void * a, const void * b)
{
  int ad = ((const struct vertex*)a)->degree;
  int an = ((const struct vertex*)a)->nbhd_degree;
  int ai = ((const struct vertex*)a)->index;
  int bd = ((const struct vertex*)b)->degree;
  int bn = ((const struct vertex*)b)->nbhd_degree;
  int bi = ((const struct vertex*)b)->index;
  if(ai==0)return -1;
  if(bi==0)return 1;
  if(ad<bd)return -1;
  if(ad==bd && an<bn)return -1;
  if(ad==bd && an==bn && ai<bi)return -1;
  return 1;
}

void order_vertices(){
  int i,j;
  vertices=calloc( (size+1) , sizeof(struct vertex));
  for(i=1;i<=size;i++){
    vertices[i].index=i;
    vertices[i].degree = popcount(nbhd(i));
    for(j=0;j<=size;j++){
      if(has_edge(i,j,NULL))vertices[i].nbhd_degree+=popcount(nbhd(j));
    }
  }
  qsort(vertices,size+1,sizeof(struct vertex),compare_vertices);
  for(i=0;i<=size;i++){
    for(j=0;j<=size;j++){
      if(has_edge(vertices[i].index,
		  vertices[j].index,NULL)){
	add_edge(i,j,graph_n);
      }
    }
  }
  for(i=1;i<=size;i++){
    for(j=0;j<words;j++){
      inverse_n[i*words+j] = graph_n[i*words+j] ^ all_on[j];
    }
    inverse_n[i*words]=(inverse_n[i*words]>>1)<<1;
  }

  /*  for(i=0;i<size+1;i++){
    printf("(%d,%d,%d)  ",vertices[i].index,vertices[i].degree,vertices[i].nbhd_degree);
  }
  printf("---------------\n");*/
  save_pixmap("/tmp/g.xpm",graph);
  save_pixmap("/tmp/n.xpm",graph_n);
  save_pixmap("/tmp/inv_n.xpm",inverse_n);
}

void search(){
  int i;
  all_off=(uint64_t*)calloc(words, sizeof(uint64_t));
  all_on=(uint64_t*)calloc(words, sizeof(uint64_t));
  for(i=0;i<words-1;i++)all_on[i]=ALL_ONES;
  all_on[words-1]=(size%64==63)?ALL_ONES:(ONE<<(size%64+1))-1;
  uint64_t* c=intersection(all_off,all_off);   /* Using intersection for copy */
  uint64_t* p=intersection(all_on,all_on);
  p[0]=(p[0]>>1)<<1;
  order_vertices();
  bb_max_clique(c,p,0,size);
}

int main ( int argc, char *argv[] ){
  if ( argc != 2 ){
    printf( "usage: %s filename", argv[0] );
  }else{
    float start=start_clock();
    read_graph(argv[1]);
    printf("size: %d\n",size);
    search();
    int c =popcount( solution );
    printf("solution %"PRIx64" \n %d elements\n",solution[0],c);
    printSet(solution,1);
    printf("solution %"PRIx64" \n %d elements %d nodes\n",solution[0],c,nodes);
    // save_pixmap();
    stop_clock(start);
  }
  return 0;
}
