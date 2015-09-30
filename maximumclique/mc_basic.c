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

/* graph is represented as an adjacency matrix.
 * As the format is 1 based (the first element is 1 not 0), to simplify
 * we keep unused the bit 0 of every adjacency list as well as the first row
 * of the table.
 * TODO: This could be a struct, but as we are not planning to manage several
 * graphs at once and for convenience, we keep as a set of global variables. */
int size=0;          /* the number of vertices of the graph */
int max_size=0;       /* the size of the bigger cliquer found so far */
int words=1;         /* how many uint64_t are required for a vertex's adjacency list*/
uint64_t* graph;
uint64_t* solution;  /* In the same adjaceny list format */
uint64_t* all_off;    /* This is an adjacency list with all bits set */
uint64_t* all_on;     /* This is an adjacency list with all bits unset */
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
void add_edge(int i,int j){
  if( i == j || i > size || j > size || i < 0 || j < 0)return;
  graph[i*words+j/64]|=ONE<<(j%64);
  graph[j*words+i/64]|=ONE<<(i%64);
}

/* has_edge -- returns 0 or 1 should the matrix contain the edge (i,j)
 *             note that (i,j) is there iff (j,i) is there
 * Parameters
 * i.j     -- The indexes of the vertices                            */
int has_edge(int i,int j){
  if( i == j || i > size || j > size || i < 0 || j < 0)return 0;
  return ((graph[i*words+j/64] & ONE<<(j%64)) >0 )?1:0;
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
void print_graph(){
  int i,j;
  for(i=1;i<=size;i++){
    for(j=1;j<=size;j++)printf("%d",has_edge(i,j));
    printf("\n");
  }
}

/* save_pixmap -- utility function that saves an image on xpm format of the
 *  matrix of adjacency the graph on the file '/tmp/sol.xpm'                    */
void save_pixmap(){
  int i,j;
  char c;
  FILE *fp = fopen("/tmp/sol.xpm", "w");
  if (fp == NULL) exit(1);
  fprintf(fp, "/* XPM */\nstatic char * XFACE[] = {\n\"%d %d 3 1\",\n",size,size);
  fprintf(fp, "\n\"w c #FFFFFF\",\n\"g c #555555\",\n\"r c #FF0000\",\n");
  for(i=1;i<=size;i++){
    putc('"',fp);
    for(j=1;j<=size;j++){
      if(has_edge(i,j))
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
      }
    }

    if(linebuf[0]=='e'){
      int v1,v2;
      char p[linesiz];
      sscanf(linebuf, "%s %d  %d", p, &v1, &v2 );
      add_edge(v1,v2);
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

int getIndexNthBit(uint64_t* c,int n){
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

void saveSolution(uint64_t* c){
  int pcc=popcount(c);
  free(solution);
  solution=intersection(c,c);
  max_size=pcc;
  printf("Current sol: [%d]",max_size);
  printSet(c,1);
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

void expand(uint64_t* c,uint64_t* p,int c_count,int p_count){
  int i,pnp;
  nodes++;
  for(i=p_count;i>0;i--){
    if(c_count+p_count<=max_size)return;
    int v=getIndexNthBit(p,i);
    set_bit(c,v,1);c_count++;
    uint64_t* np=intersection(p,nbhd(v));
    pnp=popcount(np);
    if(pnp==0 && ((c_count+1)>max_size) )saveSolution(c);
    if(pnp>0){
      expand(c,np,c_count,pnp);
    }
    free(np);
    set_bit(c,v,0);c_count--;
    set_bit(p,v,0);p_count--;
  }
}

void search(){
  uint64_t* c=intersection(all_off,all_off);   /* Using intersection for copy */
  uint64_t* p=intersection(all_on,all_on);
  p[0]=(p[0]>>1)<<1;
  expand(c,p,0,size);
}


int main ( int argc, char *argv[] ){
  int i;
  if ( argc != 2 ){
    printf( "usage: %s filename", argv[0] );
  }else{
    float start=start_clock();
    read_graph(argv[1]);
    printf("size: %d\n",size);
    all_off=(uint64_t*)calloc(words, sizeof(uint64_t));
    all_on=(uint64_t*)calloc(words, sizeof(uint64_t));
    for(i=0;i<words-1;i++)all_on[i]=ALL_ONES;
    all_on[words-1]=(size%64==63)?ALL_ONES:(ONE<<(size%64+1))-1;
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
