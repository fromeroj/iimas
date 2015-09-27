#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

int size=0,maxSize=0,segments=1;
uint64_t* solution;
uint64_t* graph;
uint64_t* allOff;
uint64_t* allOn;

#define ONE 0x1ULL
#define ALL_ONES 0xFFFFFFFFFFFFFFFFULL

float startClock(){
  return (float)clock()/CLOCKS_PER_SEC;
}

float stopClock(float startTime){
  float endTime = (float)clock()/CLOCKS_PER_SEC;
  float elapsed = endTime - startTime;
  printf("Time elapsed: %fs\n",elapsed);
  return elapsed;
}

uint64_t* intersection(uint64_t* a,uint64_t* b){
  int i;
  uint64_t* c=(uint64_t*)calloc(segments, sizeof(uint64_t));
  for(i=0;i<segments;i++){
    c[i] = a[i] & b[i];
  }
  return c;
}

void addEdge(int i,int j){
  if( i == j || i > size || j > size || i < 0 || j < 0)return;
  graph[i*segments+j/64]|=ONE<<(j%64);
  graph[j*segments+i/64]|=ONE<<(i%64);
}

int hasEdge(int i,int j){
  if( i == j || i > size || j > size || i < 0 || j < 0)return 0;
  return ((graph[i*segments+j/64] & ONE<<(j%64)) >0 )?1:0;
}

uint64_t* nbhd(int v){
  return &graph[v*segments];
}

void printGraph(){
  int i,j;
  for(i=1;i<=size;i++){
    for(j=1;j<=size;j++)printf("%d",hasEdge(i,j));
    printf("\n");
  }
}


void savePixmap(){
  int i,j;
  char c;
  FILE *fp = fopen("sol.xpm", "w");
  if (fp == NULL)
    {
      printf("Error opening file!\n");
      exit(1);
    }
  fprintf(fp, "! XPM2\n%d %d 3 1\nw c #FFFFFF\nb c #000000\nr c #FF0000\n",size,size);
  for(i=1;i<=size;i++){
    for(j=1;j<=size;j++){
      if(hasEdge(i,j)){
	c=(((solution[i/64] & ONE<<(i%64)) >0) &&
	   ((solution[j/64] & ONE<<(j%64)) >0))?'r':'b';
      }else{
	c='w';
      }
      putc(c,fp);
    }
    putc('\n',fp);
  }
  fclose(fp);
}

void readGraph(char* fileName){
  FILE *inputfile=fopen(fileName, "r");
  size_t linesiz=0;
  char* linebuf=0;
  ssize_t linelen=0;

  while ( (linelen=getline(&linebuf, &linesiz, inputfile))>0) {
    if(linebuf[0]=='p'){
      int edges;
      char p[linesiz],edge[linesiz];
      sscanf(linebuf, "%s %s %d  %d", p, edge, &size, &edges );
      segments=((size/64)+1);
      if(strcmp(edge,"edge")==0){
	printf("Initializing graph with %d segments of size %d\n",size+1,segments);
	graph=(uint64_t*)calloc((size+1)*segments, sizeof(uint64_t));
      }
    }

    if(linebuf[0]=='e'){
      int v1,v2;
      char p[linesiz];
      sscanf(linebuf, "%s %d  %d", p, &v1, &v2 );
      addEdge(v1,v2);
    }
  }
}

void printSet(uint64_t* c,int newLine){
  int i;
  printf("{");
  for(i=0;i<segments;i++){
    printf("%"PRIx64,c[i]);
  }
  printf(":");
  for(i=1;i<=size;i++){
    if((c[i/64] & ONE<<(i%64))>0){
      printf("%d,",i);
    }
  }
  printf("}");
  if(newLine)printf("\n");
}

void setBit(uint64_t* c,int index,int value){
  if(index>size) return;
  uint64_t base=(value==0)?ALL_ONES:0x0ULL;
  uint64_t val=(ONE<<(index%64))^base;
  if(value==0){
    c[index/64]&=val;
  }else{
    c[index/64]|=val;
  }
}

int popcount(uint64_t* c){
  int i,count=0;
  for(i=0; i<segments; i++) count+=__builtin_popcountll(c[i]);
  return count;
}

int getIndexNthBit(uint64_t* c,int n){
  if(n>size) return -1;
  int i,j,count=0;
  for(i=0;i<segments;i++){
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
  free(solution);
  solution=intersection(allOn,c);
  maxSize=popcount(c);
  printf("Solucion actual: ");
  printSet(c,1);
}

void expand(uint64_t* c,uint64_t* p){
  int i;
  //  printf("[[Expand]] p: %s c: %s)\n",printSet(p),printSet(c));
  //  (&operations)+;
  for(i=popcount(p);i>0;i--){
    if(popcount(c)+popcount(p)<=maxSize)return;
    int v=getIndexNthBit(p,i);
    setBit(c,v,1);
    uint64_t* np=intersection(p,nbhd(v));
    //    printf("adding v:%d, Nbhd v:%s ->np:%s \n",v,printSet(nbhd(v)),printSet(np));
    if(popcount(np)==0 && (popcount(c)>=maxSize) )saveSolution(c);
    if(popcount(np)>0){
      expand(c,np);
    }
    free(np);
    setBit(c,v,0);
    setBit(p,v,0);
    //printf("[[Retract %d]] p: %s c: %s)\n",v,printSet(p),printSet(c));
  }
}

void search(){
  uint64_t* c=intersection(allOff,allOff);
  uint64_t* p=intersection(allOn,allOn);
  p[0]=(p[0]>>1)<<1;
  printf("Start search: c:");
  printSet(c,0);
  printf("  p:");
  printSet(c,1);
  expand(c,p);
}

int main ( int argc, char *argv[] ){
  int i;
  if ( argc != 2 ){
    printf( "usage: %s filename", argv[0] );
  }else{
    float start=startClock();
    readGraph(argv[1]);
    //printGraph();
    printf("size: %d\n",size);
    allOff=(uint64_t*)calloc(segments, sizeof(uint64_t));
    allOn=(uint64_t*)calloc(segments, sizeof(uint64_t));
    for(i=0;i<segments-1;i++)allOn[i]=ALL_ONES;
    allOn[segments-1]=(size%64==63)?ALL_ONES:(ONE<<(size%64+1))-1;
    search();
    int c =popcount( solution );
    printf("solution %"PRIx64" \n %d elements\n",solution[0],c);
    printSet(solution,1);
    printf("solution %"PRIx64" \n %d elements\n",solution[0],c);
    savePixmap();
    stopClock(start);
  }
  return 0;
}

int getBit(uint64_t* c,int index){
  if(index>size) return 0;
  return ((c[index/64] & ONE<<(index%64))>0)?1:0;
}
