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

float startClock(){
  return (float)clock()/CLOCKS_PER_SEC;
}

float stopClock(float startTime){
  float endTime = (float)clock()/CLOCKS_PER_SEC;
  float elapsed = endTime - startTime;
  printf("Time elapsed: %fs\n",elapsed);
  return elapsed;
}

uint64_t* or(uint64_t* a,uint64_t* b){
  int i;
  uint64_t* c=(uint64_t*)calloc(segments, sizeof(uint64_t));
  for(i=0;i<segments;i++){
    c[i] = a[i] | b[i];
  }
  return c;
}

uint64_t* and(uint64_t* a,uint64_t* b){
  int i;
  uint64_t* c=(uint64_t*)calloc(segments, sizeof(uint64_t));
  for(i=0;i<segments;i++){
    c[i] = a[i] & b[i];
  }
  return c;
}

void readGraph(char* fileName){
  FILE *inputfile=fopen(fileName, "r");
  size_t linesiz=0;
  char* linebuf=0;
  ssize_t linelen=0;

  while (linelen=getline(&linebuf, &linesiz, inputfile)>0) {
    if(linebuf[0]=='p'){
      int edges;
      char p[linesiz],edge[linesiz];
      sscanf(linebuf, "%s %s %d  %d", p, edge, &size, &edges );
      segments=(((size-1)/64)+1);
      if(strcmp(edge,"edge")==0){
	int x=(1+(size *(size-1)-1)/128);
	graph=(uint64_t*)calloc(x, sizeof(uint64_t));
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

int address(int i,int j){
  if(i>j){int k=i;i=j;j=k;}
  return size*(size-1)/2 - (size-i+1)*(size-i)/2 + j - i -1;
}

void addEdge(int i,int j){
  if(i==j)return;
  int a=address(i,j);
  graph[a/64]|=0x1ULL<<(a%64);
}

int hasEdge(int i,int j){
  if(i==j)return 0;
  int a=address(i,j);
  return ((graph[a/64] & 0x1ULL<<(a%64)) >0 )?1:0;
}

char* printSet(uint64_t* c){
  char* s=calloc(size*4, sizeof(char));
  char* tmp=calloc(6, sizeof(char));
  int i;
  strcpy(s,"{");
  for(i=0;i<segments;i++){
    sprintf(tmp,"%"PRIx64,c[i]);
    strcat(s,tmp);
  }
  strcat(s,":");
  for(i=1;i<=size;i++){
    if((c[i/64] & 0x1ULL<<(i%64-1))>0){
      sprintf(tmp,"%d,",i);
      strcat(s,tmp);
    }
  }
  strcat(s,"}");
  free(tmp);
  return s;
}

void printGraph(){
  int i,j;
  for(i=1;i<=size;i++){
    for(j=1;j<=size;j++)printf("%d",hasEdge(i,j));
    printf("\n");
  }
}

int main ( int argc, char *argv[] )
{
  int i;
  if ( argc != 2 )
    {
      printf( "usage: %s filename", argv[0] );
    }
  else
    {
      float start=startClock();
      readGraph(argv[1]);
      printGraph();
      printf("size: %d\n",size);
      allOff=(uint64_t*)calloc(segments, sizeof(uint64_t));
      allOn=(uint64_t*)calloc(segments, sizeof(uint64_t));
      for(i=0;i<segments-2;i++)allOn[i]=0xFFFFFFFFFFFFFFFF;
      allOn[segments-1]=(0x1ULL<<(size%64))-1;
      search();
      int c =__builtin_popcount( solution );
      printf("%d unos en la solucion %"PRIx64" %s \n ",c,solution[0],printSet(solution));
      stopClock(start);
    }
}

int popcount(uint64_t* c){
  int i,count=0;
  for(i=0; i<segments; i++){
    count+=__builtin_popcount(c[i]);
  }
  return count;
}

void search(){
  int i,operations=0;
  uint64_t* c=and(allOff,allOff);
  uint64_t* p=and(allOn,allOn);

  printf("Start search: c:%" PRIx64 " p:%" PRIx64 " %s\n",c[0],p[0],printSet(p));
  expand(c,p);
}

int getBit(uint64_t* c,int index){
  if(index>size) return 0;
  return ((c[index/64] & 0x1ULL<<(index%64))>0)?1:0;
}

int getIndexNthBit(uint64_t* c,int n){
  //  printf("getIndexNthBit %" PRIx64 " -- %d\n",c[0],n);
  if(n>size) return 0;
  int i,j,count=0;
  for(i=0;i<segments;i++){
    if(count+__builtin_popcount(c[i])>=n){
      for(j=0;j<64;j++){
	count+=((c[i] & 0x1ULL<<j)>0)?1:0;
	if(count==n){
	  return i*64+j;
	}
      }
    }
    else{
      count+=__builtin_popcount(c[i]);
    }
  }
  return -1;
}

void setBit(uint64_t* c,int index,int value){
  if(index>size) return 0;
  uint64_t base=(value==0)?0xFFFFFFFFFFFFFFFFULL:0x0ULL;
  uint64_t val=0x1ULL<<(index%64-1)^base;
  if(value==0){
    c[index/64]&=val;
  }else{
    c[index/64]|=val;
  }
}



uint64_t* nbhd(int v){
  int i;
  uint64_t* c=(uint64_t*)calloc(segments, sizeof(uint64_t));
  for(i=1;i<=size;i++){
    uint64_t val=hasEdge(i,v)?0x1ULL<<(i%64-1):0x0ULL;
    c[i/64]|=val;
  }
  return c;
}

void expand(uint64_t* c,uint64_t* p){
  int i;
  printf("[[Expand]] p: %s c: %s)\n",printSet(p),printSet(c));
//  (&operations)+;
  for(i=popcount(p)-1;i>=0;i--){
    if(popcount(c)+popcount(p)<=maxSize)return;
    int v=getIndexNthBit(p,i+1)+1;
    setBit(c,v,1);
    uint64_t* np=and(p,nbhd(v));
    printf("adding v:%d, Nbhd v:%s ->np:%s \n",v,printSet(nbhd(v)),printSet(np));
    if(popcount(np)==0 && (popcount(c)>maxSize) )saveSolution(c);
    if(popcount(np)>0){
      printf("->");
      expand(c,np);
    }
    setBit(c,v,0);
    setBit(p,v,0);
    printf("[[Retract %d]] p: %s c: %s)\n",v,printSet(p),printSet(c));
  }
}

void saveSolution(uint64_t* c){
  solution=and(allOn,c);
  maxSize=popcount(c);
  printf("Solucion actual: %s \n",printSet(c));
}
