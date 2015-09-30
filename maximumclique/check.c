#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define ONE 0x1ULL
int words=1,size;
uint64_t* graph;

void add_edge(int i,int j){
  if( i == j || i > size || j > size || i < 0 || j < 0)return;
  graph[i*words+j/64]|=ONE<<(j%64);
  graph[j*words+i/64]|=ONE<<(i%64);
}

int has_edge(int i,int j){
  if( i == j || i > size || j > size || i < 0 || j < 0)return 0;
  return ((graph[i*words+j/64] & ONE<<(j%64)) >0 )?1:0;
}

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


int main ( int argc, char *argv[] ){
  int i,j,size=argc-2;
  int* nums;
  printf( "Called with %d elements\n", argc-2 );
  if ( argc < 2 ){
    printf( "usage: %s filename [elements]", argv[0] );
    exit(1);
  }
  nums=calloc(size,sizeof(int));
  for(i=0;i<size;i++)nums[i]=atoi(argv[i+2]);
  read_graph(argv[1]);
  int errors=0;
  for(i=0;i<size-1;i++)
    for(j=i+1;j<size;j++)
      if(!has_edge(nums[i],nums[j]))
	printf("Error[%d] doesn't contain, %d %d\n",++errors,nums[i],nums[j]);
  if(!errors)printf("Checked!\n");
  return 0;
}
