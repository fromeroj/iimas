#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

uint64_t* readGraph(char* fileName, int* size){
  FILE *inputfile=fopen(fileName, "r");
  size_t linesiz=0;
  char* linebuf=0;
  ssize_t linelen=0;
  uint64_t* bit_matrix;

  while (linelen=getline(&linebuf, &linesiz, inputfile)>0) {
    if(linebuf[0]=='p'){
	int edges;
	char p[linesiz],edge[linesiz];
	sscanf(linebuf, "%s %s %d  %d", p, edge, size, &edges );
	if(strcmp(edge,"edge")==0){
	  int x=(1+(*size *( *size-1)-1)/128);
	  bit_matrix=(uint64_t*)calloc(x, sizeof(uint64_t));
	}
    }
    if(linebuf[0]=='e'){
	int v1,v2;
	char p[linesiz];
	sscanf(linebuf, "%s %d  %d", p, &v1, &v2 );
	addEdge(v1,v2,*size,bit_matrix);
    }
  }
  printMatrix(bit_matrix,*size);
}

int address(int i,int j,int n){
  if(i>j){
    int k=i;
    i=j;
    j=k;
  }
  int pos= n*(n-1)/2 - (n-i+1)*(n-i)/2 + j - i -1;
  return pos;
}

void addEdge(int i,int j,int n,uint64_t* bit_matrix){
  int a=address(i,j,n);
  uint64_t i2 = 0x1ULL<<(a%64);
  bit_matrix[a/64]=bit_matrix[a/64] | i2;
}

int hasEdge(int i,int j,int n,uint64_t* bit_matrix){
  if(i==j)return 0;
  int a=address(i,j,n);
  return ((bit_matrix[a/64] & 0x1ULL<<(a%64)) >0 )?1:0;
}

void printMatrix(uint64_t* bit_matrix,int n){
  int i,j;
  for(i=1;i<=n;i++){
    for(j=1;j<=n;j++){
      printf("%d",hasEdge(i,j,n,bit_matrix));
    }
    printf("\n");
  }
}

int main ( int argc, char *argv[] )
{
  if ( argc != 2 )
    {
      printf( "usage: %s filename", argv[0] );
    }
  else
    {
      int size=0;
      readGraph(argv[1],&size);

      printf("size: %d\n",size);
    }
}
