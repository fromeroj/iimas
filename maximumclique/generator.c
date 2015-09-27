#include <stdio.h>
#include <stdlib.h>

int main ( int argc, char *argv[] )
{
  int i,j,size;
  if ( argc != 2 )printf( "usage: %s size", argv[0] );
  else{
    size= atoi(argv[1]);
    printf("p edge %d %d\n",size,size);
    for(i=1;i<size;i++)
      for(j=i+1;j<=size;j++)
	printf("e %d %d\n",i,j);
  }
  return 0;
}
