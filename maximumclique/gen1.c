#include <stdio.h>
#include <stdlib.h>

int cmpfunc (const void * a, const void * b)
{
  return ( *(int*)b - *(int*)a   );
}

int main ( int argc, char *argv[] )
{
  int i,j,size=argc-1;
  int* nums;
  if ( argc < 2 ){
    printf( "usage: %s size\n", argv[0] );
    exit(1);
  }
  nums=calloc(size,sizeof(int));
  for(i=0;i<size;i++){
    nums[i]=atoi(argv[i+1]);
  }
  qsort(nums, argc-1, sizeof(int), cmpfunc);
  for(i=0;i<size-1;i++)
    for(j=i+1;j<size;j++)
      printf("e %d %d\n",nums[i],nums[j]);
  return 0;
}
