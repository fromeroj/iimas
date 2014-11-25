#include<stdio.h>
#include<stdint.h>

#define BIT_FIELD int_fast32_t
#define max_n 32 

BIT_FIELD g[max_n];

void print_matrix(){
  int j,k,m;
  for(k=0;k<max_n;k++)if(g[k])m=k+1;
  for(k=0;k<m;k++){
    for(j=0;j<m;j++)printf("%c",((1<<j)&g[k])?'1':'.');
    printf("\n");
  }
}

void print_set(BIT_FIELD i) {
  int j;
  for(j=0;j<max_n;j++)if((1<<j)&i)printf("%d ",j);
  printf("\n");
}

void readfile(char* filename){
    FILE *datafile;
    char line[80];
    int k=0;
    for(k=0;k<max_n;k++)g[k]=0;
    datafile =fopen(filename,"r");
    int i,j,v;
    while(fgets(line, 80, datafile) != NULL){
      sscanf (line, "%d %d", &i, &j);
      g[i]=g[i] | 1<<j;
      g[j]=g[j] | 1<<i;
    }
    fclose(datafile);
}

BIT_FIELD bx(int j){
  int k;
  BIT_FIELD r=0;
  for(k=j;k<max_n;k++)r=r|1<<k;
  return r;
}

void allCliques(BIT_FIELD clique, BIT_FIELD candidatos){
  int k;
  if(candidatos==0){
    print_set(clique);
    return;
  }
  for(k=0;k<max_n;k++){
    if(candidatos & 1<<k){
      allCliques(clique | 1<<k , candidatos & g[k] & bx(k) );
    }
  }
}

int main(int argc, char** argv)
{
  BIT_FIELD clique, candidatos;
  int k;
  readfile("data.txt");
  print_matrix();
  candidatos=0;
  for(k=0;k<max_n;k++){
    if(g[k]) candidatos=candidatos | 1<<k;
  }
  clique=0;
  allCliques(clique, candidatos );
  return(0);
}
