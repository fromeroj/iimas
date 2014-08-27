#include <stdio.h> 
#define max_n 50 

int B[max_n];
int size;

void printSol(){ 
  int k;
  for(k=1;k<=size;k++) printf("%4d",B[k]); 
  printf("\n"); 
} 

int noConflictos(int k) 
{ 
  printf("no conflictos la columna %d no debe estar en coflicto \n",k);
  printSol();
  int i; 
  for(i=0;i<k;i++){ 
    if(B[i]==B[k] || abs(k-i)==abs(B[k]-B[i])) {
      printf("conflicto!");
      return(0);
    }
    printf("no conflicto!");
    return(1); 
  }
}

void queens(int current) 
{ 
  int j,k;
  for(k=0;k<size;k++){
    for(j=0;j<current;j++){
      if(B[j]==k){
        break;
      }
    }
    printf("Intentando en %d, el valor %d\n",current,k);
    B[current]=k;
    if(noConflictos(k)){
      if(current==size){
        printSol(size);
        return;
      }
      queens(current+1);
    }
  }
}

int main(int argc, char **argv) 
{ 
  int k;
  size=(argc>1)?atoi(argv[1]):8;
  for(k=0;k<size;k++)B[k]=-1;
  queens(0);
} 

