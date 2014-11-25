#include <stdio.h> 
#define max_n 50 
int BOARD[max_n];
int size;
int Count;

void print_sol(){ 
  int k;
  printf("%8d:",Count);
  for(k=0;k<size;k++) printf("%4d",BOARD[k]+1); 
  printf("\n"); 
} 

void PrintCount(){ 
  printf("The %d-queens problem has %d solutions.\n",size,Count); 
}

int no_conflictos(int k) 
{ 
  int i; 
  for(i=0;i<k;i++){ 
    if(BOARD[i]==BOARD[k] || abs(k-i)==abs(BOARD[k]-BOARD[i])) {
      return 0;
    }
  }
  return 1; 
}

int queens(int current) 
{ 
  int k;
  if(current==size){
    Count++;
    //    print_sol();
  }
  for(k=0;k<size;k++){
    BOARD[current]=k;
    if(no_conflictos(current) && queens(current+1) )return 1;
  }
  return 0;
}

int main(int argc, char **argv) 
{ 
  int k;
  size=(argc>1)?atoi(argv[1]):8;
  for(k=0;k<size;k++)BOARD[k]=0;
  queens(0);
  PrintCount();
}
