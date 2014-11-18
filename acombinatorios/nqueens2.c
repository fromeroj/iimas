#include <stdio.h> 
#define max_n 50 

int BOARD[max_n];
int size;

void print_sol(){ 
  int k;
  for(k=0;k<size;k++) printf("%4d",BOARD[k]+1); 
  printf("\n"); 
} 

int no_conflictos(int k) 
{ 
  int i; 
  for(i=0;i<k;i++){ 
    if(BOARD[i]==BOARD[k] || abs(k-i)==abs(BOARD[k]-BOARD[i])) {
      return(0);
    }
  }
  return(1); 
}

int queens(int current) 
{ 
  int k;
  print_sol();
  if(current==size){
    print_sol();
    return(1);
  }
  for(k=0;k<size;k++){
    BOARD[current]=k;
    if(no_conflictos(current)){
      if(queens(current+1))return(1);
    }
  }
  return(0);
}

int main(int argc, char **argv) 
{ 
  int k;
  size=(argc>1)?atoi(argv[1]):8;
  for(k=0;k<size;k++)BOARD[k]=-1;
  queens(0);
}
