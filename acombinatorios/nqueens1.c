#include <stdio.h> 
#define max_n 50 
int A[max_n],S[max_n]; 

void printSol(int m){ 
  int k; 
  for(k=1;k<=m;k++) printf("%4d",A[k]); 
  printf("\n"); 
} 

int noReina_Fila_Col(int k) 
{ 
  int i; 
  for(i=1;i<k;i++) 
    if(A[i]==S[k] || abs(k-i)==abs(S[k]-A[i])) 
      return(1); 
  return(0); 
} 
 
void BackTrack(int n) 
{ 
  int k; 
  k = 1; S[k] = 1; 
  while(k>0){ 
    while(S[k]<=n){ 
      A[k] = S[k]; S[k] = S[k] + 1; 
      while(S[k]<=n && noReina_Fila_Col(k)) 
        S[k] = S[k] + 1; 
      if(k==n) printSol(k); 
      k = k + 1; S[k] = 1; 
      while(S[k]<=n && noReina_Fila_Col(k)) 
        S[k] = S[k] + 1; 
    } 
    k = k-1; 
  } 
} 

int main(int argc, char **argv) 
{ 
  int n = 8; 
  if(argc>1) n=atoi(argv[1]);
  BackTrack(n); 
} 

