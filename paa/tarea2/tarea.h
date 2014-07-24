#include <stdlib.h>
#include <stdio.h>

#ifndef proc_structs_
#define proc_structs_

typedef struct inds_arreglo {
  int indice;
  int *inds_d;
  int tam_inds_d;
} i_arreglo;

typedef struct pos_mat {
	int dim_m;
	int dim_n;
} i_pos;

typedef struct inds_arreglo_mat {
	int indice;
	i_pos *inds_d;
	int tam_inds_d;
} i_matriz;

typedef struct inds_mat_mat {
	i_pos indice;
	i_pos *inds_d;
	int tam_inds_d;
} i_matriz_matriz;

#endif // proc_structs
