#include "tarea.h"

i_arreglo* indices_arreglo_arreglo (int dim_proc, int dim_datos) {
  i_arreglo* result = malloc(sizeof(i_arreglo) * dim_datos);
  int ii=0;
  for(int i=0;i<dim_datos;i++){
    if(i<dim_proc){ //Inicializamos el procesador.
      result[i].indice=0;
      ii=(i%dim_proc < dim_datos%dim_proc)?1:0;
      result[i].tam_inds_d =ii + dim_datos/dim_proc;
      result[i].inds_d = malloc(sizeof(int)*result[i].tam_inds_d);
    }
    result[i%dim_proc].inds_d[i/dim_proc] = i;
  }
  return result;
}

void pinta_indices_arreglo_arreglo (i_arreglo *ids_a, int dim_proc) {
  for(int i=0; i<dim_proc; i++) {
    printf("Procesador (%i) %i tareas -> ", i,ids_a[i].tam_inds_d);
    for(int j = 0; j < ids_a[i].tam_inds_d;j++){
      printf("%i ", ids_a[i].inds_d[j]);
    }
    printf("\n");
  }
}

void delete_arreglo(i_arreglo *ids_a, int dim_proc) {
  for(int i=0; i<dim_proc; i++) {
    if(ids_a[i].inds_d!=NULL){
      free(ids_a[i].inds_d);
    }
  }
  if(ids_a!=NULL){
    free(ids_a);
  }
}

i_matriz* indices_arreglo_matriz (int dim_proc, int dim_m, int dim_n) {
  i_matriz* result = malloc(sizeof(i_matriz)*dim_proc);
  int ii=0;
  for(int i=0;i<dim_m * dim_n;i++){
    if(i<dim_proc){
      result[i].indice=0;
      ii=(i%dim_proc < (dim_m*dim_n) %dim_proc)?1:0;
      result[i].tam_inds_d =ii + (dim_m*dim_n)/dim_proc;
      result[i].inds_d = malloc(sizeof(i_pos)*result[i].tam_inds_d);
    }
    result[i%dim_proc].inds_d[i/dim_proc].dim_m = (int)(i / dim_n);
    result[i%dim_proc].inds_d[i/dim_proc].dim_n = (int)(i % dim_n);
  }
  return result;
}

void pinta_indices_arreglo_matriz (i_matriz *ids_m, int dim_proc) {
  for(int i=0; i<dim_proc; i++) {
    printf("Procesador (%i) %i tareas -> ", i,ids_m[i].tam_inds_d);
    for(int j = 0; j < ids_m[i].tam_inds_d; j++) {
      printf("(%i,%i) ", ids_m[i].inds_d[j].dim_m, ids_m[i].inds_d[j].dim_n);
    }
    printf("\n");
  }
}

void delete_matriz(i_matriz *ids_m, int dim_proc) {
  for(int p=0; p<dim_proc; p++){
    if(ids_m[p].inds_d!=NULL){
    free(ids_m[p].inds_d);
    }
  }
  if(ids_m!=NULL){
    free(ids_m);
  }
}


i_matriz_matriz* indices_matriz_matriz (int dim_r, int dim_s, int dim_m, int dim_n) {
  int dim_proc=dim_r*dim_s;
  i_matriz_matriz* result = malloc(sizeof(i_matriz_matriz)*dim_proc);
  int ii=0;
  for(int i=0;i<dim_m * dim_n;i++){
    if(i<dim_proc){
      ii=(i%dim_proc < (dim_m*dim_n) %dim_proc)?1:0;
      result[i].indice.dim_m = (int)(i / dim_s);
      result[i].indice.dim_n = i % dim_s;
      result[i].tam_inds_d =ii + (dim_m*dim_n)/dim_proc;
      result[i].inds_d = malloc(sizeof(i_pos)*result[i].tam_inds_d);
    }
    result[i%dim_proc].inds_d[i/dim_proc].dim_m = (int)(i / dim_n);
    result[i%dim_proc].inds_d[i/dim_proc].dim_n = (int)(i % dim_n);
  }
  return result;
}

void pinta_indices_matriz_matriz (i_matriz_matriz *ids_mm, int dim_r, int dim_s) {
  int dim_proc =  dim_r*dim_s;
  for(int p=0; p<dim_proc; p++) {
    printf("Procesador (%i,%i) %i tareas -> ", ids_mm[p].indice.dim_m, ids_mm[p].indice.dim_n,ids_mm[p].tam_inds_d);
    for(int q=0; q<ids_mm[p].tam_inds_d; q++) {
      printf(" (%i,%i) ", ids_mm[p].inds_d[q].dim_m, ids_mm[p].inds_d[q].dim_n);
    }
    printf("\n");
  }
}

void delete_matriz_matriz(i_matriz_matriz *ids_mm, int dim_p_m, int dim_p_n) {
  int procs = dim_p_m*dim_p_n;
  for(int i=0; i<procs; i++){
    if(ids_mm[i].inds_d!=NULL)
    free(ids_mm[i].inds_d);
  }
  if(ids_mm !=NULL){
  free(ids_mm);
  }
}
