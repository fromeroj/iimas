#include "tarea_lib.c"
#include "encabezados.c"

int test1(int dim_datos, int dim_proc){
  printf("\nDatos arreglo %i procesadores %i\n", dim_datos, dim_proc);
  i_arreglo* resp = indices_arreglo_arreglo(dim_proc, dim_datos);
  pinta_indices_arreglo_arreglo(resp, dim_proc);
}

int test2(int dim_m, int dim_n, int dim_proc){
  i_matriz* resp = indices_arreglo_matriz(dim_proc, dim_m, dim_n);
  printf("\nDatos arreglo %i x %i, procesadores %i\n",dim_m, dim_n, dim_proc);
  pinta_indices_arreglo_matriz(resp, dim_proc);
  delete_matriz(resp, dim_proc);
}

int test3(int dim_r, int dim_s, int dim_m,int dim_n){
  printf("\nDatos arreglo %i x %i, procesadores %i x %i\n",
         dim_m, dim_n, dim_r, dim_s);
  i_matriz_matriz* resp = indices_matriz_matriz(dim_r, dim_s, dim_m, dim_n);
  pinta_indices_matriz_matriz(resp, dim_r, dim_s);
  delete_matriz_matriz(resp, dim_r, dim_s);
}

int main()
{
  printEncabezado1();
  test1(3,2);
  test1(10,10);
  test1(105,10);

  printEncabezado2();
  test2(2,2,6);
  test2(2,2,4);
  test2(10,10,10);

  printEncabezado3();
  test3(3,3,4,4);
  test3(2,2,8,4);
  test3(5,3,10,10);
  return(0);
}
