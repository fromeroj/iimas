package mx.unam.mcc.pa

@Data class PosMat{
    int x
    int y
    override toString()'''(«this.x»,«this.y»)'''
}

class IndsArreglo{
    @Property int id
    @Property Iterable<Integer> datos
    override toString(){
        '''Procesador («this.id») «this.datos.size» tareas -> «this.datos.join(" ")»'''
    }
    new(int p,Iterable<Integer> d){this.id=p;this.datos=d}
}

class IndsArregloMat{
    @Property int id
    @Property Iterable<PosMat> datos
    override toString(){
        '''Procesador («this.id») «this.datos.size» tareas -> «this.datos.join(" ")»'''
    }
    new(int p,Iterable<PosMat> d){this.id=p;this.datos=d}
}

class IndsMatMat{
    @Property int r
    @Property int s
    @Property Iterable<PosMat> datos
    override toString(){
        '''Procesador («this.r»,«this.s») «this.datos.size» tareas -> «this.datos.join(" ")»'''
    }
    new(int r,int s,Iterable<PosMat> d){this.r=r;this.s=s;this.datos=d}
}

class Indices{
    def static indices_arreglo_arreglo(int dim_proc,int dim_datos){
        (0..(dim_proc-1)).map(
            [int i | new IndsArreglo(i, 
                                   (0..(dim_datos-1)).filter[it%dim_proc==i] )])
        }

    def static indices_arreglo_matriz(int dim_proc,int dim_m,int dim_n){
        (0..(dim_proc-1)).map(
            [int i | new IndsArregloMat(i, 
                                   (0..(dim_m*dim_n-1)).
                                   filter[it%dim_proc==i].
                                   map[new PosMat(it%dim_n,it/dim_n )])])
        }

    def static indices_matriz_matriz(int dim_r, int dim_s, int dim_m, int dim_n){
        val dim_proc=(dim_r)*(dim_s)
        (0..(dim_proc-1)).map(
            [int i | new IndsMatMat(i%dim_r,i/dim_r, 
                                   (0..(dim_m*dim_n-1)).
                                   filter[it%dim_proc==i].
                                   map[new PosMat(it%dim_n,it/dim_n )])])
        }   
}
