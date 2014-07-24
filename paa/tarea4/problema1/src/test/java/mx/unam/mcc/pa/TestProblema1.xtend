package mx.unam.mcc.pa
import org.junit.Test;
import static org.junit.Assert.*;

class TestProblema1 {
    @Test
    def void testIndices1(){
        println("Datos arreglo 3 procesadores 2")
        val procs=Indices::indices_arreglo_arreglo(2,3)
        procs.forEach[IndsArreglo p | println(p)]
        assertEquals(procs.get(0).datos.size,2)
        assertEquals(procs.get(1).datos.size,1)
    }

    @Test
    def void testIndices2(){
        println("Datos arreglo 10 procesadores 10")
        val procs=Indices::indices_arreglo_arreglo(10,10)
        procs.forEach[IndsArreglo p | println(p)]
        assertEquals(procs.get(0).datos.size,1)
        assertEquals(procs.get(7).datos.size,1)
    }

    @Test
    def void testIndices3(){
        println("Datos arreglo 105 procesadores 10")
        val procs=Indices::indices_arreglo_arreglo(10,105)
        procs.forEach[IndsArreglo p | println(p)]
        assertEquals(procs.get(0).datos.size,11)
        assertEquals(procs.get(5).datos.size,10)
    }

    @Test
    def void testIndices4(){
        println("Datos arreglo 2 x 2, procesadores 6")
        val procs=Indices::indices_arreglo_matriz(6,2,2)
        procs.forEach[IndsArregloMat p | println(p)]
        assertEquals(procs.get(0).datos.size,1)
        assertEquals(procs.get(4).datos.size,0)
    }

    @Test
    def void testIndices5(){
        println("Datos arreglo 10 x 10, procesadores 10")
        val procs=Indices::indices_arreglo_matriz(10,10,10)
        procs.forEach[IndsArregloMat p | println(p)]
        assertEquals(procs.get(0).datos.size,10)
        assertEquals(procs.get(4).datos.size,10)
    }

    @Test
    def void testIndices6(){
        println("Datos arreglo 4 x 4, procesadores 3 x 3")
        val procs=Indices::indices_matriz_matriz(3,3,4,4)
        procs.forEach[IndsMatMat p | println(p)]
        assertEquals(2,2)
        assertEquals(procs.get(0).datos.size,2)
        assertEquals(procs.get(7).datos.size,1)
    }

    @Test
    def void testIndices7(){
        println("Datos arreglo 10 x 10, procesadores 5 x 3")
        val procs=Indices::indices_matriz_matriz(5,3,10,10)
        procs.forEach[IndsMatMat p | println(p)]
        assertEquals(2,2)
        assertEquals(procs.get(0).datos.size,7)
        assertEquals(procs.get(10).datos.size,6)
    }
}
