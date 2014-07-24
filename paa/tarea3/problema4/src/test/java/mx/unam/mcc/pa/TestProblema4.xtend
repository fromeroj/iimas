package mx.unam.mcc.pa
import org.junit.Test;
import static org.junit.Assert.*;

class TestProblema4 {

    @Test
    def void basicTest(){
        assertEquals(2,2);
    }

    @Test
    def void TestPositionNewRobot(){
        val t=new Tablero()
        val r=new Robot(t)
        assertEquals(r.posicion,new Coordenada(0,0));
    }

    @Test
    def void TestNoMovimientoPosicionInvalida(){
        val t=new Tablero()
        val r1=new Robot(t)
        r1.arriba()
        assertEquals(r1.posicion,new Coordenada(0,1));
        val r2=new Robot(t)
        r2.arriba()
        println(r2.posicion)
        assertEquals(r2.posicion,new Coordenada(0,0));
    }
}
