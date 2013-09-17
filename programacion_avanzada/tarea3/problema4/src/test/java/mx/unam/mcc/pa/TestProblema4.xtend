package mx.unam.mcc.pa
import org.junit.Test;
import static org.junit.Assert.*;

class TestProblema3 {

    @Test
    def void basicTest(){
        assertEquals(2,2);
    }

    @Test
    def void TestEqual(){
        assertEquals( new Complejo(1.5,2.0),new Complejo(1.5,2.0));
    }

    @Test
    def void TestSumaComplejos(){
        val x=new Complejo(1.5,2.0)
        val y=new Complejo(3.0,4.0)
        assertEquals(x+x,y);
    }

    @Test
    def void TestSumaEscalar(){
        val x=new Complejo(1.5,2.0)
        val y=new Complejo(3.0,2.0)
        assertEquals(x + 1.5 ,y);
    }

    @Test
    def void TestRestaComplejos(){
        val x=new Complejo(1.5,2.0)
        val y=new Complejo(3.0,4.0)
        assertEquals(y-x,x);
    }

    @Test
    def void TestRestaEscalar(){
        val x=new Complejo(1.5,2.0)
        val y=new Complejo(3.0,2.0)
        assertEquals(y-1.5 ,x);
    }

    @Test
    def void TestMultiplicacionComplejos(){
        val x=new Complejo(2.0,3.0)
        val y=new Complejo(3.0,1.0)
        val z=new Complejo(3.0,11.0)
        assertEquals(x*y,z);
    }

    @Test
    def void TestMultiplicacionEscalar(){
        val x=new Complejo(1.5,2.0)
        val y=new Complejo(3.0,4.0)
        assertEquals(x*2.0,y);
    }

    @Test
    def void TestDivisionComplejos(){
        val x=new Complejo(2.0,3.0)
        val y=new Complejo(3.0,1.0)
        val z=new Complejo(3.0,11.0)
        assertEquals(z/x,y);
    }

    @Test
    def void TestDivisionEscalar(){
        val x=new Complejo(1.5,2.0)
        val y=new Complejo(3.0,4.0)
        assertEquals(y/2.0,x);
    }
}
