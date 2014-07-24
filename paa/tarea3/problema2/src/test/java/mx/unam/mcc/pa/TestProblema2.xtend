package mx.unam.mcc.pa
import org.junit.Test;
import static org.junit.Assert.*;
import java.util.Date

class TestProblema2 {

    @Test
    def void basicTest(){
        assertEquals(2,2);
    }

    @Test
    def void TestGuardar(){
        var m=new Meteorologia
        m.lecturas.add(new Lectura(new Date(113,0,16,12, 0,0),50.0,50.0))
        m.lecturas.add(new Lectura(new Date(113,0,16,12,20,0),51.0,55.0))
        m.lecturas.add(new Lectura(new Date(113,0,16,12,40,0),52.0,60.0))
        m.guardar("test.csv")
        assertEquals(2,2);
    }

    @Test
    def void TestLeer(){
        var m=new Meteorologia
        m.leer("test.csv")
        assertEquals(m.lecturas.head.temperatura,50.0,0.1);
        assertEquals(m.lecturas.head.humedad,50.0,0.1);
    }


    @Test
    def void TestPromedioHumedad(){
        var m=new Meteorologia
        m.lecturas.add(new Lectura(new Date(113,0,16,12, 0,0),50.0,0.0))
        m.lecturas.add(new Lectura(new Date(113,0,16,12,20,0),51.0,0.0))
        m.lecturas.add(new Lectura(new Date(113,0,16,12,40,0),52.0,0.0))
        assertEquals(m.promedioHumedad,51.0,0.1);
    }

    @Test
    def void TestPromedioTemperatura(){
        var m=new Meteorologia
        m.lecturas.add(new Lectura(new Date(113,0,16,12, 0,0),0.0,10.0))
        m.lecturas.add(new Lectura(new Date(113,0,16,12,20,0),0.0,20.0))
        m.lecturas.add(new Lectura(new Date(113,0,16,12,40,0),0.0,30.0))
        assertEquals(m.promedioTemperatura,20.0,0.1);
    }


    @Test
    def void TestTemperaturaDespues(){
        var m=new Meteorologia
        m.lecturas.add(new Lectura(new Date(113,0,16,12, 0,0),0.0,10.0))
        m.lecturas.add(new Lectura(new Date(113,0,16,12,20,0),0.0,20.0))
        m.lecturas.add(new Lectura(new Date(113,0,16,12,40,0),0.0,30.0))
        assertEquals(m.temperaturaDespues(new Date(113,0,16,12,15,0)),20.0,0.1);
    }

    @Test
    def void TestTemperaturaFDespues(){
        var m=new Meteorologia
        m.lecturas.add(new Lectura(new Date(113,0,16,12, 0,0),0.0,10.0))
        m.lecturas.add(new Lectura(new Date(113,0,16,12,20,0),0.0,20.0))
        m.lecturas.add(new Lectura(new Date(113,0,16,12,40,0),0.0,30.0))
        assertEquals(m.temperaturaFDespues(new Date(113,0,16,12,15,0)),68.0,0.1);
    }

}
