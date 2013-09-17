package mx.unam.mcc.pa
import org.junit.Test;
import static org.junit.Assert.*;
import java.util.Date

class TestProblema1 {

    @Test
    def void basicTest(){
        assertEquals(2,2);
    } 	

    @Test
    def void NewPropietario(){
        val p=new Propietario=>[
            it.nombre="Fabian"
            it.apellidoPaterno="Romero"
            it.apellidoMaterno="Jimenez"
        ]
        assertEquals(p.nombre,"Fabian")
    } 	

    @Test
    def void UltimaLocalizationAutomovil(){
        val a1=new Automovil=>[
            it.marca="Audi"
            it.modelo="A4"
            it.year=2010]
        a1.ruta.add(new Localizacion(0,0,new Date(63,0,16)))
        a1.ruta.add(new Localizacion(0,0,new Date(113,0,16)))
        assertEquals(a1.ultimaLocalization().hora,new Date(113,0,16))
        }

    @Test
    def void UltimaLocalizationPersona(){
        val p=new Propietario=>[
            it.nombre="Fabian"
            it.apellidoPaterno="Romero"
            it.apellidoMaterno="Jimenez"
        ]
        val a1=new Automovil=>[
            it.marca="Audi"
            it.modelo="A4"
            it.year=2010]
        val a2=new Automovil=>[
            it.marca="Volkswagen"
            it.modelo="Golf"
            it.year=2004]
        p.automoviles.add(a1)
        p.automoviles.add(a2)
        a1.ruta.add(new Localizacion(0,0,new Date(63,0,16)))
        a1.ruta.add(new Localizacion(0,0,new Date(113,0,16)))
        a2.ruta.add(new Localizacion(0,0,new Date(113,0,16)))
        assertEquals(p.ultimaLocalization().hora,new Date(113,0,16))
        }
}
