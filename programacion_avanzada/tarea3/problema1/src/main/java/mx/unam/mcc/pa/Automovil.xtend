package mx.unam.mcc.pa
import java.util.Date
import java.util.List
import java.util.ArrayList


@Data class Localizacion{
    float lat
    float lon
    Date hora
}

class Automovil {
  @Property String marca
  @Property String modelo
  @Property int year
  @Property int cilindros
  @Property int potencia
  @Property List<Localizacion> ruta

  new(){this.ruta=new ArrayList<Localizacion>()}

  def Localizacion ultimaLocalization(){
        this.ruta.sortBy[ hora ].last
  }
}

class Propietario {
    @Property String nombre
    @Property String apellidoPaterno
    @Property String apellidoMaterno
    @Property Date nacimiento
    @Property List<Automovil> automoviles

    new(){this.automoviles=new ArrayList<Automovil>()}

    def Localizacion ultimaLocalization(){
        automoviles.map[ ultimaLocalization ].sortBy[ hora ].last
    }
}
