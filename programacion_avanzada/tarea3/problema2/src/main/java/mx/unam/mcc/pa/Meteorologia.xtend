package mx.unam.mcc.pa

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.text.SimpleDateFormat;
import java.util.ArrayList
import java.util.Date
import java.util.List

import static extension com.google.common.io.CharStreams.*

@Data class Lectura{
    Date hora
    double humedad
    double temperatura
    override toString(){
        val df = new SimpleDateFormat("dd MMM yyyy hh:mm:ss");
        '''«df.format(hora)»,«this.humedad»,«this.temperatura»'''
        }
}

class Meteorologia{
   @Property List<Lectura> lecturas

   new(){this.lecturas=new ArrayList<Lectura>()}

   def guardar(String nombreArchivo){
        val content=this.lecturas.map[ toString ].join("\n")
        val file = new File(nombreArchivo)
        if (!file.exists()) {file.createNewFile()}
        val fw = new FileWriter(file.getAbsoluteFile());
        val bw = new BufferedWriter(fw)
        bw.write(content)
        bw.close()
        }

   def leer(String nombreArchivo){
        val df = new SimpleDateFormat("dd MMM yyyy hh:mm:ss");
        (new FileReader(nombreArchivo)).readLines.forEach [ 
            val segments = it.split(',').iterator
            this.lecturas.add(new Lectura(
                df.parse(segments.next),
                Double.parseDouble(segments.next), 
                Double.parseDouble(segments.next)))
            ]
        }

    def promedioTemperatura(){
        lecturas.map[temperatura].reduce[ a, b | a + b ] / lecturas.length()
        }

    def promedioHumedad(){
        lecturas.map[humedad].reduce[ a, b | a + b ] / lecturas.length()
        }

    //Regresa la primera medicion de temperatura despues de date
    def temperaturaDespues(Date date){
        lecturas.filter[hora >= date].sortBy[ hora ].head.temperatura
        }

    def temperaturaFDespues(Date date){
        1.8 * (this.temperaturaDespues(date)) + 32.0
        }
}
