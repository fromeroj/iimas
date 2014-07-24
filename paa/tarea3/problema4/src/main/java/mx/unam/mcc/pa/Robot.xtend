package mx.unam.mcc.pa
import java.util.ArrayList
import java.util.List

@Data class Coordenada{
    int x
    int y
    override toString(){
        '''(«this.x»,«this.y»)'''
        }

    def equals(Coordenada otra){
        return (this.x==otra.x) && (this.y==otra.y)
        }
    def operator_plus(Coordenada otra) {
        return new Coordenada(this.x + otra.x,this.y + otra.y)
        }
}

class Tablero{
    @Property List<Robot> robots

    new(){
        this.robots=new ArrayList<Robot>()
    }

    def libre(Coordenada c){
        !this.robots.exists[ it.posicion == c ]
    }

}

class Robot{
    @Property Coordenada posicion    
    Tablero tablero
 
     new(Tablero tablero){
        this.posicion=new Coordenada(0,0)
        this.tablero=tablero
        tablero.robots.add(this)
     }

     def arriba(){
        val newPos=this.posicion+new Coordenada(0,1)
        if(tablero.libre(newPos)){
            this.posicion=newPos
            }
        this
     }

     def abajo(){
        val newPos=this.posicion+new Coordenada(0,-1)
        if(tablero.libre(newPos)){
            this.posicion=newPos
            }
        this
     }

     def izquierda(){
        val newPos=this.posicion+new Coordenada(-1,0)
        if(tablero.libre(newPos)){
            this.posicion=newPos
            }
        this
     }

     def derecha(){
        val newPos=this.posicion+new Coordenada(1,0)
        if(tablero.libre(newPos)){
            this.posicion=newPos
            }
        this
     }
}
