package mx.unam.mcc.pa

@Data class Complejo{
    double real
    double imaginaria
    override toString(){
        '''(«this.real»,«this.imaginaria»)'''
        }

    def equals(Complejo otro){
        return (this.real==otro.real) && (this.imaginaria==otro.imaginaria)
        }

    def operator_plus(Complejo otro) {
        return new Complejo(this.real + otro.real,this.imaginaria + otro.imaginaria)
        }

    def operator_plus(Double x) {
        return new Complejo(this.real + x,this.imaginaria)
        }
 
    def operator_minus(Complejo otro) {
        return new Complejo(this.real - otro.real,this.imaginaria - otro.imaginaria)
        }
    def operator_minus(Double x) {
        return new Complejo(this.real - x,this.imaginaria)
        }

    def operator_multiply(Complejo otro) {
        return new Complejo( (this.real * otro.real) - (this.imaginaria * otro.imaginaria), (this.real * otro.imaginaria)+ (this.imaginaria * otro.real))
        }
    def operator_multiply(Double x) {
        return new Complejo( (this.real * x) , (this.imaginaria * x))
        }

    def operator_divide(Complejo otro) {
        val mod=otro.real*otro.real +otro.imaginaria*otro.imaginaria
        return new Complejo( ((this.real * otro.real) + (this.imaginaria * otro.imaginaria))/mod , ((this.imaginaria * otro.real) - (this.real * otro.imaginaria))/mod)
        }    
    def operator_divide(Double c) {
        return new Complejo(this.real/c ,this.imaginaria/c)
        }    
}
