def x(point): return point[0]
def y(point): return point[1]

def derecha(p1,p2,p3):
    """Regresa un booleano que indica si el punto 3 esta a la derecha 
    de la linea (dirijida) p1,p2 usando el hecho de que la direccion 
    es el signo del determinante"""
    return (y(p1)-y(p3))*(y(p2)-y(p3))>(x(p1)-x(p3))*(x(p2)-x(p3))

def doble_area(p1,p2,p3):
    """Regresa el doble del area dirigida de un triangulo"""
    return (-x(p2)*y(p1)+x(p3)*y(p1)+x(p1)*y(p2)-x(p3)*y(p2)-x(p1)*y(p3)+x(p2)*y(p3))


def join(l1,l2):
    #Primero encontramos el elemento en comun.
    

def envolvente_convexa(l):
    """ """
   if len(l)==3:
       return l if doble_area(l[0],l[1],l[2])>0 else [l[0],l[2],l[1]]
   if len(l)<3:
       return l
   h=len(l)/2
   return join(envolvente_convexa(l[:h]),envolvente_convexa(l[h:]))
