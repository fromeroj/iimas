#!/usr/bin/env python
import matplotlib.pyplot as plt
import sys, string, random

def x(point): return point[0]
def y(point): return point[1]

def derecha((p1,p2,p3)):
    return (x(p2)*y(p3)+x(p1)*y(p2)+
            x(p3)*y(p1)-x(p2)*y(p1)-
            x(p3)*y(p2)-x(p1)*y(p3))<1

def puntos_a_la_derecha(puntos):
    c = [puntos[0], puntos[1]]
    for p in puntos[2:]:
        c.append(p)
        while len(c) > 2 and not derecha(c[-3:]):
            del c[-2]
    return c

def cierre_convexo(puntos):
    puntos.sort() # Consideramos los puntos ordenados
    arriba=puntos_a_la_derecha(puntos)
    abajo=puntos_a_la_derecha(puntos[::-1])[1:-1]
    return arriba + abajo

def genera_puntos(num):
    rand = random.randint
    return [(rand(1,999),rand(1,999)) for i in xrange(num)]

def grafica(P, H):
    H=H+[H[0]]
    plt.plot([i[0] for i in P],[i[1] for i in P],'ro')
    plt.plot([i[0] for i in H],[i[1] for i in H],'o-')
    plt.show()

p = genera_puntos(200)
c = cierre_convexo(p)
grafica(p,c)
