#!/usr/bin/env python
import matplotlib.pyplot as plt
import sys
fo = open(sys.argv[1], "rw+")
data=[float("0"+x) for x in fo.readline().split(", ")][-1:]
print data
x=range(1,len(data)+1)
print len(x)
plt.plot(x,data,'ro-')
print "Guardando Imagen en grafica.jpg"
plt.savefig('grafica.jpg')

