#
def bin(s): return str(s) if s<=1 else bin(s>>1) + str(s&1)


def prueba(a,b):
    m=dv_mult(bin(a),bin(b))
    print bin(a)
    print bin(b)
    print m
    print int(m,2)

def dv_mult(a,b):
    if len(a)==1 or len(b)==1:
        return bin(int(a,2) * int (b,2))
    n=max(len(a),len(b))/2
    a1=a[:len(a)/2]
    a2=a[len(a)/2:]
    b1=b[:len(b)/2]
    b2=b[len(b)/2:]
    x1=dv_mult(a1,b1)
    x2=bin(int(dv_mult(a1,b2),2)+int(dv_mult(a2,b1),2))
    x3=dv_mult(a2,b2)
    print [a1,a2,b1,b2]
    print [x1,x2,x3]
    return x1 + x2.zfill(n) + x3.zfill(n)
