# http://networkx.github.io/documentation/latest/tutorial/tutorial.html
# http://code.enthought.com/projects/mayavi/
import networkx as nx
import numpy as np
import numpy.ma as ma
import itertools
from mayavi import mlab

# Generate graph to visualize
#H=nx.random_lobster(100,0.9,0.9)
#H=nx.balanced_tree(5, 2)
#H=nx.complete_graph(15)

def draw_graph(H):
    G=nx.convert_node_labels_to_integers(H)
    pos=nx.spring_layout(H,dim=3,scale=100)
    xyz=np.array([pos[v] for v in sorted(H)])
    nodes=np.array(H.nodes())
    mlab.figure(1, bgcolor=(0, 0, 0))
    mlab.clf()
    pts = mlab.points3d(xyz[:,0], xyz[:,1], xyz[:,2],
        [ x if type(x)==np.int64 else ord(x[0][0])-90 for x in nodes],
        scale_factor=1,
        scale_mode='none',
        colormap='file',
        resolution=20)
    pts.mlab_source.dataset.lines = np.array(G.edges())
    tube = mlab.pipeline.tube(pts, tube_radius=0.2)
    mlab.pipeline.surface(tube, color=(0.8, 0.8, 0.8))
    mlab.show()

class Dmodel:
    "Distributed computing model"

    def __init__(self,agents,values,rounds):
        ""
        self.colours=colours
        self.values=values
        self.rounds=rounds
    
    def combinatorial_model():
        ""
        
        pass
    
    def kripke_model():
        ""
        pass

# execfile("ejemplo.py")
#
def include(a,b):
    elm=len([x for x in a if x in b])
    return elm==len(a) or elm==len(b)

def is_connected(a,b):
    return a[0]!=b[0] and include(a[1],b[1])

# [item for sublist in l for item in z]


# sum(map(lambda r: list(itertools.combinations(s, r)), range(1, len(s)+1)), [])


# z=[[ (y,x) for y in x ] for x in d]

# elements=set(['a','b','c'])

def combinatorial(elements):
    GGG=nx.Graph()
    subsets=sum(map(lambda r: list(itertools.combinations(elements, r)), range(1, len(elements)+1)), [])
    pairs=[[ (y,x) for y in x ] for x in subsets]
    flatten=[item for sublist in pairs for item in sublist]
    d={}
    i=0
    for x in flatten:
        d[(x[0]+"{}").format(i)]=x
        i=i+1        
    res=[(x,y) for x in d.keys() for y in d.keys() if is_connected(d[x],d[y])]
    GGG.add_edges_from(res)
    return GGG


def kripke(elements):
    
