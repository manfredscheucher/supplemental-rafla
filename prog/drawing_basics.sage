from copy import *


def iterated_tutte_layout(G,outer_face):
    G2 = copy(G)

    weights = dict()
    for u,v in G2.edges(labels=None):
        weights[u,v] = weights[v,u] = 0.000001


    eps = 0.01
    maxit = 20
    mypoly = lambda x: x
    for it in range(1,maxit+1):
        #print ("tutte #",it)
        if it > 1:
            weights_old = weights
            weights = dict()
            for (u,v) in G.edges(labels=None):
                weights[u,v] = weights[v,u] = (RR(weights_old[u,v]+eps*(mypoly(dist2(u,v))-weights_old[u,v])))


            pos = G2.get_pos()
            for f in G2.faces():
                try:
                    vol_f = ConvexHull([pos[v] for u,v in f]).volume
                    qf = RR(vol_f)
                    for u,v in f:
                        weights[u,v] += float(it*qf)
                        weights[v,u] += float(it*qf)
                except:
                    None

            vw0 = vector([weights_old[e] for e in G.edges(labels=False)]).normalized()
            vw1 = vector([weights[e] for e in G.edges(labels=False)]).normalized()
            dvw = (vw0-vw1).norm()
            #print "weight-diff:",dvw
            if dvw < 10^-10: break
                    
        G2.set_pos(tutte_layout(G2,outer_face,weights))
        pos = G2.get_pos()
        dist2 = lambda u,v: (pos[u][0]-pos[v][0])^2+(pos[u][1]-pos[v][1])^2

    return G2.get_pos()


def tutte_layout(G,outer_face,weights=None):
    V = G.vertices()
    pos = dict()
    l = len(outer_face)

    a0 = pi/l+pi/2
    for i in range(l):
        ai = a0+pi*2*i/l
        pos[outer_face[i]] = (cos(ai),sin(ai))
    
    n = len(V)
    M = zero_matrix(RR,n,n)
    b = zero_matrix(RR,n,2)

    for i in range(n):
        v = V[i]
        if v in pos:
            M[i,i] = 1
            b[i,0] = pos[v][0]
            b[i,1] = pos[v][1]
        else:
            nv = G.neighbors(v)
            s = 0
            for u in nv:
                j = V.index(u)
                wu = weights[u,v] if weights else 1
                s += wu
                M[i,j] = -wu
            M[i,i] = s

    sol = M.pseudoinverse()*b
    return {V[i]:sol[i] for i in range(n)}
 

def compute_curves(G):
    curves = {}

    for c in G.edge_labels():
        if len(c) == 1: continue
        curves[c] = []

        v = (c[0],)
        curves[c].append(v)
        while v != (c[1],):
            change = 0
            for (a,b,cc) in G.edges_incident(v):
                if cc == c:
                    w = (a if a != v else b)
                    if w not in curves[c]:
                        curves[c].append(w)
                        v = w
                        change = 1
                        break
            if not change:
                print("error: no change!")
                print(c,curves[c],v)
                print(G.edges_incident(v))
                exit()
        

    return curves


def graph_2_ipe(G,filepath,DEBUG=False):
    points = G.get_pos()

    ipestyle = 'ipestyle.txt'
    g = open(filepath,'w')
    g.write("""<?xml version="1.0"?>
        <!DOCTYPE ipe SYSTEM "ipe.dtd">
        <ipe version="70005" creator="Ipe 7.1.4">
        <info created="D:20150825115823" modified="D:20150825115852"/>
        """)
    with open(ipestyle) as f:
        for l in f.readlines():
            g.write("\t\t"+l)
    g.write("""<page>
        <layer name="alpha"/>
        <layer name="beta"/>
        <layer name="gamma"/>
        <view layers="alpha beta gamma" active="alpha"/>\n""")
    
    # normalize
    x0 = min(x for (x,y) in points.values())
    y0 = min(y for (x,y) in points.values())
    x1 = max(1,max(x for (x,y) in points.values())-x0,1)
    y1 = max(1,max(y for (x,y) in points.values())-y0,1)
    maxval = max(x1,y1)
    
    #scale 
    M = 300
    M0 = 100
    points = {i:(M0+float((points[i][0]-x0)*M)/maxval,M0+float((points[i][1]-y0)*M)/maxval) for i in points}

    # write edges
    if DEBUG: print ("compute_curves")
    curves = compute_curves(G)
    if DEBUG: 
        print ("curves:")
        for c in curves: print (c,"->",curves[c])
    

    distances = {v:[] for v in G.vertices()}
    for c in curves:
        for i in range(len(curves[c])):
            p0 = x0,y0 = points[curves[c][i-1]]
            p1 = x1,y1 = points[curves[c][i  ]]
            d2 = (x0-x1)^2+(y0-y1)^2
            distances[curves[c][i-1]].append(d2)
            distances[curves[c][i  ]].append(d2)

    IPE_COLORS = ['red','blue','green','orange','pink','lightblue','purple','lightgray','black','darkgray','navy','darkred','darkgreen','brown','gold','lightgreen','turquoise']

    for c in curves:
        for color in c:
            # B-splines
            DASHED = '' if color == c[0] else ' dash="dashed"'
            g.write('<path layer="alpha" pen="fat" stroke="'+IPE_COLORS[color]+'" '+DASHED+'>\n')
            lc = len(curves[c])
            for i in range(lc):
                x0,y0 = points[curves[c][(i-1)%lc]]
                x1,y1 = points[curves[c][ i      ]]
                x2,y2 = points[curves[c][(i+1)%lc]]
                d0 = (x0-x1)^2+(y0-y1)^2
                d2 = (x2-x1)^2+(y2-y1)^2
                lmbd0 = sqrt(min(distances[curves[c][i]])/d0)/3
                lmbd2 = sqrt(min(distances[curves[c][i]])/d2)/3
                xl,yl = x1+lmbd0*(x0-x1),y1+lmbd0*(y0-y1)
                xr,yr = x1+lmbd2*(x2-x1),y1+lmbd2*(y2-y1)
                if i != 0   : g.write(str(xl)+" "+str(yl)+"\n")
                g.write(str(x1)+" "+str(y1)+(" m" if i == 0 else "")+"\n")
                if i != lc-1: g.write(str(xr)+" "+str(yr)+"\n")
            g.write("c\n</path>\n")
        

    proper_vertices = [v for v in G.vertices() if len(v) == 1]

    for u in proper_vertices:
        x,y = points[u]
        g.write('<use transformations="translations" layer="beta" name="mark/fdisk(sfx)" pos="'+str(x)+' '+str(y)+'" size="large" stroke="black" fill="'+IPE_COLORS[u[0]]+'"/>\n')
        g.write('<text transformations="translations" layer="gamma" pos="'+str(x+2)+' '+str(y+2)+'" stroke="black" type="label">$'+str(u[0])+'$</text>\n')

    
    g.write("""</page>\n</ipe>""")
    g.close()
    print ("wrote to ipe-file: ",filepath)



