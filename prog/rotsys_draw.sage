#!/usr/bin/python
"""
    A SAT framework for topological drawings
    (c) 2022 Manfred Scheucher <scheucher@math.tu-berlin.de>
"""


from itertools import combinations, permutations
import itertools
def combinations(X,r): return itertools.combinations(X,int(r)) # sage versus python integers...
def permutations(X,r): return itertools.permutations(X,int(r)) # sage versus python integers...

from sys import *
from ast import literal_eval




load("drawing_basics.sage")


def does_a_see_bcd(rs,a,b,c,d):
    i = rs[a].index(b)
    rs_a = rs[a][i:]+rs[a][:i]
    return rs_a.index(c) < rs_a.index(d) 


def does_ab_cross_cd(rs,a,b,c,d):
    return does_a_see_bcd(rs,a,c,b,d) and \
            does_a_see_bcd(rs,b,d,a,c) and \
            does_a_see_bcd(rs,c,b,d,a) and \
            does_a_see_bcd(rs,d,a,c,b)


def compute_crossings(rs):
    crossings = {(a,b):[] for (a,b) in permutations(N,2)}

    for a,b,c,d in permutations(N,4):
        if does_ab_cross_cd(rs,a,b,c,d):
            crossings[a,b].append((c,d))

    return crossings



def find_planarization(rs,DEBUG=False):
    crossings = compute_crossings(rs)
    #print("crossings:",crossings)

    def _crossing_to_vertex(a,b,c,d): 
        if a>b: a,b = b,a
        if c>d: c,d = d,c
        return (a,b,c,d) if a<c else (c,d,a,b)

    def _edge_color(u,v):
        if len(v) < len(u): u,v = v,u
        if len(u)==1:
            if len(v) == 1: return tuple(sorted([u[0],v[0]]))
            if len(v) == 2: return tuple(sorted(v))
            elif u[0] in v[:2]: return v[:2]
            elif u[0] in v[2:]: return v[2:]
            else: 
                print (u,v)
                exit("error")
        elif len(u) == 2:
            if len(v) != 2:
                return tuple(sorted(u)) 
            else:
                if u[0] == v[0]:
                    return (u[0],) 
                else:
                    assert(u[0] == v[1] and v[1] == u[0])
                    return tuple(sorted(u))
        else:
            return u[2:] if set(u[:2])-set(v) else u[:2]

        print ("ERROR",u,v)
        exit()

    all_vertices = []
    vertices_along_edge = {}
    for a,b in combinations(N,2):
        vertices_along_edge[a,b] = []
        vertices_along_edge[a,b] += [(a,)]
        vertices_along_edge[a,b] += [_crossing_to_vertex(a,b,c,d) for c,d in crossings[a,b]]
        vertices_along_edge[a,b] += [(b,)]
        #print ("crossings along",a,b,":",vertices_along_edge[a,b])

        for v in vertices_along_edge[a,b]:
            if v not in all_vertices:
                all_vertices.append(v)
                #print("vertex:",v)

    all_vertices.sort()
    print("total number of vertices:",len(all_vertices))
    #print(all_vertices)


    all_variables = []

    # variables for planarization
    all_variables += [('order',(a,b,i,v)) for a,b in combinations(N,2) for i in range(len(vertices_along_edge[a,b])) for v in vertices_along_edge[a,b]] 
    all_variables += [('order2',(a,b,i,u,v)) for a,b in combinations(N,2) for i in range(1,len(vertices_along_edge[a,b])) for u,v in permutations(vertices_along_edge[a,b],2)] 
    all_variables += [('edge',(u,v)) for u,v in permutations(all_vertices,2)] 

    # variables for planarity
    all_variables += [('is_smaller',(i,u,v)) for i in range(3) for u,v in permutations(all_vertices,2)] # u < v in i-th linear order 
    all_variables += [('3rd_is_biggest',(i,u,v,w)) for i in range(3) for u,v,w in permutations(all_vertices,3) if u<v] # u < w and v < w in i-th linear order 


    all_variables_index = {}

    _num_vars = 0
    for v in all_variables:
        all_variables_index[v] = _num_vars
        _num_vars += 1

    def var(L): return 1+all_variables_index[L]
    def var_edge (*L): return var(('edge' ,L))
    def var_order(*L): return var(('order',L))
    def var_order2(*L): return var(('order2',L))

    def var_is_smaller(*L): return var(('is_smaller',L))
    def var_3rd_is_biggest(*L): return var(('3rd_is_biggest',L))


    constraints = []


    if DEBUG: print ("(*) undirected edges")
    for u,v in permutations(all_vertices,2):
        constraints.append([-var_edge(u,v),+var_edge(v,u)])

    potential_edges = set()

    if DEBUG: print ("(*) permutation of crosses along edges")
    for a,b in combinations(N,2):
        v_ab = vertices_along_edge[a,b]
        l_ab = len(v_ab)

        # permutation
        for i in range(l_ab):
            constraints.append([+var_order(a,b,i,v) for v in v_ab])

            for u,v in combinations(v_ab,2):
                constraints.append([-var_order(a,b,i,u),-var_order(a,b,i,v)])
        
        for v in v_ab:
            constraints.append([+var_order(a,b,i,v) for i in range(l_ab)])

            for i,j in combinations(range(l_ab),2):
                constraints.append([-var_order(a,b,i,v),-var_order(a,b,j,v)])

        # fix first+second from both sides
        for i in [0,l_ab-1]: 
            constraints.append([+var_order(a,b,i,v_ab[i])])


    if DEBUG: print ("(*) edges from permutations")
    for a,b in combinations(N,2):
        v_ab = vertices_along_edge[a,b]
        l_ab = len(v_ab)

        for u,v in permutations(v_ab,2):
            for i in range(1,l_ab):
                constraints.append([-var_order(a,b,i-1,u),-var_order(a,b,i,v),+var_order2(a,b,i,u,v)])
                constraints.append([+var_order(a,b,i-1,u),-var_order2(a,b,i,u,v)])
                constraints.append([+var_order(a,b,i  ,v),-var_order2(a,b,i,u,v)])

        for u,v in combinations(v_ab,2):
            constraints.append([-var_edge(u,v)]+[+var_order2(a,b,i,u,v) for i in range(1,l_ab)]+[+var_order2(a,b,i,v,u) for i in range(1,l_ab)])
            for i in range(1,l_ab):
                constraints.append([+var_edge(u,v),-var_order2(a,b,i,u,v)])
                constraints.append([+var_edge(u,v),-var_order2(a,b,i,v,u)])

                potential_edges.add((u,v))


    if DEBUG: print ("(*) only valid edges")
    for u,v in combinations(all_vertices,2):
        if (u,v) not in potential_edges and (v,u) not in potential_edges:
            constraints.append([-var_edge(u,v)])


    if DEBUG: print("(*) planarity: define linear orders")
    for i in range(3):
        # anti-symmetrie and total order (u<v or v<u)
        for u,v in permutations(all_vertices,2):
            constraints.append([+var_is_smaller(i,u,v),+var_is_smaller(i,v,u)])
            constraints.append([-var_is_smaller(i,u,v),-var_is_smaller(i,v,u)])

        # transitivity
        for u,v,w in permutations(all_vertices,3):
            constraints.append([-var_is_smaller(i,u,v),-var_is_smaller(i,v,w),+var_is_smaller(i,u,w)])


    if DEBUG: print("(*) planarity: assert 3rd_is_biggest variable")
    for i in range(3):
        for u,v,w in permutations(all_vertices,3):
            if u<v:
                constraints.append([-var_3rd_is_biggest(i,u,v,w),+var_is_smaller(i,u,w)])
                constraints.append([-var_3rd_is_biggest(i,u,v,w),+var_is_smaller(i,v,w)])
                constraints.append([+var_3rd_is_biggest(i,u,v,w),-var_is_smaller(i,u,w),-var_is_smaller(i,v,w)])


    if DEBUG: print("(*) planarity criterion")
    # definition 1.1 from http://page.math.tu-berlin.de/~felsner/Paper/ppg-rev.pdf
    for (u,v) in combinations(all_vertices,2):
        if u>v: u,v=v,u
        for x in set(all_vertices)-{u,v}:
            constraints.append([-var_edge(u,v)]+[+var_3rd_is_biggest(i,u,v,x) for i in range(3)])




    print ("Total number of constraints:",len(constraints))

    constraints = [[int(x) for x in C] for C in constraints] # sage versus python integers...
    


    if args.solver == "cadical":
        print ("use pysat/Cadical")
        from pysat.solvers import Cadical    
        solver = Cadical()
        for c in constraints: solver.add_clause(c)
        solution_iterator = solver.enum_models()
    else:
        print ("use pycosat")
        import pycosat
        solution_iterator = pycosat.itersolve(constraints)


    for sol in solution_iterator:
        sol = set(sol)
        edges = [(u,v,_edge_color(u,v)) for (u,v) in combinations(all_vertices,2) if var_edge(u,v) in sol]
        yield edges




def draw_with_outer_face(G,f):

    G.set_pos(iterated_tutte_layout(G,outer_face=f))

    # compute colors for sage graph plot
    def tuple2str(L): 
        return ''.join(str(x) for x in L)

    H = Graph([(tuple2str(a),tuple2str(b),tuple2str(l)) for a,b,l in G.edges()])
    pos = G.get_pos()
    H.set_pos({tuple2str(x):pos[x] for x in G})
    edge_labels = list(sorted(set(H.edge_labels()))) 
    rainbow = sage.plot.colors.rainbow(len(edge_labels))
    edge_colors = {rainbow[i]: [] for i in range(len(rainbow))}
    for u,v,l in H.edges():
        edge_colors[rainbow[edge_labels.index(l)]].append((u,v))

    ofp = fp+"_"+str(ct)+"_"+str(len(planarization_fingerprints))+".pdf"
    H.plot(edge_labels=1,edge_colors=edge_colors).save(ofp)
    #print("edges",H.edges())


    ofp = fp+"_"+str(ct)+"_"+str(len(planarization_fingerprints))+".ipe"
    graph_2_ipe(G,ofp)
    
    


import argparse
parser = argparse.ArgumentParser()
#parser.add_argument("n",type=int,help="number of elements")


parser.add_argument("filepath", help="input file for rotation systems to draw")

parser.add_argument("--solver", choices=['cadical', 'pycosat'], default='cadical', help="SAT solver")
parser.add_argument("--all","-a",action='store_true',help="compute all planarizations of rotation system")
parser.add_argument("--visualize","-v",action='store_true',help="visualize/draw the found embeddings")

args = parser.parse_args()

print("args",args)




fp = args.filepath

ct = 0
ct_drawable = 0
for line in open(fp):
    ct += 1
    print("")
    print("# ct",ct)

    if line == "": break
    rs = literal_eval(line)
    print(rs)

    n = len(rs)
    N = range(n)

    N_without_last = list(range(n-1))
    N_without = {i:list(range(i))+list(range(i+1,n)) for i in N}
    
    planarization_fingerprints = set()

    for edges in find_planarization(rs):
        if not planarization_fingerprints: ct_drawable += 1

        G = Graph(edges)

        gstr = G.canonical_label().sparse6_string()
        if gstr in planarization_fingerprints: continue # avoid duplicate drawings

        print ("found planarization!")
        planarization_fingerprints.add(gstr)


        assert(G.is_planar(set_pos=True))

        connectivity = G.vertex_connectivity()
        assert(connectivity >= 3) # unique embedding


        for v in G:
            if len(v) == 1: 
                assert(G.degree(v) == n-1)
            elif len(v)==4: 
                assert(G.degree(v) == 4)
            else:
                assert(len(v) == 2)
                assert(G.degree(v) in [2,4])


        F_directed = G.faces()
        F = [[u for (u,v) in f] for f in F_directed] # vertex list instead of edge list
        #print("faces",F)


        print("test proper crossings in embedding")
        for f in F:
            for i in range(len(f)):
                u = f[i-2]
                v = f[i-1]
                w = f[i]
                if len(v) == 4: 
                    assert(G.edge_label(u,v) != G.edge_label(v,w)) # would be a touching otherwise (instead of crossing)

        
        print("test rotation system in embedding")
        found_rs = []
        found_rs_mir = []
        for i in N:
            v = (i,)
            Nv = G.neighbors(v)
            rot_v = [Nv[0]]
            while len(rot_v) < len(Nv):
                e1 = (v,rot_v[-1])
                found = 0
                for f in F_directed:
                    if e1 in f:
                        e2 = f[f.index(e1)-1]
                        assert(e2[1] == v)
                        rot_v.append(e2[0])
                        found += 1
                assert(found == 1)

            assert(set(Nv) == set(rot_v))

            rot_i = []
            for w in rot_v:
                (a,b) = G.edge_label(v,w)
                rot_i.append(a if a != i else b)

            i0 = rot_i.index(1 if i == 0 else 0)
            rot_i = rot_i[i0:]+rot_i[:i0]
            rot_i_rev = rot_i[:1]+list(reversed(rot_i[1:]))
            
            found_rs.append(rot_i)
            found_rs_mir.append(rot_i_rev)

        assert(rs == found_rs or rs == found_rs_mir) # drawing must have the same rotation system or mirrored



        if args.visualize:
            def _quality(f): return 1
            #def _quality(f): return len([v for v in f if len(v)==1]) # maximize vertices on outer face
    
            max_q = max(len(f) for f in F)
            
            best_f = None
            for f in F:
                if len(f) == max_q:
                    best_f = f # choose a large outer face for the drawing
                if len([v for v in f if len(v)==1]) == len(f):
                    best_f = f # or face which contains only vertices
                    break
            
            draw_with_outer_face(G,best_f) 
                    

        
        if not args.all: break # just draw once
    

    print("# of non-isomorphic planarizations = ",len(planarization_fingerprints))
    
    if not planarization_fingerprints:
        print("error: no solution found! invalid rotation system!")
    

print(80*"-")
print("total: ",ct_drawable,"of",ct,"pre-rotation systems are drawable")