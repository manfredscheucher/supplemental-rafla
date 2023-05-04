"""
	A SAT framework for topological drawings
    (c) 2022 Manfred Scheucher <scheucher@math.tu-berlin.de>
             Helena Bergold <helena.bergold@fu-berlin.de>
             Meghana M. Reddy <meghana.mreddy@inf.ethz.ch>
"""


from itertools import combinations, permutations
from ast import literal_eval
import datetime

import argparse
parser = argparse.ArgumentParser()
parser.add_argument("n",type=int,help="number of elements")
parser.add_argument("-a","--all",action='store_true', help="enumerate all configurations")
parser.add_argument("-l","--lexmin",action='store_true', help="restrict to lexigraphic minima (symmetry breaking w.r.t. relabeling+mirroring)")
parser.add_argument("-c","--convex",action='store_true', help="restrict to convex")
parser.add_argument("-hc","--hconvex",action='store_true', help="restrict to h-convex")

parser.add_argument("-nat","--natural",action='store_false',help="remove assumption that first line needs not to be 2,3,...,n (enabled by default, use parameter to disable)")
parser.add_argument("-v4","--valid4tuples",action='store_false',help="remove assumption that 4-tuples are valid (enabled by default, use parameter to disable)")
parser.add_argument("-v5","--valid5tuples",action='store_false',help="remove assumption that 5-tuples are valid (enabled by default, use parameter to disable)")

parser.add_argument("-HC","--forbidHC",action='store_true', help="forbid plane Hamiltonian cycle")
parser.add_argument("-HC+","--forbidHCplus",action='store_true', help="forbid plane Hamiltonian subgraphs on 2n-3 edges")
parser.add_argument("-HC++","--forbidHCplusplus",action='store_true', help="assume that not every plane Hamiltonian cycle can be extended to a plane Hamiltonian subgraph on 2n-3 edges")

parser.add_argument("-HPe","--forbidHPedge",action='store_true', help="assume that for one edge there is no plane Hamiltonian path")

parser.add_argument("-HT+","--HoffmannTothplus",type=int, help="check strengthened Hoffmann-Toth property")

parser.add_argument("-aec","--alledgescrossed",action='store_true', help="assert that all edges are crossed")
parser.add_argument("-aecsub","--alledgescrossedsub",action='store_true', help="assert that all edges are crossed in subconfigurations")

parser.add_argument("-cpc","--checkpairsofcrossings",action='store_true', help="check pairs of crossing edges")

parser.add_argument("-crf","--crossingfamily",type=int,help="forbid crossing family of given size")

parser.add_argument("-C5","--forbidC5",action='store_true', help="forbid the perfect convex C5")
parser.add_argument("-C6","--forbidC6",action='store_true', help="forbid the perfect convex C6")
parser.add_argument("-T5","--forbidT5",action='store_true', help="forbid the perfect twisted T5")
parser.add_argument("-T6","--forbidT6",action='store_true', help="forbid the perfect twisted T6")

parser.add_argument("--testHConvexBadEdgeLemma",action='store_true',help="test testHConvexBadEdgeLemma")
parser.add_argument("--testNestedLemmaPart1",action='store_true',help="test nesting lemma part 1")
parser.add_argument("--testNestedLemmaPart2Case",type=int,help="test nesting lemma part 2")
parser.add_argument("--testNoCrossingInRLemmaCase",type=int,help="test no crossing in R lemma")

parser.add_argument("-etlow",type=int,help="minimum number of empty triangles")
parser.add_argument("-etupp",type=int,help="maximum number of empty triangles")

parser.add_argument("-kholes",type=int,help="forbid convex k-holes")
parser.add_argument("-kholessub",type=int,help="forbid convex k-holes in subconfigurations")

parser.add_argument("--test6gon5hole",action='store_true', help="assume there is a 6-gon but no 5-hole")

parser.add_argument("-r2f","--rs2file", help="if specified, export rotation systems to this file")
parser.add_argument("-c2f","--cnf2file", help="if specified, export CNF to this file")
parser.add_argument("--solver", choices=['cadical', 'pycosat'], default='cadical', help="SAT solver")

args = parser.parse_args()
print("args",args)

#vargs = vars(args)
#print("c\tactive args:",{x:vargs[x] for x in vargs if vargs[x] != None and vargs[x] != False})


if args.hconvex: args.convex = True

emptytriangles = False
if args.etlow != None or args.etupp != None: emptytriangles = True
if args.kholes: emptytriangles = True

emptytrianglessub = False
if args.kholessub: 
    emptytriangles = True
    emptytrianglessub = True


if args.all:
    print("args.all set to true. set args.solver to pycosat for enumeration")
    args.solver = 'pycosat'



time_start = datetime.datetime.now()

n = args.n
N = list(range(n))

N_without_last = list(range(n-1))
N_without = {i:list(range(i))+list(range(i+1,n)) for i in N}


all_variables = []

all_variables += [('rotsys',(a,i,b)) for a in N for i in N_without_last for b in N_without[a]] 
# b is the i-th vertex in cyclic order around vertex a

all_variables += [('a_sees_bcd',(a,b,c,d)) for a,b,c,d in permutations(N,4)] 
# around vertex a, we have b then c then d

all_variables += [('ab_cross_cd',(a,b,c,d)) for a,b,c,d in permutations(N,4)] 
all_variables += [('ab_cross_cd_directed',(a,b,c,d)) for a,b,c,d in permutations(N,4)] 

if args.lexmin:
    # for symmetry breaking
    all_variables += [('perm',(x0,x1,a,b)) for x0 in N for x1 in N_without[x0] for a in N for b in N]
    all_variables += [('rotsys_perm',(x0,x1,a,i,b,mir)) for x0 in N for x1 in N_without[x0] for a in N for i in N_without_last for b in N_without[a] for mir in [False,True]]
    all_variables += [('rotsys_perm_eq_orig',(x0,x1,a,i,b,mir)) for x0 in N for x1 in N_without[x0] for a in N for i in N_without_last for b in N_without[a] for mir in [False,True]]
    all_variables += [('rotsys_perm_gt_orig',(x0,x1,a,i,b,mir)) for x0 in N for x1 in N_without[x0] for a in N for i in N_without_last for b in N_without[a] for mir in [False,True]]
    all_variables += [('rotsys_perm_lt_orig',(x0,x1,a,i,b,mir)) for x0 in N for x1 in N_without[x0] for a in N for i in N_without_last for b in N_without[a] for mir in [False,True]]

if emptytriangles:
    all_variables += [('abc_contains_d',(a,b,c,d)) for a,b,c,d in permutations(N,4)] 

    containment_types = [(1,1,1),(-1,1,1),(1,-1,1),(1,1,-1)]
    all_variables += [('abc_contains_d_type',(a,b,c,d,t)) for a,b,c,d in permutations(N,4) for t in containment_types] 
    
    all_variables += [('abc_empty',(a,b,c)) for a,b,c in permutations(N,3)] 

if emptytrianglessub:
    all_variables += [('abc_empty_sub',(a,b,c,k)) for k in range(3,n+1) for a,b,c in permutations(range(k),3)] 

all_variables_index = {} 
# python dictionary for faster lookup of variables (compared to lists) 

_num_vars = 0
for v in all_variables:
    _num_vars += 1
    all_variables_index[v] = _num_vars

def var(L):	return all_variables_index[L]
def var_rotsys(*L): return var(('rotsys',L))
def var_a_sees_bcd(*L): return var(('a_sees_bcd',L))

def var_ab_cross_cd(*L): return var(('ab_cross_cd',L))
def var_ab_cross_cd_directed(*L): return var(('ab_cross_cd_directed',L))

def var_perm(*L): return var(('perm',L))
def var_rotsys_perm(*L): return var(('rotsys_perm',L))
def var_rotsys_perm_eq_orig(*L): return var(('rotsys_perm_eq_orig',L))
def var_rotsys_perm_gt_orig(*L): return var(('rotsys_perm_gt_orig',L))
def var_rotsys_perm_lt_orig(*L): return var(('rotsys_perm_lt_orig',L))

def var_abc_contains_d(*L): return var(('abc_contains_d',L))
def var_abc_contains_d_type(*L): return var(('abc_contains_d_type',L))
def var_abc_empty(*L): return var(('abc_empty',L))
def var_abc_empty_sub(*L): return var(('abc_empty_sub',L))

from pysat.card import *
vpool = IDPool(start_from=_num_vars+1)  # for auxiliary pysat variables

constraints = []


print ("(*) wlog: first column is 1,0,0,...,0")
constraints.append([var_rotsys(0,0,1)])
for a in N_without[0]:
    constraints.append([var_rotsys(a,0,0)])
        

if args.natural:
    print ("(*) wlog: first line is 1,2,3,4,...")
    for a in N_without_last:
        constraints.append([var_rotsys(0,a,a+1)])



print ("(*) assert permutations",len(constraints))
for a in N:
    for i in N_without_last:
        constraints.append([var_rotsys(a,i,b) for b in N_without[a]])
        for b1,b2 in combinations(N_without[a],2):
            constraints.append([-var_rotsys(a,i,b1),-var_rotsys(a,i,b2)])

    for b in N_without[a]:
        constraints.append([var_rotsys(a,i,b) for i in N_without_last])
        for i1,i2 in combinations(N_without_last,2):
            constraints.append([-var_rotsys(a,i1,b),-var_rotsys(a,i2,b)])


print ("(*) assert a_sees_bcd",len(constraints))
for a in N:
    for b,c,d in combinations(N_without[a],3):
        for x,y,z in permutations([b,c,d]):
            inversions = sum(+1 for u,v in combinations([x,y,z],2) if u>v)
            sign = (-1)**inversions
            constraints.append([-var_a_sees_bcd(a,b,c,d),+sign*var_a_sees_bcd(a,x,y,z)])
            constraints.append([+var_a_sees_bcd(a,b,c,d),-sign*var_a_sees_bcd(a,x,y,z)])


print ("(*) assert a_sees_bcd",len(constraints))
for a,b,c,d in permutations(N,4):
    for i,j,k in combinations(N_without_last,3):
        constraints.append([-var_rotsys(a,i,b),-var_rotsys(a,j,c),-var_rotsys(a,k,d),+var_a_sees_bcd(a,b,c,d)])


def forbid_subrs(subrs):
    k = len(subrs)
    constraints = []
    for I in permutations(N,k):
        for s in [+1,-1]: # forbid original and mirrored
            constraints.append([-s*var_a_sees_bcd(I[a],I[b],I[c],I[d]) for a in range(k) for b,c,d in combinations(subrs[a],3)])
    return constraints


if args.valid4tuples:
    print ("(*) assert valid 4-tuples",len(constraints))
    constraints += forbid_subrs(
        [[1,2,3],[0,2,3],[0,1,3],[0,2,1]])


if args.valid5tuples:
    print ("(*) assert valid 5-tuples")
    constraints += forbid_subrs(
        [[1,2,3,4],[0,2,3,4],[0,3,1,4],[0,4,2,1],[0,3,1,2]]) # forbidden type I
    constraints += forbid_subrs(
        [[1,2,3,4],[0,2,4,3],[0,3,1,4],[0,4,2,1],[0,1,3,2]]) # forbidden type II


if args.convex:
    print ("(C) restrict to convex drawings",len(constraints))
    constraints += forbid_subrs(
        [[1,2,3,4],[0,2,4,3],[0,1,3,4],[0,1,4,2],[0,3,1,2]]) # obstruction with 3 crossings
    constraints += forbid_subrs(
        [[1,2,3,4],[0,2,3,4],[0,1,3,4],[0,1,4,2],[0,1,3,2]]) # T5, i.e., obstruction 5 crossings


if args.hconvex:
    assert(args.convex)
    print ("(H) restrict to h-convex drawings",len(constraints))
    constraints += forbid_subrs(
        [[1,2,3,4,5],[0,2,3,4,5],[0,1,5,3,4],[0,1,2,4,5],[0,1,2,3,5],[0,1,3,4,2]])



print ("(*) assert ab_cross_cd",len(constraints))
for a,b,c,d in permutations(N,4):
    constraints.append([
        -var_a_sees_bcd(a,b,d,c),
        -var_a_sees_bcd(b,a,c,d),
        -var_a_sees_bcd(c,a,b,d),
        -var_a_sees_bcd(d,a,c,b),+var_ab_cross_cd_directed(a,b,c,d)])
    constraints.append([
        +var_a_sees_bcd(a,b,d,c),-var_ab_cross_cd_directed(a,b,c,d)])
    constraints.append([
        +var_a_sees_bcd(b,a,c,d),-var_ab_cross_cd_directed(a,b,c,d)])
    constraints.append([
        +var_a_sees_bcd(c,a,b,d),-var_ab_cross_cd_directed(a,b,c,d)])
    constraints.append([
        +var_a_sees_bcd(d,a,c,b),-var_ab_cross_cd_directed(a,b,c,d)])

    constraints.append([-var_ab_cross_cd_directed(a,b,c,d),+var_ab_cross_cd(a,b,c,d)])
    constraints.append([-var_ab_cross_cd_directed(a,b,d,c),+var_ab_cross_cd(a,b,c,d)]) 
    constraints.append([+var_ab_cross_cd_directed(a,b,c,d),+var_ab_cross_cd_directed(a,b,d,c),-var_ab_cross_cd(a,b,c,d)])



if args.lexmin:
    assert(args.natural)
    print ("(*) assert permutations for lexmin / symmetry breaking",len(constraints))
    for x0 in N: # x0 = pi^-1(0)
        for x1 in N_without[x0]: # x1 = pi^-1(1)
            for a in N:
                constraints.append([var_perm(x0,x1,a,b) for b in N])
                for b1,b2 in combinations(N,2):
                    constraints.append([-var_perm(x0,x1,a,b1),-var_perm(x0,x1,a,b2)])

            for b in N:
                constraints.append([var_perm(x0,x1,a,b) for a in N])
                for a1,a2 in combinations(N,2):
                    constraints.append([-var_perm(x0,x1,a1,b),-var_perm(x0,x1,a2,b)])

            constraints.append([+var_perm(x0,x1,x0,0)])
            constraints.append([+var_perm(x0,x1,x1,1)])
            
            for l in N_without_last: # l = position of x1 in row x0
                for i in N_without_last: # column 
                    for x in N_without[x0]: # x = entry in row x0 column l+i in original rotsys = pi^-1( entry (0,i) in new rot sys )
                        constraints.append([-var_rotsys(x0,l,x1),-var_rotsys(x0,(l+i)%(n-1),x),+var_perm(x0,x1,x,(1+i))])



    print ("(*) assert permuted+mirrored rotation systems",len(constraints))
    for x0 in N: # x0 = pi^-1(0)
        for x1 in N_without[x0]: # x1 = pi^-1(1)
            for a in N:
                for mir in [False,True]:
                    for i in N_without_last:
                        constraints.append([var_rotsys_perm(x0,x1,a,i,b,mir) for b in N if b != a])
                        for b1,b2 in combinations(N_without[a],2):
                            constraints.append([-var_rotsys_perm(x0,x1,a,i,b1,mir),-var_rotsys_perm(x0,x1,a,i,b2,mir)])

                    for b in N_without[a]:
                        constraints.append([var_rotsys_perm(x0,x1,a,i,b,mir) for i in N_without_last])
                        for i1,i2 in combinations(N_without_last,2):
                            constraints.append([-var_rotsys_perm(x0,x1,a,i1,b,mir),-var_rotsys_perm(x0,x1,a,i2,b,mir)])



    print ("(*) synchronize permuted rotation systems",len(constraints))
    for x0 in N: # x0 = pi^-1(0)
        for x1 in N_without[x0]: # x1 = pi^-1(1)
            for k in N: # row
                for xk in N: # xk = pi^-1(k)
                    for l in N_without_last: # l = position of x0 in row xk
                        for i in N_without_last: # column
                            for x in N_without[xk]: # x = entry in row xk column l+i in original rotsys = pi^-1( entry (k,i) in new rot sys )
                                for pix in N_without[k]: # pix = pi(x) = entry (k,i) in new rot sys
                                    if xk == x0 and k == 0: # first row
                                        constraints.append([-var_perm(x0,x1,xk,k),-var_rotsys(xk,l,x1),-var_rotsys(xk,(l+i)%(n-1),x),-var_perm(x0,x1,x,pix),+var_rotsys_perm(x0,x1,k,i,pix,False)])
                                        # this is equal to
                                        #constraints.append([-var_perm(x0,x1,x0,0),-var_rotsys(x0,l,x1),-var_rotsys(x0,(l+i)%(n-1),x),-var_perm(x0,x1,x,pix),+var_rotsys_perm(x0,x1,0,i,pix)])
                                    if xk != x0 and k != 0: # other rows
                                        constraints.append([-var_perm(x0,x1,xk,k),-var_rotsys(xk,l,x0),-var_rotsys(xk,(l+i)%(n-1),x),-var_perm(x0,x1,x,pix),+var_rotsys_perm(x0,x1,k,i,pix,False)])



    print ("(*) synchronize mirrored rotation systems",len(constraints))
    mirrored_rows = [0,1]+list(reversed(range(2,n  ))) # permutation of elements/rows for mirroring
    mirrored_cols = [0]  +list(reversed(range(1,n-1))) # permutation of cols for mirroring
    for i in N:              assert(mirrored_rows[mirrored_rows[i]]==i) # involution
    for i in N_without_last: assert(mirrored_cols[mirrored_cols[i]]==i) # involution

    for x0 in N: 
        for x1 in N_without[x0]: 
            for a in N:
                for i in N_without_last:
                    for b in N_without[a]:
                        for mir in [False,True]:
                            constraints.append([-var_rotsys_perm(x0,x1,a,i,b,mir),+var_rotsys_perm(x0,x1,mirrored_rows[a],mirrored_cols[i],mirrored_rows[b],not mir)])
                    


    print ("(*) compare permuted rotation systems for symmetry breaking",len(constraints))
    for x0 in N: # x0 = pi^-1(0)
        for x1 in N_without[x0]: # x1 = pi^-1(1)
            prev_a = None
            prev_i = None
            prev_b = None
            for a in N:
                for i in N_without_last:
                    for b in N_without[a]:
                        for mir in [False,True]:
                            constraints.append([-var_rotsys_perm_lt_orig(x0,x1,a,i,b,mir)]) # permuted rotation systems should not be smaller
                            constraints.append([-var_rotsys_perm_gt_orig(x0,x1,a,i,b,mir),-var_rotsys_perm_eq_orig(x0,x1,a,i,b,mir)]) # but equal or greater (not both) 

                            if prev_a == None:
                                constraints.append([-var_rotsys(a,i,b),-var_rotsys_perm(x0,x1,a,i,b,mir),+var_rotsys_perm_eq_orig(x0,x1,a,i,b,mir)])
                                constraints.append([-var_rotsys(a,i,b),+var_rotsys_perm(x0,x1,a,i,b,mir),+var_rotsys_perm_gt_orig(x0,x1,a,i,b,mir)])
                                constraints.append([+var_rotsys(a,i,b),-var_rotsys_perm(x0,x1,a,i,b,mir),+var_rotsys_perm_lt_orig(x0,x1,a,i,b,mir)])
                                constraints.append([+var_rotsys(a,i,b),+var_rotsys_perm(x0,x1,a,i,b,mir),+var_rotsys_perm_eq_orig(x0,x1,a,i,b,mir)])
                            else:
                                constraints.append([-var_rotsys_perm_lt_orig(x0,x1,prev_a,prev_i,prev_b,mir),+var_rotsys_perm_lt_orig(x0,x1,a,i,b,mir)])
                                constraints.append([-var_rotsys_perm_gt_orig(x0,x1,prev_a,prev_i,prev_b,mir),+var_rotsys_perm_gt_orig(x0,x1,a,i,b,mir)])
                                constraints.append([-var_rotsys_perm_eq_orig(x0,x1,prev_a,prev_i,prev_b,mir),-var_rotsys(a,i,b),-var_rotsys_perm(x0,x1,a,i,b,mir),+var_rotsys_perm_eq_orig(x0,x1,a,i,b,mir)])
                                constraints.append([-var_rotsys_perm_eq_orig(x0,x1,prev_a,prev_i,prev_b,mir),-var_rotsys(a,i,b),+var_rotsys_perm(x0,x1,a,i,b,mir),+var_rotsys_perm_gt_orig(x0,x1,a,i,b,mir)])
                                constraints.append([-var_rotsys_perm_eq_orig(x0,x1,prev_a,prev_i,prev_b,mir),+var_rotsys(a,i,b),-var_rotsys_perm(x0,x1,a,i,b,mir),+var_rotsys_perm_lt_orig(x0,x1,a,i,b,mir)])
                                constraints.append([-var_rotsys_perm_eq_orig(x0,x1,prev_a,prev_i,prev_b,mir),+var_rotsys(a,i,b),+var_rotsys_perm(x0,x1,a,i,b,mir),+var_rotsys_perm_eq_orig(x0,x1,a,i,b,mir)])

                        prev_a = a
                        prev_i = i
                        prev_b = b





def forbid_planar_subgraph(edges):
    return [[+var_ab_cross_cd(a,b,c,d) for (a,b),(c,d) in combinations(edges,2) if len({a,b,c,d}) == 4]]

def assert_planar_subgraph(edges):
    return [[-var_ab_cross_cd(a,b,c,d)] for (a,b),(c,d) in combinations(edges,2) if len({a,b,c,d}) == 4]


if args.forbidHC:
    print ("(HC) there is no plane Hamiltonian cycle",len(constraints))
    for perm in permutations(N):
        if perm[0] == 0 and perm[1] < perm[-1]: # wlog
            constraints += forbid_planar_subgraph([(perm[i-1],perm[i]) for i in N])


if args.forbidHCplus:
    print ("(HC+) there is no plane Hamiltonian subgraph on 2n-3 edges",len(constraints))
    for perm in permutations(N):
        if perm[0] == 0 and perm[1] < perm[-1]: # wlog
            HC_edges = [(perm[i-1],perm[i]) for i in N]
            remaining_edges = [(a,b) for (a,b) in combinations(N,2) if (a,b) not in HC_edges and (b,a) not in HC_edges]
            for E in combinations(remaining_edges,n-3):
                constraints += forbid_planar_subgraph(HC_edges+list(E))


if args.forbidHCplusplus:
    assert(not args.natural) 
    print ("(HC++) Assume C is a Hamiltonian cycle through 1,2,3,...n ...",len(constraints))
    perm = N
    HC_edges = [(perm[i-1],perm[i]) for i in N]
    constraints += assert_planar_subgraph(HC_edges)

    print ("(HC++) ... which cannot be extended to a plane Hamiltonian subgraph on 2n-3 edges",len(constraints))
    remaining_edges = [(a,b) for (a,b) in combinations(N,2) if (a,b) not in HC_edges and (b,a) not in HC_edges]
    for E in combinations(remaining_edges,n-3):
        constraints += forbid_planar_subgraph(HC_edges+list(E))


if args.forbidHPedge:
    assert(not args.lexmin)
    print ("(HPe) for one edge there is no plane Hamiltonian path; wlog edge 01",len(constraints))
    for perm in permutations(N):
        if perm.index(1) == perm.index(0)+1:
            constraints += forbid_planar_subgraph([(perm[i-1],perm[i]) for i in range(1,n)])



if args.HoffmannTothplus:
    k = args.HoffmannTothplus
    assert(n >= 2*k) 
    print ("(HT+) test strengthened HoffmannToth property: for every plane matching of size",k,"there is a plane HC not crossing any of the edges")

    matching_edges = [(2*i,2*i+1) for i in range(k)]

    constraints += assert_planar_subgraph(matching_edges)

    for perm in permutations(N):
        if perm[0] == 0: # wlog
            HC_edges = [(perm[i-1],perm[i]) for i in N]
            constraints += forbid_planar_subgraph(HC_edges + matching_edges)
    
    if k > 1: assert(not args.natural) 
    # the following assumptions are w.l.o.g. to break symmetries;
    # those assumptions are a generalization of the assumptions for natural labelings (for k=1 they coincide)
    remaining_vertices = range(2*k,n)
    for a,b in matching_edges[1:]:
        constraints.append([+var_a_sees_bcd(0,1,a,b)])
    for (a,b),(c,d) in combinations(matching_edges[1:],2):
        constraints.append([+var_a_sees_bcd(0,1,a,c)])
    for a,c in combinations(remaining_vertices,2):
        constraints.append([+var_a_sees_bcd(0,1,a,c)])



if emptytriangles:
    print ("(et) assert triangle containment and empty triangles",len(constraints))
    for a,b,c,d in permutations(N,4):
        for t in containment_types:
            constraints.append([-var_abc_contains_d_type(a,b,c,d,t)]+[+t[0]*var_a_sees_bcd(a,b,d,c)])
            constraints.append([-var_abc_contains_d_type(a,b,c,d,t)]+[+t[1]*var_a_sees_bcd(b,c,d,a)])
            constraints.append([-var_abc_contains_d_type(a,b,c,d,t)]+[+t[2]*var_a_sees_bcd(c,a,d,b)])
            constraints.append([+var_abc_contains_d_type(a,b,c,d,t),
                -t[0]*var_a_sees_bcd(a,b,d,c),
                -t[1]*var_a_sees_bcd(b,c,d,a),
                -t[2]*var_a_sees_bcd(c,a,d,b)])


    for a,b,c,d in permutations(N,4):
        constraints.append([-var_abc_contains_d(a,b,c,d)]+[+var_abc_contains_d_type(a,b,c,d,t) for t in containment_types])
        for t in containment_types:
            constraints.append([+var_abc_contains_d(a,b,c,d),-var_abc_contains_d_type(a,b,c,d,t)])

    for a,b,c in permutations(N,3):
        for d in set(N)-{a,b,c}:
            constraints.append([-var_abc_empty(a,b,c),-var_abc_contains_d(a,b,c,d)])
        constraints.append([+var_abc_empty(a,b,c)]+[+var_abc_contains_d(a,b,c,d) for d in set(N)-{a,b,c}])


if emptytrianglessub:
    print ("(etsub) assert empty triangles in subconfigurations",len(constraints))
    for k in range(3,n+1):
        for a,b,c in permutations(range(k),3):
            for d in set(range(k))-{a,b,c}:
                constraints.append([-var_abc_empty_sub(a,b,c,k),-var_abc_contains_d(a,b,c,d)])
            constraints.append([+var_abc_empty_sub(a,b,c,k)]+[+var_abc_contains_d(a,b,c,d) for d in set(range(k))-{a,b,c}])



if args.etlow != None or args.etupp != None:
    emptytriangles_vars = [var_abc_empty(a,b,c) for (a,b,c) in permutations(N,3) if a == min(a,b,c)]

if args.etlow != None:
    print ("(etlow) minimum number of empty triangles:",args.etlow,len(constraints))
    constraints += list(CardEnc.atleast(lits=emptytriangles_vars, bound=args.etlow, encoding=EncType.totalizer, vpool=vpool)) 

if args.etupp != None:
    print ("(etupp) maximum number of empty triangles:",args.etupp,len(constraints))
    constraints += list(CardEnc.atmost(lits=emptytriangles_vars, bound=args.etupp, encoding=EncType.totalizer, vpool=vpool))

if args.kholes:
    k = args.kholes
    assert(emptytriangles)
    print ("(kholes) forbid convex k-holes of size",k,len(constraints))
    for I in permutations(N,k):
        if I[0] == min(I):
            constraints.append([-var_abc_empty(a,b,c) for (a,b,c) in combinations(I,3)])


if args.kholessub:
    k = args.kholessub
    assert(emptytriangles)
    assert(emptytrianglessub)
    print ("(kholessub) forbid convex "+str(k)+"-holes in subconfigurations",len(constraints))
    for m in range(3,n+1):
        for I in permutations(range(m),k):
            if I[0] == min(I):
                constraints.append([-var_abc_empty_sub(a,b,c,m) for (a,b,c) in combinations(I,3)])



if args.testNoCrossingInRLemmaCase:
    assert(args.convex)
    assert(args.testNoCrossingInRLemmaCase in [1,2,3,4])    
    
    if args.testNoCrossingInRLemmaCase == 1: 
        assert(args.n == 10)
        constraints.append([+var_ab_cross_cd(0,1,8,9)])
        constraints.append([+var_ab_cross_cd(0,7,2,6)])
        constraints.append([+var_ab_cross_cd(0,3,4,5)])
        
    if args.testNoCrossingInRLemmaCase == 2: 
        assert(args.n == 9)
        constraints.append([+var_ab_cross_cd(0,1,7,8)])
        constraints.append([+var_ab_cross_cd(0,6,2,5)])
        constraints.append([+var_ab_cross_cd(0,3,4,5)])

    if args.testNoCrossingInRLemmaCase == 3: 
        assert(args.n == 10)
        constraints.append([+var_ab_cross_cd(0,1,8,9)])
        constraints.append([+var_ab_cross_cd(0,6,2,7)])
        constraints.append([+var_ab_cross_cd(0,3,4,5)])
        
    if args.testNoCrossingInRLemmaCase == 4: 
        assert(args.n == 9)
        constraints.append([+var_ab_cross_cd(0,1,7,8)])
        constraints.append([+var_ab_cross_cd(0,6,2,7)])
        constraints.append([+var_ab_cross_cd(0,3,4,5)])


if args.testNestedLemmaPart2Case:
    assert(args.convex)
    assert(args.testNestedLemmaPart2Case in [1,2,3])    
    if args.testNestedLemmaPart2Case == 4: 
        assert(args.n == 7)
        # If  $v_i+1$ is in the non-convex side
        constraints.append([+var_ab_cross_cd(0,1,5,6)])
        constraints.append([+var_ab_cross_cd(0,3,5,6)])
        constraints.append([+var_ab_cross_cd(0,2,3,4)])

    if args.testNestedLemmaPart2Case == 5: 
        assert(args.n == 7)
        # If $v_i$ is in the non-convex-side
        constraints.append([+var_ab_cross_cd(0,1,5,6)])
        constraints.append([+var_ab_cross_cd(0,4,5,6)])
        constraints.append([+var_ab_cross_cd(0,2,3,4)])
        
    if args.testNestedLemmaPart2Case == 6:
        assert(args.n == 6)
        # If $v_i+1 = v_j$ and $v_i$ is in the non convex side of $T_{b_j}$
        constraints.append([+var_ab_cross_cd(0,1,4,5)])
        constraints.append([+var_ab_cross_cd(0,3,4,5)])
        constraints.append([+var_ab_cross_cd(0,2,3,4)])
        
    if args.testNestedLemmaPart2Case == 1: 
        assert(args.n == 7)
        # If  $v_i+1$ is in the non-convex side
        constraints.append([+var_ab_cross_cd(0,1,5,6)])
        constraints.append([+var_ab_cross_cd(0,3,4,5)])
        constraints.append([+var_ab_cross_cd(0,2,3,4)])

    if args.testNestedLemmaPart2Case == 2: 
        assert(args.n == 7)
        # If $v_i$ is in the non-convex-side
        constraints.append([+var_ab_cross_cd(0,1,5,6)])
        constraints.append([+var_ab_cross_cd(0,3,4,6)])
        constraints.append([+var_ab_cross_cd(0,2,3,4)])
        
    if args.testNestedLemmaPart2Case == 3:
        assert(args.n == 6)
        # If $v_i+1 = v_j$ and $v_i$ is in the non convex side of $T_{b_j}$
        constraints.append([+var_ab_cross_cd(0,1,4,5)])
        constraints.append([+var_ab_cross_cd(0,3,4,5)])
        constraints.append([+var_ab_cross_cd(0,2,3,4)])


if args.crossingfamily:
    k = args.crossingfamily
    print ("(crf) forbid crossing family of size",k,len(constraints))
    for I in combinations(N,2*k):
        for A in combinations(I,k):
            for B in permutations(set(I)-set(A),k):
                edges = [ (A[i],B[i]) for i in range(k) if A[i]<B[i] ] 
                if len(edges) == k: # wlog
                    constraints.append([-var_ab_cross_cd(u,v,w,x) for (u,v),(w,x) in combinations(edges,2)])


if args.alledgescrossed:
    print ("(*) assert that all edges are crossed",len(constraints))
    for a,b in combinations(N,2):
        constraints.append([var_ab_cross_cd(a,b,c,d) for c,d in combinations(set(N)-{a,b},2)])


if args.alledgescrossedsub:
    k0 = 11 if args.convex else 8
    print ("(*) assert that all edges are crossed in subconfigurations of size >=",k0,len(constraints))
    for k in range(k0,n+1):
        for a,b in combinations(range(k),2):
            constraints.append([var_ab_cross_cd(a,b,c,d) for c,d in combinations(set(range(k))-{a,b},2)])


if args.forbidC5: 
    print ("(C5) forbid C5")
    constraints += forbid_subrs([[1,2,3,4],[0,2,3,4],[0,1,3,4],[0,1,2,4],[0,1,2,3]])

if args.forbidC6: 
    print ("(C6) forbid C6")
    constraints += forbid_subrs([[1,2,3,4,5],[0,2,3,4,5],[0,1,3,4,5],[0,1,2,4,5],[0,1,2,3,5],[0,1,2,3,4]])

if args.forbidT5: 
    print ("(T5) forbid T5")
    constraints += forbid_subrs([[4,3,2,1],[0,4,3,2],[0,1,4,3],[0,1,2,4],[0,1,2,3]])

if args.forbidT6: 
    print ("(T6) forbid T6")
    constraints += forbid_subrs([[5,4,3,2,1],[0,5,4,3,2],[0,1,5,4,3],[0,1,2,5,4],[0,1,2,3,5],[0,1,2,3,4]])


if args.test6gon5hole:
    assert(args.n >= 6)
    assert(args.convex)
    assert(not args.natural) 
    #assert(args.kholes == 5)
    print("(test6gon5hole) assume there is a 6-gon but no 5-hole")
    

    G = range(6)
    # G={0,1,2,3,4,5} forms C6
    for a,b,c,d in combinations(G,4):
        constraints.append([+var_ab_cross_cd(a,c,b,d)])

    # w.l.o.g.: cyclic order of inner points
    for a,b in combinations(sorted(set(N)-set(G)),2):
        constraints.append([+var_a_sees_bcd(0,1,a,b)]) 

    # w.l.o.g.: i-1 and i+1 are consecutive in cyclic order around i (for i mod 6)
    for v in G:
        u = (v-1)%6
        w = (v+1)%6
        for x in set(N)-{u,v,w}:
            constraints.append([+var_a_sees_bcd(v,u,x,w)])




print ("Total number of constraints:",len(constraints))
time_before_solving = datetime.datetime.now()
print("creating time:",time_before_solving-time_start)
print ()


if args.cnf2file:
    print ("write cnf instance to file:",args.cnf2file)
    from pysat.formula import CNF
    cnf = CNF()
    for c in constraints: cnf.append(c)
    cnf.to_file(args.cnf2file)
    exit()


DEBUG = 0

outfile = None
if args.rs2file:
    print ("write rotation systems to file:",args.rs2file)
    outfile = open(args.rs2file,"w")

ct = 0
found = []
fingerprints = []

if True:
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


    print (datetime.datetime.now(),"start solving")
    for sol in solution_iterator:
        ct += 1
        sol = set(sol) # it's faster to lookup values in set than in list

        rs = []
        for a in N:
            order_a = []
            for i in N_without_last:
                for b in N_without[a]:
                    if var_rotsys(a,i,b) in sol:
                        order_a.append(b)

            rs.append(order_a)
        
        assert(rs not in found)        
        found.append(rs)
        if outfile: outfile.write(str(rs)+"\n")
        print (datetime.datetime.now(),"solution #",ct,"\t",rs)
        

        if args.checkpairsofcrossings:
            assert(args.valid4tuples)
            N2 = combinations(N,2)
            cross_pairs = [(e,f) for e,f in combinations(N2,2) if not set(e)&set(f) and var_ab_cross_cd(*e,*f) in sol]
            if rs[0][1] < rs[0][-1]: # wlog, otherwise reflection
                assert(cross_pairs not in fingerprints) # make sure there is no duplicate
                fingerprints.append(cross_pairs)
            print("crossing edge pairs are fine (not found before):",cross_pairs)


        if args.testNestedLemmaPart1: # this proves NestedLemma !!!
            assert(args.convex)
            assert(not args.hconvex)
            assert(args.n in [5,6,7])

            i = max(N) # wlog i is rightmost; thus we have either wi < wj < j < i or j <  wj < wi < i.
            i_plus_1 = 1+(i%(n-1))

            for j in set(N)-{0,i}:
                #if j > i: continue
                j_plus_1 = 1+(j%(n-1))
                for wi in set(N)-{0,i,i_plus_1}:
                    for wj in set(N)-{0,j,j_plus_1}:
                        if wi < wj and wj < j and j < i: continue # nested 
                        if j < wj and wj < wi and wi < i: continue # nested after cyclically relabeling
                        if var_ab_cross_cd(0,wi,i,i_plus_1) in sol and var_ab_cross_cd(0,wj,j,j_plus_1) in sol:
                            print("found two badedges of unknown type: ",i,i_plus_1,":",wi,"and",j,j_plus_1,":",wj)
                            exit("ERROR")
            
            print("test of NestedLemma: fine")


        if args.testHConvexBadEdgeLemma: # this proves the HConvexBadEdgeLemma !!!
            assert(args.hconvex)
            assert(args.n in [5,6,7])
            assert(args.all)

            i = max(N) # wlog i is rightmost; thus we have either wi < wj < j < i or j <  wj < wi < i.
            i_plus_1 = 1+(i%(n-1))

            for j in set(N)-{0,i}:
                #if j > i: continue
                j_plus_1 = 1+(j%(n-1))
                for wi in set(N)-{0,i,i_plus_1}:
                    for wj in set(N)-{0,j,j_plus_1}:
                        if var_ab_cross_cd(0,wi,i,i_plus_1) in sol and var_ab_cross_cd(0,wj,j,j_plus_1) in sol:
                            exit("ERROR")
            
            print("test of HConvexBadEdgeLemma: fine")

        if not args.all: break





time_end = datetime.datetime.now()

if ct == 0:
    print (time_end,"no solution!?")
else:
    if args.all:
        print (time_end,"total count:",len(found))
    else:
        print("use parameter -a/--all to enumerate all solutions")


print("solving time :",time_end-time_before_solving)
print("total time   :",time_end-time_start)

