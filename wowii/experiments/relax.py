# Relaxation cost for incidence cubic graph of a (3,B2) formula: i(G) - #vars = min |W|-|K|.
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from pysat.solvers import Cadical153
import itertools, random, collections
def is_unsat(clauses):
    with Cadical153(bootstrap_with=clauses) as s: return not s.solve()
def check_B2(clauses,nv):
    occ=collections.Counter(l for c in clauses for l in c)
    return all(len(set(abs(l) for l in c))==3 for c in clauses) and all(occ[x]==2 and occ[-x]==2 for x in range(1,nv+1))
def graph(clauses,nv):
    E=[(2*(i-1),2*(i-1)+1) for i in range(1,nv+1)]
    for j,c in enumerate(clauses):
        for l in c: E.append((2*(abs(l)-1)+(0 if l>0 else 1), 2*nv+j))
    return 2*nv+len(clauses),E
def ids_ilp(n,E):
    N=[[v] for v in range(n)]
    for a,b in E: N[a].append(b); N[b].append(a)
    rows=[];lb=[];ub=[]
    for v in range(n):
        r=np.zeros(n); r[N[v]]=1; rows.append(r); lb.append(1); ub.append(np.inf)
    for a,b in E:
        r=np.zeros(n); r[a]=r[b]=1; rows.append(r); lb.append(0); ub.append(1)
    res=milp(np.ones(n),constraints=LinearConstraint(np.array(rows),lb,ub),integrality=np.ones(n),bounds=Bounds(0,1))
    return round(res.fun),[v for v in range(n) if res.x[v]>0.5]
def cost(clauses,nv):
    n,E=graph(clauses,nv); i,S=ids_ilp(n,E); return i-nv,S
if __name__=="__main__":
    zps=[[1,4,-6],[2,-4,5],[2,-5,6],[4,5,6],[-4,-5,-6],[1,7,-9],[-2,-7,8],[-2,-8,9],[7,8,9],[-7,-8,-9],
     [-1,10,-12],[3,-10,11],[3,-11,12],[10,11,12],[-10,-11,-12],[-1,13,-15],[-3,-13,14],[-3,-14,15],[13,14,15],[-13,-14,-15]]
    print(check_B2(zps,15), is_unsat(zps), cost(zps,15))
