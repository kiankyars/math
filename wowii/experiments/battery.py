import networkx as nx, numpy as np, itertools, sys
from scipy.optimize import milp, LinearConstraint, Bounds
def i_ilp(G):
    nodes=list(G.nodes()); idx={v:k for k,v in enumerate(nodes)}; n=len(nodes); rows=[];lb=[];ub=[]
    for v in nodes:
        r=np.zeros(n); r[idx[v]]=1
        for u in G[v]: r[idx[u]]=1
        rows.append(r); lb.append(1); ub.append(np.inf)
    for a,b in G.edges():
        r=np.zeros(n); r[idx[a]]=r[idx[b]]=1; rows.append(r); lb.append(0); ub.append(1)
    res=milp(np.ones(n),constraints=LinearConstraint(np.array(rows),lb,ub),integrality=np.ones(n),bounds=Bounds(0,1),options={"time_limit":60})
    return round(res.fun)
def ge_ilp(G):
    E=list(G.edges()); m=len(E); inc={v:[] for v in G}
    for k,(a,b) in enumerate(E): inc[a].append(k); inc[b].append(k)
    rows=[];lb=[];ub=[]
    for v in G:
        r=np.zeros(m); r[inc[v]]=1; rows.append(r); lb.append(0); ub.append(1)
    for k,(a,b) in enumerate(E):
        r=np.zeros(m); r[inc[a]]=1; r[inc[b]]=1; rows.append(r); lb.append(1); ub.append(np.inf)
    res=milp(np.ones(m),constraints=LinearConstraint(np.array(rows),lb,ub),integrality=np.ones(m),bounds=Bounds(0,1),options={"time_limit":60})
    return round(res.fun)
def test(name,G):
    if not nx.is_connected(G): return
    degs=set(d for _,d in G.degree());
    if len(degs)!=1: return
    i=i_ilp(G); g=ge_ilp(G)
    flag="  <<<<< COUNTEREXAMPLE" if i>g else (" tight" if i==g else "")
    print(f"{name:30s} n={G.number_of_nodes():3d} r={degs.pop()} i={i} ge={g}{flag}",flush=True)
gs=[]
for n in range(5,26):
    for k in range(1,(n+1)//2):
        if 2*k!=n: gs.append((f"GP({n},{k})",nx.generalized_petersen_graph(n,k) if hasattr(nx,'generalized_petersen_graph') else None))
for n in range(3,21): gs.append((f"prism{n}",nx.circular_ladder_graph(n))); gs.append((f"mobius{n}",nx.circulant_graph(2*n,[1,n])))
for n in range(5,17):
    for a,b in itertools.combinations(range(1,n//2+1),2):
        gs.append((f"circ{n}({a},{b})",nx.circulant_graph(n,[a,b])))
for a in range(3,8):
    for b in range(3,8):
        if a<=b: gs.append((f"torus{a}x{b}",nx.grid_2d_graph(a,b,periodic=True)))
named=[("tutte_coxeter",nx.LCF_graph(30,[-13,-9,7,-7,9,13],5)),("dodeca",nx.dodecahedral_graph()),("desargues",nx.desargues_graph()),("heawood",nx.heawood_graph()),("pappus",nx.pappus_graph()),("mcgee",nx.LCF_graph(24,[12,7,-7],8)),("nauru",nx.LCF_graph(24,[5,-9,7,-7,9,-5],4)),("frucht",nx.frucht_graph()),("truncated_tetra",nx.truncated_tetrahedron_graph()),("truncated_cube",nx.truncated_cube_graph()),("cubical",nx.cubical_graph()),("moebius_kantor",nx.moebius_kantor_graph()),("petersen",nx.petersen_graph()),("icosa",nx.icosahedral_graph()),("octa",nx.octahedral_graph()),("hoffman_singleton",nx.hoffman_singleton_graph()),("clebsch?K",nx.complement(nx.petersen_graph()))]
for name,G in named: gs.append((name,G))
# line graphs of cubic graphs are 4-regular
for name,G in named[:10]: gs.append(("L("+name+")",nx.line_graph(G)))
for name,G in gs:
    if G is not None: test(name,G)
