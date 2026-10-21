import networkx as nx, itertools, numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
def gammat(G):
    n=G.number_of_nodes(); nodes=list(G); idx={v:i for i,v in enumerate(nodes)}
    A=np.zeros((n,n))
    for v in nodes:
        for u in G[v]: A[idx[v],idx[u]]=1
    r=milp(c=np.ones(n),constraints=LinearConstraint(A,lb=np.ones(n),ub=np.inf),integrality=np.ones(n),bounds=Bounds(0,1))
    return round(r.fun)
def build(L,k0,k1,extra):
    G=nx.Graph(); nx.add_path(G,[f'u{i}' for i in range(L+1)])
    for j in range(k0): G.add_edge('u0',f'a{j}')
    for j in range(k1): G.add_edge(f'u{L}',f'b{j}')
    for (i,j) in extra:  # path u_i - x - y - u_j
        G.add_edge(f'u{i}',f'x{i}{j}'); G.add_edge(f'x{i}{j}',f'y{i}{j}'); G.add_edge(f'y{i}{j}',f'u{j}')
    return G
def report(G):
    n=G.number_of_nodes(); D=dict(nx.all_pairs_shortest_path_length(G))
    dl=min(d for _,d in G.degree()); A=[v for v in G if G.degree(v)==dl]
    s=sum(D[a][v] for a in A for v in G)
    return dict(n=n,girth=nx.girth(G),gt=gammat(G),incl0=s/(len(A)*n),excl0=s/(len(A)*(n-1)),A=len(A),sum=s)
G=build(5,7,7,[(1,4)]); print(report(G))
G=build(5,6,7,[(1,4)]); print(report(G))
G=build(5,6,6,[(1,4)]); print(report(G))
G=build(9,13,13,[(1,4)]); print(report(G))
