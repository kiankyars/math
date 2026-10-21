import networkx as nx, itertools, sys
E=[tuple(map(int,e.split('-'))) for e in sys.argv[1:]]
G=nx.Graph(E); n=G.number_of_nodes(); V=list(G)
def is2dom(S): return all(v in S or sum(1 for u in G[v] if u in S)>=2 for v in G)
def g2():
    for k in range(1,n+1):
        for S in itertools.combinations(V,k):
            if is2dom(set(S)): return k,S
deg=dict(G.degree()); D=max(deg.values())
P=[v for v in V if deg[v]==1]; NP=set(u for p in P for u in G[p]); NNP=set(w for u in NP for w in G[u])
H=G.subgraph([v for v in V if v not in NNP]); mu=len(nx.max_weight_matching(H,maxcardinality=True))
M=[v for v in V if deg[v]==D]; R=G.subgraph([v for v in V if v not in M]); a=max(len(c) for c in nx.find_cliques(nx.complement(R))) if len(R) else 0
k4={v:sum(1 for a_,b,c in itertools.combinations(sorted(G[v]),3) if G.has_edge(a_,b) and G.has_edge(a_,c) and G.has_edge(b,c)) for v in V}
km=max(k4.values()); M4=[v for v in V if k4[v]==km]
print('n',n,'m',G.number_of_edges(),'conn',nx.is_connected(G))
print('gamma2',g2()); print('P',P,'N(N(P))',sorted(NNP),'mu',mu,'M',M,'alpha(G-M)',a,'K4',k4,'M4',M4,'bound',mu+a+len(M4))
print('deg',deg)
