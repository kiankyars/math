import networkx as nx, itertools, sys
E=[tuple(map(int,e.split('-'))) for e in sys.argv[1:]]
G=nx.Graph(E); n=G.number_of_nodes(); V=list(G)
def isdom(S,H): return all(v in S or any(u in S for u in H[v]) for v in H)
def minsize(pred, nodes):
    for k in range(0,len(nodes)+1):
        for S in itertools.combinations(nodes,k):
            if pred(set(S)): return k,S
i=minsize(lambda S: isdom(S,G) and not any(G.has_edge(a,b) for a,b in itertools.combinations(S,2)), V)
tri={v:sum(1 for a,b in itertools.combinations(G[v],2) if G.has_edge(a,b)) for v in V}; tm=min(tri.values()); Tm=[v for v in V if tri[v]==tm]
k4={v:sum(1 for a,b,c in itertools.combinations(sorted(G[v]),3) if G.has_edge(a,b) and G.has_edge(a,c) and G.has_edge(b,c)) for v in V}
P=[v for v in V if G.degree(v)==1]; NP=set(u for p in P for u in G[p]); R=G.subgraph([v for v in V if v not in NP])
g=minsize(lambda S: isdom(S,R), list(R))
print('n',n,'conn',nx.is_connected(G),'i',i,'Tmin',Tm,'tri',tri,'sumK4',sum(k4.values()),'P',P,'gammaR',g,'bound',len(Tm)+sum(k4.values())+g[0])
