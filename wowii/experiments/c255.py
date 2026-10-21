import networkx as nx, itertools
def build(p, H1edges):
    G=nx.Graph(); c,l1,l2=0,1,2; a=[3+i for i in range(p)]; b=[3+p+i for i in range(p)]
    G.add_edges_from([(c,l1),(c,l2)])
    for i in range(p): G.add_edge(l1,a[i]); G.add_edge(l2,b[i]); G.add_edge(a[i],b[i])
    H1=set(map(frozenset,H1edges))
    for i,j in itertools.combinations(range(p),2):
        if frozenset((i,j)) in H1: G.add_edge(a[i],a[j])
        else: G.add_edge(b[i],b[j])
    return G
def gamma_t(G):
    V=list(G)
    for r in range(2,len(V)+1):
        for S in itertools.combinations(V,r):
            s=set(S)
            if all(any(w in s for w in G[v]) for v in V): return r
for p,H1 in [(4,[(0,1),(1,2),(2,3),(3,0)]),(4,[(0,1),(2,3)]),(4,[(0,1),(0,2),(0,3)]),(4,[]),(5,[(0,1),(1,2),(2,3),(3,4),(4,0)])]:
    G=build(p,H1)
    D=dict(nx.all_pairs_shortest_path_length(G)); ecc={v:max(D[v].values()) for v in G}; rad=min(ecc.values()); C=[v for v in G if ecc[v]==rad]
    mNe=max(len(set(G[u])|set(G[v])) for u,v in G.edges())
    gt=gamma_t(G)
    print(p,H1,'n=',G.number_of_nodes(),'diam',max(ecc.values()),'|C|',len(C),'maxNe',mNe,'gt',gt,'bound',round(2*len(C)/mNe,3),'FAIL' if gt<2*len(C)/mNe else '', nx.to_graph6_bytes(G,header=False).decode().strip())
