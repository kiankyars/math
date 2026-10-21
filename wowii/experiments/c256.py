import networkx as nx, itertools
def build(t,p):
    G=nx.Graph(); c=0; G.add_node(c); idx=1; L=[]
    for i in range(t):
        l=idx; idx+=1; L.append(l); G.add_edge(c,l)
        xs=list(range(idx,idx+p)); idx+=p
        for x in xs: G.add_edge(l,x)
        for j in range(0,p,2): G.add_edge(xs[j],xs[j+1])
    return G
def gamma_t(G):
    V=list(G); n=len(V)
    for r in range(2,n+1):
        for S in itertools.combinations(V,r):
            s=set(S)
            if all(any(w in s for w in G[v]) for v in V): return r
def check(G):
    deg=dict(G.degree()); d=min(deg.values()); A={v for v in G if deg[v]==d}
    NA=set().union(*[set(G[a]) for a in A])
    mNe=max(len(set(G[u])|set(G[v])) for u,v in G.edges())
    gt=gamma_t(G)
    D=dict(nx.all_pairs_shortest_path_length(G)); ecc={v:max(D[v].values()) for v in G}; rad=min(ecc.values()); C=[v for v in G if ecc[v]==rad]
    return gt, mNe, len(NA), 2*len(NA)/mNe, len(C), 2*len(C)/mNe
for t,p in [(2,4),(2,6),(3,6),(2,8)]:
    G=build(t,p); r=check(G)
    print(t,p,'n=',G.number_of_nodes(),'gt,maxNe,|N(A)|,bound256,|C|,bound255 =',r, 'FAIL256' if r[0]<r[3] else '', nx.to_graph6_bytes(G,header=False).decode().strip())
