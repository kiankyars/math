import networkx as nx, itertools, sys
def alpha(G, X):
    X=list(X); best=0
    for r in range(len(X),0,-1):
        for S in itertools.combinations(X,r):
            if all(not G.has_edge(a,b) for a,b in itertools.combinations(S,2)): return r
    return 0
def alpha2(G):
    V=list(G)
    for r in range(len(V),0,-1):
        for S in itertools.combinations(V,r):
            s=set(S)
            if all(sum(1 for w in G[v] if w in s)<=1 for v in S): return r
    return 0
def annih(G, X):
    H=G.subgraph(X); m=H.number_of_edges(); d=sorted(dict(H.degree()).values()); k=0; t=0
    for x in d:
        if t+x<=m: t+=x; k+=1
        else: break
    return k
bad=0; tight=0; tot=0
for n in range(4,8):
    for line in open(f'g{n}.g6')  # connected graphs from nauty-geng -c:
        G=nx.from_graph6_bytes(line.strip().encode())
        deg=dict(G.degree()); dm=min(deg.values()); A=[v for v in G if deg[v]==dm]; R=[v for v in G if deg[v]!=dm]
        eA=G.subgraph(A).number_of_edges()
        a2=alpha2(G); mid=alpha(G,G)+alpha(G,R)+eA; rhs=annih(G,G)+annih(G,R)+eA
        tot+=1
        if not (a2<=mid<=rhs): bad+=1; print('BAD',line.strip(),a2,mid,rhs)
        if a2==rhs: tight+=1
print('total',tot,'bad',bad,'tight',tight)
