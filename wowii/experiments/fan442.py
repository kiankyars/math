import networkx as nx, itertools
def alpha2(G):
    nodes=list(G); n=len(nodes); best=0
    # dissociation number via simple branch and bound
    order=sorted(nodes,key=lambda v:-G.degree(v))
    def rec(i,S,deg):
        nonlocal best
        if len(S)+(n-i)<=best: return
        if i==n: best=max(best,len(S)); return
        v=order[i]
        nb=[u for u in G[v] if u in S]
        if len(nb)<=1 and all(deg[u]==0 for u in nb):
            S.add(v); 
            for u in nb: deg[u]+=1
            deg[v]=len(nb)
            rec(i+1,S,deg)
            S.remove(v)
            for u in nb: deg[u]-=1
            deg[v]=0
        rec(i+1,S,deg)
    rec(0,set(),{v:0 for v in nodes}); return best
def longest_induced_path(H):
    best=0; nodes=list(H)
    def ext(path,blocked):
        nonlocal best
        best=max(best,len(path))
        last=path[-1]
        for u in H[last]:
            if u in blocked: continue
            # u must not be adjacent to path vertices except last
            if any(H.has_edge(u,w) for w in path[:-1]): continue
            ext(path+[u],blocked|{u})
    for v in nodes: ext([v],{v})
    return best
for p in range(8,18):
    G=nx.Graph(); nx.add_path(G,range(p)); 
    for i in range(p): G.add_edge('x',i)
    n=G.number_of_nodes(); H3=[v for v in G if G.degree(v)>=3]; H=G.subgraph(H3)
    lp=longest_induced_path(H); a2=alpha2(G)
    import math
    print(p,'n=',n,'alpha2=',a2,'path(vertices)=',lp,'bound_v=',n-math.ceil(lp/2),'bound_len=',n-math.ceil((lp-1)/2))
