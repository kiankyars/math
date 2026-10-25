# Follows the proof's case analysis for every (G,S) and checks every claimed step numerically.
import sys, itertools, networkx as nx
from functools import lru_cache
def Lmax(G):
    # max leaves of a spanning tree (n>=2): n - gamma_c for n>=3, 2 for n==2
    n=G.number_of_nodes()
    if n==2: return 2
    V=list(G)
    for k in range(1,n+1):
        for D in itertools.combinations(V,k):
            Ds=set(D)
            if nx.is_connected(G.subgraph(D)) and all(v in Ds or any(u in Ds for u in G[v]) for v in V): return n-k
def alpha(G,W):
    H=G.subgraph(W)
    if H.number_of_nodes()==0: return 0
    return max(len(c) for c in nx.find_cliques(nx.complement(H)))
def d2(G,S):
    ds=sorted(G.degree(v) for v in S); return ds[1]
def rhs(G,S): W=[v for v in G if v not in S]; return len(S)-alpha(G,W)+d2(G,S)
cnt=0; stats={}
def st(k): stats[k]=stats.get(k,0)+1
def check(G,S):
    S=set(S); W=[v for v in G if v not in S]; L=Lmax(G); aW=alpha(G,W); d=d2(G,S)
    assert L>=len(S)-aW+d, ('V2 fails',)
    if d==1:
        c=nx.number_connected_components(G.subgraph(W)); assert L>=len(S)-c+1; st('D1'); return
    bridges=set(frozenset(e) for e in nx.bridges(G))
    low=[v for v in S if G.degree(v)<d]
    if not low:
        nb=[(s,w) for s in S for w in G[s] if frozenset((s,w)) not in bridges]
        if nb:
            s,w=nb[0]; H=G.copy(); H.remove_edge(s,w); assert nx.is_connected(H)
            assert d2(H,S)>=d and Lmax(G)>=Lmax(H) and alpha(H,W)==aW; st('I-R3'); return
        we=[(y,z) for y,z in G.edges() if y in W and z in W]
        if we:
            y,z=we[0]; assert not (set(G[y])&set(G[z])&S)
            H=nx.contracted_nodes(G,y,z,self_loops=False); W2=[v for v in H if v not in S]
            assert d2(H,S)==d and alpha(H,W2)<=aW and L>=Lmax(H); st('I-R2'); return
        assert nx.is_tree(G); assert len(S)-aW+d<=1; st('I-tree'); return
    u=low[0]; assert len(low)==1
    nbu=[w for w in G[u] if frozenset((u,w)) not in bridges]
    if nbu:
        H=G.copy(); H.remove_edge(u,nbu[0]); assert d2(H,S)>=d and L>=Lmax(H); st('II-R3'); return
    if G.degree(u)>=2:
        H=G.copy(); H.remove_node(u); comps=list(nx.connected_components(H)); t=len(comps); assert t==G.degree(u)
        tot=0; es=0
        for C in comps:
            P=G.subgraph(set(C)|{u}).copy(); Si=(S&set(C))|{u}; Wi=[v for v in C if v not in S]
            Lp=Lmax(P); tot+=Lp
            if len(Si)>=2: e=d2(P,Si); assert Lp>=len(Si)-alpha(P,Wi)+e
            else: e=1; assert Lp>=len(Si)-alpha(P,Wi)+e
            es+=e
        assert L>=tot-t and es>=d+1; st('II-R5'); return
    w1=next(iter(G[u]))
    if len(S)==2:
        s=[v for v in S if v!=u][0]
        if aW>=2: assert L>=max(dict(G.degree()).values())>=d; st('II-S2-a'); return
        assert L>=d+1; st('II-S2-b'); return
    # leaf block
    blocks=[set(b) for b in nx.biconnected_components(G)]; cuts=set(nx.articulation_points(G))
    leafb=[b for b in blocks if len(b&cuts)==1 and b!={u,w1}]
    assert leafb
    B=leafb[0]; c=next(iter(B&cuts))
    if len(B)==2:
        x=next(iter(B-{c})); assert x!=u and x not in S
        if c in S:
            H=G.copy(); H.remove_node(x); W2=[v for v in W if v!=x]; assert alpha(H,W2)==aW-1 and L>=Lmax(H); st('II-leaf2-R4'); return
        H=nx.contracted_nodes(G,c,x,self_loops=False); W2=[v for v in H if v not in S]
        assert d2(H,S)==d and alpha(H,W2)<=aW and L>=Lmax(H); st('II-leaf2-R2'); return
    x=[v for v in G[c] if v in B][0]; assert x not in cuts and x!=u
    H=G.copy(); H.remove_node(x); assert nx.is_connected(H) and c in set(nx.articulation_points(H))
    assert L>=Lmax(H)+1
    if x in S: assert d2(H,S-{x})>=d; st('II-R7')
    else: st('II-R8')
for line in sys.stdin:
    g6=line.strip()
    if not g6: continue
    G=nx.from_graph6_bytes(g6.encode()); n=G.number_of_nodes()
    if n<2: continue
    V=list(G)
    for k in range(2,n):
        for S in itertools.combinations(V,k):
            if any(G.has_edge(a,b) for a,b in itertools.combinations(S,2)): continue
            check(G,S); cnt+=1
print('instances',cnt,stats)
