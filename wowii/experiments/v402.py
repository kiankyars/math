import networkx as nx, itertools, sys
E=[tuple(map(int,e.split('-'))) for e in sys.argv[2:]]
G=nx.Graph(E); n=G.number_of_nodes(); V=list(G)
def is2dom(S): return all(v in S or sum(1 for u in G[v] if u in S)>=2 for v in G)
def isdom(S,H): return all(v in S or any(u in S for u in H[v]) for v in H)
def istds(S): return all(any(u in S for u in G[v]) for v in G)
def minsize(pred, nodes):
    for k in range(0,len(nodes)+1):
        for S in itertools.combinations(nodes,k):
            if pred(set(S)): return k,S
deg=dict(G.degree()); d=min(deg.values()); D=max(deg.values())
Ad=[v for v in V if deg[v]==d]; AD=[v for v in V if deg[v]==D]
print('n',n,'m',G.number_of_edges(),'conn',nx.is_connected(G),'delta',d,'Delta',D)
if sys.argv[1]=='402':
    g2=minsize(is2dom,V); gt=minsize(istds,V)
    iso=sum(1 for v in Ad if not any(u in Ad for u in G[v])); c1=sum(1 for v in V if sum(1 for u in G[v] if u in AD)==1)
    print('gamma2',g2,'gammat',gt,'iso',iso,'c1',c1,'bound',2*(iso+c1+gt[0]))
else:
    # i(G): min independent dominating
    def isid(S): return isdom(S,G) and not any(G.has_edge(a,b) for a,b in itertools.combinations(S,2))
    i=minsize(isid,V)
    H=G.subgraph(AD); a=max(len(c) for c in nx.find_cliques(nx.complement(H))) if AD else 0
    R=G.subgraph([v for v in V if v not in AD]); gR=minsize(lambda S: isdom(S,R), list(R))
    print('i',i,'alpha(G[M])',a,'gamma(G[V-M])',gR,'bound',a+gR[0]**2, 'M',AD)
