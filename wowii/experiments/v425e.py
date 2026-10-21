import networkx as nx, itertools, sys
def check(es):
  G=nx.Graph([tuple(map(int,e.split('-'))) for e in es.split()]); n=G.number_of_nodes()
  assert nx.is_connected(G)
  def idom():
    for r in range(1,n+1):
      for S in itertools.combinations(G,r):
        if all(not G.has_edge(a,b) for a,b in itertools.combinations(S,2)) and all(v in S or any(G.has_edge(v,u) for u in S) for v in G): return r,S
  tri={v:sum(1 for a,b in itertools.combinations(G[v],2) if G.has_edge(a,b)) for v in G}
  tm=min(tri.values()); Tmin=[v for v in G if tri[v]==tm]
  N=lambda v:set(G[v])|{v}
  D=[v for v in G if any(u!=v and N(u)<=N(v) for u in G)]
  eD=G.subgraph(D).number_of_edges()
  i,S=idom()
  print("n=",n,"m=",G.number_of_edges(),"i=",i,S,"tri=",tri,"Tmin=",Tmin,"D=",D,"E(D)=",eD,"bound=",4*len(Tmin)+eD, "CE" if i>4*len(Tmin)+eD else "")
for line in sys.stdin:
  check(line.split('edges:')[1])
