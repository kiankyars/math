import networkx as nx, itertools, sys
def check(es):
  G=nx.Graph([tuple(map(int,e.split('-'))) for e in es.split()]); n=G.number_of_nodes(); assert nx.is_connected(G)
  def g2():
    for r in range(1,n+1):
      for S in itertools.combinations(G,r):
        s=set(S)
        if all(v in s or sum(1 for u in G[v] if u in s)>=2 for v in G): return r,S
  H=nx.complement(G); cd=sorted((d for _,d in H.degree()),reverse=True)
  WP=max(min(cd[i]+1,i+1) for i in range(n))
  A3=[v for v in G if G.degree(v)>=3]
  a3=max(len(c) for c in nx.find_cliques(nx.complement(G.subgraph(A3))))
  r,S=g2()
  print("n",n,"m",G.number_of_edges(),"g2",r,S,"WP(Gbar)",WP,"compl degs",cd,"alpha(A3)",a3,"bound",WP+3//a3,"CE" if r>WP+3//a3 else "", "degs",sorted(d for _,d in G.degree()))
for line in sys.stdin: check(line.split('edges:')[1])
