import networkx as nx, itertools, sys
def hyp(G):
  D=dict(nx.all_pairs_shortest_path_length(G)); H=nx.complement(G)
  if H.number_of_edges()==0: return False
  mx=max(len(set(H[u])|set(H[v])) for u,v in H.edges())
  best=max(sum(1 for w in G if D[v][w]%2==1)-sum(1 for a,b in G.edges() if D[v][a]==D[v][b] and D[v][a]%2==1) for v in G)
  return mx<=1+best
def mtds(G):
  n=G.number_of_nodes(); sizes=set()
  def tds(S): return all(any(u in S for u in G[v]) for v in G)
  for r in range(2,n+1):
    for S in itertools.combinations(G,r):
      s=set(S)
      if tds(s) and all(not tds(s-{x}) for x in s): sizes.add(r)
  return sizes
for k in range(4,10):
  cnt=0; props=set()
  for line in open(f'g{k}.g6'):
    G=nx.from_graph6_bytes(line.strip().encode())
    if not hyp(G): continue
    cnt+=1
    univ=any(G.degree(v)==k-1 for v in G)
    edgeTDS=all(all(w in (u,v) or G.has_edge(w,u) or G.has_edge(w,v) for w in G) for u,v in G.edges())
    props.add((nx.diameter(G), univ, edgeTDS, tuple(sorted(mtds(G))) if k<=8 else None, nx.is_bipartite(G)))
  print(k,cnt,sorted(props, key=str))
