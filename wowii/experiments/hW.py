import networkx as nx, itertools, sys
def residue(G):
  d=sorted((x for _,x in G.degree()),reverse=True)
  while d and d[0]>0:
    x=d.pop(0)
    for i in range(min(x,len(d))): d[i]-=1
    d.sort(reverse=True)
  return len(d)
def gamma(G):
  n=G.number_of_nodes()
  for r in range(1,n+1):
    for S in itertools.combinations(G,r):
      s=set(S)
      if all(v in s or any(u in s for u in G[v]) for v in G): return r
def hyp(G,which):
  H=nx.complement(G); n=G.number_of_nodes()
  if which in ('324','325'):
    if H.number_of_edges()==0: return None
    vals=[len(set(H[u])|set(H[v])) for u,v in H.edges()]
    if which=='324': return max(vals)<=1+residue(G)
    S=[v for v in G if G.degree(v)==2]; NS=set(S)|{u for v in S for u in G[v]}
    c=nx.number_connected_components(G.subgraph(NS)) if NS else 0
    return min(vals)<=1+c
  if which=='319':
    D=dict(nx.all_pairs_shortest_path_length(G))
    de=max(sum(1 for w in G if D[v][w]%2==0) for v in G)
    return de==gamma(G)
def mtds(G):
  n=G.number_of_nodes(); sizes=set()
  def tds(S): return all(any(u in S for u in G[v]) for v in G)
  for r in range(2,n+1):
    for S in itertools.combinations(G,r):
      s=set(S)
      if tds(s) and all(not tds(s-{x}) for x in s): sizes.add(r)
  return sizes
which=sys.argv[1]
for k in range(4,9):
  cnt=0; props={}
  for line in open(f'g{k}.g6'):
    G=nx.from_graph6_bytes(line.strip().encode())
    if not hyp(G,which): continue
    cnt+=1
    key=(nx.diameter(G), tuple(sorted(mtds(G))), nx.is_bipartite(G))
    props[key]=props.get(key,0)+1
  print(which,k,cnt,props)
