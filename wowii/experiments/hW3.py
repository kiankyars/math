import networkx as nx, sys, itertools
exec(open('hW.py').read().split('which=sys.argv[1]')[0])
from collections import Counter
stats=Counter()
for k in range(5,10):
  for line in open(f'g{k}.g6'):
    G=nx.from_graph6_bytes(line.strip().encode())
    if not hyp(G,'325'): continue
    n=k; S=[v for v in G if G.degree(v)==2]; NS=set(S)|{u for v in S for u in G[v]}
    c=nx.number_connected_components(G.subgraph(NS))
    best=None
    for u,w in itertools.combinations(G,2):
      if G.has_edge(u,w): continue
      X=set(G[u])&set(G[w])
      if n-len(X)<=1+c:
        rest=set(G)-X-{u,w}
        # do all minimal TDS contain u or w? check: every TDS contains u or w?
        best=(len(X),len(rest),c, all(G.degree(r)==2 for r in rest), all(any(G.degree(x)==2 for x in [u,w]) for _ in [0]))
        break
    stats[(n,)+best]+=1
for k,v in sorted(stats.items()): print(k,v)
