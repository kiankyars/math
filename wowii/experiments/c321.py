import networkx as nx, itertools
from fractions import Fraction
tot=0; allwtd=True
for k in range(2,9):
  for line in open(f'g{k}.g6'):
    G=nx.from_graph6_bytes(line.strip().encode()); n=G.number_of_nodes()
    D=dict(nx.all_pairs_shortest_path_length(G))
    ecc=[max(D[v].values()) for v in G]; Td=[sum(D[v].values()) for v in G]
    if 3*Fraction(sum(ecc),n) >= max(Td):
      tot+=1
      def tds(S): return all(any(G.has_edge(v,u) for u in S) for v in G)
      sizes=set()
      for r in range(1,n+1):
        for S in itertools.combinations(G,r):
          if tds(S) and all(not tds([x for x in S if x!=y]) for y in S): sizes.add(r)
      if len(sizes)!=1: allwtd=False
      print(n, G.number_of_edges(), sorted(G.edges()), sizes)
print("total",tot,"all WTD",allwtd)
