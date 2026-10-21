import networkx as nx
exec(open('h323.py').read().split('for k in range')[0])
for k in [6,7]:
  for line in open(f'g{k}.g6'):
    G=nx.from_graph6_bytes(line.strip().encode())
    if not hyp(G): continue
    D=dict(nx.all_pairs_shortest_path_length(G)); H=nx.complement(G)
    mx=max(len(set(H[u])|set(H[v])) for u,v in H.edges())
    vals={v:sum(1 for w in G if D[v][w]%2==1)-sum(1 for a,b in G.edges() if D[v][a]==D[v][b] and D[v][a]%2==1) for v in G}
    best=max(vals.values()); vs=[v for v in G if vals[v]==best][0]
    A=[w for w in G if D[vs][w]==1]; B=[w for w in G if D[vs][w]!=1]
    print(k, "LHS",mx,"best",best,"v*",vs,"A",A,"B",B,"e(A)",G.subgraph(A).number_of_edges(),"e(B)",G.subgraph(B).number_of_edges(),"cross missing",sum(1 for a in A for b in B if not G.has_edge(a,b)), "degs",sorted(d for _,d in G.degree()))
