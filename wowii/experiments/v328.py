import networkx as nx, itertools
E="0-1 0-2 0-3 0-4 0-5 0-6 0-7 1-2 1-3 1-4 1-5 1-6 1-7 1-8 2-3 2-4 2-5 2-6 2-7 2-9 3-4 3-5 3-6 3-7 4-5 4-6 4-7 4-8 5-6 5-7 6-7 6-9 8-9".split()
G=nx.Graph([tuple(map(int,e.split('-'))) for e in E]); n=G.number_of_nodes()
print(n, G.number_of_edges(), nx.is_connected(G))
H=nx.complement(G); mu=len(nx.max_weight_matching(H,maxcardinality=True))
k4={v:sum(1 for c in nx.enumerate_all_cliques(G) if len(c)==4 and v in c) for v in G}
mx=max(k4.values()); f=sum(1 for v in k4 if k4[v]==mx)
print("mu(Gbar)=",mu,"K4:",k4,"freq=",f, "hyp:",4*mu<=f)
def tds(S): return all(any(G.has_edge(v,u) for u in S) for v in G)
sizes=set(); 
for r in range(1,n+1):
  for S in itertools.combinations(G,r):
    if tds(S) and all(not tds([x for x in S if x!=y]) for y in S): sizes.add(r)
print("minimal TDS sizes:",sizes)
print(tds([1,8]), tds([8,9,0,3]))
