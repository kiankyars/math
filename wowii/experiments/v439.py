import networkx as nx, itertools, sys, math
from fractions import Fraction
def check(es):
  G=nx.Graph([tuple(map(int,e.split('-'))) for e in es.split()]); n=G.number_of_nodes(); assert nx.is_connected(G)
  best=0;bS=None
  nodes=list(G)
  for mask in range(1<<n):
    S=[v for v in nodes if mask>>v&1]
    if len(S)<=best: continue
    if all(sum(1 for u in G[v] if mask>>u&1)<=1 for v in S): best=len(S); bS=S
  deg=dict(G.degree()); D=max(deg.values()); Mx=[v for v in G if deg[v]==D]
  NM=set().union(*[set(G[v]) for v in Mx])
  CW=sum(Fraction(1,deg[v]+1) for v in G)
  rhs=len(NM)+math.floor(2*(CW-1))
  print("n",n,"m",G.number_of_edges(),"a2",best,bS,"Delta",D,"M",Mx,"|N(M)|",len(NM),"CW",CW,float(CW),"rhs",rhs,"CE" if best>rhs else "", "degs",sorted(deg.values()))
for line in sys.stdin: check(line.split('edges:')[1])
