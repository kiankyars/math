import networkx as nx, sys
exec(open('hW.py').read().split('which=sys.argv[1]')[0])
which=sys.argv[1]
for k in range(4,10):
  cnt=0; cm=0; ex=[]
  fn=f'g{k}.g6'
  for line in open(fn):
    G=nx.from_graph6_bytes(line.strip().encode())
    if not hyp(G,which): continue
    cnt+=1
    H=nx.complement(G)
    iscm=all(nx.is_isomorphic(H.subgraph(c), nx.complete_graph(len(c))) for c in nx.connected_components(H))
    if iscm: cm+=1
    elif len(ex)<3: ex.append((sorted(G.edges()), sorted(d for _,d in G.degree())))
  print(which,k,cnt,"complete multipartite:",cm, ex[:2])
