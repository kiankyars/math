# Build Gupta's 50-vertex cubic graph from the 20-clause (3,2,2) unsat formula.
clauses = [
 [1,4,-6],[2,-4,5],[2,-5,6],[4,5,6],[-4,-5,-6],
 [1,7,-9],[-2,-7,8],[-2,-8,9],[7,8,9],[-7,-8,-9],
 [-1,10,-12],[3,-10,11],[3,-11,12],[10,11,12],[-10,-11,-12],
 [-1,13,-15],[-3,-13,14],[-3,-14,15],[13,14,15],[-13,-14,-15]]
# vertex ids: v_i = 2(i-1), vbar_i = 2(i-1)+1, w_j = 30 + (j-1)
E=[]
for i in range(1,16): E.append((2*(i-1),2*(i-1)+1))
for j,c in enumerate(clauses):
    w=30+j
    for lit in c:
        x=abs(lit); v=2*(x-1)+(0 if lit>0 else 1)
        E.append((v,w))
import collections
deg=collections.Counter()
for a,b in E: deg[a]+=1; deg[b]+=1
assert all(deg[v]==3 for v in range(50)), deg
assert len(set(tuple(sorted(e)) for e in E))==len(E)
# literal occurrence check
occ=collections.Counter(l for c in clauses for l in c)
assert all(occ[l]==2 for l in list(range(1,16))+[-x for x in range(1,16)])
# brute-force unsat check
sat=False
for m in range(1<<15):
    if all(any(((m>>(abs(l)-1))&1)==(1 if l>0 else 0) for l in c) for c in clauses): sat=True; break
print("formula satisfiable?",sat)
import networkx as nx
G=nx.Graph(); G.add_edges_from(E)
print("connected",nx.is_connected(G),"n",G.number_of_nodes(),"m",G.number_of_edges())
open("gupta50.g6","w").write(nx.to_graph6_bytes(G,header=False).decode())
with open("gupta50.edges","w") as f:
    f.write("50 %d\n"%len(E)); [f.write("%d %d\n"%e) for e in E]
