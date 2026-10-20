import random, sys, time
from relax import *
random.seed(int(sys.argv[1]) if len(sys.argv)>1 else 1)
zps=[[1,4,-6],[2,-4,5],[2,-5,6],[4,5,6],[-4,-5,-6],[1,7,-9],[-2,-7,8],[-2,-8,9],[7,8,9],[-7,-8,-9],
     [-1,10,-12],[3,-10,11],[3,-11,12],[10,11,12],[-10,-11,-12],[-1,13,-15],[-3,-13,14],[-3,-14,15],[13,14,15],[-13,-14,-15]]
f=[c[:] for c in zps]; nv=15
seen=set(); best=0; t0=time.time(); steps=0; acc=0
def key(f): return tuple(sorted(tuple(sorted(c)) for c in f))
while time.time()-t0<float(sys.argv[2] if len(sys.argv)>2 else 120):
    steps+=1
    g=[c[:] for c in f]
    a,b=random.sample(range(len(g)),2); i=random.randrange(3); j=random.randrange(3)
    g[a][i],g[b][j]=g[b][j],g[a][i]
    if len(set(abs(l) for l in g[a]))<3 or len(set(abs(l) for l in g[b]))<3: continue
    if len(set(key([c]) for c in g))<len(g): continue
    if not is_unsat(g): continue
    f=g; acc+=1; k=key(f)
    if k in seen: continue
    seen.add(k)
    c,S=cost(f,nv)
    if c>=1: print("FOUND cost",c,f,flush=True); break
print("steps",steps,"accepted",acc,"distinct unsat",len(seen))
