import random, sys, time
from relax import *
seed=int(sys.argv[1]); extra=int(sys.argv[2]); T=float(sys.argv[3])
random.seed(seed)
zps=[[1,4,-6],[2,-4,5],[2,-5,6],[4,5,6],[-4,-5,-6],[1,7,-9],[-2,-7,8],[-2,-8,9],[7,8,9],[-7,-8,-9],
     [-1,10,-12],[3,-10,11],[3,-11,12],[10,11,12],[-10,-11,-12],[-1,13,-15],[-3,-13,14],[-3,-14,15],[13,14,15],[-13,-14,-15]]
f=[c[:] for c in zps]; nv=15
for e in range(extra):
    p,q,r=nv+1,nv+2,nv+3; nv+=3
    f+= [[p,q,r],[p,-q,-r],[-p,q,-r],[-p,-q,r]]
assert check_B2(f,nv) and is_unsat(f)
def key(f): return tuple(sorted(tuple(sorted(c)) for c in f))
seen=set(); t0=time.time(); steps=0; acc=0; nc=0; hist={}
while time.time()-t0<T:
    steps+=1
    g=[c[:] for c in f]
    a,b=random.sample(range(len(g)),2); i=random.randrange(3); j=random.randrange(3)
    g[a][i],g[b][j]=g[b][j],g[a][i]
    if len(set(abs(l) for l in g[a]))<3 or len(set(abs(l) for l in g[b]))<3: continue
    if not is_unsat(g): continue
    f=g; acc+=1; k=key(f)
    if k in seen: continue
    seen.add(k)
    if len(seen)%5: continue   # evaluate every 5th new formula
    c,S=cost(f,nv); nc+=1; hist[c]=hist.get(c,0)+1
    if c>=1: print("FOUND cost",c,nv,f,flush=True); break
print("nv",nv,"steps",steps,"acc",acc,"distinct",len(seen),"evaluated",nc,"hist",hist,flush=True)
