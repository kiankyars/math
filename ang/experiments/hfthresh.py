# Hole-freeness of R(D,m) for threshold down-sets D={e: sum a_i e_i <= 1}, multiplicities m>=1 (random or monotone)
import random, sys, itertools, numpy as np
from scipy.spatial import ConvexHull
rnd=random.Random(int(sys.argv[1])); trials=int(sys.argv[2]); dmax=int(sys.argv[3]); maxm=int(sys.argv[4]); mono=int(sys.argv[5]); maxR=int(sys.argv[6])
bad=0; tested=0
for t in range(trials):
    d=rnd.randint(2,dmax)
    a=[0.08+0.5*rnd.random() for _ in range(d)]
    D=[]
    def rec(i,e,s):
        if i==d:
            if any(e): D.append(tuple(e))
            return
        k=0
        while s+k*a[i]<=1+1e-12:
            rec(i+1,e+[k],s+k*a[i]); k+=1
    rec(0,[],0.0)
    if len(D)<3 or len(D)>18: continue
    D.sort(key=lambda w:(sum(w),w))
    m={}
    for w in D:
        ub=maxm
        if mono:
            for u in m:
                if all(x<=y for x,y in zip(u,w)): ub=min(ub,m[u])
        m[w]=rnd.randint(1,ub)
    R={tuple([0]*d)}
    for w in D:
        R={tuple(x+k*y for x,y in zip(r,w)) for r in R for k in range(m[w]+1)}
        if len(R)>maxR: break
    if len(R)>maxR: continue
    tested+=1
    pts=np.array(sorted(R))
    try:
        H=ConvexHull(pts)
    except Exception:
        continue
    mins=pts.min(0); maxs=pts.max(0)
    eqs=H.equations
    found=False
    for x in itertools.product(*[range(mins[i],maxs[i]+1) for i in range(d)]):
        if x in R: continue
        if np.all(eqs[:,:-1].dot(x)+eqs[:,-1]<=1e-9):
            bad+=1; found=True
            if bad<=3: print("HOLE d=",d,"D,m=",[(w,m[w]) for w in D],"x=",x)
            break
print("mono",mono,"tested",tested,"with holes",bad)
