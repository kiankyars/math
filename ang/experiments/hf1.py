# HF1: for convex (threshold) down-sets D, Sigma(D*) == Z cap Z^d, Z = sum [0,w]. Membership in Z via LP.
import random, sys, itertools, numpy as np
from scipy.optimize import linprog
rnd=random.Random(int(sys.argv[1])); trials=int(sys.argv[2]); dmin=int(sys.argv[3]); dmax=int(sys.argv[4]); maxcols=int(sys.argv[5]); maxbox=int(sys.argv[6]); amin=float(sys.argv[7])
def inZ(x,W):
    # exists lam in [0,1]^n with W^T lam = x
    n=len(W); A=np.array(W,dtype=float).T
    res=linprog(np.zeros(n),A_eq=A,b_eq=np.array(x,dtype=float),bounds=[(0,1)]*n,method='highs')
    return res.status==0
bad=0; tested=0
for t in range(trials):
    d=rnd.randint(dmin,dmax)
    a=[amin+(0.7-amin)*rnd.random() for _ in range(d)]
    D=[]
    def rec(i,e,s):
        if i==d:
            if any(e): D.append(tuple(e))
            return
        k=0
        while s+k*a[i]<=1+1e-12:
            rec(i+1,e+[k],s+k*a[i]); k+=1
    rec(0,[],0.0)
    if len(D)<2 or len(D)>maxcols: continue
    S={tuple([0]*d)}
    for w in D: S|={tuple(x+y for x,y in zip(s,w)) for s in S}
    tot=[sum(w[i] for w in D) for i in range(d)]
    box=1
    for x in tot: box*=(x+1)
    if box>maxbox: continue
    tested+=1
    for x in itertools.product(*[range(v+1) for v in tot]):
        if x in S: continue
        if inZ(x,D):
            bad+=1; print("HOLE d=",d,"a=",[round(z,3) for z in a],"D=",D,"x=",x); break
print("tested",tested,"bad",bad)
