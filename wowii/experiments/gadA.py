# Enumerate OR(a,b) gadgets: a once, b twice (pattern given), l locals each literal exactly twice.
# Compute local relaxation cost profile c(a,b) = min |W|-|K| over K subset L, W subset clauses (exhaustive).
import itertools, sys, collections
from pysat.solvers import Cadical153
def sat(cl,assump=[]):
    with Cadical153(bootstrap_with=cl) as s: return s.solve(assumptions=assump)
def enum_gadgets(ext, l):
    # ext: list of external literal slots e.g. [1,2,2] (a once, b twice); locals 3..l+2
    Z=list(range(3,3+l)); lits=ext+[x for z in Z for x in (z,z,-z,-z)]
    m=len(lits)//3; found=set()
    def rec(rem, cls):
        if not rem:
            found.add(tuple(sorted(cls))); return
        first=rem[0]; rest=rem[1:]; seen=set()
        for i,j in itertools.combinations(range(len(rest)),2):
            c=tuple(sorted((first,rest[i],rest[j]),key=lambda x:(abs(x),x)))
            if len(set(abs(x) for x in c))<3 or c in seen: continue
            seen.add(c); rec([rest[k] for k in range(len(rest)) if k not in (i,j)], cls+[c])
    rec(sorted(lits,key=lambda x:(abs(x),x)),[])
    return found
def is_or_gadget(g):
    cl=[list(c) for c in g]
    return (not sat(cl,[-1,-2])) and sat(cl,[1,-2]) and sat(cl,[-1,2]) and sat(cl,[1,2])
def local_cost(g, l, a, b):
    Z=list(range(3,3+l)); cls=[list(c) for c in g]; best=10**9
    val={1:a,2:b}
    for kmask in range(1<<l):
        K=set(Z[i] for i in range(l) if kmask>>i&1)
        rest=[z for z in Z if z not in K]
        for wmask in range(1<<len(cls)):
            W=[cls[j] for j in range(len(cls)) if wmask>>j&1]
            c=len(W)-len(K)
            if c>=best: continue
            # coverage
            ok=all(any(z in C for C in W) and any(-z in C for C in W) for z in K)
            if not ok: continue
            # clauses entirely in K must be in W
            for sig in range(1<<len(rest)):
                v=dict(val); v.update({rest[i]:bool(sig>>i&1) for i in range(len(rest))})
                def tru(x): return (abs(x) in v) and (v[abs(x)]==(x>0))
                good=True
                for j,C in enumerate(cls):
                    inW=(wmask>>j&1)
                    if inW:
                        if any(tru(x) for x in C): good=False;break
                    else:
                        if not any(tru(x) for x in C): good=False;break
                if good: best=c; break
    return best
if __name__=="__main__":
    ext=eval(sys.argv[1]); l=int(sys.argv[2])
    gs=enum_gadgets(ext,l); ors=[g for g in gs if is_or_gadget(g)]
    print("raw",len(gs),"OR gadgets",len(ors))
    prof=collections.Counter()
    for g in ors:
        p=tuple(local_cost(g,l,a,b) for a in (True,False) for b in (True,False))
        prof[p]+=1
        if p[0]>=0 and prof[p]<=3: print("profile (TT,TF,FT,FF)=",p,g)
    print(prof)
