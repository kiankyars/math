# Search skeletons: clauses typed A (w1 lit, w2 lit), B (w2,w2), P (w1,w1,w1); each literal total weight exactly 2.
# unsat skeleton & min abstract cost >= 1.
import itertools, sys
from pysat.solvers import Cadical153
def sat(cl):
    with Cadical153(bootstrap_with=cl) as s: return s.solve()
V=int(sys.argv[1])
L=[x for v in range(1,V+1) for x in (v,-v)]
# a literal's weight 2 is split as: one w2 slot (in A or B) or two w1 slots (in A or P)
results=[]
def abstract_min(clauses):
    best=10**9
    for m in range(1<<V):
        val=lambda x: ((m>>(abs(x)-1))&1)==(1 if x>0 else 0)
        c=0
        for t,lits in clauses:
            nt=sum(val(x) for x in lits)
            if t=='A': c+= 1-nt
            else: c+= (nt==0)
        best=min(best,c)
    return best
count=0
def rec(slots1, slots2, clauses):
    # slots1: multiset of literals needing w1 slots; slots2: literals needing a w2 slot
    global count
    if not slots1 and not slots2:
        count+=1
        cl=[list(l) for t,l in clauses]
        if not sat(cl):
            a=abstract_min(clauses)
            if a>=1: results.append(clauses); print("FOUND",a,clauses,flush=True)
        return
    # pick smallest pending item to place
    if slots2:
        x=slots2[0]; r2=slots2[1:]
        # B with another w2 literal y (distinct var)
        for i,y in enumerate(r2):
            if abs(y)!=abs(x) and (i==0 or r2[i-1]!=y):
                rec(slots1, r2[:i]+r2[i+1:], clauses+[('B',(x,y))])
        # A with a w1 literal
        seen=set()
        for i,y in enumerate(slots1):
            if abs(y)!=abs(x) and y not in seen:
                seen.add(y); rec(slots1[:i]+slots1[i+1:], r2, clauses+[('A',(y,x))])
    else:
        x=slots1[0]; r1=slots1[1:]; seen=set()
        for i,j in itertools.combinations(range(len(r1)),2):
            y,z=r1[i],r1[j]
            if len({abs(x),abs(y),abs(z)})<3: continue
            key=tuple(sorted((y,z)))
            if key in seen: continue
            seen.add(key)
            rec([r1[k] for k in range(len(r1)) if k not in (i,j)], [], clauses+[('P',(x,y,z))])
# choose for each literal whether type w2 (one slot) or w1 (two slots)
for mask in range(1<<len(L)):
    s1=[];s2=[]
    for i,x in enumerate(L):
        if mask>>i&1: s2.append(x)
        else: s1+= [x,x]
    # feasibility: #w2 literals in A equals #A; parity conditions handled by recursion
    rec(sorted(s1,key=lambda x:(abs(x),x)), sorted(s2,key=lambda x:(abs(x),x)), [])
print("skeletons enumerated",count,"found",len(results))
