import itertools
spec="(0,0,1,)m4 (0,1,0,)m3 (1,0,0,)m4 (0,0,2,)m2 (0,1,1,)m2 (0,2,0,)m2 (1,0,1,)m2 (1,1,0,)m1 (2,0,0,)m3 (0,0,3,)m1 (0,1,2,)m1 (0,2,1,)m1 (1,1,1,)m1 (2,0,1,)m2 (2,1,0,)m1 (3,0,0,)m3 (0,1,3,)m1 (0,2,2,)m1 (2,1,1,)m1 (3,0,1,)m1 (3,1,0,)m1 (0,2,3,)m1 (3,1,1,)m1"
cols=[]
for tok in spec.split():
    v,m=tok.split(")m"); v=tuple(int(x) for x in v.strip("(").strip(",").split(",") if x!=""); cols.append((v,int(m)))
D=set(c for c,_ in cols)|{(0,0,0)}
print("down-closed:",all(tuple(y) in D for c in D for y in itertools.product(*[range(ci+1) for ci in c])))
mono=all(m1>=m2 for c1,m1 in cols for c2,m2 in cols if all(a<=b for a,b in zip(c1,c2)))
print("monotone:",mono)
def B(elts):
    Dd={(0,0,0):1}
    for w,h in elts:
        N=dict(Dd)
        for R,m in Dd.items():
            R2=(R[0]+w[0],R[1]+w[1],R[2]+w[2]); N[R2]=N.get(R2,0)|(m<<h)
        Dd=N
    return Dd
w=(1,1,1); u=(6,18,8)
flat=[(c,0) for c,m in cols for _ in range(m)]
Bf=B(flat)
sub=lambda a,b,k=1:tuple(x-k*y for x,y in zip(a,b))
print("u in R:",u in Bf,"u-w in R:",sub(u,w) in Bf,"u-2w in R:",sub(u,w,2) in Bf)
Bx=B(flat+[(w,1),(w,1)])
m=Bx[u]; print("G_ms system flat+2(w,1) at u: hset",[i for i in range(m.bit_length()) if m>>i&1])
# Theorem G (distinct heights) system with J=m-1, monotone => a down-set in N^4
G=[(c,h) for c,m in cols for h in range(m)]
BG=B(G)
def isint(m):
    m2=m>>((m&-m).bit_length()-1); return (m2&(m2+1))==0
print("Theorem G on this down-set: all intervals:",all(isint(x) for x in BG.values()))
# raise column w (J: 0->1, 1->2)
for extra in [[(w,1)],[(w,1),(w,2)]]:
    Be=B(G+extra); bad=[uu for uu,x in Be.items() if not isint(x)]
    print("G with extra",extra,"failures",len(bad),bad[:3])
