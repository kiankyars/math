import itertools
cols=[((0,0,1),3),((0,0,2),1),((0,0,3),2),((0,1,0),2),((0,1,1),1),((0,1,2),3),((0,1,3),3),((1,0,0),1),((1,0,1),3),((1,0,2),3),((1,0,3),3),((1,1,0),2),((1,1,1),2),((2,0,0),2),((2,0,1),1),((2,0,2),1),((2,0,3),1),((2,1,0),3),((2,1,1),2),((3,0,0),1),((3,0,1),3),((3,0,2),2),((3,0,3),3),((3,1,0),1),((3,1,1),3)]
def B(elts):
    D={(0,0,0):1}
    for w,h in elts:
        N=dict(D)
        for R,m in D.items():
            R2=(R[0]+w[0],R[1]+w[1],R[2]+w[2]); N[R2]=N.get(R2,0)|(m<<h)
        D=N
    return D
def isint(m):
    m2=m>>((m&-m).bit_length()-1); return (m2&(m2+1))==0
base=[(w,h) for w,m in cols for h in range(m)]   # heights 0..m-1 (distinct) = Theorem G system
Bb=B(base)
print("G on base system:", all(isint(m) for m in Bb.values()), "points",len(Bb))
w=(3,1,0); w2=(2,1,1)
J={c:m-1 for c,m in cols}
for extra in [[(w,J[w]+1)],[(w2,J[w2]+1)],[(w,J[w]+1),(w2,J[w2]+1)]]:
    Be=B(base+extra)
    bad=[u for u,m in Be.items() if not isint(m)]
    print("extra",extra,"interval failures:",len(bad), bad[:3])
    for u in bad[:2]:
        m=Be[u]; print("  u",u,"hset",[i for i in range(m.bit_length()) if m>>i&1])
