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
mn=lambda m:(m&-m).bit_length()-1
mx=lambda m:m.bit_length()-1
sub=lambda a,b:(a[0]-b[0],a[1]-b[1],a[2]-b[2])
J={c:m-1 for c,m in cols}
for raised in [None,(2,1,1),(3,1,0)]:
    JJ=dict(J)
    if raised: JJ[raised]+=1
    elts=[(w,h) for w in JJ for h in range(JJ[w]+1)]
    Bs=B(elts)
    bad=0; d2=0
    for u,m in Bs.items():
        for v in JJ:
            z=sub(u,v)
            if z in Bs:
                m2=Bs[z]
                if max(mn(m),mn(m2)+JJ[v])>min(mx(m),mx(m2)+JJ[v]): bad+=1
    print("raised",raised,"KL failures:",bad)

print("---- details for raised (2,1,1)")
JJ=dict(J); JJ[(2,1,1)]+=1
elts=[(w,h) for w in JJ for h in range(JJ[w]+1)]
Bs=B(elts)
fails=[]
for u,m in Bs.items():
    for v in JJ:
        z=sub(u,v)
        if z in Bs:
            m2=Bs[z]
            if max(mn(m),mn(m2)+JJ[v])>min(mx(m),mx(m2)+JJ[v]):
                fails.append((u,v)); print("u",u,"v",v,"J(v)",JJ[v],"B(u)",(mn(m),mx(m)),"B(u-v)",(mn(m2),mx(m2)))
for u,v in fails:
    JJ2=dict(JJ); JJ2[v]+=1
    elts2=[(w,h) for w in JJ2 for h in range(JJ2[w]+1)]
    B2=B(elts2)
    m=B2[u]; hs=[i for i in range(m.bit_length()) if m>>i&1]
    print("after raising",v,"at u",u,"hset",hs, "interval" if hs==list(range(hs[0],hs[-1]+1)) else "GAP!")
