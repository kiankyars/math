cols=[((0,0,1),3),((0,0,2),1),((0,0,3),2),((0,1,0),2),((0,1,1),1),((0,1,2),3),((0,1,3),3),((1,0,0),1),((1,0,1),3),((1,0,2),3),((1,0,3),3),((1,1,0),2),((1,1,1),2),((2,0,0),2),((2,0,1),1),((2,0,2),1),((2,0,3),1),((2,1,0),3),((2,1,1),2),((3,0,0),1),((3,0,1),3),((3,0,2),2),((3,0,3),3),((3,1,0),1),((3,1,1),3)]
D=set(c for c,_ in cols)|{(0,0,0)}
import itertools
ok=all(tuple(y) in D for c in D for y in itertools.product(*[range(ci+1) for ci in c]))
print("down-closed:",ok)
R={(0,0,0)}
for w,m in cols:
    R={tuple(a+k*b for a,b in zip(y,w)) for y in R for k in range(m+1)}
print("|R|=",len(R))
w=(3,1,0); w2=(2,1,1)
add=lambda a,b,s=1: tuple(p+s*q for p,q in zip(a,b))
for x in [(11,14,11),(11,15,14),(11,16,17)]:
    print(x, "x+w in R:",add(x,w) in R, "x+w2 in R:",add(x,w2) in R, "x in R:", x in R, "x+w+w2 in R:", add(add(x,w),w2) in R)
