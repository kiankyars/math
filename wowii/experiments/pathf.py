import itertools
from functools import lru_cache
def gprime(a,i):  # vertices 1..a, exempt i; min |D| with every v != i having a neighbour in D (path adjacency)
    best=None
    # DP over positions with state (prev in D, prevprev in D) -- brute force via bitmask for small a
    for mask in range(1<<a):
        c=bin(mask).count('1')
        if best is not None and c>=best: continue
        ok=True
        for v in range(1,a+1):
            if v==i: continue
            nb=[u for u in (v-1,v+1) if 1<=u<=a]
            if not any(mask>>(u-1)&1 for u in nb): ok=False;break
        if ok: best=c
    return best
bad=[]
for a in range(1,19):
    row=[]
    for i in range(1,a+1):
        f=gprime(a,i)-a//2
        row.append(f)
        need = 1 if (a%2==1 and i%2==1) else 0
        if f<need: bad.append((a,i,f))
    print(a,row)
print("violations of f>=[a,i odd]:",bad)
def hmin(a,i):
    best=None
    for mask in range(1<<a):
        if not (mask>>(i-1))&1: continue
        c=bin(mask).count('1')
        if best is not None and c>=best: continue
        ok=all(any(mask>>(u-1)&1 for u in (v-1,v+1) if 1<=u<=a) for v in range(1,a+1) if v!=i)
        if ok: best=c
    return best
print("h(a,i)-floor(a/2):")
for a in range(1,18):
    print(a,[hmin(a,i)-a//2 for i in range(1,a+1)])
