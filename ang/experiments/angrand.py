import sys, random
from functools import lru_cache
from sympy import primerange
sys.setrecursionlimit(100000)
def interval_sum(S,a,b):
    # S (bitmask) Minkowski-sum [a,b]
    if b<a: return 0
    res=0; width=b-a+1; cur=S<<a; acc=0
    # doubling trick
    t=1; block=cur
    res=0; shift=0; w=width; base=cur
    while w>0:
        if w&1: res|=base<<shift; shift+=t
        base=base|(base<<t); t*=2; w>>=1
    return res
def check(n,p,trials,seed):
    rnd=random.Random(seed)
    cls=[r for r in range(2,n+1) if r%p]
    def J(r):
        j=0
        while r*p**(j+1)<=n: j+=1
        return j
    Jr={r:J(r) for r in cls}
    J1=0
    while p**(J1+1)<=n: J1+=1
    T=J1*(J1+1)//2
    small=[r for r in cls if Jr[r]>=1]
    bad=0
    for t in range(trials):
        # structured random R: product of random blocks with repeats among small classes
        R=1
        for r in rnd.sample(small,min(len(small),rnd.randint(1,5))):
            R*=r**rnd.randint(1,Jr[r]+1)
        for r in rnd.sample(cls,rnd.randint(0,8)):
            R*=r
        rel=[r for r in cls if R%r==0]
        @lru_cache(maxsize=None)
        def dp(i,q):
            if q==1: return 1  # bit 0
            if i==len(rel): return 0
            r=rel[i]; res=dp(i+1,q); qq=q; k=0
            while qq%r==0 and k+1<=Jr[r]+1:
                qq//=r; k+=1
                sub=dp(i+1,qq)
                if sub: res|=interval_sum(sub,k*(k-1)//2,k*Jr[r]-k*(k-1)//2)
            return res
        E=dp(0,R)
        if E==0: continue
        E=interval_sum(E,0,T)
        lo=(E&-E).bit_length()-1; hi=E.bit_length()-1
        full=((1<<(hi-lo+1))-1)<<lo
        if E!=full:
            bad+=1; print("GAP n=%d p=%d R=%d E=%s"%(n,p,R,bin(E)),flush=True)
    return bad
tot=0
for n in [50,70,90,120]:
    for p in list(primerange(2,n//2+1)):
        b=check(n,p,150,n*7919+p); tot+=b
    print("n",n,"done, gaps so far",tot,flush=True)
