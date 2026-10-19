#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64;
// encode exponent vectors of primes <= n/2 with fixed bit widths
int main(int argc,char**argv){
  int N=atoi(argv[1]);
  vector<int> primes; for(int i=2;i<=N;i++){bool ok=true; for(int j=2;j*j<=i;j++) if(i%j==0){ok=false;break;} if(ok) primes.push_back(i);}
  // field widths based on N
  int np=primes.size(); vector<int> width(np), shift(np); int tot=0;
  for(int i=0;i<np;i++){ int p=primes[i]; long v=0; for(long q=p;q<=N;q*=p) v+=N/q; int w=1; while((1L<<w)<=v) w++; width[i]=w; shift[i]=tot; tot+=w; }
  if(tot>64){fprintf(stderr,"too many bits %d\n",tot); return 1;}
  vector<u64> P={0}; // encoded, 0 = product 1
  for(int n=1;n<=N;n++){
    // skip primes > N/2? we do full but skip large primes p > n/2 at time n? Large prime relative to final N only.
    // Use current n: element n. Compute encoding of n.
    u64 enc=0; int m=n; bool skip=false;
    for(int i=0;i<np;i++){int p=primes[i]; int e=0; while(m%p==0){m/=p;e++;} enc += (u64)e<<shift[i]; if(e && p==n && 2*p>N) skip=true;}
    if(!skip){
      vector<u64> Q; Q.reserve(P.size()*2);
      for(u64 x:P){Q.push_back(x); Q.push_back(x+enc);}
      sort(Q.begin(),Q.end()); Q.erase(unique(Q.begin(),Q.end()),Q.end()); P.swap(Q);
    }
    // check conjecture for primes p <= n/2 using current set (which is P(n) minus primes > N/2, those don't matter)
    // but primes in (n/2, N/2] at stage n: also fine to check
    long bad=0;
    for(int i=0;i<np && 2*primes[i]<=n;i++){
      u64 unit=1ULL<<shift[i]; u64 mask=((1ULL<<width[i])-1)<<shift[i];
      for(u64 x:P){
        // x is the bottom of a run if x-unit not in P (or exponent 0). Find top of run, then check nothing above.
        u64 e=(x&mask)>>shift[i];
        if(e>0 && binary_search(P.begin(),P.end(),x-unit)) continue;
        u64 y=x; u64 ey=e;
        while(ey+1 < (1ULL<<width[i]) && binary_search(P.begin(),P.end(),y+unit)){y+=unit;ey++;}
        // gap: check further
        u64 z=y+unit; u64 ez=ey+1; bool gap=false;
        while(ez < (1ULL<<width[i])){ z+=unit; ez++; if(ez>=(1ULL<<width[i])) break; if(binary_search(P.begin(),P.end(),z)){gap=true;break;} }
        if(gap){ bad++; if(bad<5) printf("COUNTEREXAMPLE n=%d p=%d base exps run %llu..%llu then present at %llu\n",n,primes[i],e,ey,ez); }
      }
    }
    printf("n=%d |P|=%zu bad=%ld\n",n,P.size(),bad); fflush(stdout);
  }
}
