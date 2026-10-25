#include <bits/stdc++.h>
using namespace std;
typedef unsigned M;
int n; M adj[32], ALL;
static inline int pc(M x){ return __builtin_popcount(x); }
void parse(const string& s){ int p=0; n=s[p++]-63; for(int i=0;i<n;i++) adj[i]=0; int val=0,k=6;
  for(int j=1;j<n;j++) for(int i=0;i<j;i++){ if(k==6){ val=s[p++]-63; k=0; } if((val>>(5-k))&1){ adj[i]|=1u<<j; adj[j]|=1u<<i; } k++; }
  ALL=(n==32)?~0u:((1u<<n)-1); }
static inline M openN(M S){ M r=0; for(M t=S;t;t&=t-1) r|=adj[__builtin_ctz(t)]; return r; }
bool connM(M m){ if(!m) return true; M seen=m&(-m),fr=seen; while(fr){ M nf=openN(fr)&m&~seen; seen|=nf; fr=nf; } return seen==m; }
int alphaM(M m){ if(!m) return 0; int v=__builtin_ctz(m); M rest=m&~(1u<<v); int a=alphaM(rest&~adj[v])+1; if(!(adj[v]&rest)) return a; return max(a,alphaM(rest)); }
int ncomp(M m){ int c=0; while(m){ M seen=m&(-m),fr=seen; while(fr){ M nf=openN(fr)&m&~seen; seen|=nf; fr=nf; } m&=~seen; c++; } return c; }
bool isBip(M m){ M left=m; while(left){ M c0=left&(-left),c1=0,fr0=c0,fr1=0; while(fr0||fr1){ M n1=openN(fr0)&m, n0=openN(fr1)&m; if((n1&c0)||(n0&c1)) return false; n1&=~c1; n0&=~c0; c1|=n1; c0|=n0; fr0=n0; fr1=n1; } left&=~(c0|c1);} return true; }
string toG6(){ string s; s+=char(n+63); int val=0,k=0; for(int j=1;j<n;j++) for(int i=0;i<j;i++){ val=(val<<1)|((adj[i]>>j)&1); k++; if(k==6){ s+=char(val+63); val=0;k=0;} } if(k){ val<<=(6-k); s+=char(val+63);} return s; }
