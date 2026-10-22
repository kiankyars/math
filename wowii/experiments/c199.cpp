// Lemma test: alpha >= kappa + 2  ==>  tree(G) >= kappa + 3 (tree = order of a largest induced tree).
#include <bits/stdc++.h>
using namespace std;
typedef unsigned M; int n; M adj[16], ALL;
static inline int pc(M x){ return __builtin_popcount(x); }
void parse(const string& s){ int p=0; n=s[p++]-63; for(int i=0;i<n;i++) adj[i]=0; int val=0,k=6;
  for(int j=1;j<n;j++) for(int i=0;i<j;i++){ if(k==6){ val=s[p++]-63; k=0; } if((val>>(5-k))&1){ adj[i]|=1u<<j; adj[j]|=1u<<i; } k++; } ALL=(1u<<n)-1; }
static inline M openN(M S){ M r=0; for(M t=S;t;t&=t-1) r|=adj[__builtin_ctz(t)]; return r; }
bool connM(M m){ if(!m) return true; M seen=m&(-m),fr=seen; while(fr){ M nf=openN(fr)&m&~seen; seen|=nf; fr=nf; } return seen==m; }
int edgesIn(M m){ int e=0; for(M t=m;t;t&=t-1) e+=pc(adj[__builtin_ctz(t)]&m); return e/2; }
int alphaM(M m){ if(!m) return 0; int v=__builtin_ctz(m); M rest=m&~(1u<<v); int a=alphaM(rest&~adj[v])+1; if(!(adj[v]&rest)) return a; return max(a,alphaM(rest)); }
int main(){ string s; long cnt=0, fails=0, rel=0; string first; int minsl=99;
  while(getline(cin,s)){ if(s.empty()) continue; parse(s); cnt++;
    int alpha=alphaM(ALL);
    int kappa=n-1; for(M X=0;X<=ALL;X++){ int c=pc(X); if(c>=kappa) { if(X==ALL) break; continue; } if(!connM(ALL&~X) && pc(ALL&~X)>=2) kappa=c; if(X==ALL) break; }
    // complete graph: kappa = n-1
    if(alpha<kappa+2) continue; rel++;
    int tr=1; for(M S=1;S<=ALL;S++){ int c=pc(S); if(c>tr && edgesIn(S)==c-1 && connM(S)) tr=c; if(S==ALL) break; }
    minsl=min(minsl,tr-(kappa+3)); if(tr<kappa+3){ if(!fails++) first=s; }
  }
  printf("graphs=%ld relevant=%ld fails=%ld minslack=%d %s\n",cnt,rel,fails,minsl,first.c_str()); }
