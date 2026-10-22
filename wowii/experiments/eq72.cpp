#include <bits/stdc++.h>
using namespace std;
typedef unsigned M; int n; M adj[32]; int best;
static inline int pc(M x){ return __builtin_popcount(x); }
void grow(M S, M excl, int sz){ if(sz>best) best=sz; M nb=0; for(M t=S;t;t&=t-1) nb|=adj[__builtin_ctz(t)]; nb&=~S&~excl; M avail=((1u<<n)-1)&~S&~excl; if(sz+pc(avail)<=best) return;
  for(M t=nb;t;t&=t-1){ int v=__builtin_ctz(t); if(pc(adj[v]&S)==1){ grow(S|(1u<<v), excl, sz+1); excl|=1u<<v; if(sz+pc(((1u<<n)-1)&~S&~excl)<=best) return; } else { excl|=1u<<v; } } }
int treeNum(){ best=1; M excl=0; for(int v=0;v<n;v++){ grow(1u<<v, excl, 1); excl|=1u<<v; } return best; }
int alphaM(M m){ if(!m) return 0; int v=__builtin_ctz(m); M rest=m&~(1u<<v); int a=alphaM(rest&~adj[v])+1; if(!(adj[v]&rest)) return a; return max(a,alphaM(rest)); }
int main(){ string s; map<string,int> stats; while(getline(cin,s)){ int p=0; n=s[p++]-63; for(int i=0;i<n;i++) adj[i]=0; int val=0,k=6; for(int j=1;j<n;j++) for(int i=0;i<j;i++){ if(k==6){ val=s[p++]-63; k=0; } if((val>>(5-k))&1){ adj[i]|=1u<<j; adj[j]|=1u<<i; } k++; }
  double esum=0; int diam=0; for(int v=0;v<n;v++){ M seen=1u<<v,fr=seen; int d=0; while(fr){ M nf=0; for(M t=fr;t;t&=t-1) nf|=adj[__builtin_ctz(t)]; nf&=~seen; if(nf) d++; seen|=nf; fr=nf; } esum+=d; diam=max(diam,d);} int lmax=0; for(int v=0;v<n;v++) lmax=max(lmax,alphaM(adj[v]));
  int tr=treeNum(); double rhs=ceil(esum/n+lmax/3.0-1e-9); if(tr-rhs<=0.5){ char buf[100]; sprintf(buf,"tree=%d diam=%d lmax=%d eavg=%.2f",tr,diam,lmax,esum/n); stats[buf]++; if(lmax>=4 || diam>=3) printf("%s %s\n",s.c_str(),buf);} }
  for(auto&[k,v]:stats) fprintf(stderr,"%6d %s\n",v,k.c_str()); }
