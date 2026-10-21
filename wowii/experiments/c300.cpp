#include <bits/stdc++.h>
using namespace std; typedef unsigned M; int n; M adj[32]; M ALL;
inline int pc(M x){ return __builtin_popcount(x); }
void parse(const string& s){ int p=0; n=s[p++]-63; for(int i=0;i<n;i++) adj[i]=0; int val=0,k=6;
  for(int j=1;j<n;j++) for(int i=0;i<j;i++){ if(k==6){ val=s[p++]-63; k=0; } int b=(val>>(5-k))&1; k++; if(b){ adj[i]|=1u<<j; adj[j]|=1u<<i; } } ALL=(1u<<n)-1; }
M openN(M S){ M r=0; for(M t=S;t;t&=t-1) r|=adj[__builtin_ctz(t)]; return r; }
int gammat(int cap){ int best=cap; function<void(M,int)> rec=[&](M S,int sz){ if(sz>=best) return; M dom=openN(S); if(dom==ALL){ best=sz; return; } M und=~dom&ALL; int v=-1,bd=99; for(M t=und;t;t&=t-1){ int x=__builtin_ctz(t); int d=pc(adj[x]&~S); if(d<bd){bd=d;v=x;} } if(sz+1>=best) return; for(M t=adj[v]&~S;t;t&=t-1){ int u=__builtin_ctz(t); rec(S|(1u<<u),sz+1);} }; rec(0,0); return best; }
int omega(M m){ if(!m) return 0; int v=__builtin_ctz(m); M rest=m&~(1u<<v); int a=omega(rest&adj[v])+1; if((adj[v]&rest)==rest) return a; return max(a,omega(rest)); }
int main(){ string s; long cnt=0,bad=0; while(getline(cin,s)){ if(s.empty()) continue; parse(s); cnt++;
    int lc[32],lmin=99; for(int v=0;v<n;v++){ lc[v]=omega(ALL&~adj[v]&~(1u<<v)); lmin=min(lmin,lc[v]); } int f=0; for(int v=0;v<n;v++) if(lc[v]==lmin) f++;
    int bound=(n+f)/2; // gamma_t must be <= floor((n+f)/2)
    int g=gammat(bound+2); if(g>bound){ bad++; if(bad<=5) printf("CE %s gt=%d n=%d f=%d\n",s.c_str(),g,n,f); } }
  printf("graphs=%ld bad=%ld\n",cnt,bad); }
