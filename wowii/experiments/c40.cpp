// WOWII 40 (f >= ceil((p + b + 1)/2)) and 100 (alpha <= ceil((max lambda + 0.5 length(co-G))/2)).
#include <bits/stdc++.h>
using namespace std;
typedef unsigned M;
int n; M adj[16], ALL;
static inline int pc(M x){ return __builtin_popcount(x); }
void parse(const string& s){ int p=0; n=s[p++]-63; for(int i=0;i<n;i++) adj[i]=0; int val=0,k=6;
  for(int j=1;j<n;j++) for(int i=0;i<j;i++){ if(k==6){ val=s[p++]-63; k=0; } if((val>>(5-k))&1){ adj[i]|=1u<<j; adj[j]|=1u<<i; } k++; }
  ALL=(1u<<n)-1; }
static inline M openN(M S){ M r=0; for(M t=S;t;t&=t-1) r|=adj[__builtin_ctz(t)]; return r; }
int alphaM(M m){ if(!m) return 0; int v=__builtin_ctz(m); M rest=m&~(1u<<v); int a=alphaM(rest&~adj[v])+1; if(!(adj[v]&rest)) return a; return max(a,alphaM(rest)); }
int edgesIn(M m){ int e=0; for(M t=m;t;t&=t-1) e+=pc(adj[__builtin_ctz(t)]&m); return e/2; }
int ncomp(M m){ int c=0; while(m){ M seen=m&(-m),fr=seen; while(fr){ M nf=openN(fr)&m&~seen; seen|=nf; fr=nf; } m&=~seen; c++; } return c; }
bool isBip(M m){ M left=m; while(left){ M c0=left&(-left),c1=0,fr0=c0,fr1=0; while(fr0||fr1){ M n1=openN(fr0)&m, n0=openN(fr1)&m; if((n1&c0)||(n0&c1)) return false; n1&=~c1; n0&=~c0; c1|=n1; c0|=n0; fr0=n0; fr1=n1; } left&=~(c0|c1);} return true; }
int pathCover(){ int N=1<<n; static M endset[1<<12]; static int cover[1<<12]; for(int m=0;m<N;m++) endset[m]=0; for(int v=0;v<n;v++) endset[1<<v]=1u<<v;
  for(int m=1;m<N;m++){ if(!endset[m]) continue; for(M t=endset[m];t;t&=t-1){ int v=__builtin_ctz(t); for(M u=adj[v]&~m;u;u&=u-1){ int w=__builtin_ctz(u); endset[m|(1<<w)]|=1u<<w; } } }
  cover[0]=0; for(int m=1;m<N;m++){ cover[m]=99; int low=m&-m; for(int sub=m;sub;sub=(sub-1)&m){ if(!(sub&low)) continue; if(endset[sub] && cover[m^sub]+1<cover[m]) cover[m]=cover[m^sub]+1; } } return cover[N-1]; }
int main(){ string s; long cnt=0, f40=0, f100=0; double ms40=1e9, ms100=1e9; string w40, w100;
  while(getline(cin,s)){ if(s.empty()) continue; parse(s); if(n<2) continue; cnt++;
    int b=1,f=1; for(M S=1;S<=ALL;S++){ int c=pc(S); if(c>b && isBip(S)) b=c; if(c>f && edgesIn(S)==c-ncomp(S)) f=c; if(S==ALL) break; }
    int p=pathCover();
    double sl=f-ceil((p+b+1)/2.0-1e-9); if(sl<ms40){ ms40=sl; } if(sl<0){ if(!f40++) w40=s; }
    int alpha=alphaM(ALL), lmax=0; double sq=0; for(int v=0;v<n;v++){ lmax=max(lmax,alphaM(adj[v])); int cd=n-1-pc(adj[v]); sq+=cd*cd; }
    double r=ceil((lmax+0.5*sqrt(sq))/2-1e-9)-alpha; if(r<ms100) ms100=r; if(r<0){ if(!f100++) w100=s; }
  }
  printf("graphs=%ld\n40  fails=%ld minslack=%.0f %s\n100 fails=%ld minslack=%.0f %s\n",cnt,f40,ms40,w40.c_str(),f100,ms100,w100.c_str()); }
