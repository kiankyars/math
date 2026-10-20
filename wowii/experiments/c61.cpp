// C61 variants: f vs residue + ceil(D/3), alpha + ceil(D/3).
#include <bits/stdc++.h>
using namespace std;
int n; unsigned adj[32];
void parse(const string& s){ int p=0; n=s[p++]-63; for(int i=0;i<n;i++) adj[i]=0; int val=0,k=6;
  for(int j=1;j<n;j++) for(int i=0;i<j;i++){ if(k==6){ val=s[p++]-63; k=0; } int b=(val>>(5-k))&1; k++; if(b){ adj[i]|=1u<<j; adj[j]|=1u<<i; } } }
int alphaMask(unsigned m){ if(!m) return 0; int v=__builtin_ctz(m); unsigned rest=m&~(1u<<v); int a=alphaMask(rest&~adj[v])+1; if(!(adj[v]&rest)) return a; return max(a,alphaMask(rest)); }
// largest induced forest by branch: grow forest with union-find check
int bestF; unsigned ALL;
bool acyclicAdd(unsigned F,int v){ // adding v to forest F keeps acyclic iff v's neighbours in F lie in distinct components
  unsigned nb=adj[v]&F; unsigned seen=0; while(nb){ int u=__builtin_ctz(nb); if(seen>>u&1) return false; unsigned c=1u<<u,fr=c; while(fr){ unsigned nf=0; for(unsigned t=fr;t;t&=t-1) nf|=adj[__builtin_ctz(t)]&F; nf&=~c; c|=nf; fr=nf; } if(c&seen) return false; seen|=c; nb&=~(1u<<u); if(nb&c) return false; } return true; }
void growF(unsigned F,unsigned cand,int sz){ if(sz>bestF) bestF=sz; if(sz+__builtin_popcount(cand)<=bestF) return; if(!cand) return; int v=__builtin_ctz(cand); unsigned rest=cand&~(1u<<v);
  if(acyclicAdd(F,v)) growF(F|(1u<<v),rest,sz+1); growF(F,rest,sz); }
int residueOf(vector<int> d){ sort(d.rbegin(),d.rend()); while(!d.empty()&&d[0]>0){ int x=d[0]; d.erase(d.begin()); for(int i=0;i<x&&i<(int)d.size();i++) d[i]--; sort(d.rbegin(),d.rend()); } return d.size(); }
int main(){ string s; long cnt=0; int minR=99,minA=99; long failA=0;
  while(getline(cin,s)){ if(s.empty()) continue; parse(s); cnt++; ALL=(1u<<n)-1;
    int D=0; for(int v=0;v<n;v++){ unsigned seen=1u<<v,fr=seen; int d=0; while(seen!=ALL){ unsigned nf=0; for(unsigned t=fr;t;t&=t-1) nf|=adj[__builtin_ctz(t)]; nf&=~seen; seen|=nf; fr=nf; d++; } D=max(D,d); }
    vector<int> deg(n); for(int v=0;v<n;v++) deg[v]=__builtin_popcount(adj[v]); int R=residueOf(deg); int a=alphaMask(ALL);
    bestF=0; growF(0,ALL,0); int f=bestF; int c3=(D+2)/3;
    minR=min(minR,f-R-c3); if(f-a-c3<minA) minA=f-a-c3;
    if(f-a-c3<0){ failA++; if(failA<=5) printf("alpha-variant FAIL %s n=%d f=%d alpha=%d R=%d D=%d\n",s.c_str(),n,f,a,R,D); }
    if(f-R-c3<0) printf("C61 FAIL %s\n",s.c_str());
  }
  printf("graphs=%ld min(f-R-c3)=%d min(f-alpha-c3)=%d failsAlpha=%ld\n",cnt,minR,minA,failA); }
