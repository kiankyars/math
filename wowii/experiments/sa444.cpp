#include <bits/stdc++.h>
using namespace std; typedef unsigned M; int n; M adj[32]; M ALL; mt19937_64 rng(1);
inline int pc(M x){ return __builtin_popcount(x); }
M openN(M S){ M r=0; for(M t=S;t;t&=t-1) r|=adj[__builtin_ctz(t)]; return r; }
bool connM(M m){ if(!m) return true; M seen=m&(-m),fr=seen; while(fr){ M nf=openN(fr)&m&~seen; seen|=nf; fr=nf; } return seen==m; }
int best2;
void rec(int i, M S, M deg1, int sz){ // deg1: vertices in S with one S-neighbour
  if(sz+(n-i)<=best2) return; if(i==n){ best2=max(best2,sz); return; }
  M nb=adj[i]&S; if(pc(nb)<=1 && !(nb&deg1)){ M d1=deg1; if(nb){ d1|=nb; d1|=1u<<i; } rec(i+1,S|(1u<<i),d1,sz+1); }
  rec(i+1,S,deg1,sz); }
int alpha2(){ best2=0; rec(0,0,0,0); return best2; }
double score(){ if(!connM(ALL)) return -1e9; set<int> k4; for(int v=0;v<n;v++){ int c=0; M N=adj[v]; for(M t=N;t;t&=t-1){ int a=__builtin_ctz(t); for(M u=N&adj[a]&~((2u<<a)-1);u;u&=u-1){ int b=__builtin_ctz(u); c+=pc(N&adj[a]&adj[b]&~((2u<<b)-1)); } } k4.insert(c); }
  return alpha2()-(n-(int)k4.size()/2); }
int main(int argc,char**argv){ n=atoi(argv[1]); long iters=atol(argv[2]); rng.seed(atoi(argv[3])); double p=atof(argv[4]); ALL=(1u<<n)-1;
  for(int v=0;v<n;v++) adj[v]=0; for(int i=1;i<n;i++){ int j=rng()%i; adj[i]|=1u<<j; adj[j]|=1u<<i; } for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if((rng()%1000)/1000.0<p){ adj[i]|=1u<<j; adj[j]|=1u<<i; }
  double cur=score(),best=cur; M bestA[32]; memcpy(bestA,adj,sizeof adj); double T=1.0;
  for(long it=0;it<iters;it++){ int i=rng()%n,j=rng()%n; if(i==j) continue; adj[i]^=1u<<j; adj[j]^=1u<<i; double s=score();
    if(s>=cur || exp((s-cur)/T)>(rng()%1000000)/1e6){ cur=s; if(s>best){best=s; memcpy(bestA,adj,sizeof adj);} } else { adj[i]^=1u<<j; adj[j]^=1u<<i; } T=max(0.05,T*0.9995); }
  memcpy(adj,bestA,sizeof adj); printf("444 n=%d best=%.3f edges:",n,best); for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if(adj[i]>>j&1) printf(" %d-%d",i,j); printf("\n"); }
