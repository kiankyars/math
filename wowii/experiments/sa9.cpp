#include <bits/stdc++.h>
using namespace std; typedef unsigned M; int n; M adj[32]; M ALL; mt19937_64 rng(1); string which;
inline int pc(M x){ return __builtin_popcount(x); }
M openN(M S){ M r=0; for(M t=S;t;t&=t-1) r|=adj[__builtin_ctz(t)]; return r; }
M closedN(M S){ return S|openN(S); }
bool connM(M m){ if(!m) return true; M seen=m&(-m),fr=seen; while(fr){ M nf=openN(fr)&m&~seen; seen|=nf; fr=nf; } return seen==m; }
int edgesIn(M m){ int e=0; for(M t=m;t;t&=t-1) e+=pc(adj[__builtin_ctz(t)]&m); return e/2; }
int bestI;
void recI(M dom, M avail, int k){ if(dom==ALL){ bestI=min(bestI,k); return; } if(k+1>=bestI) return;
  int v=__builtin_ctz(~dom&ALL); M cand=(adj[v]|(1u<<v))&avail; for(M t=cand;t;t&=t-1){ int x=__builtin_ctz(t); M cx=adj[x]|(1u<<x); recI(dom|cx, avail&~cx, k+1); } }
int idom(){ bestI=n+1; recI(0,ALL,0); return bestI; }
double score(){ if(!connM(ALL)) return -1e9;
  vector<int> tri(n); for(int v=0;v<n;v++) tri[v]=edgesIn(adj[v]); int tm=*min_element(tri.begin(),tri.end()); int Tm=0; for(int v=0;v<n;v++) if(tri[v]==tm) Tm++;
  M Dd=0; for(int v=0;v<n;v++) for(int u=0;u<n;u++) if(u!=v && ((closedN(1u<<u)&~closedN(1u<<v))==0)) { Dd|=1u<<v; break; }
  if(which=="425e") return idom()-(4.0*Tm+edgesIn(Dd)) - 0.01*pc(Dd);
  return 0; }
void parse(const string& s){ int p=0; n=s[p++]-63; for(int i=0;i<n;i++) adj[i]=0; int val=0,k=6;
  for(int j=1;j<n;j++) for(int i=0;i<j;i++){ if(k==6){ val=s[p++]-63; k=0;} if(val>>(5-k)&1){ adj[i]|=1u<<j; adj[j]|=1u<<i;} k++; } }
int main(int argc,char**argv){ which=argv[1]; n=atoi(argv[2]); long iters=atol(argv[3]);
  if(iters==0){ string s; long cnt=0,tot=0; double mx=-1e9; while(getline(cin,s)){ parse(s); ALL=(1u<<n)-1; double sc=score(); tot++; mx=max(mx,sc); if(sc>0.5){ cnt++; if(cnt<=3) printf("CE %s %s %.3f\n",which.c_str(),s.c_str(),sc);} } printf("%s n=%d tot=%ld ce=%ld max=%.3f\n",which.c_str(),n,tot,cnt,mx); return 0; } rng.seed(atoi(argv[4])); double p=atof(argv[5]); ALL=(n==32)?~0u:(1u<<n)-1;
  for(int v=0;v<n;v++) adj[v]=0; for(int i=1;i<n;i++){ int j=rng()%i; adj[i]|=1u<<j; adj[j]|=1u<<i; } for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if((rng()%1000)/1000.0<p){ adj[i]|=1u<<j; adj[j]|=1u<<i; }
  double cur=score(),best=cur; M bestA[32]; memcpy(bestA,adj,sizeof adj); double T=1.0;
  for(long it=0;it<iters;it++){ int i=rng()%n,j=rng()%n; if(i==j) continue; adj[i]^=1u<<j; adj[j]^=1u<<i; double s=score();
    if(s>=cur || exp((s-cur)/T)>(rng()%1000000)/1e6){ cur=s; if(s>best){best=s; memcpy(bestA,adj,sizeof adj);} } else { adj[i]^=1u<<j; adj[j]^=1u<<i; } T=max(0.05,T*0.9995); }
  memcpy(adj,bestA,sizeof adj); printf("%s n=%d best=%.3f edges:",which.c_str(),n,best); for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if(adj[i]>>j&1) printf(" %d-%d",i,j); printf("\n"); }
