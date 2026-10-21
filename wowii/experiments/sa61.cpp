#include <bits/stdc++.h>
using namespace std; typedef unsigned M; int n; M adj[32]; M ALL; mt19937_64 rng(1);
inline int pc(M x){ return __builtin_popcount(x); }
M openN(M S){ M r=0; for(M t=S;t;t&=t-1) r|=adj[__builtin_ctz(t)]; return r; }
bool connM(M m){ if(!m) return true; M seen=m&(-m),fr=seen; while(fr){ M nf=openN(fr)&m&~seen; seen|=nf; fr=nf; } return seen==m; }
M compOf(M S, int v){ M seen=1u<<v,fr=seen; while(fr){ M nf=openN(fr)&S&~seen; seen|=nf; fr=nf; } return seen; }
bool canAdd(M S,int v){ M nb=adj[v]&S; M used=0; for(M t=nb;t;t&=t-1){ int u=__builtin_ctz(t); M c=compOf(S,u); if(c&used) return false; if(pc(c&nb)>1) return false; used|=c; } return true; }
int bestF; void recF(int v, M S, int cnt){ if(cnt+(n-v)<=bestF) return; if(v==n){ bestF=cnt; return; } if(canAdd(S,v)) recF(v+1,S|(1u<<v),cnt+1); recF(v+1,S,cnt); }
int forestN(){ bestF=0; recF(0,0,0); return bestF; }
int residueOf(vector<int> d){ sort(d.rbegin(),d.rend()); while(!d.empty()&&d[0]>0){ int x=d[0]; d.erase(d.begin()); for(int i=0;i<x&&i<(int)d.size();i++) d[i]--; sort(d.rbegin(),d.rend()); } return d.size(); }
double score(){ if(!connM(ALL)) return -1e9; vector<int> deg(n); for(int v=0;v<n;v++) deg[v]=pc(adj[v]);
  int diam=0; for(int v=0;v<n;v++){ M seen=1u<<v,fr=seen; int d=0; while(seen!=ALL){ M nf=openN(fr)&~seen; if(!nf) break; seen|=nf; fr=nf; d++; } diam=max(diam,d); }
  return residueOf(deg)+(diam+2)/3-forestN(); }
void parse(const string& s){ int p=0; n=s[p++]-63; for(int i=0;i<n;i++) adj[i]=0; int val=0,k=6; for(int j=1;j<n;j++) for(int i=0;i<j;i++){ if(k==6){ val=s[p++]-63; k=0;} if(val>>(5-k)&1){ adj[i]|=1u<<j; adj[j]|=1u<<i;} k++; } }
int main(int argc,char**argv){ n=atoi(argv[1]); long iters=atol(argv[2]); rng.seed(atoi(argv[3])); double p=atof(argv[4]); ALL=(1u<<n)-1;
  if(iters==0){ string s; long cnt=0,tot=0; double mx=-1e9; while(getline(cin,s)){ parse(s); ALL=(1u<<n)-1; double sc=score(); tot++; mx=max(mx,sc); if(sc>0.5){ cnt++; if(cnt<=3) printf("CE %s %.1f\n",s.c_str(),sc);} } printf("n=%d tot=%ld ce=%ld max=%.1f\n",n,tot,cnt,mx); return 0; }
  for(int v=0;v<n;v++) adj[v]=0; for(int i=1;i<n;i++){ int j=rng()%i; adj[i]|=1u<<j; adj[j]|=1u<<i; } for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if((rng()%1000)/1000.0<p){ adj[i]|=1u<<j; adj[j]|=1u<<i; }
  double cur=score(),best=cur; M bestA[32]; memcpy(bestA,adj,sizeof adj); double T=1.0;
  for(long it=0;it<iters;it++){ int i=rng()%n,j=rng()%n; if(i==j) continue; adj[i]^=1u<<j; adj[j]^=1u<<i; double s=score();
    if(s>=cur || exp((s-cur)/T)>(rng()%1000000)/1e6){ cur=s; if(s>best){best=s; memcpy(bestA,adj,sizeof adj);} } else { adj[i]^=1u<<j; adj[j]^=1u<<i; } T=max(0.05,T*0.9995); }
  memcpy(adj,bestA,sizeof adj); printf("61 n=%d best=%.1f edges:",n,best); for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if(adj[i]>>j&1) printf(" %d-%d",i,j); printf("\n"); }
