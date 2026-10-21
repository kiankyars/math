#include <bits/stdc++.h>
using namespace std; typedef unsigned M; int n; M adj[32]; M ALL; mt19937_64 rng(1);
inline int pc(M x){ return __builtin_popcount(x); }
M openN(M S){ M r=0; for(M t=S;t;t&=t-1) r|=adj[__builtin_ctz(t)]; return r; }
bool connM(M m){ if(!m) return true; M seen=m&(-m),fr=seen; while(fr){ M nf=openN(fr)&m&~seen; seen|=nf; fr=nf; } return seen==m; }
int bestA2;
// S current set, C candidates (each individually addable)
void rec(M S, M C){ int s=pc(S); if(s>bestA2) bestA2=s; if(s+pc(C)<=bestA2) return; if(!C) return;
  int v=__builtin_ctz(C); M C2=C&~(1u<<v);
  // include v
  M S2=S|(1u<<v); // remove candidates that become invalid
  M full=0; for(M t=S2;t;t&=t-1){ int x=__builtin_ctz(t); if(pc(adj[x]&S2)>=1) full|=1u<<x; }
  M nc=0; for(M t=C2;t;t&=t-1){ int w=__builtin_ctz(t); M nw=adj[w]&S2; if(pc(nw)>=2) continue; if(nw&full) continue; nc|=1u<<w; }
  rec(S2,nc);
  rec(S,C2); }
int alpha2(){ bestA2=0; rec(0,ALL); return bestA2; }
double score(){ if(!connM(ALL)) return -1e9; vector<int> deg(n); for(int v=0;v<n;v++) deg[v]=pc(adj[v]); int D=*max_element(deg.begin(),deg.end()); M Mx=0; for(int v=0;v<n;v++) if(deg[v]==D) Mx|=1u<<v;
  double CW=0; for(int v=0;v<n;v++) CW+=1.0/(deg[v]+1); return alpha2()-(pc(openN(Mx))+floor(2*(CW-1)+1e-9)); }
void parse(const string& s){ int p=0; n=s[p++]-63; for(int i=0;i<n;i++) adj[i]=0; int val=0,k=6;
  for(int j=1;j<n;j++) for(int i=0;i<j;i++){ if(k==6){ val=s[p++]-63; k=0;} if(val>>(5-k)&1){ adj[i]|=1u<<j; adj[j]|=1u<<i;} k++; } }
int main(int argc,char**argv){ n=atoi(argv[1]); long iters=atol(argv[2]); rng.seed(atoi(argv[3])); double p=atof(argv[4]); ALL=(1u<<n)-1;
  if(iters==0){ string s; long cnt=0,tot=0; double mx=-1e9; while(getline(cin,s)){ parse(s); ALL=(1u<<n)-1; double sc=score(); tot++; mx=max(mx,sc); if(sc>0.5){ cnt++; if(cnt<=3) printf("CE %s %.3f\n",s.c_str(),sc);} } printf("n=%d tot=%ld ce=%ld max=%.3f\n",n,tot,cnt,mx); return 0; }
  for(int v=0;v<n;v++) adj[v]=0; for(int i=1;i<n;i++){ int j=rng()%i; adj[i]|=1u<<j; adj[j]|=1u<<i; } for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if((rng()%1000)/1000.0<p){ adj[i]|=1u<<j; adj[j]|=1u<<i; }
  double cur=score(),best=cur; M bestA[32]; memcpy(bestA,adj,sizeof adj); double T=1.0;
  for(long it=0;it<iters;it++){ int i=rng()%n,j=rng()%n; if(i==j) continue; adj[i]^=1u<<j; adj[j]^=1u<<i; double s=score();
    if(s>=cur || exp((s-cur)/T)>(rng()%1000000)/1e6){ cur=s; if(s>best){best=s; memcpy(bestA,adj,sizeof adj);} } else { adj[i]^=1u<<j; adj[j]^=1u<<i; } T=max(0.05,T*0.9995); }
  memcpy(adj,bestA,sizeof adj); printf("439 n=%d best=%.3f edges:",n,best); for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if(adj[i]>>j&1) printf(" %d-%d",i,j); printf("\n"); }
