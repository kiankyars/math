#include <bits/stdc++.h>
using namespace std; typedef unsigned M; int n; M adj[32]; M ALL; mt19937_64 rng(1); string which;
inline int pc(M x){ return __builtin_popcount(x); }
M openN(M S){ M r=0; for(M t=S;t;t&=t-1) r|=adj[__builtin_ctz(t)]; return r; }
M closedN(M S){ return S|openN(S); }
bool connM(M m){ if(!m) return true; M seen=m&(-m),fr=seen; while(fr){ M nf=openN(fr)&m&~seen; seen|=nf; fr=nf; } return seen==m; }
int edgesIn(M m){ int e=0; for(M t=m;t;t&=t-1) e+=pc(adj[__builtin_ctz(t)]&m); return e/2; }
int alphaM(M m){ if(!m) return 0; int v=__builtin_ctz(m); M rest=m&~(1u<<v); int a=alphaM(rest&~adj[v])+1; if(!(adj[v]&rest)) return a; return max(a,alphaM(rest)); }
#include "fastinv.h"
int bestK,K; M *KA; void recK(M S, M X){ if(pc(S)>=bestK) return; int w=-1; for(int v=0;v<n;v++){ if(S>>v&1) continue; if(pc(KA[v]&S)<K){ w=v; break; } } if(w<0){ bestK=pc(S); return; }
  M U=ALL&~S&~X; for(M t=X;t;t&=t-1){ int x=__builtin_ctz(t); if(pc(KA[x]&S)+pc(KA[x]&U)<K) return; }
  if(!(X>>w&1)){ recK(S|(1u<<w),X); recK(S,X|(1u<<w)); return; } M cand=KA[w]&U; if(!cand) return; int u=__builtin_ctz(cand); recK(S|(1u<<u),X); recK(S,X|(1u<<u)); }
int kdom(M* A,int k){ KA=A; K=k; bestK=n+1; recK(0,0); return bestK; }
int bestI; void recI(M dom, M avail, int k){ if(dom==ALL){ bestI=min(bestI,k); return; } if(k+1>=bestI) return; int v=__builtin_ctz(~dom&ALL); M cand=(adj[v]|(1u<<v))&avail; for(M t=cand;t;t&=t-1){ int x=__builtin_ctz(t); M cx=adj[x]|(1u<<x); recI(dom|cx, avail&~cx, k+1); } }
int idom(){ bestI=n+1; recI(0,ALL,0); return bestI; }
vector<M> endset;
void buildEnd(){ int N=1<<n; endset.assign(N,0); for(int v=0;v<n;v++) endset[1<<v]=1u<<v; for(int m=1;m<N;m++){ if(!endset[m]) continue; for(M t=endset[m];t;t&=t-1){ int v=__builtin_ctz(t); for(M u=adj[v]&~m;u;u&=u-1){ int w=__builtin_ctz(u); endset[m|(1<<w)]|=1u<<w; } } } }
bool hamPath(){ buildEnd(); return endset[(1<<n)-1]!=0; }
int pathCover(){ buildEnd(); int N=1<<n; vector<int> cover(N,99); cover[0]=0; for(int m=1;m<N;m++){ int low=m&-m; for(int sub=m;sub;sub=(sub-1)&m){ if(!(sub&low)) continue; if(endset[sub] && cover[m^sub]+1<cover[m]) cover[m]=cover[m^sub]+1; } } return cover[N-1]; }
int kappa(){ if(edgesIn(ALL)==n*(n-1)/2) return n-1; int best=n-1; // min vertex cut by brute force over sizes
  for(int k=1;k<n-1;k++){ // enumerate subsets of size k
    vector<int> idx(k); function<bool(int,int,M)> rec=[&](int start,int left,M S)->bool{ if(left==0){ M rest=ALL&~S; return pc(rest)>=2 && !connM(rest); } for(int v=start;v<=n-left;v++) if(rec(v+1,left-1,S|(1u<<v))) return true; return false; };
    if(rec(0,k,0)) return k; } return best; }
double score(){ if(!connM(ALL)) return -1e9;
  int D[32][32]; for(int v=0;v<n;v++){ for(int w=0;w<n;w++) D[v][w]=99; D[v][v]=0; M seen=1u<<v,fr=seen; int d=0; while(fr){ M nf=openN(fr)&~seen; d++; for(M t=nf;t;t&=t-1) D[v][__builtin_ctz(t)]=d; seen|=nf; fr=nf; } }
  vector<int> deg(n); for(int v=0;v<n;v++) deg[v]=pc(adj[v]); vector<int> sd=deg; sort(sd.begin(),sd.end()); int sigma=sd[1];
  int delta=sd[0]; M A=0; for(int v=0;v<n;v++) if(deg[v]==delta) A|=1u<<v;
  M cadj[32]; for(int v=0;v<n;v++) cadj[v]=ALL&~adj[v]&~(1u<<v);
  if(which=="418b"){ int id=idom(); int aR=alphaM(ALL&~A); int e=edgesIn(openN(A)); if(id<=aR+e) return id-aR-e-1; return id-(aR+e*pathCover()); }
  if(which=="384b"){ set<int> T; for(int v=0;v<n;v++) T.insert(edgesIn(adj[v])); return kdom(adj,2)-floor(n-T.size()/2.0+1e-9); }
  if(which=="177"){ return 2*alphaM(ALL)+sigma-(Ls()+bipB()); }
  double slack;
  if(which=="189"){ int mde=0; for(int v=0;v<n;v++){ int c=0; for(int w=0;w<n;w++) if(D[v][w]%2==0) c++; mde=max(mde,c);} slack=1+sigma-mde; }
  else if(which=="190"){ slack=sigma-0.5*(Ls()+1); }
  else if(which=="199"){ slack=kappa()-(treeN()-2); }
  else if(which=="213"){ vector<int> cd(n); for(int v=0;v<n;v++) cd[v]=n-1-deg[v]; sort(cd.begin(),cd.end()); int lm=cd[(n-1)/2]; slack=kdom(cadj,2)-(2+lm); }
  else return 0;
  if(slack<0) return slack-1; return hamPath()? -0.5 : 1; }
int main(int argc,char**argv){ which=argv[1]; n=atoi(argv[2]); long iters=atol(argv[3]); rng.seed(atoi(argv[4])); double p=atof(argv[5]); ALL=(1u<<n)-1;
  for(int v=0;v<n;v++) adj[v]=0; for(int i=1;i<n;i++){ int j=rng()%i; adj[i]|=1u<<j; adj[j]|=1u<<i; } for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if((rng()%1000)/1000.0<p){ adj[i]|=1u<<j; adj[j]|=1u<<i; }
  double cur=score(),best=cur; M bestA[32]; memcpy(bestA,adj,sizeof adj); double T=1.0;
  for(long it=0;it<iters;it++){ int i=rng()%n,j=rng()%n; if(i==j) continue; adj[i]^=1u<<j; adj[j]^=1u<<i; double s=score();
    if(s>=cur || exp((s-cur)/T)>(rng()%1000000)/1e6){ cur=s; if(s>best){best=s; memcpy(bestA,adj,sizeof adj);} } else { adj[i]^=1u<<j; adj[j]^=1u<<i; } T=max(0.05,T*0.999); }
  memcpy(adj,bestA,sizeof adj); printf("%s n=%d best=%.3f edges:",which.c_str(),n,best); for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if(adj[i]>>j&1) printf(" %d-%d",i,j); printf("\n"); }
