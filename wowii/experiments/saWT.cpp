#include <bits/stdc++.h>
using namespace std; typedef unsigned M; int n; M adj[32]; M ALL; mt19937_64 rng(1); string which;
inline int pc(M x){ return __builtin_popcount(x); }
M openN(M S){ M r=0; for(M t=S;t;t&=t-1) r|=adj[__builtin_ctz(t)]; return r; }
M closedN(M S){ return S|openN(S); }
bool connM(M m){ if(!m) return true; M seen=m&(-m),fr=seen; while(fr){ M nf=openN(fr)&m&~seen; seen|=nf; fr=nf; } return seen==m; }
int residueOf(vector<int> d){ sort(d.rbegin(),d.rend()); while(!d.empty()&&d[0]>0){ int x=d[0]; d.erase(d.begin()); for(int i=0;i<x&&i<(int)d.size();i++) d[i]--; sort(d.rbegin(),d.rend()); } return d.size(); }
int bestK; void recK(M S, M X){ if(pc(S)>=bestK) return; int w=-1; for(int v=0;v<n;v++){ if(S>>v&1) continue; if(!(adj[v]&S)){ w=v; break; } } if(w<0){ bestK=pc(S); return; }
  M cand=(adj[w]|(1u<<w))&~S&~X; M X2=X; for(M t=cand;t;t&=t-1){ int u=__builtin_ctz(t); recK(S|(1u<<u),X2); X2|=1u<<u; } }
int gam(){ bestK=n+1; recK(0,0); return bestK; }
// minimal TDS sizes: enumerate TDS minimal via recursion: generate minimal total dominating sets by B&B over all subsets (2^n)
int wtdSizes(){ set<int> sz; for(M S=1;S<=ALL;S++){ if(openN(S)==ALL){ bool minimal=true; for(M t=S;t;t&=t-1){ if(openN(S&~(t&-t))==ALL){minimal=false;break;} } if(minimal){ sz.insert(pc(S)); if(sz.size()>1) return 2; } } if(S==ALL) break; } return sz.size(); }
double score(){ if(!connM(ALL)) return -1e9;
  int D[32][32]; for(int v=0;v<n;v++){ for(int w=0;w<n;w++) D[v][w]=99; D[v][v]=0; M seen=1u<<v,fr=seen; int d=0; while(fr){ M nf=openN(fr)&~seen; d++; for(M t=nf;t;t&=t-1) D[v][__builtin_ctz(t)]=d; seen|=nf; fr=nf; } }
  vector<int> deg(n); for(int v=0;v<n;v++) deg[v]=pc(adj[v]); M cadj[32]; for(int v=0;v<n;v++) cadj[v]=ALL&~adj[v]&~(1u<<v);
  double slack;
  if(which=="319"){ int mde=0; for(int v=0;v<n;v++){ int c=0; for(int w=0;w<n;w++) if(D[v][w]%2==0) c++; mde=max(mde,c);} slack=gam()-mde; }
  else { int mx=-1,mn=99; for(int u=0;u<n;u++) for(int v=u+1;v<n;v++) if(!(adj[u]>>v&1)){ int x=pc(cadj[u]|cadj[v]); mx=max(mx,x); mn=min(mn,x);} if(mx<0) return -1e9;
    if(which=="324") slack=1+residueOf(deg)-mx;
    else { M S=0; for(int v=0;v<n;v++) if(deg[v]==2) S|=1u<<v; M NS=closedN(S); int comp=0; M left=NS; while(left){ M c=left&(-left),fr=c; while(fr){ M nf=openN(fr)&NS&~c; c|=nf; fr=nf; } left&=~c; comp++; } slack=1+comp-mn; } }
  if(slack<0) return slack-1;
  return wtdSizes()>1 ? 1 : -0.5; }
int main(int argc,char**argv){ which=argv[1]; n=atoi(argv[2]); long iters=atol(argv[3]); rng.seed(atoi(argv[4])); double p=atof(argv[5]); ALL=(1u<<n)-1;
  for(int v=0;v<n;v++) adj[v]=0; for(int i=1;i<n;i++){ int j=rng()%i; adj[i]|=1u<<j; adj[j]|=1u<<i; } for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if((rng()%1000)/1000.0<p){ adj[i]|=1u<<j; adj[j]|=1u<<i; }
  double cur=score(),best=cur; M bestA[32]; memcpy(bestA,adj,sizeof adj); double T=1.0;
  for(long it=0;it<iters;it++){ int i=rng()%n,j=rng()%n; if(i==j) continue; adj[i]^=1u<<j; adj[j]^=1u<<i; double s=score();
    if(s>=cur || exp((s-cur)/T)>(rng()%1000000)/1e6){ cur=s; if(s>best){best=s; memcpy(bestA,adj,sizeof adj);} } else { adj[i]^=1u<<j; adj[j]^=1u<<i; } T=max(0.05,T*0.999); }
  memcpy(adj,bestA,sizeof adj); printf("%s n=%d best=%.3f edges:",which.c_str(),n,best); for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if(adj[i]>>j&1) printf(" %d-%d",i,j); printf("\n"); }
