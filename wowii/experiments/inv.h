// Graph invariants by bitmask brute force, n <= 12.
#include <bits/stdc++.h>
using namespace std;
typedef unsigned M;
int n; M adj[32]; M ALL;
inline int pc(M x){ return __builtin_popcount(x); }
void parse(const string& s){ int p=0; n=s[p++]-63; for(int i=0;i<n;i++) adj[i]=0; int val=0,k=6;
  for(int j=1;j<n;j++) for(int i=0;i<j;i++){ if(k==6){ val=s[p++]-63; k=0; } int b=(val>>(5-k))&1; k++; if(b){ adj[i]|=1u<<j; adj[j]|=1u<<i; } } ALL=(1u<<n)-1; }
int alphaM(M m){ if(!m) return 0; int v=__builtin_ctz(m); M rest=m&~(1u<<v); int a=alphaM(rest&~adj[v])+1; if(!(adj[v]&rest)) return a; return max(a,alphaM(rest)); }
M closedN(M S){ M r=S; for(M t=S;t;t&=t-1) r|=adj[__builtin_ctz(t)]; return r; }
M openN(M S){ M r=0; for(M t=S;t;t&=t-1) r|=adj[__builtin_ctz(t)]; return r; }
bool connectedM(M m){ if(!m) return true; M seen=m&(-m), fr=seen; while(fr){ M nf=openN(fr)&m&~seen; seen|=nf; fr=nf; } return seen==m; }
int edgesIn(M m){ int e=0; for(M t=m;t;t&=t-1) e+=pc(adj[__builtin_ctz(t)]&m); return e/2; }
// domination number of induced subgraph on m (subset enumeration, small)
int gammaM(M m){ if(!m) return 0; int best=pc(m); vector<int> elems; for(M t=m;t;t&=t-1) elems.push_back(__builtin_ctz(t)); int k=elems.size();
  for(int s=1;s<(1<<k);s++){ int c=__builtin_popcount(s); if(c>=best) continue; M S=0; for(int i=0;i<k;i++) if(s>>i&1) S|=1u<<elems[i]; if((closedN(S)&m)==m) best=c; } return best; }
int matchM(M m){ if(!m) return 0; int v=__builtin_ctz(m); M rest=m&~(1u<<v); int best=matchM(rest); for(M t=adj[v]&rest;t;t&=t-1){ int w=__builtin_ctz(t); best=max(best,1+matchM(rest&~(1u<<w))); } return best; }
struct Inv { int n,m,delta,Delta,rad,diam,alpha,gamma,gammat,gamma2,idom,mu,tree,f,b,Ls,kappa,pcov,res; bool hampath,c4; vector<int> deg,ecc,lam,tri; };
bool isForest(M m){ int e=edgesIn(m); int comp=0; M left=m; while(left){ M c=left&(-left),fr=c; while(fr){ M nf=openN(fr)&m&~c; c|=nf; fr=nf; } left&=~c; comp++; } return e==pc(m)-comp; }
bool isBip(M m){ M left=m; while(left){ M c0=left&(-left),c1=0,fr0=c0,fr1=0; while(fr0||fr1){ M n1=openN(fr0)&m, n0=openN(fr1)&m; if((n1&c0)||(n0&c1)) return false; n1&=~c1; n0&=~c0; c1|=n1; c0|=n0; fr0=n0; fr1=n1; } left&=~(c0|c1);} return true; }
int residueOf(vector<int> d){ sort(d.rbegin(),d.rend()); while(!d.empty()&&d[0]>0){ int x=d[0]; d.erase(d.begin()); for(int i=0;i<x&&i<(int)d.size();i++) d[i]--; sort(d.rbegin(),d.rend()); } return d.size(); }
Inv compute(){ Inv I; I.n=n; I.deg.resize(n); I.m=0; for(int v=0;v<n;v++){ I.deg[v]=pc(adj[v]); I.m+=I.deg[v]; } I.m/=2;
  I.delta=*min_element(I.deg.begin(),I.deg.end()); I.Delta=*max_element(I.deg.begin(),I.deg.end());
  I.ecc.resize(n); for(int v=0;v<n;v++){ M seen=1u<<v,fr=seen; int d=0; while(seen!=ALL){ M nf=openN(fr)&~seen; if(!nf) break; seen|=nf; fr=nf; d++; } I.ecc[v]=d; }
  I.rad=*min_element(I.ecc.begin(),I.ecc.end()); I.diam=*max_element(I.ecc.begin(),I.ecc.end());
  I.alpha=alphaM(ALL); I.lam.resize(n); I.tri.resize(n); for(int v=0;v<n;v++){ I.lam[v]=alphaM(adj[v]); I.tri[v]=edgesIn(adj[v]); }
  I.mu=matchM(ALL); I.res=residueOf(I.deg);
  // subset-based invariants
  I.gamma=n; I.gammat=n; I.gamma2=n; I.idom=n; I.tree=1; I.f=1; I.b=1; int gc=n;
  for(M S=1;S<=ALL;S++){ int c=pc(S); M cn=closedN(S);
    if(c<I.gamma && cn==ALL) I.gamma=c;
    if(c<I.gammat && openN(S)==ALL) I.gammat=c;
    if(c<I.idom && cn==ALL && !(openN(S)&S)) I.idom=c;
    if(c<I.gamma2){ bool ok=true; for(int v=0;v<n&&ok;v++) if(!(S>>v&1) && pc(adj[v]&S)<2) ok=false; if(ok) I.gamma2=c; }
    if(c>I.f && isForest(S)){ I.f=c; }
    if(c>I.tree && connectedM(S) && edgesIn(S)==c-1) I.tree=c;
    if(c>I.b && isBip(S)) I.b=c;
    if(c<gc && cn==ALL && connectedM(S)) gc=c;
    if(S==ALL) break; }
  I.Ls = (n<=2)? 1 : n-gc; if(n==2) I.Ls=1;
  // kappa: min vertex cut
  I.kappa=n-1; for(M S=0;S<ALL;S++){ int c=pc(S); if(c>=I.kappa) continue; M rest=ALL&~S; if(pc(rest)>=2 && !connectedM(rest)) I.kappa=c; }
  // hamiltonian path & path cover via DP
  { int N=1<<n; vector<M> endset(N,0); for(int v=0;v<n;v++) endset[1<<v]=1u<<v;
    for(int m=1;m<N;m++){ if(!endset[m]) continue; for(M t=endset[m];t;t&=t-1){ int v=__builtin_ctz(t); for(M u=adj[v]&~m;u;u&=u-1){ int w=__builtin_ctz(u); endset[m|(1<<w)]|=1u<<w; } } }
    I.hampath = endset[N-1]!=0; vector<int> cover(N,99); cover[0]=0; for(int m=1;m<N;m++){ int low=m&-m; for(int sub=m;sub;sub=(sub-1)&m){ if(!(sub&low)) continue; if(endset[sub] && cover[m^sub]+1<cover[m]) cover[m]=cover[m^sub]+1; } } I.pcov=cover[N-1]; }
  I.c4=false; for(int a=0;a<n&&!I.c4;a++) for(int c=a+1;c<n;c++) if(pc(adj[a]&adj[c])>=2){ I.c4=true; break; }
  return I; }
