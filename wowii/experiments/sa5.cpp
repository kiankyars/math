#include <bits/stdc++.h>
using namespace std; typedef unsigned M; int n; M adj[32]; M ALL; mt19937_64 rng(1); string which;
inline int pc(M x){ return __builtin_popcount(x); }
M openN(M S){ M r=0; for(M t=S;t;t&=t-1) r|=adj[__builtin_ctz(t)]; return r; }
M closedN(M S){ return S|openN(S); }
bool connM(M m){ if(!m) return true; M seen=m&(-m),fr=seen; while(fr){ M nf=openN(fr)&m&~seen; seen|=nf; fr=nf; } return seen==m; }
int edgesIn(M m){ int e=0; for(M t=m;t;t&=t-1) e+=pc(adj[__builtin_ctz(t)]&m); return e/2; }
int alphaM(M m){ if(!m) return 0; int v=__builtin_ctz(m); M rest=m&~(1u<<v); int a=alphaM(rest&~adj[v])+1; if(!(adj[v]&rest)) return a; return max(a,alphaM(rest)); }
int matchM(M m){ if(!m) return 0; int v=__builtin_ctz(m); M rest=m&~(1u<<v); int best=matchM(rest); for(M t=adj[v]&rest;t;t&=t-1){ int w=__builtin_ctz(t); best=max(best,1+matchM(rest&~(1u<<w))); if(best*2>=pc(m)) break; } return best; }
int degeneracy(const M* A, M m){ int best=0; M left=m; while(left){ int mn=99,v=-1; for(M t=left;t;t&=t-1){ int x=__builtin_ctz(t); int d=pc(A[x]&left); if(d<mn){mn=d;v=x;} } best=max(best,mn); left&=~(1u<<v); } return best; }
double score(){ if(!connM(ALL)) return -1e9;
  int D[32][32]; for(int v=0;v<n;v++){ for(int w=0;w<n;w++) D[v][w]=-1; D[v][v]=0; M seen=1u<<v,fr=seen; int d=0; while(fr){ M nf=openN(fr)&~seen; d++; for(M t=nf;t;t&=t-1) D[v][__builtin_ctz(t)]=d; seen|=nf; fr=nf; } }
  vector<int> deg(n),ecc(n); for(int v=0;v<n;v++){ deg[v]=pc(adj[v]); ecc[v]=0; for(int w=0;w<n;w++) ecc[v]=max(ecc[v],D[v][w]); }
  int rad=*min_element(ecc.begin(),ecc.end()), diam=*max_element(ecc.begin(),ecc.end());
  M cadj[32]; for(int v=0;v<n;v++) cadj[v]=ALL&~adj[v]&~(1u<<v); int SW=degeneracy(cadj,ALL)+1;
  int id=n, g2=n, a2=0; for(M S=1;S<=ALL;S++){ int c=pc(S); M cn=closedN(S); if(c<id && cn==ALL && !(openN(S)&S)) id=c;
    if(c<g2){ bool ok=true; for(int v=0;v<n&&ok;v++) if(!(S>>v&1) && pc(adj[v]&S)<2) ok=false; if(ok) g2=c; }
    if(c>a2){ bool ok=true; for(M t=S;t;t&=t-1) if(pc(adj[__builtin_ctz(t)]&S)>1){ok=false;break;} if(ok) a2=c; } if(S==ALL) break; }
  if(which=="434d"){ M B=0; for(int v=0;v<n;v++) if(ecc[v]==diam) B|=1u<<v; M NB=closedN(B); int comp=0; M left=NB; while(left){ M c=left&(-left),fr=c; while(fr){ M nf=openN(fr)&NB&~c; c|=nf; fr=nf; } left&=~c; comp++; } return id-(SW-comp+2); }
  if(which=="434e"){ M C=0; for(int v=0;v<n;v++) if(ecc[v]==rad) C|=1u<<v; int eC=0; for(int v=0;v<n;v++){ int mn=99; for(M t=C;t;t&=t-1) mn=min(mn,D[v][__builtin_ctz(t)]); eC=max(eC,mn);} return id-(SW-eC+2); }
  if(which=="435"){ // G^2 degrees
    vector<int> d2(n); for(int v=0;v<n;v++){ int c=0; for(int w=0;w<n;w++) if(w!=v&&D[v][w]<=2) c++; d2[v]=c; } int mn=*min_element(d2.begin(),d2.end()); vector<int> A; for(int v=0;v<n;v++) if(d2[v]==mn) A.push_back(v); int e=0; for(int i=0;i<(int)A.size();i++) for(int j=i+1;j<(int)A.size();j++) if(D[A[i]][A[j]]<=2) e++;
    return a2-(SW+ceil((1+e)/3.0-1e-9)); }
  if(which=="393d"){ M P=0; for(int v=0;v<n;v++) if(deg[v]==1) P|=1u<<v; M NNP=openN(openN(P)); int Delta=*max_element(deg.begin(),deg.end()); M Mx=0; for(int v=0;v<n;v++) if(deg[v]==Delta) Mx|=1u<<v;
    vector<int> k4(n); for(int v=0;v<n;v++){ int c=0; M N=adj[v]; for(M t=N;t;t&=t-1){ int a=__builtin_ctz(t); for(M u=N&adj[a]&~((2u<<a)-1);u;u&=u-1){ int b=__builtin_ctz(u); c+=pc(N&adj[a]&adj[b]&~((2u<<b)-1)); } } k4[v]=c; } int km=*max_element(k4.begin(),k4.end()); int M4=0; for(int v=0;v<n;v++) if(k4[v]==km) M4++;
    return g2-(matchM(ALL&~NNP)+alphaM(ALL&~Mx)+M4); }
  return 0; }
int main(int argc,char**argv){ which=argv[1]; n=atoi(argv[2]); long iters=atol(argv[3]); rng.seed(atoi(argv[4])); double p=atof(argv[5]); ALL=(1u<<n)-1;
  for(int v=0;v<n;v++) adj[v]=0; for(int i=1;i<n;i++){ int j=rng()%i; adj[i]|=1u<<j; adj[j]|=1u<<i; } for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if((rng()%1000)/1000.0<p){ adj[i]|=1u<<j; adj[j]|=1u<<i; }
  double cur=score(),best=cur; M bestA[32]; memcpy(bestA,adj,sizeof adj); double T=1.0;
  for(long it=0;it<iters;it++){ int i=rng()%n,j=rng()%n; if(i==j) continue; adj[i]^=1u<<j; adj[j]^=1u<<i; double s=score();
    if(s>=cur || exp((s-cur)/T)>(rng()%1000000)/1e6){ cur=s; if(s>best){best=s; memcpy(bestA,adj,sizeof adj);} } else { adj[i]^=1u<<j; adj[j]^=1u<<i; } T=max(0.05,T*0.999); }
  memcpy(adj,bestA,sizeof adj); printf("%s n=%d best=%.3f edges:",which.c_str(),n,best); for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if(adj[i]>>j&1) printf(" %d-%d",i,j); printf("\n"); }
