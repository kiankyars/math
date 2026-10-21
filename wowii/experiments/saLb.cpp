#include <bits/stdc++.h>
using namespace std; typedef unsigned M; int n; M adj[32]; M ALL; mt19937_64 rng(1); string which;
inline int pc(M x){ return __builtin_popcount(x); }
M openN(M S){ M r=0; for(M t=S;t;t&=t-1) r|=adj[__builtin_ctz(t)]; return r; }
M closedN(M S){ return S|openN(S); }
bool connM(M m){ if(!m) return true; M seen=m&(-m),fr=seen; while(fr){ M nf=openN(fr)&m&~seen; seen|=nf; fr=nf; } return seen==m; }
bool bipM(M m){ M left=m; while(left){ M c0=left&(-left),c1=0,fr0=c0,fr1=0; while(fr0||fr1){ M n1=openN(fr0)&m, n0=openN(fr1)&m; if((n1&c0)||(n0&c1)) return false; n1&=~c1; n0&=~c0; c1|=n1; c0|=n0; fr0=n0; fr1=n1; } left&=~(c0|c1);} return true; }
int edgesIn(M m){ int e=0; for(M t=m;t;t&=t-1) e+=pc(adj[__builtin_ctz(t)]&m); return e/2; }
int alphaM(M m){ if(!m) return 0; int v=__builtin_ctz(m); M rest=m&~(1u<<v); int a=alphaM(rest&~adj[v])+1; if(!(adj[v]&rest)) return a; return max(a,alphaM(rest)); }
int matchM(M m){ if(!m) return 0; int v=__builtin_ctz(m); M rest=m&~(1u<<v); int best=matchM(rest); for(M t=adj[v]&rest;t;t&=t-1){ int w=__builtin_ctz(t); best=max(best,1+matchM(rest&~(1u<<w))); if(best*2>=pc(m)) break; } return best; }
struct Inv{ int Ls,b,gamma,gamma2,alpha,tree; };
Inv subsets(bool needLb,bool needG2,bool needTree){ Inv I; I.gamma=n; I.gamma2=n; int gc=n; I.b=1; I.tree=1; I.alpha=0;
  for(M S=1;S<=ALL;S++){ int c=pc(S); M cn=closedN(S);
    if(c<I.gamma && cn==ALL) I.gamma=c;
    if(needLb){ if(c<gc && cn==ALL && connM(S)) gc=c; if(c>I.b && bipM(S)) I.b=c; }
    if(needG2 && c<I.gamma2){ bool ok=true; for(int v=0;v<n&&ok;v++) if(!(S>>v&1) && pc(adj[v]&S)<2) ok=false; if(ok) I.gamma2=c; }
    if(needTree && c>I.tree && edgesIn(S)==c-1 && connM(S)) I.tree=c;
    if(S==ALL) break; }
  I.Ls=n-gc; I.alpha=alphaM(ALL); return I; }
double score(){ if(!connM(ALL)) return -1e9;
  int D[32][32]; for(int v=0;v<n;v++){ for(int w=0;w<n;w++) D[v][w]=-1; D[v][v]=0; M seen=1u<<v,fr=seen; int d=0; while(fr){ M nf=openN(fr)&~seen; d++; for(M t=nf;t;t&=t-1) D[v][__builtin_ctz(t)]=d; seen|=nf; fr=nf; } }
  vector<int> deg(n),ecc(n); for(int v=0;v<n;v++){ deg[v]=pc(adj[v]); ecc[v]=0; for(int w=0;w<n;w++) ecc[v]=max(ecc[v],D[v][w]); }
  int Delta=*max_element(deg.begin(),deg.end()), delta=*min_element(deg.begin(),deg.end()); int rad=*min_element(ecc.begin(),ecc.end()), diam=*max_element(ecc.begin(),ecc.end());
  vector<int> lam(n); int lmax=0; for(int v=0;v<n;v++){ lam[v]=alphaM(adj[v]); lmax=max(lmax,lam[v]); }
  bool Lb = which=="174"||which=="177"||which=="179"||which=="180"||which=="183"||which=="185"||which=="165"||which=="166";
  bool G2 = which[0]=='3'; bool Tr = which=="84";
  Inv I=subsets(Lb,G2,Tr);
  if(which=="174") return (n+lmax-1)-(I.Ls+I.b);
  if(which=="177"){ vector<int> ds=deg; sort(ds.begin(),ds.end()); return 2*I.alpha+ds[1]-(I.Ls+I.b); }
  if(which=="179") return Delta+I.gamma+lmax-(I.Ls+I.b);
  if(which=="180"){ int demax=0; for(int v=0;v<n;v++){ int e=0; for(int w=0;w<n;w++) if(D[v][w]%2==0) e++; demax=max(demax,e);} return 1+I.alpha+demax-(I.Ls+I.b); }
  if(which=="183"||which=="185"){ int D2max=0; for(int v=0;v<n;v++){ int c=0; for(int w=0;w<n;w++) if(w!=v&&D[v][w]<=2) c++; D2max=max(D2max,c);} int rad2=99; for(int v=0;v<n;v++){ int e=0; for(int w=0;w<n;w++) e=max(e,(D[v][w]+1)/2); rad2=min(rad2,e);} double avg2=0; for(int v=0;v<n;v++) for(int w=0;w<n;w++) if(v!=w) avg2+=(D[v][w]+1)/2; avg2/=(double)n*(n-1);
    if(which=="183") return D2max+2*rad2-(I.Ls+I.b); return D2max+2*avg2-(I.Ls+I.b); }
  M Mx=0; for(int v=0;v<n;v++) if(deg[v]==Delta) Mx|=1u<<v; int NM=pc(openN(Mx)&~Mx);
  if(which=="165") return ceil(sqrt(2.0*NM)-1e-9)-I.Ls;
  if(which=="166") return NM/sqrt((double)rad)-I.Ls;
  if(which=="84") return 2.0*rad/delta-I.tree;
  int g2=I.gamma2;
  M Ad=0,A2=0,T=0,P=0; for(int v=0;v<n;v++){ if(deg[v]==delta) Ad|=1u<<v; if(deg[v]<=2) A2|=1u<<v; if(deg[v]==2) T|=1u<<v; if(deg[v]==1) P|=1u<<v; }
  if(which=="382c"){ double eA=0; for(M t=Ad;t;t&=t-1) eA+=ecc[__builtin_ctz(t)]; eA/=pc(Ad); int B=0; for(int v=0;v<n;v++) if(ecc[v]==diam) B++; return g2-(I.alpha*eA+B)/2.0; }
  if(which=="382d"){ int X=0; for(int v=0;v<n;v++) if(lam[v]==lmax) X++; return g2-diam*(I.alpha+X)/2.0; }
  if(which=="384b"){ set<int> Ts; for(int v=0;v<n;v++) Ts.insert(edgesIn(adj[v])); return g2-floor(n-Ts.size()/2.0+1e-9); }
  if(which=="387"){ vector<int> ds=deg; sort(ds.begin(),ds.end()); int m=ds[n/2]; return g2-(n-m+1); }
  int mVA=matchM(ALL&~Ad);
  if(which=="392b"){ int c2=0; for(int v=0;v<n;v++) if(pc(adj[v]&T)==1) c2++; return g2-(mVA+pc(Ad)+c2); }
  if(which=="392c"){ int cutv=0; for(int v=0;v<n;v++) if(!connM(ALL&~(1u<<v))) cutv++; return g2-(mVA+pc(Ad)+cutv); }
  int mu=matchM(ALL);
  if(which=="392d"){ M NNP=openN(openN(P)); return g2-(mu+matchM(ALL&~NNP)+pc(Ad)); }
  if(which=="392e") return g2-(mu+matchM(openN(T))+pc(Ad));
  if(which=="392f"){ M NA=openN(Ad); int cf=0; for(int v=0;v<n;v++) if(pc(adj[v]&NA)==1) cf++; return g2-(mu+matchM(openN(T))+cf); }
  return 0; }
int main(int argc,char**argv){ which=argv[1]; n=atoi(argv[2]); long iters=atol(argv[3]); rng.seed(atoi(argv[4])); double p=atof(argv[5]); ALL=(1u<<n)-1;
  for(int v=0;v<n;v++) adj[v]=0; for(int i=1;i<n;i++){ int j=rng()%i; adj[i]|=1u<<j; adj[j]|=1u<<i; } for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if((rng()%1000)/1000.0<p){ adj[i]|=1u<<j; adj[j]|=1u<<i; }
  double cur=score(),best=cur; M bestA[32]; memcpy(bestA,adj,sizeof adj); double T=1.0;
  for(long it=0;it<iters;it++){ int i=rng()%n,j=rng()%n; if(i==j) continue; adj[i]^=1u<<j; adj[j]^=1u<<i; double s=score();
    if(s>=cur || exp((s-cur)/T)>(rng()%1000000)/1e6){ cur=s; if(s>best){best=s; memcpy(bestA,adj,sizeof adj);} } else { adj[i]^=1u<<j; adj[j]^=1u<<i; } T=max(0.05,T*0.999); }
  memcpy(adj,bestA,sizeof adj); printf("%s n=%d best=%.3f edges:",which.c_str(),n,best); for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if(adj[i]>>j&1) printf(" %d-%d",i,j); printf("\n"); }
