#include <bits/stdc++.h>
using namespace std; typedef unsigned M; int n; M adj[32]; M ALL; mt19937_64 rng(1); string which;
inline int pc(M x){ return __builtin_popcount(x); }
M openN(M S){ M r=0; for(M t=S;t;t&=t-1) r|=adj[__builtin_ctz(t)]; return r; }
M closedN(M S){ return S|openN(S); }
bool connM(M m){ if(!m) return true; M seen=m&(-m),fr=seen; while(fr){ M nf=openN(fr)&m&~seen; seen|=nf; fr=nf; } return seen==m; }
int edgesIn(M m){ int e=0; for(M t=m;t;t&=t-1) e+=pc(adj[__builtin_ctz(t)]&m); return e/2; }
int alphaM(M m){ if(!m) return 0; int v=__builtin_ctz(m); M rest=m&~(1u<<v); int a=alphaM(rest&~adj[v])+1; if(!(adj[v]&rest)) return a; return max(a,alphaM(rest)); }
int matchM(M m){ if(!m) return 0; int v=__builtin_ctz(m); M rest=m&~(1u<<v); int best=matchM(rest); for(M t=adj[v]&rest;t;t&=t-1){ int w=__builtin_ctz(t); best=max(best,1+matchM(rest&~(1u<<w))); if(best*2>=pc(m)) break; } return best; }
int gammaM(M m){ if(!m) return 0; int best=pc(m); for(M S=m;;S=(S-1)&m){ int c=pc(S); if(c<best && (closedN(S)&m)==m) best=c; if(!S) break; } return best; }
struct R{ int gamma,gammat,gamma2,idom,a2; };
R subs(){ R r{n,n,n,n,0}; for(M S=1;S<=ALL;S++){ int c=pc(S); M cn=closedN(S); if(c<r.gamma && cn==ALL) r.gamma=c; if(c<r.gammat && openN(S)==ALL) r.gammat=c; if(c<r.idom && cn==ALL && !(openN(S)&S)) r.idom=c;
    if(c<r.gamma2){ bool ok=true; for(int v=0;v<n&&ok;v++) if(!(S>>v&1) && pc(adj[v]&S)<2) ok=false; if(ok) r.gamma2=c; }
    if(c>r.a2){ bool ok=true; for(M t=S;t;t&=t-1) if(pc(adj[__builtin_ctz(t)]&S)>1){ok=false;break;} if(ok) r.a2=c; } if(S==ALL) break; } return r; }
double score(){ if(!connM(ALL)) return -1e9; R r=subs(); vector<int> deg(n),lam(n); for(int v=0;v<n;v++){ deg[v]=pc(adj[v]); lam[v]=alphaM(adj[v]); }
  int delta=*min_element(deg.begin(),deg.end()), Delta=*max_element(deg.begin(),deg.end()); int lmin=*min_element(lam.begin(),lam.end()), lmax=*max_element(lam.begin(),lam.end());
  M Ad=0,AD=0,A2=0,Mlmin=0,Mlmax=0; for(int v=0;v<n;v++){ if(deg[v]==delta) Ad|=1u<<v; if(deg[v]==Delta) AD|=1u<<v; if(deg[v]==2) A2|=1u<<v; if(lam[v]==lmin) Mlmin|=1u<<v; if(lam[v]==lmax) Mlmax|=1u<<v; }
  if(which=="394") return r.gamma2-(matchM(ALL)+edgesIn(A2)+pc(Mlmin));
  if(which=="395a"){ map<int,int> fr; for(int d:deg) fr[d]++; int bc=0,mm=0; for(auto&[d,c]:fr) if(c>bc){bc=c;mm=d;} return r.gamma2-(bc+matchM(ALL&~Ad)+matchM(openN(A2))); }
  if(which=="402"){ int iso=0; for(M t=Ad;t;t&=t-1) if(!(adj[__builtin_ctz(t)]&Ad)) iso++; int c1=0; for(int v=0;v<n;v++) if(pc(adj[v]&AD)==1) c1++; return r.gamma2-2*(iso+c1+r.gammat); }
  if(which=="421b"){ int Nmax=0; for(int u=0;u<n;u++) for(M t=adj[u];t;t&=t-1){ int w=__builtin_ctz(t); Nmax=max(Nmax,pc(adj[u]|adj[w])); } return r.idom-r.gamma*floor(0.5*Nmax-1+1e-9); }
  if(which=="421c") return r.idom-r.gamma*(pc(closedN(Mlmax))-3);
  if(which=="422a") return r.idom-(alphaM(ALL&~AD)+2*(edgesIn(AD)/3));
  if(which=="422b"){ int g=gammaM(ALL&~AD); return r.idom-(alphaM(AD)+g*g); }
  if(which=="422c"){ M Ah=0; for(int v=0;v<n;v++) if(2*deg[v]<=n) Ah|=1u<<v; int dm=0; for(M t=ALL&~Ah;t;t&=t-1) dm=max(dm,pc(adj[__builtin_ctz(t)]&~Ah)); return r.idom-(alphaM(Ah)+2*(dm/3)); }
  if(which=="426") return r.idom-(n-gammaM(openN(AD)));
  if(which=="438a"){ int m=0; for(int v=0;v<n;v++) m+=deg[v]; m/=2; vector<int> dd=deg; sort(dd.begin(),dd.end()); int a=0,sm=0; for(int i=0;i<n;i++){ sm+=dd[i]; if(sm<=m) a=i+1; else break; }
    M Rm=ALL&~Ad; vector<int> rd; int rm=0; for(M t=Rm;t;t&=t-1){ int v=__builtin_ctz(t); rd.push_back(pc(adj[v]&Rm)); rm+=pc(adj[v]&Rm);} rm/=2; sort(rd.begin(),rd.end()); int aR=0; sm=0; for(int i=0;i<(int)rd.size();i++){ sm+=rd[i]; if(sm<=rm) aR=i+1; else break; }
    return r.a2-(a+aR+edgesIn(Ad)); }
  return 0; }
int main(int argc,char**argv){ which=argv[1]; n=atoi(argv[2]); long iters=atol(argv[3]); rng.seed(atoi(argv[4])); double p=atof(argv[5]); ALL=(1u<<n)-1;
  for(int v=0;v<n;v++) adj[v]=0; for(int i=1;i<n;i++){ int j=rng()%i; adj[i]|=1u<<j; adj[j]|=1u<<i; } for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if((rng()%1000)/1000.0<p){ adj[i]|=1u<<j; adj[j]|=1u<<i; }
  double cur=score(),best=cur; M bestA[32]; memcpy(bestA,adj,sizeof adj); double T=1.0;
  for(long it=0;it<iters;it++){ int i=rng()%n,j=rng()%n; if(i==j) continue; adj[i]^=1u<<j; adj[j]^=1u<<i; double s=score();
    if(s>=cur || exp((s-cur)/T)>(rng()%1000000)/1e6){ cur=s; if(s>best){best=s; memcpy(bestA,adj,sizeof adj);} } else { adj[i]^=1u<<j; adj[j]^=1u<<i; } T=max(0.05,T*0.999); }
  memcpy(adj,bestA,sizeof adj); printf("%s n=%d best=%.3f edges:",which.c_str(),n,best); for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if(adj[i]>>j&1) printf(" %d-%d",i,j); printf("\n"); }
