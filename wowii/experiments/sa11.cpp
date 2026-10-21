#include <bits/stdc++.h>
using namespace std; typedef unsigned M; int n; M adj[32]; M ALL; mt19937_64 rng(1); string which;
inline int pc(M x){ return __builtin_popcount(x); }
M openN(M S){ M r=0; for(M t=S;t;t&=t-1) r|=adj[__builtin_ctz(t)]; return r; }
M closedN(M S){ return S|openN(S); }
bool connM(M m){ if(!m) return true; M seen=m&(-m),fr=seen; while(fr){ M nf=openN(fr)&m&~seen; seen|=nf; fr=nf; } return seen==m; }
int comps(M m){ int c=0; M left=m; while(left){ M s=left&(-left),fr=s; while(fr){ M nf=openN(fr)&m&~s; s|=nf; fr=nf; } left&=~s; c++; } return c; }
int edgesIn(M m){ int e=0; for(M t=m;t;t&=t-1) e+=pc(adj[__builtin_ctz(t)]&m); return e/2; }
int alphaM(M m){ if(!m) return 0; int v=__builtin_ctz(m); M rest=m&~(1u<<v); int a=alphaM(rest&~adj[v])+1; if(!(adj[v]&rest)) return a; return max(a,alphaM(rest)); }
int matchM(M m){ if(!m) return 0; int v=__builtin_ctz(m); M rest=m&~(1u<<v); if(!(adj[v]&rest)) return matchM(rest); int best=matchM(rest); for(M t=adj[v]&rest;t;t&=t-1){ int w=__builtin_ctz(t); best=max(best,1+matchM(rest&~(1u<<w))); if(best*2>=pc(m)-1) break; } return best; }
// k-domination B&B
int bestK,K;
void recK(M S, M X){ if(pc(S)>=bestK) return; int w=-1;
  for(int v=0;v<n;v++){ if(S>>v&1) continue; if(pc(adj[v]&S)<K){ w=v; break; } }
  if(w<0){ bestK=pc(S); return; }
  M U=ALL&~S&~X;
  // feasibility for all excluded
  for(M t=X;t;t&=t-1){ int x=__builtin_ctz(t); if(pc(adj[x]&S)+pc(adj[x]&U)<K) return; }
  if(!(X>>w&1)){ recK(S|(1u<<w),X); recK(S,X|(1u<<w)); return; }
  M cand=adj[w]&U; if(!cand) return; int u=__builtin_ctz(cand); recK(S|(1u<<u),X); recK(S,X|(1u<<u)); }
int kdom(int k){ K=k; bestK=n+1; recK(0,0); return bestK; }
int bestI; void recI(M dom, M avail, int k){ if(dom==ALL){ bestI=min(bestI,k); return; } if(k+1>=bestI) return; int v=__builtin_ctz(~dom&ALL); M cand=(adj[v]|(1u<<v))&avail; for(M t=cand;t;t&=t-1){ int x=__builtin_ctz(t); M cx=adj[x]|(1u<<x); recI(dom|cx, avail&~cx, k+1); } }
int idom(){ bestI=n+1; recI(0,ALL,0); return bestI; }
int bestA2; void recA2(M S, M C){ int s=pc(S); if(s>bestA2) bestA2=s; if(s+pc(C)<=bestA2||!C) return; int v=__builtin_ctz(C); M C2=C&~(1u<<v); M S2=S|(1u<<v); M full=0; for(M t=S2;t;t&=t-1){ int x=__builtin_ctz(t); if(adj[x]&S2) full|=1u<<x; } M nc=0; for(M t=C2;t;t&=t-1){ int w=__builtin_ctz(t); M nw=adj[w]&S2; if(pc(nw)>=2||(nw&full)) continue; nc|=1u<<w; } recA2(S2,nc); recA2(S,C2); }
int alpha2(){ bestA2=0; recA2(0,ALL); return bestA2; }
int degeneracy(const M* A, M m){ int best=0; M left=m; while(left){ int mn=99,v=-1; for(M t=left;t;t&=t-1){ int x=__builtin_ctz(t); int d=pc(A[x]&left); if(d<mn){mn=d;v=x;} } best=max(best,mn); left&=~(1u<<v); } return best; }
int annih(M m){ vector<int> d; for(M t=m;t;t&=t-1) d.push_back(pc(adj[__builtin_ctz(t)]&m)); sort(d.begin(),d.end()); int e=edgesIn(m); int s=0,k=0; for(int x:d){ if(s+x<=e){ s+=x; k++; } else break; } return k; }
double score(){ if(!connM(ALL)) return -1e9;
  int D[32][32]; for(int v=0;v<n;v++){ for(int w=0;w<n;w++) D[v][w]=99; D[v][v]=0; M seen=1u<<v,fr=seen; int d=0; while(fr){ M nf=openN(fr)&~seen; d++; for(M t=nf;t;t&=t-1) D[v][__builtin_ctz(t)]=d; seen|=nf; fr=nf; } }
  vector<int> deg(n),ecc(n); for(int v=0;v<n;v++){ deg[v]=pc(adj[v]); ecc[v]=0; for(int w=0;w<n;w++) ecc[v]=max(ecc[v],D[v][w]); }
  int rad=*min_element(ecc.begin(),ecc.end()), diam=*max_element(ecc.begin(),ecc.end());
  int delta=*min_element(deg.begin(),deg.end()), Delta=*max_element(deg.begin(),deg.end());
  M A=0,Mx=0,P=0,A2=0,A3=0,B=0,C=0; for(int v=0;v<n;v++){ if(deg[v]==delta) A|=1u<<v; if(deg[v]==Delta) Mx|=1u<<v; if(deg[v]==1) P|=1u<<v; if(deg[v]==2) A2|=1u<<v; if(deg[v]>=3) A3|=1u<<v; if(ecc[v]==diam) B|=1u<<v; if(ecc[v]==rad) C|=1u<<v; }
  M cadj[32]; for(int v=0;v<n;v++) cadj[v]=ALL&~adj[v]&~(1u<<v);
  auto WPc=[&](){ vector<int> cd(n); for(int v=0;v<n;v++) cd[v]=n-1-deg[v]; sort(cd.rbegin(),cd.rend()); int WP=0; for(int i=0;i<n;i++) WP=max(WP,min(cd[i]+1,i+1)); return WP; };
  auto lamSets=[&](M& mn, M& mx){ vector<int> lam(n); for(int v=0;v<n;v++) lam[v]=alphaM(adj[v]); int a=*min_element(lam.begin(),lam.end()), b=*max_element(lam.begin(),lam.end()); mn=mx=0; for(int v=0;v<n;v++){ if(lam[v]==a) mn|=1u<<v; if(lam[v]==b) mx|=1u<<v; } };
  if(which=="382c"){ double ea=0; for(M t=A;t;t&=t-1) ea+=ecc[__builtin_ctz(t)]; ea/=pc(A); return kdom(2)-(alphaM(ALL)*ea+pc(B))/2.0; }
  if(which=="382d"){ M mn,mx; lamSets(mn,mx); return kdom(2)-diam*(alphaM(ALL)+pc(mx))/2.0; }
  if(which=="387"){ vector<int> d=deg; sort(d.begin(),d.end()); return kdom(2)-(n-d[n/2]+1); }
  if(which=="392b"){ int c=0; for(int v=0;v<n;v++) if(pc(adj[v]&A2)==1) c++; return kdom(2)-(matchM(ALL&~A)+pc(A)+c); }
  if(which=="392c"){ int c=0; for(int v=0;v<n;v++) if(!connM(ALL&~(1u<<v))) c++; return kdom(2)-(matchM(ALL&~A)+pc(A)+c); }
  if(which=="392d"){ return kdom(2)-(matchM(ALL)+matchM(ALL&~openN(openN(P)))+pc(A)); }
  if(which=="392e"){ return kdom(2)-(matchM(ALL)+matchM(openN(A2))+pc(A)); }
  if(which=="392f"){ M NA=openN(A); int c=0; for(int v=0;v<n;v++) if(pc(adj[v]&NA)==1) c++; return kdom(2)-(matchM(ALL)+matchM(openN(A2))+c); }
  if(which=="395a"){ vector<int> f(n,0); for(int v=0;v<n;v++) f[deg[v]]++; int bf=0,md=0; for(int d=0;d<n;d++) if(f[d]>bf){bf=f[d];md=d;} return kdom(2)-(bf+matchM(ALL&~A)+matchM(openN(A2))); }
  if(which=="399b"){ int a3=alphaM(A3); if(a3==0) return -1e9; return kdom(2)-(WPc()+3/a3); }
  if(which=="399c"){ M mn,mx; lamSets(mn,mx); return kdom(2)-(2.0/3*WPc()+2*pc(mn)); }
  if(which=="418c"){ int al=alphaM(ALL); M core=0; for(int v=0;v<n;v++) if(alphaM(ALL&~(1u<<v))<al) core|=1u<<v; return idom()-(alphaM(ALL&~A)+edgesIn(openN(A))+pc(A&core)); }
  if(which=="421b"){ int mx=0; for(int u=0;u<n;u++) for(M t=adj[u]&~((2u<<u)-1);t;t&=t-1){ int v=__builtin_ctz(t); mx=max(mx,pc(adj[u]|adj[v])); } return idom()-kdom(1)*floor(0.5*mx-1+1e-9); }
  if(which=="421c"){ M mn,mx; lamSets(mn,mx); return idom()-kdom(1)*(pc(closedN(mx))-3); }
  if(which=="422a"){ return idom()-(alphaM(ALL&~Mx)+2*(edgesIn(Mx)/3)); }
  if(which=="422c"){ M Ah=0; for(int v=0;v<n;v++) if(2*deg[v]<=n) Ah|=1u<<v; M R=ALL&~Ah; int dR=0; for(M t=R;t;t&=t-1) dR=max(dR,pc(adj[__builtin_ctz(t)]&R)); return idom()-(alphaM(Ah)+2*(dR/3)); }
  if(which=="434d"){ return idom()-(degeneracy(cadj,ALL)+1-comps(closedN(B))+2); }
  if(which=="434e"){ int eC=0; for(int v=0;v<n;v++){ int mn=99; for(M t=C;t;t&=t-1) mn=min(mn,D[v][__builtin_ctz(t)]); eC=max(eC,mn);} return idom()-(degeneracy(cadj,ALL)+1-eC+2); }
  if(which=="435"){ vector<int> d2(n); M a2m[32]; for(int v=0;v<n;v++){ a2m[v]=0; for(int w=0;w<n;w++) if(w!=v&&D[v][w]<=2) a2m[v]|=1u<<w; d2[v]=pc(a2m[v]); } int mn=*min_element(d2.begin(),d2.end()); M A2s=0; for(int v=0;v<n;v++) if(d2[v]==mn) A2s|=1u<<v; int e=0; for(M t=A2s;t;t&=t-1) e+=pc(a2m[__builtin_ctz(t)]&A2s); e/=2;
    return alpha2()-(degeneracy(cadj,ALL)+1+ceil((1+e)/3.0-1e-9)); }
  if(which=="438a"){ return alpha2()-(annih(ALL)+annih(ALL&~A)+edgesIn(A)); }
  if(which=="chk"){ int g1=n,g2=n,id=n,a2=0; for(M T=1;T<=ALL;T++){ int c=pc(T); bool d1=true,d2=true; for(int v=0;v<n;v++) if(!(T>>v&1)){ int k=pc(adj[v]&T); if(k<1) d1=false; if(k<2) d2=false; } if(d1&&c<g1) g1=c; if(d2&&c<g2) g2=c; if(d1&&!(openN(T)&T)&&c<id) id=c; bool ok=true; for(M t=T;t;t&=t-1) if(pc(adj[__builtin_ctz(t)]&T)>1) ok=false; if(ok&&c>a2) a2=c; if(T==ALL) break; }
    return abs(g1-kdom(1))+abs(g2-kdom(2))+abs(id-idom())+abs(a2-alpha2()); }
  return 0; }
void parse(const string& s){ int p=0; n=s[p++]-63; for(int i=0;i<n;i++) adj[i]=0; int val=0,k=6;
  for(int j=1;j<n;j++) for(int i=0;i<j;i++){ if(k==6){ val=s[p++]-63; k=0;} if(val>>(5-k)&1){ adj[i]|=1u<<j; adj[j]|=1u<<i;} k++; } }
int main(int argc,char**argv){ which=argv[1]; n=atoi(argv[2]); long iters=atol(argv[3]); rng.seed(atoi(argv[4])); double p=atof(argv[5]); ALL=(1u<<n)-1;
  if(iters==0){ string s; long cnt=0,tot=0; double mx=-1e9; while(getline(cin,s)){ parse(s); ALL=(1u<<n)-1; double sc=score(); tot++; mx=max(mx,sc); if(sc>1e-9){ cnt++; if(cnt<=3) printf("CE %s %s %.3f\n",which.c_str(),s.c_str(),sc);} } printf("%s n=%d tot=%ld ce=%ld max=%.3f\n",which.c_str(),n,tot,cnt,mx); return 0; }
  for(int v=0;v<n;v++) adj[v]=0; for(int i=1;i<n;i++){ int j=rng()%i; adj[i]|=1u<<j; adj[j]|=1u<<i; } for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if((rng()%1000)/1000.0<p){ adj[i]|=1u<<j; adj[j]|=1u<<i; }
  double cur=score(),best=cur; M bestA[32]; memcpy(bestA,adj,sizeof adj); double T=1.0;
  for(long it=0;it<iters;it++){ int i=rng()%n,j=rng()%n; if(i==j) continue; adj[i]^=1u<<j; adj[j]^=1u<<i; double s=score();
    if(s>=cur || exp((s-cur)/T)>(rng()%1000000)/1e6){ cur=s; if(s>best){best=s; memcpy(bestA,adj,sizeof adj);} } else { adj[i]^=1u<<j; adj[j]^=1u<<i; } T=max(0.05,T*0.9995); }
  memcpy(adj,bestA,sizeof adj); printf("%s n=%d best=%.3f edges:",which.c_str(),n,best); for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if(adj[i]>>j&1) printf(" %d-%d",i,j); printf("\n"); }
