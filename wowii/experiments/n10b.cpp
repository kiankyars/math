// Exhaustive battery, part 2: upper bounds on gamma_2, i and alpha_2 (graph6 on stdin, n <= 12).
#include <bits/stdc++.h>
using namespace std;
typedef unsigned M;
int n; M adj[16], cadj[16], ALL;
static inline int pc(M x){ return __builtin_popcount(x); }
void parse(const string& s){ int p=0; n=s[p++]-63; for(int i=0;i<n;i++) adj[i]=0; int val=0,k=6;
  for(int j=1;j<n;j++) for(int i=0;i<j;i++){ if(k==6){ val=s[p++]-63; k=0; } if((val>>(5-k))&1){ adj[i]|=1u<<j; adj[j]|=1u<<i; } k++; }
  ALL=(1u<<n)-1; for(int v=0;v<n;v++) cadj[v]=ALL&~adj[v]&~(1u<<v); }
static inline M openN(M S){ M r=0; for(M t=S;t;t&=t-1) r|=adj[__builtin_ctz(t)]; return r; }
bool connM(M m){ if(!m) return true; M seen=m&(-m),fr=seen; while(fr){ M nf=openN(fr)&m&~seen; seen|=nf; fr=nf; } return seen==m; }
int alphaM(M m){ if(!m) return 0; int v=__builtin_ctz(m); M rest=m&~(1u<<v); int a=alphaM(rest&~adj[v])+1; if(!(adj[v]&rest)) return a; return max(a,alphaM(rest)); }
int matchM(M m){ if(!m) return 0; int v=__builtin_ctz(m); M rest=m&~(1u<<v); int best=matchM(rest); for(M t=adj[v]&rest;t;t&=t-1){ int w=__builtin_ctz(t); best=max(best,1+matchM(rest&~(1u<<w))); } return best; }
int edgesIn(M m){ int e=0; for(M t=m;t;t&=t-1) e+=pc(adj[__builtin_ctz(t)]&m); return e/2; }
int residueOf(vector<int> d){ sort(d.rbegin(),d.rend()); while(!d.empty()&&d[0]>0){ int x=d[0]; d.erase(d.begin()); for(int i=0;i<x&&i<(int)d.size();i++) d[i]--; sort(d.rbegin(),d.rend()); } return d.size(); }
int pathCover(){ int N=1<<n; static M endset[1<<12]; static int cover[1<<12]; for(int m=0;m<N;m++) endset[m]=0; for(int v=0;v<n;v++) endset[1<<v]=1u<<v;
  for(int m=1;m<N;m++){ if(!endset[m]) continue; for(M t=endset[m];t;t&=t-1){ int v=__builtin_ctz(t); for(M u=adj[v]&~m;u;u&=u-1){ int w=__builtin_ctz(u); endset[m|(1<<w)]|=1u<<w; } } }
  cover[0]=0; for(int m=1;m<N;m++){ cover[m]=99; int low=m&-m; for(int sub=m;sub;sub=(sub-1)&m){ if(!(sub&low)) continue; if(endset[sub] && cover[m^sub]+1<cover[m]) cover[m]=cover[m^sub]+1; } } return cover[N-1]; }
int main(){ string s; map<string,long> fails; map<string,double> minsl; map<string,string> first; long cnt=0;
  auto F=[&](const string& k,double lhs,double rhs){ double sl=lhs-rhs; if(!minsl.count(k)||sl<minsl[k]) minsl[k]=sl; if(sl<-1e-9){ if(fails[k]++==0) first[k]=s; } else fails[k]+=0; };
  while(getline(cin,s)){ if(s.empty()) continue; parse(s); if(n<4) continue; cnt++;
    int D[16][16], ecc[16];
    for(int v=0;v<n;v++){ for(int w=0;w<n;w++) D[v][w]=99; D[v][v]=0; M seen=1u<<v,fr=seen; int d=0; while(fr){ M nf=openN(fr)&~seen; d++; for(M t=nf;t;t&=t-1) D[v][__builtin_ctz(t)]=d; seen|=nf; fr=nf; } ecc[v]=0; for(int w=0;w<n;w++) ecc[v]=max(ecc[v],D[v][w]); }
    int diam=0; for(int v=0;v<n;v++) diam=max(diam,ecc[v]);
    vector<int> deg(n); for(int v=0;v<n;v++) deg[v]=pc(adj[v]);
    int delta=*min_element(deg.begin(),deg.end()), Delta=*max_element(deg.begin(),deg.end());
    vector<int> sd=deg; sort(sd.begin(),sd.end());
    // subset loop: gamma, gamma_2, i, alpha_2
    int gam=n, g2=n, idom=n, a2=0;
    for(M S=1;S<=ALL;S++){ int c=pc(S); M on=openN(S);
      if(c<gam && ((on|S)==ALL)) gam=c;
      if(c<idom && ((on|S)==ALL) && !(on&S)) idom=c;
      if(c<g2){ bool ok=true; for(int v=0;v<n&&ok;v++) if(!(S>>v&1) && pc(adj[v]&S)<2) ok=false; if(ok) g2=c; }
      if(c>a2){ bool ok=true; for(M t=S;t&&ok;t&=t-1) if(pc(adj[__builtin_ctz(t)]&S)>1) ok=false; if(ok) a2=c; }
      if(S==ALL) break; }
    int alpha=alphaM(ALL), mu=matchM(ALL);
    M A=0,A2=0,P=0,Mx=0,B=0; for(int v=0;v<n;v++){ if(deg[v]==delta) A|=1u<<v; if(deg[v]==2) A2|=1u<<v; if(deg[v]==1) P|=1u<<v; if(deg[v]==Delta) Mx|=1u<<v; if(ecc[v]==diam) B|=1u<<v; }
    int lam[16], lmax=0, lmin=99; for(int v=0;v<n;v++){ lam[v]=alphaM(adj[v]); lmax=max(lmax,lam[v]); lmin=min(lmin,lam[v]); }
    M X=0, Mlmin=0; for(int v=0;v<n;v++){ if(lam[v]==lmax) X|=1u<<v; if(lam[v]==lmin) Mlmin|=1u<<v; }
    // 382c, 382d
    { double ea=0; int ca=0; for(M t=A;t;t&=t-1){ ea+=ecc[__builtin_ctz(t)]; ca++; } ea/=ca;
      F("382c", (alpha*ea+pc(B))/2.0, g2); F("382d", diam*(alpha+pc(X))/2.0, g2); }
    // 387 upper median
    F("387", n - sd[n/2] + 1, g2);
    // 392b-f, 395a
    { int muVA=matchM(ALL&~A); int c2=0; for(int v=0;v<n;v++) if(pc(adj[v]&A2)==1) c2++;
      F("392b", muVA+pc(A)+c2, g2);
      int cut=0; for(int v=0;v<n;v++) if(!connM(ALL&~(1u<<v))) cut++;
      F("392c", muVA+pc(A)+cut, g2);
      M NNP=openN(openN(P)); F("392d", mu+matchM(ALL&~NNP)+pc(A), g2);
      M NA2=openN(A2); F("392e", mu+matchM(NA2)+pc(A), g2);
      M NA=openN(A); int cN=0; for(int v=0;v<n;v++) if(pc(adj[v]&NA)==1) cN++;
      F("392f", mu+matchM(NA2)+cN, g2);
      map<int,int> fr; for(int v=0;v<n;v++) fr[deg[v]]++; int bestc=0,mode=0; for(auto&[d,c]:fr) if(c>bestc){ bestc=c; mode=d; }
      int nm=fr[mode]; F("395a", nm+muVA+matchM(NA2), g2); }
    // 399c: WP of complement = largest k with at least k vertices of complement-degree >= k-1
    { int wp=0; for(int k=1;k<=n;k++){ int c=0; for(int v=0;v<n;v++) if(n-1-deg[v]>=k-1) c++; if(c>=k) wp=k; }
      F("399c", 2.0/3*wp+2*pc(Mlmin), g2); }
    // i-family
    { int p=pathCover(); M NA=openN(A);
      F("418b", alphaM(ALL&~A)+edgesIn(NA)*p, idom);
      int maxNe=0; for(int u=0;u<n;u++) for(M t=adj[u]&~((1u<<(u+1))-1);t;t&=t-1){ int w=__builtin_ctz(t); maxNe=max(maxNe,pc(adj[u]|adj[w])); }
      F("421b", gam*floor(0.5*maxNe-1+1e-9), idom);
      M NX=X|openN(X); F("421c", gam*(pc(NX)-3), idom);
      F("422a", alphaM(ALL&~Mx)+2*(edgesIn(Mx)/3), idom);
      M Ah=0; for(int v=0;v<n;v++) if(2*deg[v]<=n) Ah|=1u<<v; int dV=0; for(M t=ALL&~Ah;t;t&=t-1) dV=max(dV,pc(adj[__builtin_ctz(t)]&~Ah));
      F("422c", alphaM(Ah)+2*(dV/3), idom);
      int T[16],Tmax=0; for(int v=0;v<n;v++){ T[v]=0; for(int w=0;w<n;w++) T[v]+=D[v][w]; Tmax=max(Tmax,T[v]); } int nT=0; for(int v=0;v<n;v++) if(T[v]==Tmax) nT++;
      set<int> dd(deg.begin(),deg.end()); F("431c", residueOf(deg)*nT+(int)dd.size(), idom);
      M H=0; for(int v=0;v<n;v++) if(2*deg[v]>n) H|=1u<<v;
      F("448a", pc(H)+edgesIn(ALL&~H)+p, a2); }
  }
  printf("graphs=%ld\n",cnt); for(auto&[k,v]:minsl) printf("%-8s fails=%-8ld minslack=%.3f %s\n",k.c_str(),fails[k],v,first[k].c_str()); }
