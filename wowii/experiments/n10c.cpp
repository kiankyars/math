// Exhaustive battery, part 3: lower bounds involving tree(G) and L_s (graph6 on stdin, n <= 12).
#include <bits/stdc++.h>
using namespace std;
typedef unsigned M;
int n; M adj[16], ALL;
static inline int pc(M x){ return __builtin_popcount(x); }
void parse(const string& s){ int p=0; n=s[p++]-63; for(int i=0;i<n;i++) adj[i]=0; int val=0,k=6;
  for(int j=1;j<n;j++) for(int i=0;i<j;i++){ if(k==6){ val=s[p++]-63; k=0; } if((val>>(5-k))&1){ adj[i]|=1u<<j; adj[j]|=1u<<i; } k++; }
  ALL=(1u<<n)-1; }
static inline M openN(M S){ M r=0; for(M t=S;t;t&=t-1) r|=adj[__builtin_ctz(t)]; return r; }
bool connM(M m){ if(!m) return true; M seen=m&(-m),fr=seen; while(fr){ M nf=openN(fr)&m&~seen; seen|=nf; fr=nf; } return seen==m; }
int alphaM(M m){ if(!m) return 0; int v=__builtin_ctz(m); M rest=m&~(1u<<v); int a=alphaM(rest&~adj[v])+1; if(!(adj[v]&rest)) return a; return max(a,alphaM(rest)); }
int bestTr; void recTr(M S, M X){ int s=pc(S); if(s>bestTr) bestTr=s; M fr=openN(S)&~S&~X; M cand=0; for(M t=fr;t;t&=t-1){ int w=__builtin_ctz(t); if(pc(adj[w]&S)==1) cand|=1u<<w; }
  M avail=ALL&~X&~S; M reach=cand, f=cand; while(f){ M nf=openN(f)&avail&~reach; reach|=nf; f=nf; } if(s+pc(reach)<=bestTr) return; if(!cand) return;
  int w=__builtin_ctz(cand); recTr(S|(1u<<w),X); recTr(S,X|(1u<<w)); }
int treeN(){ bestTr=1; for(int v=0;v<n;v++){ M X=(1u<<v)-1; recTr(1u<<v,X); } return bestTr; }
int main(){ string s; map<string,long> fails; map<string,double> minsl; map<string,string> first; long cnt=0;
  auto F=[&](const string& k,double lhs,double rhs){ double sl=lhs-rhs; if(!minsl.count(k)||sl<minsl[k]) minsl[k]=sl; if(sl<-1e-9){ if(fails[k]++==0) first[k]=s; } else fails[k]+=0; };
  while(getline(cin,s)){ if(s.empty()) continue; parse(s); if(n<3) continue; cnt++;
    int D[16][16], ecc[16];
    for(int v=0;v<n;v++){ for(int w=0;w<n;w++) D[v][w]=99; D[v][v]=0; M seen=1u<<v,fr=seen; int d=0; while(fr){ M nf=openN(fr)&~seen; d++; for(M t=nf;t;t&=t-1) D[v][__builtin_ctz(t)]=d; seen|=nf; fr=nf; } ecc[v]=0; for(int w=0;w<n;w++) ecc[v]=max(ecc[v],D[v][w]); }
    int rad=99, diam=0; for(int v=0;v<n;v++){ rad=min(rad,ecc[v]); diam=max(diam,ecc[v]); }
    vector<int> deg(n); int m=0; for(int v=0;v<n;v++){ deg[v]=pc(adj[v]); m+=deg[v]; } m/=2;
    int delta=*min_element(deg.begin(),deg.end()), Delta=*max_element(deg.begin(),deg.end());
    int tr=treeN();
    // subset loop: total domination and connected domination
    int gt=n, gc=n;
    for(M S=1;S<=ALL;S++){ int c=pc(S); M on=openN(S);
      if(c<gt && on==ALL) gt=c;
      if(c<gc && ((on|S)==ALL) && connM(S)) gc=c;
      if(S==ALL) break; }
    int Ls = n-gc; if(gc==0) Ls=n-1;
    // 72: both readings
    { double eavg=0; for(int v=0;v<n;v++) eavg+=ecc[v]; eavg/=n; int lmax=0; for(int v=0;v<n;v++) lmax=max(lmax,alphaM(adj[v]));
      F("72 a", tr, ceil(eavg+lmax/3.0-1e-9)); F("72 b", tr, ceil((eavg+lmax)/3.0-1e-9)); }
    // 76
    { int T[16],Tmax=0; for(int v=0;v<n;v++){ T[v]=0; for(int w=0;w<n;w++) T[v]+=D[v][w]; Tmax=max(Tmax,T[v]); } int f=0; for(int v=0;v<n;v++) if(T[v]==Tmax) f++;
      int fd=(2*m)/n; F("76", tr, (double)f/fd); }
    // 84
    F("84", tr, 2.0*rad/delta);
    // 165, 166
    { M Mx=0; for(int v=0;v<n;v++) if(deg[v]==Delta) Mx|=1u<<v; int x=pc(openN(Mx)&~Mx);
      F("165", Ls, ceil(sqrt(2.0*x)-1e-9)); F("166", Ls, x/sqrt((double)rad));
      // 258-261
      int emax=0; for(int v=0;v<n;v++){ int e=0; for(int w=0;w<n;w++) if(D[v][w]%2==0) e++; emax=max(emax,e); }
      M B=0, S2=0; for(int v=0;v<n;v++){ if(ecc[v]==diam) B|=1u<<v; if(deg[v]==2) S2|=1u<<v; }
      F("258", gt, 2.0*emax/Ls); F("259", gt, 2.0*x/Ls); F("260", gt, 2.0*pc(openN(B)&~B)/Ls); F("261", gt, 2.0*pc(openN(S2)&~S2)/Ls); }
  }
  printf("graphs=%ld\n",cnt); for(auto&[k,v]:minsl) printf("%-6s fails=%-8ld minslack=%.3f %s\n",k.c_str(),fails[k],v,first[k].c_str()); }
