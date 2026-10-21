// Exhaustive battery, part 4: alpha, L_s + b, gamma_2 and forest bounds (graph6 on stdin, n <= 12).
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
int ncomp(M m){ int c=0; while(m){ M seen=m&(-m),fr=seen; while(fr){ M nf=openN(fr)&m&~seen; seen|=nf; fr=nf; } m&=~seen; c++; } return c; }
bool isBip(M m){ M left=m; while(left){ M c0=left&(-left),c1=0,fr0=c0,fr1=0; while(fr0||fr1){ M n1=openN(fr0)&m, n0=openN(fr1)&m; if((n1&c0)||(n0&c1)) return false; n1&=~c1; n0&=~c0; c1|=n1; c0|=n0; fr0=n0; fr1=n1; } left&=~(c0|c1);} return true; }
int residueOf(vector<int> d){ sort(d.rbegin(),d.rend()); while(!d.empty()&&d[0]>0){ int x=d[0]; d.erase(d.begin()); for(int i=0;i<x&&i<(int)d.size();i++) d[i]--; sort(d.rbegin(),d.rend()); } return d.size(); }
int pathCover(){ int N=1<<n; static M endset[1<<12]; static int cover[1<<12]; for(int m=0;m<N;m++) endset[m]=0; for(int v=0;v<n;v++) endset[1<<v]=1u<<v;
  for(int m=1;m<N;m++){ if(!endset[m]) continue; for(M t=endset[m];t;t&=t-1){ int v=__builtin_ctz(t); for(M u=adj[v]&~m;u;u&=u-1){ int w=__builtin_ctz(u); endset[m|(1<<w)]|=1u<<w; } } }
  cover[0]=0; for(int m=1;m<N;m++){ cover[m]=99; int low=m&-m; for(int sub=m;sub;sub=(sub-1)&m){ if(!(sub&low)) continue; if(endset[sub] && cover[m^sub]+1<cover[m]) cover[m]=cover[m^sub]+1; } } return cover[N-1]; }
int main(){ string s; map<string,long> fails; map<string,double> minsl; map<string,string> first; long cnt=0;
  auto F=[&](const string& k,double lhs,double rhs){ double sl=lhs-rhs; if(!minsl.count(k)||sl<minsl[k]) minsl[k]=sl; if(sl<-1e-9){ if(fails[k]++==0) first[k]=s; } else fails[k]+=0; };
  while(getline(cin,s)){ if(s.empty()) continue; parse(s); if(n<3) continue; cnt++;
    int D[16][16], ecc[16];
    for(int v=0;v<n;v++){ for(int w=0;w<n;w++) D[v][w]=99; D[v][v]=0; M seen=1u<<v,fr=seen; int d=0; while(fr){ M nf=openN(fr)&~seen; d++; for(M t=nf;t;t&=t-1) D[v][__builtin_ctz(t)]=d; seen|=nf; fr=nf; } ecc[v]=0; for(int w=0;w<n;w++) ecc[v]=max(ecc[v],D[v][w]); }
    int diam=0; for(int v=0;v<n;v++) diam=max(diam,ecc[v]);
    vector<int> deg(n); int m=0; for(int v=0;v<n;v++){ deg[v]=pc(adj[v]); m+=deg[v]; } m/=2;
    vector<int> sd=deg; sort(sd.begin(),sd.end()); int delta=sd[0], sigma=sd[1];
    int alpha=alphaM(ALL);
    // subset loop: gamma_2, gamma_t, connected domination, b, f, maximum independent sets
    int g2=n, gt=n, gc=n, b=1, f=1; M core=ALL;
    for(M S=1;S<=ALL;S++){ int c=pc(S); M on=openN(S);
      if(c<gt && on==ALL) gt=c;
      if(c<gc && ((on|S)==ALL) && connM(S)) gc=c;
      if(c<g2){ bool ok=true; for(int v=0;v<n&&ok;v++) if(!(S>>v&1) && pc(adj[v]&S)<2) ok=false; if(ok) g2=c; }
      if(c>b && isBip(S)) b=c;
      if(c>f && edgesIn(S)==c-ncomp(S)) f=c;
      if(c==alpha && !(on&S)) core&=S;
      if(S==ALL) break; }
    int Ls=n-gc;
    int lam[16], lmax=0; double lavg=0; for(int v=0;v<n;v++){ lam[v]=alphaM(adj[v]); lmax=max(lmax,lam[v]); lavg+=lam[v]; } lavg/=n;
    int demax=0; for(int v=0;v<n;v++){ int e=0; for(int w=0;w<n;w++) if(D[v][w]%2==0) e++; demax=max(demax,e); }
    // 108, 111
    F("108", demax+2*(pc(core)/3), alpha);
    { M S=0; for(int v=0;v<n;v++) if(deg[v]==delta) S|=1u<<v; M NS=0; for(M t=S;t;t&=t-1) NS|=cadj[__builtin_ctz(t)];
      F("111", ceil(1+pc(NS)*(lavg-1)-1e-9), alpha); }
    // L_s + b family
    F("174", Ls+b, n+lmax-1); F("177", Ls+b, 2*alpha+sigma); F("180", Ls+b, 1+alpha+demax);
    { int D2max=0; double dsum=0; int r2=99; for(int v=0;v<n;v++){ int dg=0,e2=0; for(int w=0;w<n;w++){ if(w!=v && D[v][w]<=2) dg++; int d2=(D[v][w]+1)/2; e2=max(e2,d2); if(w>v) dsum+=d2; } D2max=max(D2max,dg); r2=min(r2,e2); }
      F("183", Ls+b, D2max+2*r2); F("185", Ls+b, D2max+2*dsum/(n*(n-1)/2.0)); }
    // 298 (chi_C4 = 1 for C4-free graphs), 384b, 391, 61
    { int a=0,sm=0; for(int i=0;i<n;i++){ sm+=sd[i]; if(sm<=m) a=i+1; else break; }
      bool c4=false; for(int x=0;x<n&&!c4;x++) for(int y=x+1;y<n;y++) if(pc(adj[x]&adj[y])>=2){ c4=true; break; }
      F("298", a+(c4?0:1), gt);
      set<int> T; for(int v=0;v<n;v++) T.insert(edgesIn(adj[v])); F("384b", floor(n-T.size()/2.0+1e-9), g2);
      M A2=0,A3=0; for(int v=0;v<n;v++){ if(deg[v]==2) A2|=1u<<v; if(deg[v]>=3) A3|=1u<<v; }
      F("391", pathCover()+1+matchM(A2)+edgesIn(A3), g2);
      F("61", f, residueOf(deg)+ceil(diam/3.0-1e-9)); }
  }
  printf("graphs=%ld\n",cnt); for(auto&[k,v]:minsl) printf("%-6s fails=%-8ld minslack=%.3f %s\n",k.c_str(),fails[k],v,first[k].c_str()); }
