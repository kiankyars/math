// Exhaustive battery for WOWII conjectures on graphs read from geng (graph6), n <= 12.
// Reports, per conjecture, the number of failures, the minimum slack and the first failing graph.
#include <bits/stdc++.h>
using namespace std;
typedef unsigned M;
int n; M adj[16], cadj[16], ALL;
static inline int pc(M x){ return __builtin_popcount(x); }
void parse(const string& s){ int p=0; n=s[p++]-63; for(int i=0;i<n;i++) adj[i]=0; int val=0,k=6;
  for(int j=1;j<n;j++) for(int i=0;i<j;i++){ if(k==6){ val=s[p++]-63; k=0; } if((val>>(5-k))&1){ adj[i]|=1u<<j; adj[j]|=1u<<i; } k++; }
  ALL=(1u<<n)-1; for(int v=0;v<n;v++) cadj[v]=ALL&~adj[v]&~(1u<<v); }
static inline M openN(const M* a, M S){ M r=0; for(M t=S;t;t&=t-1) r|=a[__builtin_ctz(t)]; return r; }
bool connM(M m){ if(!m) return true; M seen=m&(-m),fr=seen; while(fr){ M nf=openN(adj,fr)&m&~seen; seen|=nf; fr=nf; } return seen==m; }
int ncomp(M m){ int c=0; while(m){ M seen=m&(-m),fr=seen; while(fr){ M nf=openN(adj,fr)&m&~seen; seen|=nf; fr=nf; } m&=~seen; c++; } return c; }
int omegaM(M m){ if(!m) return 0; int v=__builtin_ctz(m); M rest=m&~(1u<<v); int a=omegaM(rest&adj[v])+1; if((adj[v]&rest)==rest) return a; return max(a,omegaM(rest)); }
int matchC(M m){ if(!m) return 0; int v=__builtin_ctz(m); M rest=m&~(1u<<v); int best=matchC(rest); for(M t=cadj[v]&rest;t;t&=t-1){ int w=__builtin_ctz(t); best=max(best,1+matchC(rest&~(1u<<w))); } return best; }
bool isBip(){ int col[16]; for(int i=0;i<n;i++) col[i]=-1; for(int s=0;s<n;s++){ if(col[s]>=0) continue; col[s]=0; deque<int> q{s}; while(!q.empty()){ int x=q.front(); q.pop_front(); for(M t=adj[x];t;t&=t-1){ int y=__builtin_ctz(t); if(col[y]<0){ col[y]=1-col[x]; q.push_back(y);} else if(col[y]==col[x]) return false; } } } return true; }
int residueOf(vector<int> d){ sort(d.rbegin(),d.rend()); while(!d.empty()&&d[0]>0){ int x=d[0]; d.erase(d.begin()); for(int i=0;i<x&&i<(int)d.size();i++) d[i]--; sort(d.rbegin(),d.rend()); } return d.size(); }
int hhZeroStep(vector<int> d){ int k=0; for(int x:d) if(x==0) return 0; while(true){ sort(d.rbegin(),d.rend()); int x=d[0]; d.erase(d.begin()); for(int i=0;i<x&&i<(int)d.size();i++) d[i]--; k++; for(int y:d) if(y==0) return k; if(d.empty()) return k; } }
bool hamPath(){ int N=1<<n; static M endset[1<<12]; for(int m=0;m<N;m++) endset[m]=0; for(int v=0;v<n;v++) endset[1<<v]=1u<<v;
  for(int m=1;m<N;m++){ if(!endset[m]) continue; for(M t=endset[m];t;t&=t-1){ int v=__builtin_ctz(t); for(M u=adj[v]&~m;u;u&=u-1){ int w=__builtin_ctz(u); endset[m|(1<<w)]|=1u<<w; } } }
  return endset[N-1]!=0; }
int bestTr; void recTr(M S, M X){ int s=pc(S); if(s>bestTr) bestTr=s; M fr=openN(adj,S)&~S&~X; M cand=0; for(M t=fr;t;t&=t-1){ int w=__builtin_ctz(t); if(pc(adj[w]&S)==1) cand|=1u<<w; }
  M avail=ALL&~X&~S; M reach=cand, f=cand; while(f){ M nf=openN(adj,f)&avail&~reach; reach|=nf; f=nf; } if(s+pc(reach)<=bestTr) return; if(!cand) return;
  int w=__builtin_ctz(cand); recTr(S|(1u<<w),X); recTr(S,X|(1u<<w)); }
int treeN(){ bestTr=1; for(int v=0;v<n;v++){ M X=(1u<<v)-1; recTr(1u<<v,X); } return bestTr; }
int connDom(){ int best=n; for(M S=1;S<=ALL;S++){ int c=pc(S); if(c>=best) continue; if(((openN(adj,S)|S)==ALL) && connM(S)) best=c; if(S==ALL) break; } return best; }
int main(){ string s; map<string,long> fails; map<string,double> minsl; map<string,string> first; long cnt=0;
  auto F=[&](const string& k,double lhs,double rhs){ double sl=lhs-rhs; if(!minsl.count(k)||sl<minsl[k]) minsl[k]=sl; if(sl<-1e-9){ if(fails[k]++==0) first[k]=s; } else fails[k]+=0; };
  auto IMP=[&](const string& k,bool hyp,bool concl){ if(!minsl.count(k)) minsl[k]=1; if(hyp && !concl){ if(fails[k]++==0) first[k]=s; minsl[k]=-1; } else fails[k]+=0; };
  while(getline(cin,s)){ if(s.empty()) continue; parse(s); if(n<3) continue; cnt++;
    int D[16][16]; int ecc[16];
    for(int v=0;v<n;v++){ for(int w=0;w<n;w++) D[v][w]=99; D[v][v]=0; M seen=1u<<v,fr=seen; int d=0; while(fr){ M nf=openN(adj,fr)&~seen; d++; for(M t=nf;t;t&=t-1) D[v][__builtin_ctz(t)]=d; seen|=nf; fr=nf; } ecc[v]=0; for(int w=0;w<n;w++) ecc[v]=max(ecc[v],D[v][w]); }
    int rad=99,diam=0; for(int v=0;v<n;v++){ rad=min(rad,ecc[v]); diam=max(diam,ecc[v]); }
    vector<int> deg(n); int m=0; for(int v=0;v<n;v++){ deg[v]=pc(adj[v]); m+=deg[v]; } m/=2;
    int delta=*min_element(deg.begin(),deg.end()), Delta=*max_element(deg.begin(),deg.end());
    vector<int> sd=deg; sort(sd.begin(),sd.end()); int sigma=sd[1];
    // subset loop: total domination, independent domination, 2-domination of the complement
    int gt=n, idom=n, g2c=n;
    for(M S=1;S<=ALL;S++){ int c=pc(S); M on=openN(adj,S);
      if(c<gt && on==ALL) gt=c;
      if(c<idom && ((on|S)==ALL) && !(on&S)) idom=c;
      if(c<g2c){ bool ok=true; for(int v=0;v<n&&ok;v++) if(!(S>>v&1) && pc(cadj[v]&S)<2) ok=false; if(ok) g2c=c; }
      if(S==ALL) break; }
    M C=0,B=0,A=0; for(int v=0;v<n;v++){ if(ecc[v]==rad) C|=1u<<v; if(ecc[v]==diam) B|=1u<<v; if(deg[v]==delta) A|=1u<<v; }
    int maxNe=0; for(int u=0;u<n;u++) for(M t=adj[u]&~((1u<<(u+1))-1);t;t&=t-1){ int w=__builtin_ctz(t); maxNe=max(maxNe,pc(adj[u]|adj[w])); }
    F("255", gt, 2.0*pc(C)/maxNe);
    F("256", gt, 2.0*pc(openN(adj,A))/maxNe);
    // 232/233/235 with B the periphery and ecc(B) = max_v d(v, B)
    int eB=0; for(int v=0;v<n;v++){ int mn=99; for(M t=B;t;t&=t-1) mn=min(mn,D[v][__builtin_ctz(t)]); eB=max(eB,mn); }
    bool bip=isBip();
    F("232", gt, 0.5*(rad+eB)); F("233", gt, 2.0/3*(1+eB)); F("235", gt, 2.0/3*eB+(bip?1:0));
    // 268/269
    { vector<int> Cv; for(int v=0;v<n;v++) if(C>>v&1) Cv.push_back(v); double sm=0,c=0; for(size_t i=0;i<Cv.size();i++) for(size_t j=i+1;j<Cv.size();j++){ sm+=D[Cv[i]][Cv[j]]; c++; } double da=c?sm/c:0;
      double s3=0,c3=0; for(int x:Cv) for(int y=0;y<n;y++) if(y!=x){ s3+=D[x][y]; c3++; } double dcv=s3/c3;
      F("268 pairs", gt, floor(1+da+1e-9)); F("268 CV", gt, floor(1+dcv+1e-9));
      bool c4=false; for(int a=0;a<n&&!c4;a++) for(int b=a+1;b<n;b++) if(pc(adj[a]&adj[b])>=2){ c4=true; break; }
      if(!c4){ F("269 pairs", gt, ceil(1+da-1e-9)); F("269 CV", gt, ceil(1+dcv-1e-9)); } }
    // 287, 290
    int k=hhZeroStep(deg); int muc=matchC(ALL);
    F("287", k+muc, gt); F("290", k*Delta, gt);
    // 299
    { int a=0,sm=0; for(int i=0;i<n;i++){ sm+=sd[i]; if(sm<=m) a=i+1; else break; } int S2=0; for(int v=0;v<n;v++) if(deg[v]==2) S2++; F("299", a+S2, gt); }
    // 302, 304
    { int lc[16],lcmax=0; for(int v=0;v<n;v++){ lc[v]=omegaM(cadj[v]); lcmax=max(lcmax,lc[v]); } int fmax=0; for(int v=0;v<n;v++) if(lc[v]==lcmax) fmax++;
      int demin=99; for(int v=0;v<n;v++){ int e=0; for(int w=0;w<n;w++) if(D[v][w]%2==0) e++; demin=min(demin,e); }
      F("302", demin+fmax, gt);
      int nemax=-1; for(int u=0;u<n;u++) for(int w=u+1;w<n;w++) if(!(adj[u]>>w&1)) nemax=max(nemax,pc(cadj[u]|cadj[w]));
      if(nemax>=0) F("304", 0.5*(fmax+nemax), gt); }
    // 434d, 434e: i <= SW(complement) - c(G[N[B]]) + 2 and i <= SW(complement) - ecc(C) + 2
    { M left=ALL; int degen=0; while(left){ int bv=-1,bd=99; for(M t=left;t;t&=t-1){ int v=__builtin_ctz(t); int d=pc(cadj[v]&left); if(d<bd){bd=d;bv=v;} } degen=max(degen,bd); left&=~(1u<<bv); }
      int SW=1+degen; M NB=B|openN(adj,B); int cNB=ncomp(NB);
      int eC=0; for(int v=0;v<n;v++){ int mn=99; for(M t=C;t;t&=t-1) mn=min(mn,D[v][__builtin_ctz(t)]); eC=max(eC,mn); }
      F("434d", SW-cNB+2, idom); F("434e", SW-eC+2, idom); F("434e strong", n-Delta-eC+2, idom); }
    // 324
    { int res=residueOf(deg); int nemax=0; for(int u=0;u<n;u++) for(int w=u+1;w<n;w++) if(!(adj[u]>>w&1)) nemax=max(nemax,pc(cadj[u]|cadj[w]));
      if(nemax<=1+res){ set<int> sizes; for(M S=1;S<=ALL;S++){ if(openN(adj,S)==ALL){ bool mn=true; for(M t=S;t&&mn;t&=t-1){ M T=S&~(t&-t); if(openN(adj,T)==ALL) mn=false; } if(mn) sizes.insert(pc(S)); } if(S==ALL) break; }
        IMP("324", true, sizes.size()==1); } else IMP("324", false, true); }
    // Hamiltonian path conditions
    { int demax=0; for(int v=0;v<n;v++){ int e=0; for(int w=0;w<n;w++) if(D[v][w]%2==0) e++; demax=max(demax,e); }
      vector<int> cd(n); for(int v=0;v<n;v++) cd[v]=n-1-deg[v]; sort(cd.begin(),cd.end()); int lowmed=cd[(n-1)/2];
      bool h189 = demax<=1+sigma, h213 = 2+lowmed<=g2c;
      bool need190 = 2*sigma>=Delta+1; int Lsv=-1; bool h190=false; if(need190){ Lsv=n-connDom(); h190 = Lsv+1<=2*sigma; }
      bool h199=false; if(delta+2>=diam+1){ int kap=n-1; for(M S=0;S<ALL;S++){ int c=pc(S); if(c>=kap) continue; M rest=ALL&~S; if(pc(rest)>=2 && !connM(rest)) kap=c; } if(kap+2>=diam+1){ int tr=treeN(); h199 = tr-2<=kap; } }
      if(h189||h213||h190||h199){ bool hp=hamPath(); IMP("189",h189,hp); IMP("213",h213,hp); IMP("190",h190,hp); IMP("199",h199,hp); }
      else { IMP("189",false,true); IMP("213",false,true); IMP("190",false,true); IMP("199",false,true); } }
  }
  printf("graphs=%ld\n",cnt); for(auto&[k,v]:minsl) printf("%-14s fails=%-8ld minslack=%.3f %s\n",k.c_str(),fails[k],v,first[k].c_str()); }
