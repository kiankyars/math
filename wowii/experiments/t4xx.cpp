#include "inv.h"
int main(){ string s; map<string,pair<long,string>> fails; map<string,double> minsl; long cnt=0;
  auto F=[&](const string& k,double lhs,double rhs){ double sl=lhs-rhs; if(!minsl.count(k)||sl<minsl[k]) minsl[k]=sl; if(sl<-1e-9){ auto& f=fails[k]; if(f.first++==0) f.second=s; } };
  while(getline(cin,s)){ if(s.empty()) continue; parse(s); if(n<4) continue; cnt++;
    Inv I=compute(); int g2=I.gamma2, id=I.idom;
    int D[32][32]; for(int v=0;v<n;v++){ for(int w=0;w<n;w++) D[v][w]=-1; D[v][v]=0; M seen=1u<<v,fr=seen; int d=0; while(fr){ M nf=openN(fr)&~seen; d++; for(M t=nf;t;t&=t-1) D[v][__builtin_ctz(t)]=d; seen|=nf; fr=nf; } }
    vector<int>& deg=I.deg; M Ad=0,AD=0,A2=0,Mlmin=0,Mlmax=0; int lmin=*min_element(I.lam.begin(),I.lam.end()), lmax=*max_element(I.lam.begin(),I.lam.end());
    for(int v=0;v<n;v++){ if(deg[v]==I.delta) Ad|=1u<<v; if(deg[v]==I.Delta) AD|=1u<<v; if(deg[v]==2) A2|=1u<<v; if(I.lam[v]==lmin) Mlmin|=1u<<v; if(I.lam[v]==lmax) Mlmax|=1u<<v; }
    F("394", I.mu+edgesIn(A2)+pc(Mlmin), g2);
    map<int,int> fr; for(int d:deg) fr[d]++; int bestc=0,mm=0; for(auto&[d,c]:fr) if(c>bestc){bestc=c;mm=d;} M Mm=0; for(int v=0;v<n;v++) if(deg[v]==mm) Mm|=1u<<v;
    F("395a", pc(Mm)+matchM(ALL&~Ad)+matchM(openN(A2)), g2);
    int tmax=*max_element(I.tri.begin(),I.tri.end()); int ft=0; for(int v=0;v<n;v++) if(I.tri[v]==tmax) ft++; int Tdmax=0; for(int v=0;v<n;v++){ int t=0; for(int w=0;w<n;w++) t+=D[v][w]; Tdmax=max(Tdmax,t);} 
    F("401b", floor(3.0*Tdmax/ft+1e-9), g2);
    int iso=0; for(M t=Ad;t;t&=t-1) if(!(adj[__builtin_ctz(t)]&Ad)) iso++; int c1=0; for(int v=0;v<n;v++) if(pc(adj[v]&AD)==1) c1++;
    F("402", 2*(iso+c1+I.gammat), g2);
    int Nmax=0; for(int u=0;u<n;u++) for(M t=adj[u];t;t&=t-1){ int w=__builtin_ctz(t); Nmax=max(Nmax,pc(adj[u]|adj[w])); }
    F("421b", I.gamma*floor(0.5*Nmax-1+1e-9), id);
    F("421c", I.gamma*(pc(closedN(Mlmax))-3), id);
    F("422a", alphaM(ALL&~AD)+2*(edgesIn(AD)/3), id);
    F("422b", alphaM(AD)+pow(gammaM(ALL&~AD),2), id);
    M Ah=0; for(int v=0;v<n;v++) if(2*deg[v]<=n) Ah|=1u<<v; int dmax=0; for(M t=ALL&~Ah;t;t&=t-1) dmax=max(dmax,pc(adj[__builtin_ctz(t)]&~Ah));
    F("422c", alphaM(Ah)+2*(dmax/3), id);
    F("426", n-gammaM(openN(AD)), id);
    vector<int> dd=deg; sort(dd.begin(),dd.end()); int a=0,sm=0; for(int i=0;i<n;i++){ sm+=dd[i]; if(sm<=I.m) a=i+1; else break; }
    int mdiff=99; for(int v=0;v<n;v++){ int e=0,o=0; for(int w=0;w<n;w++) if(D[v][w]%2==0) e++; else o++; mdiff=min(mdiff,e-o); }
    F("432a", a+mdiff, id);
    // 438a: alpha_2 <= a(G)+a(G[V-A])+|E(G[A])|
    int a2=0; for(M S=1;S<=ALL;S++){ int c=pc(S); if(c>a2){ bool ok=true; for(M t=S;t;t&=t-1) if(pc(adj[__builtin_ctz(t)]&S)>1){ok=false;break;} if(ok) a2=c; } if(S==ALL) break; }
    M R=ALL&~Ad; vector<int> rd; int rm=0; for(M t=R;t;t&=t-1){ int v=__builtin_ctz(t); rd.push_back(pc(adj[v]&R)); rm+=pc(adj[v]&R);} rm/=2; sort(rd.begin(),rd.end()); int aR=0; sm=0; for(int i=0;i<(int)rd.size();i++){ sm+=rd[i]; if(sm<=rm) aR=i+1; else break; }
    F("438a", a+aR+edgesIn(Ad), a2);
  }
  printf("graphs=%ld\n",cnt); for(auto&[k,v]:minsl) printf("%-26s fails=%-7ld minslack=%.3f %s\n",k.c_str(),fails[k].first,v,fails[k].second.c_str()); }
