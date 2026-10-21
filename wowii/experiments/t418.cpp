#include "inv.h"
int main(){ string s; map<string,pair<long,string>> fails; map<string,double> minsl; long cnt=0;
  auto F=[&](const string& k,double lhs,double rhs){ double sl=lhs-rhs; if(!minsl.count(k)||sl<minsl[k]) minsl[k]=sl; if(sl<-1e-9){ auto& f=fails[k]; if(f.first++==0) f.second=s; } };
  while(getline(cin,s)){ if(s.empty()) continue; parse(s); if(n<4) continue; cnt++;
    Inv I=compute(); int id=I.idom;
    M A=0; for(int v=0;v<n;v++) if(I.deg[v]==I.delta) A|=1u<<v; M NA=openN(A); int eNA=edgesIn(NA); int aR=alphaM(ALL&~A);
    // core: vertices in all maximum independent sets
    M core=0; for(int v=0;v<n;v++) if(alphaM(ALL&~(1u<<v))<I.alpha) core|=1u<<v;
    F("418c", aR+eNA+pc(A&core), id);
    int pend=0; for(int v=0;v<n;v++) if(I.deg[v]==1) pend++;
    F("418b p=pendants", aR+eNA*pend, id); F("418b p=pathcover", aR+eNA*I.pcov, id);
    // 425d: |T_min| + sum K4(v) + gamma(G[V-N(P)])
    int tmin=*min_element(I.tri.begin(),I.tri.end()); int Tm=0; for(int v=0;v<n;v++) if(I.tri[v]==tmin) Tm++;
    long sk=0; for(int v=0;v<n;v++){ M N=adj[v]; for(M t=N;t;t&=t-1){ int a=__builtin_ctz(t); for(M u=N&adj[a]&~((2u<<a)-1);u;u&=u-1){ int b=__builtin_ctz(u); sk+=pc(N&adj[a]&adj[b]&~((2u<<b)-1)); } } }
    M P=0; for(int v=0;v<n;v++) if(I.deg[v]==1) P|=1u<<v; M R=ALL&~openN(P);
    F("425d", Tm+sk+gammaM(R), id);
  }
  printf("graphs=%ld\n",cnt); for(auto&[k,v]:minsl) printf("%-26s fails=%-7ld minslack=%.3f %s\n",k.c_str(),fails[k].first,v,fails[k].second.c_str()); }
