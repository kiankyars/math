#include "inv.h"
int main(){ string s; map<string,pair<long,string>> fails; map<string,double> minsl; long cnt=0;
  auto F=[&](const string& k,double lhs,double rhs){ double sl=lhs-rhs; if(!minsl.count(k)||sl<minsl[k]) minsl[k]=sl; if(sl<-1e-9){ auto& f=fails[k]; if(f.first++==0) f.second=s; } };
  while(getline(cin,s)){ if(s.empty()) continue; parse(s); if(n<3) continue; cnt++;
    Inv I=compute(); int g2=I.gamma2; int al=I.alpha;
    M Ad=0, A2=0, A3=0, T=0, P=0; for(int v=0;v<n;v++){ if(I.deg[v]==I.delta) Ad|=1u<<v; if(I.deg[v]<=2) A2|=1u<<v; if(I.deg[v]>=3) A3|=1u<<v; if(I.deg[v]==2) T|=1u<<v; if(I.deg[v]==1) P|=1u<<v; }
    M nonmin=ALL&~Ad; int A1=0; for(int v=0;v<n;v++) if(pc(adj[v]&nonmin)==1) A1++;
    F("382b", -1+al*(I.delta+A1), g2);
    double eA=0; for(M t=Ad;t;t&=t-1) eA+=I.ecc[__builtin_ctz(t)]; eA/=pc(Ad); int B=0; for(int v=0;v<n;v++) if(I.ecc[v]==I.diam) B++;
    F("382c", (al*eA+B)/2.0, g2);
    int lmax=*max_element(I.lam.begin(),I.lam.end()); int X=0; for(int v=0;v<n;v++) if(I.lam[v]==lmax) X++;
    F("382d", I.diam*(al+X)/2.0, g2);
    // mode_min
    map<int,int> fr; for(int d:I.deg) fr[d]++; int best=0,mm=0; for(auto&[d,c]:fr) if(c>best){best=c;mm=d;} int Mm=fr[mm];
    vector<int> ds=I.deg; sort(ds.begin(),ds.end());
    int q1=ds[n/4]; int q2=ds[(n-1)/4]; int q3=ds[(n+1)/4];
    F("389a q=d[n/4]", Mm*(q1+pc(A2))-1, g2); F("389a q=d[(n-1)/4]", Mm*(q2+pc(A2))-1, g2); F("389a q=d[(n+1)/4]", Mm*(q3+pc(A2))-1, g2);
    F("391 p=pathcover", I.pcov+1+matchM(T)+edgesIn(A3), g2); F("391 p=pendants", pc(P)+1+matchM(T)+edgesIn(A3), g2);
    int c2=0; for(int v=0;v<n;v++) if(pc(adj[v]&A2)==1) c2++;  // A_2 as degree <=2? statement says degree 2
    int c2b=0; for(int v=0;v<n;v++) if(pc(adj[v]&T)==1) c2b++;
    int mVA=matchM(ALL&~Ad);
    F("392b A2=deg2", mVA+pc(Ad)+c2b, g2); F("392b A2=deg<=2", mVA+pc(Ad)+c2, g2);
    int cutv=0; for(int v=0;v<n;v++) if(!connectedM(ALL&~(1u<<v))) cutv++;
    F("392c", mVA+pc(Ad)+cutv, g2);
    M NP=openN(P), NNP=openN(NP);
    F("392d", I.mu+matchM(ALL&~NNP)+pc(Ad), g2);
    M NA2=openN(T), NA2b=openN(A2);
    F("392e A2=deg2", I.mu+matchM(NA2)+pc(Ad), g2); F("392e A2=deg<=2", I.mu+matchM(NA2b)+pc(Ad), g2);
    M NA=openN(Ad); int cf=0; for(int v=0;v<n;v++) if(pc(adj[v]&NA)==1) cf++;
    F("392f A2=deg2", I.mu+matchM(NA2)+cf, g2); F("392f A2=deg<=2", I.mu+matchM(NA2b)+cf, g2);
  }
  printf("graphs=%ld\n",cnt); for(auto&[k,v]:minsl) printf("%-26s fails=%-7ld minslack=%.3f %s\n",k.c_str(),fails[k].first,v,fails[k].second.c_str()); }
