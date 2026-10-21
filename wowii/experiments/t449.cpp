#include "inv.h"
int main(){ string s; map<string,pair<long,string>> fails; map<string,double> minsl; long cnt=0;
  auto F=[&](const string& k,double lhs,double rhs){ double sl=lhs-rhs; if(!minsl.count(k)||sl<minsl[k]) minsl[k]=sl; if(sl<-1e-9){ auto& f=fails[k]; if(f.first++==0) f.second=s; } };
  while(getline(cin,s)){ if(s.empty()) continue; parse(s); if(n<4) continue; cnt++;
    int a2=0; for(M S=1;S<=ALL;S++){ int c=pc(S); if(c>a2){ bool ok=true; for(M t=S;t;t&=t-1) if(pc(adj[__builtin_ctz(t)]&S)>1){ok=false;break;} if(ok) a2=c; } if(S==ALL) break; }
    M H3=0; for(int v=0;v<n;v++) if(pc(adj[v])>=3) H3|=1u<<v;
    int eH=edgesIn(H3);
    F("449", pc(ALL&~H3)+ceil((eH-1)/2.0-1e-9), a2);
    // 442: longest induced path in G[H3]
    int lp=0; for(M S=H3;S;S=(S-1)&H3){ int c=pc(S); if(c>lp && edgesIn(S)==c-1 && connectedM(S)){ bool ok=true; for(M t=S;t;t&=t-1) if(pc(adj[__builtin_ctz(t)]&S)>2){ok=false;break;} if(ok) lp=c; } }
    F("442", n-ceil(lp/2.0-1e-9), a2);
    // 444: distinct K4 counts
    set<int> k4; for(int v=0;v<n;v++){ int c=0; M N=adj[v]; for(M t=N;t;t&=t-1){ int a=__builtin_ctz(t); for(M u=N&adj[a]&~((2u<<a)-1);u;u&=u-1){ int b=__builtin_ctz(u); c+=pc(N&adj[a]&adj[b]&~((2u<<b)-1)); } } k4.insert(c); }
    F("444", n-floor(k4.size()/2.0+1e-9), a2);
  }
  printf("graphs=%ld\n",cnt); for(auto&[k,v]:minsl) printf("%-26s fails=%-7ld minslack=%.3f %s\n",k.c_str(),fails[k].first,v,fails[k].second.c_str()); }
