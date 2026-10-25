#include "base.h"
int main(){ string s; long cnt=0; map<string,long> fails; map<string,string> first;
  while(getline(cin,s)){ if(s.empty()) continue; parse(s); if(n<3) continue; cnt++;
    vector<int> deg(n); for(int v=0;v<n;v++) deg[v]=pc(adj[v]);
    int gc=n;
    for(M S=1;S<=ALL;S++){ int c=pc(S); M on=openN(S); if(c<gc && ((on|S)==ALL) && connM(S)) gc=c; if(S==ALL) break; }
    int Ls=n-gc;
    auto F=[&](const char* k, bool ok){ if(!ok){ if(fails[k]++==0) first[k]=s; } };
    for(M S=1;S<ALL;S++){ if(openN(S)&S) continue; int k=pc(S); int aw=alphaM(ALL&~S); int slack=Ls-k+aw;
      vector<int> ds; for(int v=0;v<n;v++) if(S>>v&1) ds.push_back(deg[v]); sort(ds.begin(),ds.end());
      F("V1 min_S", slack>=ds[0]);
      if(k>=2) F("V2 2ndmin_S", slack>=ds[1]);
      if(k>=2) F("V2b 2ndmin_S - 0, aw counts comps", true);
    }
  }
  printf("graphs=%ld\n",cnt); for(auto&[k,v]:fails) printf("%s fails=%ld first=%s\n",k.c_str(),v,first[k].c_str()); }
