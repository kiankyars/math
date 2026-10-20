#include "inv.h"
int main(){ string s; long cnt=0; map<string,long> fails; map<string,string> ex;
  auto F=[&](const string& k,bool ok){ if(!ok){ if(fails[k]++==0) ex[k]=s; } };
  while(getline(cin,s)){ if(s.empty()) continue; parse(s); cnt++; if(n<2) continue; Inv I=compute();
    vector<int> d=I.deg; sort(d.begin(),d.end()); int sigma=d[1];
    // dist_even(v): # vertices at even distance (incl v), and excluding v
    int maxe=0,maxe2=0; for(int v=0;v<n;v++){ M seen=1u<<v,fr=seen; int dd=0,ev=1; while(seen!=ALL){ M nf=openN(fr)&~seen; dd++; if(dd%2==0) ev+=pc(nf); seen|=nf; fr=nf; } maxe=max(maxe,ev); maxe2=max(maxe2,ev-1); }
    F("189 incl", !(maxe<=1+sigma) || I.hampath);
    F("189 excl", !(maxe2<=1+sigma) || I.hampath);
    F("190", !(I.Ls+1<=2*sigma) || I.hampath);
    // 213: complement
    M cadj[32]; for(int v=0;v<n;v++) cadj[v]=ALL&~adj[v]&~(1u<<v); vector<int> cd(n); for(int v=0;v<n;v++) cd[v]=pc(cadj[v]); sort(cd.begin(),cd.end()); int lowmed=cd[(n-1)/2];
    int g2c=n; for(M S=1;S<=ALL;S++){ int c=pc(S); if(c>=g2c) continue; bool ok=true; for(M t=ALL&~S;t&&ok;t&=t-1){ int v=__builtin_ctz(t); if(pc(cadj[v]&S)<2) ok=false; } if(ok) g2c=c; if(S==ALL) break; }
    F("213", !(2+lowmed<=g2c) || I.hampath);
  }
  printf("graphs=%ld\n",cnt); for(auto&[k,v]:fails) printf("FAIL %s count=%ld e.g. %s\n",k.c_str(),v,ex[k].c_str()); }
