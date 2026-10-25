#include "base.h"
int main(){ string s; long cnt=0, failA_all=0, failA_ex=0, failInd=0, fail177=0, tight=0; 
  while(getline(cin,s)){ if(s.empty()) continue; parse(s); if(n<3) continue; cnt++;
    vector<int> deg(n); for(int v=0;v<n;v++) deg[v]=pc(adj[v]); vector<int> sd=deg; sort(sd.begin(),sd.end()); int sigma=sd[1];
    int alpha=alphaM(ALL); int gc=n, b=1; 
    for(M S=1;S<=ALL;S++){ int c=pc(S); M on=openN(S); if(c<gc && ((on|S)==ALL) && connM(S)) gc=c; if(c>b && isBip(S)) b=c; if(S==ALL) break; }
    int Ls=n-gc;
    if(Ls+b<2*alpha+sigma) {fail177++; printf("FAIL177 %s\n",s.c_str());}
    if(Ls+b==2*alpha+sigma) tight++;
    bool allok=true, exok=false, indok=true;
    for(M S=0;S<=ALL;S++){ if(openN(S)&S) { if(S==ALL) break; continue; } int k=pc(S); int aw=alphaM(ALL&~S);
      if(k-aw > Ls-sigma) { indok=false; if(k==alpha) allok=false; }
      else if(k==alpha) exok=true;
      if(S==ALL) break; }
    if(!allok){ failA_all++; if(failA_all<=5) printf("A_all fail %s\n",s.c_str()); }
    if(!exok){ failA_ex++; printf("A_ex fail %s\n",s.c_str()); }
    if(!indok){ failInd++; if(failInd<=5) printf("Ind fail %s\n",s.c_str()); }
  }
  printf("graphs=%ld fail177=%ld tight=%ld failA_all=%ld failA_ex=%ld failInd=%ld\n",cnt,fail177,tight,failA_all,failA_ex,failInd); }
