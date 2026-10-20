#include "inv.h"
int main(){ string s; long cnt=0,f177=0,f174=0; int ms177=99,ms174=99;
  while(getline(cin,s)){ if(s.empty()) continue; parse(s); Inv I=compute(); cnt++;
    vector<int> d=I.deg; sort(d.begin(),d.end()); int sigma=d[1]; int maxlam=*max_element(I.lam.begin(),I.lam.end());
    int s177=I.Ls+I.b-(2*I.alpha+sigma); int s174=I.Ls+I.b-(n+maxlam-1); ms177=min(ms177,s177); ms174=min(ms174,s174);
    if(s177<0){ f177++; if(f177<=5) printf("177 FAIL %s n=%d Ls=%d b=%d alpha=%d sigma=%d\n",s.c_str(),n,I.Ls,I.b,I.alpha,sigma); }
    if(s174<0){ f174++; if(f174<=5) printf("174 FAIL %s\n",s.c_str()); } }
  printf("graphs=%ld fail177=%ld minslack177=%d fail174=%ld minslack174=%d\n",cnt,f177,ms177,f174,ms174); }
