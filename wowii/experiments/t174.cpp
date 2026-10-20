#include "inv.h"
int main(){ string s; map<string,int> cat; long cnt=0; vector<string> ex;
  while(getline(cin,s)){ if(s.empty()) continue; parse(s); Inv I=compute(); cnt++; int maxlam=*max_element(I.lam.begin(),I.lam.end());
    int slack=I.Ls+I.b-(n+maxlam-1);
    if(slack==0){ char buf[200]; snprintf(buf,200,"mu=%d b=%d alpha=%d Ls=%d bip=%d",maxlam,I.b,I.alpha,I.Ls,(int)(I.b==n)); cat[buf]++; if(ex.size()<12 && maxlam>=3) ex.push_back(s+" "+buf); } }
  printf("graphs=%ld\n",cnt); for(auto&[k,v]:cat) printf("%6d %s\n",v,k.c_str()); for(auto&e:ex) printf("EX %s\n",e.c_str()); }
