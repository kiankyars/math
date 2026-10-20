#include "inv.h"
int main(){ string s; map<string,int> cat; vector<string> ex;
  while(getline(cin,s)){ if(s.empty()) continue; parse(s); Inv I=compute();
    vector<int> d=I.deg; sort(d.begin(),d.end()); int sigma=d[1];
    if(I.Ls+I.b==2*I.alpha+sigma){ char buf[200]; snprintf(buf,200,"sigma=%d delta=%d alpha=%d b=%d Ls=%d",sigma,I.delta,I.alpha,I.b,I.Ls); cat[buf]++; if(sigma>=3 && ex.size()<10) ex.push_back(s+" "+buf); } }
  for(auto&[k,v]:cat) printf("%6d %s\n",v,k.c_str()); for(auto&e:ex) printf("EX %s\n",e.c_str()); }
