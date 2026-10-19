// Column systems: down-closed D in N^d, arbitrary J(w)>=0. Check intervals, KL, and degenerate reachability configs.
#include <bits/stdc++.h>
using namespace std;
typedef vector<int> V;
int main(int argc,char**argv){
  unsigned seed=atoi(argv[1]); int trials=atoi(argv[2]); int dmax=atoi(argv[3]); int side=atoi(argv[4]); int maxJ=atoi(argv[5]); int maxcols=atoi(argv[6]);
  mt19937 rng(seed); long tested=0,badI=0,badKL=0,deg2=0,deg3=0;
  for(int t=0;t<trials;t++){
    int d=1+rng()%dmax; set<V> Ds; int ng=1+rng()%4;
    for(int g=0;g<ng;g++){ V gen(d); for(int i=0;i<d;i++) gen[i]=rng()%(side+1); V x(d,0);
      while(true){ Ds.insert(x); int i=0; while(i<d){ if(x[i]<gen[i]){x[i]++;break;} x[i]=0;i++;} if(i==d) break; } }
    if((int)Ds.size()>maxcols) continue;
    vector<V> cols(Ds.begin(),Ds.end()); map<V,int> J; for(auto&w:cols) J[w]=rng()%(maxJ+1);
    tested++;
    int maxh=0; for(auto&w:cols){int j=J[w]; maxh+=(j+1)*j/2;}
    map<V,vector<char>> D; D[V(d,0)]=vector<char>(maxh+1,0); D[V(d,0)][0]=1;
    for(auto&w:cols){ int Jr=J[w]; map<V,vector<char>> N2;
      for(auto&kv:D){ V y=kv.first; for(int k=0;k<=Jr+1;k++){ int L=k*(k-1)/2,H=k*Jr-k*(k-1)/2; auto&tg=N2[y]; if(tg.empty()) tg.assign(maxh+1,0);
          for(int h=0;h<=maxh;h++) if(kv.second[h]) for(int v=L;v<=H&&h+v<=maxh;v++) tg[h+v]=1;
          for(int i=0;i<d;i++) y[i]+=w[i]; } }
      D.swap(N2); }
    map<V,pair<int,int>> MM;
    for(auto&kv:D){ int lo=-1,hi=-1,cnt=0; for(int h=0;h<=maxh;h++) if(kv.second[h]){ if(lo<0) lo=h; hi=h; cnt++; } if(cnt!=hi-lo+1) badI++; MM[kv.first]={lo,hi}; }
    auto sub=[&](const V&a,const V&b){V c(a); for(int i=0;i<d;i++) c[i]-=b[i]; return c;};
    for(auto&w:cols){ bool z=true; for(int x:w) if(x) z=false; if(z) continue;
      for(auto&kv:MM){ auto it=MM.find(sub(kv.first,w)); if(it==MM.end()) continue;
        int a=kv.second.first,b=kv.second.second,c=it->second.first+J[w],e=it->second.second+J[w];
        if(max(a,c)>min(b,e)){ badKL++; } } }
    // degenerate configs: x in R, x+w+w0 in R, x+w notin R, x+w0 notin R  (case 3); and x notin R... (case 2a): x+w in R, x+w0 in R, x notin R, x+w+w0 notin R
    for(auto&w:cols) for(auto&w0:cols){ bool z=true; for(int x:w) if(x) z=false; for(int x:w0) if(x) z=false; if(z) continue; if(w==w0) continue;
      bool z1=true; for(int x:w) if(x) z1=false; bool z2=true; for(int x:w0) if(x) z2=false; if(z1||z2) continue;
      for(auto&kv:MM){ V x=kv.first; V a=x,b=x,c=x; for(int i=0;i<d;i++){a[i]+=w[i];b[i]+=w0[i];c[i]+=w[i]+w0[i];}
        if(MM.count(c)&&!MM.count(a)&&!MM.count(b)) deg3++; }
      for(auto&kv:MM){ V a=kv.first; // a = x+w in R
        V x=sub(a,w); bool xin=true; for(int i=0;i<d;i++) if(x[i]<0) xin=false; if(!xin) continue;
        V b=x,c=x; for(int i=0;i<d;i++){b[i]+=w0[i];c[i]+=w[i]+w0[i];}
        if(MM.count(b)&&!MM.count(x)&&!MM.count(c)) deg2++; }
    }
  }
  printf("tested=%ld badInterval=%ld badKL=%ld deg3=%ld deg2a=%ld\n",tested,badI,badKL,deg3,deg2);
}
