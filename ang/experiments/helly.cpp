// Theorem G systems: D down-closed, arbitrary J>=0. Test VKL: for all u (any), v!=v' in D*, with u-v,u-v' in R:
// (J(v)+B(u-v)) and (J(v')+B(u-v')) intersect (mode I) / overlap-or-touch (mode T). Also KL.
#include <bits/stdc++.h>
using namespace std;
typedef vector<int> V;
int main(int argc,char**argv){
  unsigned seed=atoi(argv[1]); int trials=atoi(argv[2]); int dmax=atoi(argv[3]); int side=atoi(argv[4]); int maxJ=atoi(argv[5]); int maxcols=atoi(argv[6]);
  setvbuf(stdout,NULL,_IONBF,0); mt19937 rng(seed); long tested=0,badKL=0,badVI=0,badVT=0,badVIreach=0;
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
    for(auto&kv:D){ int lo=-1,hi=-1; for(int h=0;h<=maxh;h++) if(kv.second[h]){ if(lo<0) lo=h; hi=h; } MM[kv.first]={lo,hi}; }
    vector<V> nz; for(auto&w:cols){ bool z=true; for(int x:w) if(x) z=false; if(!z) nz.push_back(w); }
    // candidate u: R + v for v in nz
    set<V> cand; for(auto&kv:MM) for(auto&v:nz){ V u=kv.first; for(int i=0;i<d;i++) u[i]+=v[i]; cand.insert(u); }
    for(auto&u:cand){
      vector<pair<int,int>> ivs; 
      for(auto&v:nz){ V z=u; for(int i=0;i<d;i++) z[i]-=v[i]; auto it=MM.find(z); if(it==MM.end()) continue; ivs.push_back({it->second.first+J[v], it->second.second+J[v]}); }
      auto itu=MM.find(u); bool reach=(itu!=MM.end());
      if(reach) for(auto&iv:ivs){ if(max(iv.first,itu->second.first)>min(iv.second,itu->second.second)) badKL++; }
      for(size_t a=0;a<ivs.size();a++) for(size_t b=a+1;b<ivs.size();b++){
        int lo=max(ivs[a].first,ivs[b].first), hi=min(ivs[a].second,ivs[b].second);
        if(lo>hi){ badVI++; if(reach) badVIreach++; }
        if(lo>hi+1) badVT++;
      }
    }
  }
  printf("tested=%ld badKL=%ld VKL-intersect-fails=%ld (of which u reachable %ld) VKL-touch-fails=%ld\n",tested,badKL,badVI,badVIreach,badVT);
}
