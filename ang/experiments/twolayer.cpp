// Two-layer monotone systems: D down-closed (all at height 0), D1 subset D down-closed raised to height 1 in a linear-extension order.
// Check: G, KL0 for unraised columns of D1, and degenerate configs D2/D3 for (w0, v unraised in D1).
#include <bits/stdc++.h>
using namespace std;
typedef vector<int> V;
int main(int argc,char**argv){
  unsigned seed=atoi(argv[1]); int trials=atoi(argv[2]); int dmax=atoi(argv[3]); int side=atoi(argv[4]); int maxcols=atoi(argv[5]);
  setvbuf(stdout,NULL,_IONBF,0); mt19937 rng(seed); long tested=0,gfail=0,klfail=0,d2=0,d3=0;
  auto box=[&](set<V>&S,const V&g,int d){ V x(d,0); while(true){ S.insert(x); int i=0; while(i<d){ if(x[i]<g[i]){x[i]++;break;} x[i]=0;i++;} if(i==d) break; } };
  for(int t=0;t<trials;t++){
    int d=1+rng()%dmax; set<V> Ds,D1s; int ng=1+rng()%4; vector<V> gens;
    for(int g=0;g<ng;g++){ V gen(d); for(int i=0;i<d;i++) gen[i]=rng()%(side+1); gens.push_back(gen); box(Ds,gen,d); }
    int n1=1+rng()%3; for(int g=0;g<n1;g++){ auto it=Ds.begin(); advance(it,rng()%Ds.size()); box(D1s,*it,d); }
    Ds.erase(V(d,0)); D1s.erase(V(d,0)); if(Ds.empty()||(int)Ds.size()>maxcols) continue;
    vector<V> cols(Ds.begin(),Ds.end()); map<V,int> idx; for(size_t i=0;i<cols.size();i++) idx[cols[i]]=i;
    vector<V> D1(D1s.begin(),D1s.end()); sort(D1.begin(),D1.end(),[](const V&a,const V&b){int sa=0,sb=0; for(int x:a)sa+=x; for(int x:b)sb+=x; if(sa!=sb) return sa<sb; return a<b;});
    tested++;
    int maxh=D1.size();
    map<V,vector<char>> B; B[V(d,0)]=vector<char>(maxh+1,0); B[V(d,0)][0]=1;
    auto addel=[&](const V&w,int h){ map<V,vector<char>> N2=B; for(auto&kv:B){ V u=kv.first; for(int i=0;i<d;i++) u[i]+=w[i]; auto&tg=N2[u]; if(tg.empty()) tg.assign(maxh+1,0); for(int x=0;x+h<=maxh;x++) if(kv.second[x]) tg[x+h]=1; } B.swap(N2); };
    for(auto&w:cols) addel(w,0);
    set<V> raised;
    auto in=[&](const V&x){ for(int v:x) if(v<0) return false; return B.count(x)>0; };
    auto sub=[&](V a,const V&b){ for(int i=0;i<d;i++) a[i]-=b[i]; return a; };
    auto add=[&](V a,const V&b){ for(int i=0;i<d;i++) a[i]+=b[i]; return a; };
    for(auto&w0:D1){
      // degenerate configs before raising w0, for v unraised in D1, v != w0
      for(auto&v:D1){ if(v==w0||raised.count(v)) continue;
        for(auto&kv:B){ V u=kv.first;
          if(in(sub(sub(u,v),w0)) && !in(sub(u,v)) && !in(sub(u,w0))) d3++;
          V uu=add(u,w0); if(!in(uu) && in(sub(uu,v)) && !in(sub(u,v))) d2++; } }
      addel(w0,1); raised.insert(w0);
      // G and KL0 for unraised
      for(auto&kv:B){ int lo=-1,hi=-1,c=0; for(int x=0;x<=maxh;x++) if(kv.second[x]){ if(lo<0) lo=x; hi=x; c++; } if(c!=hi-lo+1) gfail++;
        for(auto&v:D1){ if(raised.count(v)) continue; V z=sub(kv.first,v); if(!in(z)) continue; auto&b2=B[z]; bool inter=false; for(int x=0;x<=maxh;x++) if(kv.second[x]&&b2[x]) inter=true; if(!inter) klfail++; } }
    }
  }
  printf("tested=%ld Gfail=%ld KL0fail(unraised)=%ld D2=%ld D3=%ld\n",tested,gfail,klfail,d2,d3);
}
