// Down-set theorem stress test: random down-sets I in N^k (k=3..5), sizes up to maxsz; check axis convexity of subset sums along every axis.
// Representation: for axis ax, map from other coords (encoded) -> bitset of ax-sums (vector<uint64_t>).
#include <bits/stdc++.h>
using namespace std;
typedef vector<int> V;
int main(int argc,char**argv){
  unsigned seed=atoi(argv[1]); int trials=atoi(argv[2]); int kmin=atoi(argv[3]); int kmax=atoi(argv[4]); int side=atoi(argv[5]); int maxgen=atoi(argv[6]); int minsz=atoi(argv[7]); int maxsz=atoi(argv[8]);
  setvbuf(stdout,NULL,_IONBF,0); mt19937 rng(seed); long tested=0,bad=0;
  for(int t=0;t<trials;t++){
    int k=kmin+rng()%(kmax-kmin+1); int ng=1+rng()%maxgen; set<V> I;
    for(int g=0;g<ng;g++){ V gen(k); for(int i=0;i<k;i++) gen[i]=rng()%(side+1); V x(k,0);
      while(true){ I.insert(x); int i=0; while(i<k){ if(x[i]<gen[i]){x[i]++;break;} x[i]=0;i++;} if(i==k) break; } }
    if((int)I.size()<minsz||(int)I.size()>maxsz) continue;
    tested++;
    for(int ax=0;ax<k;ax++){
      int maxh=0; for(auto&x:I) maxh+=x[ax]; int W=maxh/64+1;
      unordered_map<unsigned long long, vector<uint64_t>> S; 
      auto enc=[&](const V&x){ unsigned long long e=0; for(int i=0;i<k;i++) if(i!=ax) e=e*4096+x[i]; return e; };
      // We'll iterate with key vectors stored separately
      map<V, vector<uint64_t>> M; V z(k,0); M[z]=vector<uint64_t>(W,0); M[z][0]=1;
      for(auto&x:I){
        if(x==V(k,0)) continue;
        vector<pair<V,vector<uint64_t>>> adds;
        for(auto&kv:M){ V key=kv.first; for(int i=0;i<k;i++) if(i!=ax) key[i]+=x[i];
          vector<uint64_t> sh(W,0); int ws=x[ax]/64, bs=x[ax]%64;
          for(int i=W-1;i>=0;i--){ uint64_t v=0; if(i-ws>=0){ v=kv.second[i-ws]<<bs; if(bs&&i-ws-1>=0) v|=kv.second[i-ws-1]>>(64-bs);} sh[i]=v; }
          adds.push_back({key,sh}); }
        for(auto&a:adds){ auto&tg=M[a.first]; if(tg.empty()) tg.assign(W,0); for(int i=0;i<W;i++) tg[i]|=a.second[i]; }
      }
      for(auto&kv:M){ int lo=-1,hi=-1; long cnt=0; for(int i=0;i<W*64;i++) if(kv.second[i/64]>>(i%64)&1){ if(lo<0) lo=i; hi=i; cnt++; }
        if(cnt!=hi-lo+1){ bad++; printf("FAIL k=%d ax=%d |I|=%zu gens:",k,ax,I.size()); printf("\n"); break; } }
    }
  }
  printf("tested=%ld bad=%ld\n",tested,bad);
}
