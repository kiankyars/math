// Random finite down-sets I in N^k; check subset-sum set is convex along each axis.
#include <bits/stdc++.h>
using namespace std;
typedef vector<int> V;
int main(int argc,char**argv){
  unsigned seed=atoi(argv[1]); int trials=atoi(argv[2]); int K=atoi(argv[3]); int side=atoi(argv[4]); int maxgen=atoi(argv[5]); int maxsz=atoi(argv[6]);
  mt19937 rng(seed);
  long bad=0, tested=0;
  for(int t=0;t<trials;t++){
    int k=1+rng()%K;
    int ng=1+rng()%maxgen;
    set<V> I;
    for(int g=0;g<ng;g++){
      V gen(k); for(int i=0;i<k;i++) gen[i]=rng()%(side+1);
      // add box
      V x(k,0);
      while(true){ I.insert(x); int i=0; while(i<k){ if(x[i]<gen[i]){x[i]++;break;} x[i]=0;i++;} if(i==k) break; }
    }
    if((int)I.size()>maxsz) continue;
    tested++;
    for(int ax=0;ax<k;ax++){
      // map key=other coords -> bitset (vector<bool>) of ax coordinate
      int maxh=0; for(auto&x:I) maxh+=x[ax];
      map<V, vector<uint64_t>> S; int W=maxh/64+1;
      V z(k-1,0); S[z]=vector<uint64_t>(W,0); S[z][0]=1;
      for(auto&x:I){
        V xo; for(int i=0;i<k;i++) if(i!=ax) xo.push_back(x[i]);
        int sh=x[ax];
        map<V, vector<uint64_t>> N=S;
        for(auto&kv:S){
          V key=kv.first; for(int i=0;i<k-1;i++) key[i]+=xo[i];
          auto& tgt=N[key]; if(tgt.empty()) tgt.assign(W,0);
          // tgt |= kv.second << sh
          int ws=sh/64, bs=sh%64;
          for(int i=W-1;i>=0;i--){
            uint64_t v=0;
            if(i-ws>=0){ v=kv.second[i-ws]<<bs; if(bs && i-ws-1>=0) v|=kv.second[i-ws-1]>>(64-bs);} 
            tgt[i]|=v;
          }
        }
        S.swap(N);
      }
      for(auto&kv:S){
        // check contiguous
        int lo=-1,hi=-1; long cnt=0;
        for(int i=0;i<W*64;i++) if(kv.second[i/64]>>(i%64)&1){ if(lo<0) lo=i; hi=i; cnt++; }
        if(cnt!=hi-lo+1){ bad++; if(bad<=5){ printf("FAIL k=%d ax=%d I=",k,ax); for(auto&x:I){printf("(");for(int v:x)printf("%d,",v);printf(")");} printf("\n");} break; }
      }
    }
  }
  printf("tested=%ld bad=%ld\n",tested,bad);
}
