// For integer systems: max gap in V(R) (v_p-sums over subsets of non-p-powers with p-free product R), vs T+1.
#include <bits/stdc++.h>
using namespace std;
typedef __uint128_t u128;
int main(int argc,char**argv){
  int N=atoi(argv[1]); int p=atoi(argv[2]);
  vector<int> pr; for(int q=2;q<=N;q++){bool ok=true; for(int d=2;d*d<=q;d++) if(q%d==0) ok=false; if(ok&&q!=p) pr.push_back(q);}
  int W=7; if((int)pr.size()*W>128){fprintf(stderr,"too big\n");return 1;}
  auto enc=[&](int x){u128 e=0; for(size_t i=0;i<pr.size();i++){int c=0; while(x%pr[i]==0){x/=pr[i];c++;} e+=((u128)c)<<(W*i);} return e;};
  int J1=0; {long x=p; while(x<=N){J1++; x*=p;}} int T=J1*(J1+1)/2;
  // V(R) as bitset (uint64 x 4 => up to 256)
  typedef array<uint64_t,4> BS;
  map<u128,BS> D; BS z{}; z[0]=1; D[0]=z;
  for(int n=2;n<=N;n++){ int j=0; long r=n; while(r%p==0){r/=p;j++;} if(r==1) continue; // skip p-powers
    u128 er=enc(r); map<u128,BS> N2=D;
    for(auto&kv:D){ BS s=kv.second, sh{}; for(int i=3;i>=0;i--){ int ws=j/64,bs=j%64; uint64_t v=0; if(i-ws>=0){ v=s[i-ws]<<bs; if(bs&&i-ws-1>=0) v|=s[i-ws-1]>>(64-bs);} sh[i]=v; }
      auto&tg=N2[kv.first+er]; for(int i=0;i<4;i++) tg[i]|=sh[i]; }
    D.swap(N2); }
  int maxgap=0; long cnt=0;
  for(auto&kv:D){ int prev=-1; for(int i=0;i<256;i++) if(kv.second[i/64]>>(i%64)&1){ if(prev>=0) maxgap=max(maxgap,i-prev); prev=i; } }
  printf("N=%d p=%d J=%d T=%d maxgap(V)=%d  (conj needs <= %d)\n",N,p,J1,T,maxgap,T+1);
}
