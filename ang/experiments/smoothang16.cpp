// Ang's conjecture restricted to a smooth slice: numbers p^j * q1^a q2^b q3^c <= N (q's != p).
// Exact fibres V(R) (heights from non-p-power columns) as bitsets; report max gap of V and whether W=V+[0,T] has gaps (=> counterexample).
#include <bits/stdc++.h>
using namespace std;
typedef long long ll; typedef unsigned long long u64;
const int WB=64; // bitset words
int main(int argc,char**argv){
  ll N=atoll(argv[1]); int p=atoi(argv[2]); vector<int> qs; for(int i=3;i<argc;i++) qs.push_back(atoi(argv[i]));
  int k=qs.size();
  // enumerate smooth numbers r (p-free, >1) <= N
  vector<ll> rs; function<void(int,ll)> gen=[&](int i,ll v){ if(i==k){ if(v>1) rs.push_back(v); return;} for(ll x=v;x<=N;x*=qs[i]) gen(i+1,x); };
  gen(0,1);
  int J1=0; {ll x=p; while(x<=N){J1++; x*=p;}} int T=J1*(J1+1)/2;
  int maxh=0; vector<int> Jr; for(ll r:rs){ int j=0; ll w=r; while(w*p<=N){w*=p;j++;} Jr.push_back(j); maxh+=j*(j+1)/2; }
  int words=maxh/64+1; if(words>WB){ printf("maxh too big %d\n",maxh); return 0; }
  // guard
  { vector<ll> tot(k,0); for(size_t ci=0;ci<rs.size();ci++){ ll r=rs[ci]; for(int i=0;i<k;i++){ int c=0; while(r%qs[i]==0){r/=qs[i];c++;} tot[i]+=(ll)c*(Jr[ci]+1);} } for(int i=0;i<k;i++) if(tot[i]>=65536||k>4){ printf("overflow risk\n"); return 0;} }
  auto enc=[&](ll r){ u64 e=0; for(int i=0;i<k;i++){ int c=0; while(r%qs[i]==0){r/=qs[i];c++;} e|=((u64)c)<<(16*i);} return e; };
  typedef array<u64,WB> BS;
  unordered_map<u64,BS> D; BS z{}; z[0]=1; D[0]=z;
  for(size_t ci=0;ci<rs.size();ci++){ u64 er=enc(rs[ci]); int J=Jr[ci];
    for(int h=0;h<=J;h++){ // add element (r,h)
      vector<pair<u64,BS>> adds; adds.reserve(D.size());
      for(auto&kv:D){ BS s{}; int ws=h/64,bs=h%64; for(int i=words-1;i>=0;i--){ u64 v=0; if(i-ws>=0){ v=kv.second[i-ws]<<bs; if(bs&&i-ws-1>=0) v|=kv.second[i-ws-1]>>(64-bs);} s[i]=v; } adds.push_back({kv.first+er,s}); }
      for(auto&a:adds){ auto it=D.find(a.first); if(it==D.end()) D.emplace(a.first,a.second); else for(int i=0;i<words;i++) it->second[i]|=a.second[i]; } } }
  int maxgap=0; long wgaps=0; u64 worstR=0;
  for(auto&kv:D){ int prev=-1; for(int h=0;h<=maxh;h++) if(kv.second[h/64]>>(h%64)&1){ if(prev>=0&&h-prev>maxgap){maxgap=h-prev; worstR=kv.first;} if(prev>=0&&h-prev>T+1) wgaps++; prev=h; } }
  printf("N=%lld p=%d smooth over",N,p); for(int q:qs) printf(" %d",q); printf(": cols=%zu |R|=%zu maxh=%d T=%d maxgap(V)=%d  W-gaps(counterexamples)=%ld\n",rs.size(),D.size(),maxh,T,maxgap,wgaps);
}
