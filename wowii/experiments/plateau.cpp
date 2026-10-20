// Plateau walk over connected cubic graphs keeping i(G) - gamma_e(G) >= 0, starting from a given graph6. Report if >= 1.
#include <bits/stdc++.h>
using namespace std; typedef unsigned long long u64;
int n; u64 adj[64]; mt19937_64 rng;
int bestI; long nodesI;
void idom(u64 und,int sz){ if(sz>=bestI) return; if(!und){ bestI=sz; return; } nodesI++;
  int lb=(__builtin_popcountll(und)+3)/4; if(sz+lb>=bestI) return;
  int bv=-1,bc=99; for(u64 t=und;t;t&=t-1){ int v=__builtin_ctzll(t); int c=__builtin_popcountll((adj[v]|(1ULL<<v))&und); if(c<bc){bc=c;bv=v; if(c<=1)break;} }
  u64 opts=(adj[bv]|(1ULL<<bv))&und;
  for(u64 t=opts;t;t&=t-1){ int w=__builtin_ctzll(t); u64 cl=adj[w]|(1ULL<<w); idom(und&~cl,sz+1); } }
int iG(int ub){ bestI=ub; u64 all=(n==64)?~0ULL:((1ULL<<n)-1); idom(all,0); return bestI; }
vector<pair<int,int>> E; int bestM;
void mm(u64 matched,int sz){ if(sz>=bestM) return; int ue=-1; int undomE=0;
  for(int i=0;i<(int)E.size();i++){ auto [a,b]=E[i]; if(!((matched>>a)&1) && !((matched>>b)&1)){ if(ue<0) ue=i; undomE++; } }
  if(ue<0){ bestM=sz; return; } if(sz+(undomE+4)/5>=bestM) return; auto [a,b]=E[ue];
  for(int end=0;end<2;end++){ int u= end? b:a; u64 fr=adj[u]&~matched; for(u64 t=fr;t;t&=t-1){ int w=__builtin_ctzll(t); if(end==1 && w==a) continue; mm(matched|(1ULL<<u)|(1ULL<<w),sz+1);} } }
int gE(int ub){ E.clear(); for(int i=0;i<n;i++) for(u64 t=adj[i];t;t&=t-1){ int j=__builtin_ctzll(t); if(j>i) E.push_back({i,j}); } bestM=ub; mm(0,0); return bestM; }
bool connected(){ u64 seen=1,fr=1; while(fr){ u64 nf=0; for(u64 t=fr;t;t&=t-1) nf|=adj[__builtin_ctzll(t)]; nf&=~seen; seen|=nf; fr=nf; } return seen==((n==64)?~0ULL:((1ULL<<n)-1)); }
void parse(const string& s){ int p=0; n=s[p++]-63; for(int i=0;i<n;i++) adj[i]=0; int val=0,k=6;
  for(int j=1;j<n;j++) for(int i=0;i<j;i++){ if(k==6){ val=s[p++]-63; k=0; } int b=(val>>(5-k))&1; k++; if(b){ adj[i]|=1ULL<<j; adj[j]|=1ULL<<i; } } }
string g6(){ string s; s+=char(n+63); int val=0,k=0; for(int j=1;j<n;j++) for(int i=0;i<j;i++){ val=(val<<1)|((adj[i]>>j)&1); if(++k==6){ s+=char(val+63); val=0;k=0;} } if(k){ val<<=(6-k); s+=char(val+63);} return s; }
int main(int argc,char**argv){ parse(argv[1]); long iters=atol(argv[2]); rng.seed(atol(argv[3]));
  auto add=[&](int a,int b){ adj[a]|=1ULL<<b; adj[b]|=1ULL<<a; };
  int ci=iG(n), cg=gE(n); printf("start n=%d i=%d ge=%d\n",n,ci,cg); fflush(stdout);
  long acc=0;
  for(long it=0;it<iters;it++){
    vector<pair<int,int>> ed; for(int i=0;i<n;i++) for(u64 t=adj[i];t;t&=t-1){ int j=__builtin_ctzll(t); if(j>i) ed.push_back({i,j}); }
    auto [a,b]=ed[rng()%ed.size()]; auto [c,d]=ed[rng()%ed.size()]; if(rng()&1) swap(c,d);
    if(a==c||a==d||b==c||b==d) continue; if((adj[a]>>c)&1 || (adj[b]>>d)&1) continue;
    u64 save[64]; memcpy(save,adj,sizeof(adj));
    adj[a]&=~(1ULL<<b); adj[b]&=~(1ULL<<a); adj[c]&=~(1ULL<<d); adj[d]&=~(1ULL<<c); add(a,c); add(b,d);
    if(!connected()){ memcpy(adj,save,sizeof(adj)); continue; }
    // need i >= ge : compute ge first (cheap-ish), then check whether i >= ge via bounded search: i < ge iff exists IDS of size <= ge-1
    int ng=gE(cg+3); int ni=iG(ng+2);
    if(ni>=ng){ ci=ni; cg=ng; acc++; if(ni>ng){ printf("FOUND i=%d ge=%d %s\n",ni,ng,g6().c_str()); fflush(stdout); return 0; } }
    else memcpy(adj,save,sizeof(adj));
    if(it%500==0){ printf("it=%ld acc=%ld i=%d ge=%d\n",it,acc,ci,cg); fflush(stdout); }
  }
  printf("done acc=%ld\n",acc); }
