// Simulated annealing over connected cubic graphs on n vertices maximizing i(G) - gamma_e(G).
#include <bits/stdc++.h>
using namespace std; typedef unsigned long long u64;
int n; u64 adj[64]; mt19937_64 rng;
int bestI;
void idom(u64 dom,u64 und,int sz){ if(sz>=bestI) return; if(!und){ bestI=sz; return; }
  // lower bound: each new vertex dominates at most 4 undominated
  int lb=(__builtin_popcountll(und)+3)/4; if(sz+lb>=bestI) return;
  // choose undominated v with fewest undominated closed-neighbours
  int bv=-1,bc=99; for(u64 t=und;t;t&=t-1){ int v=__builtin_ctzll(t); int c=__builtin_popcountll((adj[v]|(1ULL<<v))&und); if(c<bc){bc=c;bv=v; if(c<=1)break;} }
  u64 opts=(adj[bv]|(1ULL<<bv))&und;
  for(u64 t=opts;t;t&=t-1){ int w=__builtin_ctzll(t); u64 cl=adj[w]|(1ULL<<w); idom(dom|cl,und&~cl,sz+1); }
}
int iG(){ bestI=n+1; u64 all=(n==64)?~0ULL:((1ULL<<n)-1); idom(0,all,0); return bestI; }
vector<pair<int,int>> E; int bestM;
void mm(u64 matched,int sz,int lbBase){ if(sz>=bestM) return; int ue=-1; int undomE=0;
  for(int i=0;i<(int)E.size();i++){ auto [a,b]=E[i]; if(!((matched>>a)&1) && !((matched>>b)&1)){ if(ue<0) ue=i; undomE++; } }
  if(ue<0){ bestM=sz; return; } if(sz+(undomE+4)/5>=bestM) return; auto [a,b]=E[ue];
  for(int end=0;end<2;end++){ int u= end? b:a; u64 fr=adj[u]&~matched; for(u64 t=fr;t;t&=t-1){ int w=__builtin_ctzll(t); if(end==1 && w==a) continue; mm(matched|(1ULL<<u)|(1ULL<<w),sz+1,lbBase);} } }
int gE(){ E.clear(); for(int i=0;i<n;i++) for(u64 t=adj[i];t;t&=t-1){ int j=__builtin_ctzll(t); if(j>i) E.push_back({i,j}); } bestM=n/2+1; mm(0,0,0); return bestM; }
bool connected(){ u64 seen=1,fr=1; while(fr){ u64 nf=0; for(u64 t=fr;t;t&=t-1) nf|=adj[__builtin_ctzll(t)]; nf&=~seen; seen|=nf; fr=nf; } return seen==((n==64)?~0ULL:((1ULL<<n)-1)); }
string g6(){ string s; s+=char(n+63); int val=0,k=0; for(int j=1;j<n;j++) for(int i=0;i<j;i++){ val=(val<<1)|((adj[i]>>j)&1); if(++k==6){ s+=char(val+63); val=0;k=0;} } if(k){ val<<=(6-k); s+=char(val+63);} return s; }
int main(int argc,char**argv){ n=atoi(argv[1]); long iters=atol(argv[2]); rng.seed(atol(argv[3])); double T0=argc>4?atof(argv[4]):0.5;
  // random cubic graph via configuration-ish: start with circulant-ish then randomize by swaps
  for(int i=0;i<n;i++) adj[i]=0;
  auto add=[&](int a,int b){ adj[a]|=1ULL<<b; adj[b]|=1ULL<<a; };
  for(int i=0;i<n;i++) add(i,(i+1)%n); for(int i=0;i<n/2;i++) add(i,i+n/2);
  auto score=[&](int& ii,int& gg){ ii=iG(); gg=gE(); return ii-gg; };
  int ci,cg; int cur=score(ci,cg); int best=cur;
  for(long it=0;it<iters;it++){
    // double edge swap
    vector<pair<int,int>> ed; for(int i=0;i<n;i++) for(u64 t=adj[i];t;t&=t-1){ int j=__builtin_ctzll(t); if(j>i) ed.push_back({i,j}); }
    auto [a,b]=ed[rng()%ed.size()]; auto [c,d]=ed[rng()%ed.size()];
    if(rng()&1) swap(c,d);
    if(a==c||a==d||b==c||b==d) continue; if((adj[a]>>c)&1 || (adj[b]>>d)&1) continue;
    u64 save[64]; memcpy(save,adj,sizeof(adj));
    adj[a]&=~(1ULL<<b); adj[b]&=~(1ULL<<a); adj[c]&=~(1ULL<<d); adj[d]&=~(1ULL<<c); add(a,c); add(b,d);
    if(!connected()){ memcpy(adj,save,sizeof(adj)); continue; }
    int ni,ng; int s=score(ni,ng);
    double T=T0*(1.0-(double)it/iters)+1e-3;
    if(s>=cur || exp((s-cur)/T) > (rng()%1000000)/1e6){ cur=s; ci=ni; cg=ng; if(s>best){ best=s; } if(s>=1){ printf("FOUND i=%d gamma_e=%d %s\n",ni,ng,g6().c_str()); fflush(stdout); return 0; } }
    else memcpy(adj,save,sizeof(adj));
    if(it%2000==0){ printf("it=%ld cur=%d (i=%d,ge=%d) best=%d\n",it,cur,ci,cg,best); fflush(stdout); }
  }
  printf("done best=%d\n",best);
}
