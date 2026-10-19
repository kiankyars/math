// Flat-first order: start with all (r,0), r p-free in [2,N]; then add (r,j), j>=1, in increasing order of p^j r.
// Check KL (all columns) at all stages, and degenerate configs D1 (w0) / D2,D3 (w0,v) at each raise.
#include <bits/stdc++.h>
using namespace std;
typedef __uint128_t K;
int main(int argc,char**argv){
  int N=atoi(argv[1]); int p=atoi(argv[2]);
  vector<int> pr; for(int q=2;q<=N;q++){bool ok=true; for(int d=2;d*d<=q;d++) if(q%d==0) ok=false; if(ok&&q!=p) pr.push_back(q);}
  int W=7; if((int)pr.size()*W>126){fprintf(stderr,"too big\n");return 1;}
  auto enc=[&](long x){K e=0; for(size_t i=0;i<pr.size();i++){int c=0; while(x%pr[i]==0){x/=pr[i];c++;} e+=((K)c)<<(W*i);} return e;};
  auto geq=[&](K a,K b){ for(size_t i=0;i<pr.size();i++) if(((a>>(W*i))&127)<((b>>(W*i))&127)) return false; return true; };
  vector<int> cols; for(int r=2;r<=N;r++) if(r%p) cols.push_back(r);
  map<int,int> J; for(int r:cols) J[r]=0;
  map<K,pair<int,int>> B; B[0]={0,0};
  auto addel=[&](int r,int j){ K er=enc(r); map<K,pair<int,int>> N2=B;
      for(auto&kv:B){ K u=kv.first+er; pair<int,int> c={kv.second.first+j,kv.second.second+j}; auto it=N2.find(u);
        if(it==N2.end()) N2[u]=c; else { it->second.first=min(it->second.first,c.first); it->second.second=max(it->second.second,c.second);} }
      B.swap(N2); };
  for(int r:cols) addel(r,0);
  long klfail=0,gfail=0,d1=0,d2=0,d3=0;
  for(int n=2;n<=N;n++){
    int j=0; long r=n; while(r%p==0){r/=p;j++;} if(j==0||r==1) continue;
    K er=enc(r); auto in=[&](K x){ return B.count(x)>0; };
    for(auto&kv:B){ K u=kv.first;
      if(geq(u,er+er) && in(u-er-er) && !in(u-er)) d1++;
      for(int v:cols){ if(v==r) continue; K ev=enc(v);
        if(geq(u,ev+er) && in(u-ev-er) && !(geq(u,ev)&&in(u-ev)) && !(geq(u,er)&&in(u-er))) d3++;
        K uu=u+er; if(!in(uu) && geq(uu,ev) && in(uu-ev) && !(geq(u,ev)&&in(u-ev))) d2++; } }
    addel(r,j); J[r]=j;
    // G and KL check
    for(auto&kv:B){ (void)kv; }
    for(auto&kv:B){ for(int v:cols){ K ev=enc(v); K u=kv.first; if(!geq(u,ev)) continue; auto it=B.find(u-ev); if(it==B.end()) continue;
        int lo=max(kv.second.first,it->second.first+J[v]), hi=min(kv.second.second,it->second.second+J[v]); if(lo>hi) klfail++; } }
  }
  printf("N=%d p=%d flat-first: KLfail=%ld  degenerate at raises: D1=%ld D2=%ld D3=%ld  |R|=%zu\n",N,p,klfail,d1,d2,d3,B.size());
}
