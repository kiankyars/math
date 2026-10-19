// Natural-order induction for Ang (excluding p-powers' column, i.e. columns r>=2 p-free).
// At stage n, columns v in D_N* (p-free 2..N) have J_v = floor(log_p(n/v)) (=-1 if v>n).
// Check: KL for all v (incl. future, J=-1) at all stages; and degenerate configs for the step n->n+1.
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
  map<K,pair<int,int>> B; B[0]={0,0};
  auto Jv=[&](int v,int n){ if(v>n) return -1; int j=0; long x=v; while(x*p<=n){x*=p;j++;} return j; };
  long klfail=0, klfut0=0, kltouch=0, d1=0,d2p=0,d2f=0,d3p=0,d3f=0;
  for(int n=1;n<=N;n++){
    // step: add element n
    int j=0; long r=n; while(r%p==0){r/=p;j++;}
    if(r>1){
      K er=enc(r);
      // degenerate configs for w0=r w.r.t. current R (stage n-1)
      auto in=[&](K x){ return B.count(x)>0; };
      for(auto&kv:B){ K u=kv.first;
        // D1: u, u-2w0 in R, u-w0 not
        if(geq(u,er+er) && in(u-er-er) && !in(u-er)) d1++;
        for(int v:cols){ if(v==r) continue; K ev=enc(v);
          // D3: u in R, u-v-w0 in R, u-v, u-w0 not
          if(geq(u,ev+er) && in(u-ev-er) && !(geq(u,ev)&&in(u-ev)) && !(geq(u,er)&&in(u-er))){ if(v<=n-1) d3p++; else d3f++; }
          // D2: (u = a + w0 with a in R) u not in R, u-v in R, u-v-w0 not in R
          K uu=u+er; if(!in(uu) && geq(uu,ev) && in(uu-ev) && !(geq(u,ev)&&in(u-ev))){ if(v<=n-1) d2p++; else d2f++; }
        } }
      map<K,pair<int,int>> N2=B;
      for(auto&kv:B){ K u=kv.first+er; pair<int,int> c={kv.second.first+j,kv.second.second+j}; auto it=N2.find(u);
        if(it==N2.end()) N2[u]=c; else { it->second.first=min(it->second.first,c.first); it->second.second=max(it->second.second,c.second);} }
      B.swap(N2);
    }
    // KL check at stage n for all columns v in D_N* (including future J=-1)
    for(auto&kv:B){ for(int v:cols){ K ev=enc(v); K u=kv.first; if(!geq(u,ev)) continue; auto it=B.find(u-ev); if(it==B.end()) continue; int J=Jv(v,n);
        if(J>=0){ int lo=max(kv.second.first,it->second.first+J), hi=min(kv.second.second,it->second.second+J); if(lo>hi) klfail++; }
        else { int lo=max(kv.second.first,it->second.first), hi=min(kv.second.second,it->second.second); if(lo>hi) klfut0++; if(lo>hi+1) kltouch++; } } }
  }
  printf("N=%d p=%d: KLfail(present)=%ld KL0fail(future,intersect)=%ld (touch-fail %ld) | steps: D1=%ld D2 present=%ld future=%ld D3 present=%ld future=%ld\n",N,p,klfail,klfut0,kltouch,d1,d2p,d2f,d3p,d3f);
}
