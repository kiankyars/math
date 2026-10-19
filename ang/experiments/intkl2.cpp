// Integer systems: stage n (elements 1..n). Check KL (intersect) and R1-R3 for R_n (p-free parts), all p-free r,r'<=n.
#include <bits/stdc++.h>
using namespace std;
typedef __uint128_t u64;
int main(int argc,char**argv){
  int NMAX=atoi(argv[1]); int p=atoi(argv[2]);
  vector<int> pr; for(int q=2;q<=NMAX;q++){bool ok=true; for(int d=2;d*d<=q;d++) if(q%d==0) ok=false; if(ok&&q!=p) pr.push_back(q);}
  // encode exponent vector: 5 bits per prime -> need pr.size()*5 <= 64
  int W=7; if((int)pr.size()*W>124){fprintf(stderr,"too big\n");return 1;}
  auto enc=[&](long x){u64 e=0; for(size_t i=0;i<pr.size();i++){int c=0; while(x%pr[i]==0){x/=pr[i];c++;} e+=((u64)c)<<(W*i);} return e;};
  // state: map R -> (minh,maxh) of v_p-sum including p-powers
  map<u64,pair<int,int>> B; B[0]={0,0};
  map<int,int> J; // column heights J(r) = max j with r p^j <= n  (for r p-free, r>1)
  long totKL=0, r1=0,r2=0,r3=0;
  for(int n=1;n<=NMAX;n++){
    int j=0; long r=n; while(r%p==0){r/=p;j++;}
    u64 er=enc(r);
    // add element n = p^j r: B'(u) = B(u) U (j + B(u-er))
    map<u64,pair<int,int>> N2=B;
    for(auto&kv:B){ u64 u=kv.first+er; auto it=N2.find(u); pair<int,int> c={kv.second.first+j,kv.second.second+j};
      if(it==N2.end()) N2[u]=c; else { it->second.first=min(it->second.first,c.first); it->second.second=max(it->second.second,c.second);} }
    B.swap(N2);
    if(r>1) J[r]=j;
    // checks at stage n (only every stage for small n)
    vector<pair<u64,int>> cols; for(auto&kv:J) cols.push_back({enc(kv.first),kv.second});
    long kl=0;
    for(auto&kv:B){ for(auto&c:cols){ u64 u=kv.first; // check u-c in R: need componentwise >=
        bool ge=true; for(size_t i=0;i<pr.size();i++){ if(((u>>(W*i))&127)<((c.first>>(W*i))&127)){ge=false;break;} } if(!ge) continue;
        auto it=B.find(u-c.first); if(it==B.end()) continue;
        int lo=max(kv.second.first,it->second.first+c.second), hi=min(kv.second.second,it->second.second+c.second); if(lo>hi) kl++; } }
    // R1-R3
    auto in=[&](u64 x){ return B.count(x)>0; };
    auto geq=[&](u64 a,u64 b){ for(size_t i=0;i<pr.size();i++) if(((a>>(W*i))&127)<((b>>(W*i))&127)) return false; return true; };
    long f1=0,f2=0,f3=0;
    for(auto&kv:B){ u64 u=kv.first;
      for(size_t a=0;a<cols.size();a++){ u64 w=cols[a].first;
        if(geq(u,w+w) && in(u-w-w) && !(geq(u,w)&&in(u-w))) f1++;
        for(size_t b=a+1;b<cols.size();b++){ u64 w2=cols[b].first;
          // R3: u, u-w-w2 in R => u-w or u-w2
          if(geq(u,w+w2)&&in(u-w-w2)){ bool o1=geq(u,w)&&in(u-w), o2=geq(u,w2)&&in(u-w2); if(!o1&&!o2) f3++; }
          // R2 with x = u - w - w2 (x may be "negative"): x+w = u-w2, x+w2 = u-w in R, need u in R (true) ... handle: a = u in R as x+w
        }
        for(size_t b=0;b<cols.size();b++){ if(b==a) continue; u64 w2=cols[b].first;
          // R2: a=u=x+w in R, x+w2 = u-w+w2 in R => x=u-w in R or x+w+w2 = u+w2 in R
          // compute u-w+w2 (need u+w2 >= w)
          u64 s=u+w2; if(!geq(s,w)) continue; u64 b2=s-w; if(!in(b2)) continue;
          bool ok1= geq(u,w)&&in(u-w); bool ok2=in(s); if(!ok1&&!ok2) f2++; }
      } }
    totKL+=kl; r1+=f1; r2+=f2; r3+=f3;
    if(kl||f1||f2||f3) printf("n=%d p=%d: KLfail=%ld R1=%ld R2=%ld R3=%ld |R|=%zu\n",n,p,kl,f1,f2,f3,B.size());
  }
  printf("p=%d up to n=%d: KLfail=%ld R1=%ld R2=%ld R3=%ld\n",p,NMAX,totKL,r1,r2,r3);
}
