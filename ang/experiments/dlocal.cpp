// J1=1 regime (p^2 > N): factorizations c of R over p-free r in [2,N], caps 2 for r<=N/p else 1.
// d(c) = #{r: c_r=2}. Check (1) gaps of D(R) <= 2 and actual max gap; (2) every quadratic-move-local-min of d is global min.
#include <bits/stdc++.h>
using namespace std;
int main(int argc,char**argv){
  int N=atoi(argv[1]); int p=atoi(argv[2]);
  if((long)p*p<=N){ printf("need p^2>N\n"); return 0; }
  vector<int> cls; vector<int> cap; for(int r=2;r<=N;r++) if(r%p){ cls.push_back(r); cap.push_back(2*r<=N/p*2 && r<=N/p ? 2 : 1); }
  int n=cls.size(); map<int,int> idx; for(int i=0;i<n;i++) idx[cls[i]]=i;
  // enumerate factorizations grouped by product (product may be huge: use exponent vector key)
  vector<int> pr; for(int q=2;q<=N;q++){bool ok=true; for(int d=2;d*d<=q;d++) if(q%d==0) ok=false; if(ok&&q!=p) pr.push_back(q);}
  vector<vector<int>> E(n, vector<int>(pr.size(),0)); for(int i=0;i<n;i++){ int x=cls[i]; for(size_t j=0;j<pr.size();j++) while(x%pr[j]==0){x/=pr[j];E[i][j]++;} }
  map<vector<int>, vector<vector<char>>> G; vector<char> c(n,0); vector<int> R(pr.size(),0);
  function<void(int)> rec=[&](int i){ if(i==n){ G[R].push_back(c); return; } for(int k=0;k<=cap[i];k++){ c[i]=k; rec(i+1); for(size_t j=0;j<pr.size();j++) R[j]+=E[i][j]; } for(size_t j=0;j<pr.size();j++) R[j]-=(cap[i]+1)*E[i][j]; c[i]=0; };
  rec(0);
  long maxgapD=0, badlocal=0, nR=0;
  for(auto&kv:G){ auto&L=kv.second; if(L.size()<2) continue; nR++;
    set<int> Ds; auto dfun=[&](const vector<char>&x){ int d=0; for(int i=0;i<n;i++) if(x[i]==2) d++; return d; };
    int dmin=INT_MAX; for(auto&x:L){ int d=dfun(x); Ds.insert(d); dmin=min(dmin,d); }
    int prev=-1; for(int d:Ds){ if(prev>=0) maxgapD=max<long>(maxgapD,d-prev); prev=d; }
    set<vector<char>> S(L.begin(),L.end());
    for(auto&x:L){ int d=dfun(x); if(d==dmin) continue;
      // try all quadratic moves: remove up to 2 copies (blocks a,b) and add up to 2 (e,f) with same product
      bool improved=false; vector<int> bl; for(int i=0;i<n;i++) for(int k=0;k<x[i];k++) bl.push_back(i);
      for(size_t a=0;a<bl.size()&&!improved;a++) for(int b=-1;b<(int)bl.size()&&!improved;b++){ if(b>=0&&b<=(int)a) continue;
        long P=cls[bl[a]]*(long)(b<0?1:cls[bl[b]]);
        for(long d1=1;d1*d1<=P&&!improved;d1++) if(P%d1==0){ long d2=P/d1; if(d2>N) continue; if(d1%p==0||d2%p==0) continue;
          auto y=x; y[bl[a]]--; if(b>=0) y[bl[b]]--; bool ok=true;
          for(long z:{d1,d2}){ if(z==1) continue; int id=idx[(int)z]; y[id]++; if(y[id]>cap[id]) ok=false; }
          if(ok && dfun(y)<d){ improved=true; } } }
      if(!improved) badlocal++; }
  }
  printf("N=%d p=%d #R(multi)=%ld maxgap(D)=%ld local-nonglobal-d-min=%ld\n",N,p,nR,maxgapD,badlocal);
}
