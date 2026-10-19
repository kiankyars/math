// Test TC: for each R, exists L-minimizer c1 and H-maximizer c2 with L(c2) <= H(c1)+T+1.
#include <bits/stdc++.h>
using namespace std;
typedef __uint128_t u128;
int main(int argc,char**argv){
  int N=atoi(argv[1]); int p=atoi(argv[2]);
  vector<int> pr; for(int q=2;q<=N;q++){bool ok=true; for(int d=2;d*d<=q;d++) if(q%d==0) ok=false; if(ok&&q!=p) pr.push_back(q);}
  int W=7; if((int)pr.size()*W>128){fprintf(stderr,"too big\n");return 1;}
  auto enc=[&](int x){u128 e=0; for(size_t i=0;i<pr.size();i++){int c=0; while(x%pr[i]==0){x/=pr[i];c++;} e+=((u128)c)<<(W*i);} return e;};
  int J1=0; {long x=p; while(x<=N){J1++; x*=p;}} int T=J1*(J1+1)/2;
  // state per R: (minL, maxH among minL), (maxH, minL among maxH)
  struct St{int mL,hAtmL,MH,lAtMH;};
  map<u128,St> D; D[0]={0,0,0,0};
  for(int r=2;r<=N;r++){ if(r%p==0) continue; int c=0; for(long x=r;x<=N;x*=p) c++; int Jr=c-1;
    u128 er=enc(r); map<u128,St> N2;
    for(auto&kv:D){ u128 y=kv.first; for(int k=0;k<=c;k++){ int L=k*(k-1)/2, H=k*Jr-k*(k-1)/2; St s=kv.second; St n2={s.mL+L,s.hAtmL+H,s.MH+H,s.lAtMH+L};
        auto it=N2.find(y); if(it==N2.end()) N2[y]=n2; else { St&t=it->second; if(n2.mL<t.mL||(n2.mL==t.mL&&n2.hAtmL>t.hAtmL)){t.mL=n2.mL;t.hAtmL=n2.hAtmL;} if(n2.MH>t.MH||(n2.MH==t.MH&&n2.lAtMH<t.lAtMH)){t.MH=n2.MH;t.lAtMH=n2.lAtMH;} }
        y+=er; } }
    D.swap(N2);}
  long fail=0, single=0; int worst=-1000;
  for(auto&kv:D){ St s=kv.second; int slack=s.hAtmL+T+1-s.lAtMH; worst=max(worst,-slack); if(slack<0) fail++; if(s.hAtmL==s.MH) single++; }
  printf("N=%d p=%d T=%d #R=%zu TCfail=%ld singleCfg=%ld worstDeficit=%d\n",N,p,T,D.size(),fail,single,worst);
}
