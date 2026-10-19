// CheapMove lemma test: for every R and every factorization c with L(c) > L*(R): exists Delta (<=2 copies from repeated classes)
// such that min{ L(c') : c' >= core(c)-Delta, c' in Gamma_R } < L(c).
#include <bits/stdc++.h>
using namespace std;
int N,p; vector<int> cls; vector<int> capv; vector<vector<int>> E; int np;
map<vector<int>,int> memo; vector<int> base; // base counts
int bestcost(int i, vector<int>& q){ // min added L to factor q using classes i..end given base
  bool zero=true; for(int x:q) if(x){zero=false;break;} if(zero) return 0;
  if(i==(int)cls.size()) return 1e9;
  vector<int> key=q; key.push_back(i);
  auto it=memo.find(key); if(it!=memo.end()) return it->second;
  int res=bestcost(i+1,q);
  int k0=base[i]; vector<int> qq=q; int k=0;
  while(true){ bool ok=true; for(int j=0;j<np;j++) if(qq[j]<E[i][j]){ok=false;break;} if(!ok) break; if(k0+k+1>capv[i]) break;
    for(int j=0;j<np;j++) qq[j]-=E[i][j]; k++;
    int cost=(k0+k)*(k0+k-1)/2-k0*(k0-1)/2;
    int r=bestcost(i+1,qq); if(r<1e9) res=min(res,cost+r); }
  memo[key]=res; return res;
}
int main(int argc,char**argv){
  N=atoi(argv[1]); p=atoi(argv[2]);
  for(int r=2;r<=N;r++) if(r%p){int c=0; for(long x=r;x<=N;x*=p) c++; cls.push_back(r); capv.push_back(c);}
  vector<int> pr; for(int q=2;q<=N;q++){bool ok=true; for(int d=2;d*d<=q;d++) if(q%d==0) ok=false; if(ok&&q!=p) pr.push_back(q);}
  np=pr.size();
  for(int r:cls){vector<int> e(np); int x=r; for(int j=0;j<np;j++) while(x%pr[j]==0){x/=pr[j];e[j]++;} E.push_back(e);}
  map<vector<int>, vector<vector<int>>> G; vector<int> cnt(cls.size(),0), Rv(np,0);
  function<void(int)> rec=[&](int i){ if(i==(int)cls.size()){ G[Rv].push_back(cnt); return; }
    for(int k=0;k<=capv[i];k++){ cnt[i]=k; if(k) for(int j=0;j<np;j++) Rv[j]+=E[i][j]; rec(i+1);} for(int j=0;j<np;j++) Rv[j]-=capv[i]*E[i][j]; cnt[i]=0; };
  rec(0);
  long tested=0, fails=0;
  for(auto& kv:G){ auto& lst=kv.second; if(lst.size()<2) continue;
    auto Lf=[&](const vector<int>& c){int s=0; for(int k:c) s+=k*(k-1)/2; return s;};
    int Ls=INT_MAX; for(auto&c:lst) Ls=min(Ls,Lf(c));
    for(auto& c:lst){ int Lc=Lf(c); if(Lc==Ls) continue; tested++;
      vector<int> rep; for(size_t i=0;i<cls.size();i++) if(c[i]>=2) rep.push_back(i);
      bool found=false;
      vector<vector<int>> choices; for(int a:rep) choices.push_back({a}); for(size_t a=0;a<rep.size();a++) for(size_t b=a;b<rep.size();b++) choices.push_back({rep[a],rep[b]});
      for(auto& ch:choices){
        base.assign(cls.size(),0); vector<int> q(np,0);
        for(size_t i=0;i<cls.size();i++){ if(c[i]>=2) base[i]=c[i]; else if(c[i]==1){ for(int j=0;j<np;j++) q[j]+=E[i][j]; } }
        bool ok=true; for(int a:ch){ if(base[a]<1){ok=false;break;} base[a]--; for(int j=0;j<np;j++) q[j]+=E[a][j]; }
        if(!ok) continue;
        int b0=0; for(int k:base) b0+=k*(k-1)/2;
        if(b0>=Lc) continue;
        memo.clear(); int add=bestcost(0,q);
        if(b0+add<Lc){found=true;break;}
      }
      if(!found){ fails++; if(fails<5){ printf("FAIL c:"); for(size_t i=0;i<cls.size();i++) if(c[i]) printf(" %d^%d",cls[i],c[i]); printf("  L=%d L*=%d\n",Lc,Ls);} }
    } }
  printf("N=%d p=%d tested=%ld fails=%ld\n",N,p,tested,fails); fflush(stdout);
}
