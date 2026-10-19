// For each level n and prime p: for each R, compute pair-move components of Gamma_R; check each contains an L-minimizer.
#include <bits/stdc++.h>
using namespace std;
int main(int argc,char**argv){
  int NMAX=atoi(argv[1]); int p=atoi(argv[2]); int NMIN=argc>3?atoi(argv[3]):4;
  for(int N=NMIN;N<=NMAX;N++){
  vector<int> cls; map<int,int> capv;
  for(int r=2;r<=N;r++) if(r%p){int c=0; for(long x=r;x<=N;x*=p) c++; cls.push_back(r); capv[r]=c;}
  vector<int> pr; for(int q=2;q<=N;q++){bool ok=true; for(int d=2;d*d<=q;d++) if(q%d==0) ok=false; if(ok&&q!=p) pr.push_back(q);}
  auto expv=[&](long x){vector<int> e(pr.size()); for(size_t i=0;i<pr.size();i++) while(x%pr[i]==0){x/=pr[i];e[i]++;} return e;};
  vector<vector<int>> E; for(int r:cls) E.push_back(expv(r));
  map<vector<int>, vector<vector<int>>> G;
  vector<int> cnt(cls.size(),0), Rv(pr.size(),0);
  function<void(int)> rec=[&](int i){
    if(i==(int)cls.size()){ G[Rv].push_back(cnt); return; }
    int c=capv[cls[i]];
    for(int k=0;k<=c;k++){ cnt[i]=k; if(k) for(size_t j=0;j<pr.size();j++) Rv[j]+=E[i][j];  rec(i+1); }
    for(size_t j=0;j<pr.size();j++) Rv[j]-=c*E[i][j]; cnt[i]=0;
  };
  rec(0);
  map<int,int> idx; for(size_t i=0;i<cls.size();i++) idx[cls[i]]=i;
  auto Lf=[&](const vector<int>& c){int s=0; for(int k:c) s+=k*(k-1)/2; return s;};
  long badcomp=0, disc=0;
  for(auto& kv:G){
    auto& lst=kv.second; if(lst.size()<2) continue;
    int Lstar=INT_MAX; for(auto&c:lst) Lstar=min(Lstar,Lf(c));
    set<vector<int>> S(lst.begin(),lst.end()); set<vector<int>> seen;
    for(auto& start:lst){ if(seen.count(start)) continue;
      vector<vector<int>> st={start}; seen.insert(start); bool hasMin=false; int compsize=0;
      while(!st.empty()){
        auto c=st.back(); st.pop_back(); compsize++; if(Lf(c)==Lstar) hasMin=true;
        vector<int> blocks; for(size_t i=0;i<cls.size();i++) if(c[i]) blocks.push_back(i);
        for(size_t a=0;a<blocks.size();a++) for(int bb=-1;bb<(int)blocks.size();bb++){
          int A=cls[blocks[a]]; int B= bb<0?1:cls[blocks[bb]];
          if(bb==(int)a && c[blocks[a]]<2) continue;
          if(bb>=0 && bb<(int)a) continue;
          long P=(long)A*B;
          for(long d=1; d*d<=P; d++) if(P%d==0){ long e=P/d; if(e>N) continue;
            auto c2=c; c2[blocks[a]]--; if(bb>=0) c2[blocks[bb]]--;
            bool okk=true;
            for(long x: {d,e}){ if(x==1) continue; if(x%p==0){okk=false;break;} c2[idx[x]]++; }
            if(!okk) continue;
            for(long x: {d,e}) if(x!=1 && c2[idx[x]]>capv[(int)x]) okk=false;
            if(!okk) continue;
            if(!seen.count(c2)){ seen.insert(c2); st.push_back(c2);} }
        }
      }
      if(compsize!=(int)S.size()) disc++;
      if(!hasMin){ badcomp++; }
    }
  }
  printf("p=%d N=%d #R=%zu Rs-with-disconnected-comps=%ld components-without-Lmin=%ld\n",p,N,G.size(),disc,badcomp); fflush(stdout);
  }
}
