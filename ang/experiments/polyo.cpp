// For random down-sets I in N^k: compute Sigma(I) fully (set of k-vectors); for each pair of axes (j,h) and each 2D slice,
// check 4-connectivity (HV-convexity checked too).
#include <bits/stdc++.h>
using namespace std;
typedef vector<int> V;
int main(int argc,char**argv){
  unsigned seed=atoi(argv[1]); int trials=atoi(argv[2]); int kmin=atoi(argv[3]); int kmax=atoi(argv[4]); int side=atoi(argv[5]); int maxgen=atoi(argv[6]); int maxsz=atoi(argv[7]); int punct=atoi(argv[8]);
  setvbuf(stdout,NULL,_IONBF,0); mt19937 rng(seed); long tested=0,badconn=0,badconv=0;
  for(int t=0;t<trials;t++){
    int k=kmin+rng()%(kmax-kmin+1); int ng=1+rng()%maxgen; set<V> I;
    for(int g=0;g<ng;g++){ V gen(k); for(int i=0;i<k;i++) gen[i]=rng()%(side+1); V x(k,0);
      while(true){ I.insert(x); int i=0; while(i<k){ if(x[i]<gen[i]){x[i]++;break;} x[i]=0;i++;} if(i==k) break; } }
    if((int)I.size()>maxsz) continue;
    int hax=k-1; // punctured: remove axis line of coordinate hax
    vector<V> el; for(auto&x:I){ bool onaxis=true; for(int i=0;i<k;i++) if(i!=hax&&x[i]) onaxis=false; if(punct&&onaxis) continue; el.push_back(x); }
    set<V> S; S.insert(V(k,0));
    for(auto&x:el){ vector<V> add; for(auto&s:S){ V y=s; for(int i=0;i<k;i++) y[i]+=x[i]; add.push_back(y);} for(auto&y:add) S.insert(y); if(S.size()>2000000) break; }
    if(S.size()>2000000) continue;
    tested++;
    int jmax = punct? 1 : k; // in punctured mode only slices containing hax direction matter: (j, hax)
    for(int j=0;j<k;j++) for(int h=j+1;h<k;h++){
      if(punct && h!=hax && j!=hax) continue;
      // group by other coords
      map<V, vector<pair<int,int>>> slices;
      for(auto&s:S){ V key; for(int i=0;i<k;i++) if(i!=j&&i!=h) key.push_back(s[i]); slices[key].push_back({s[j],s[h]}); }
      for(auto&kv:slices){ auto&pts=kv.second; set<pair<int,int>> P(pts.begin(),pts.end());
        // connectivity
        auto st=*P.begin(); set<pair<int,int>> seen={st}; vector<pair<int,int>> stk={st};
        while(!stk.empty()){ auto c=stk.back(); stk.pop_back(); int dx[4]={1,-1,0,0},dy[4]={0,0,1,-1}; for(int q=0;q<4;q++){ pair<int,int> nb={c.first+dx[q],c.second+dy[q]}; if(P.count(nb)&&!seen.count(nb)){seen.insert(nb); stk.push_back(nb);} } }
        if(seen.size()!=P.size()){ badconn++; if(badconn<=2){ printf("DISCONNECTED slice k=%d axes(%d,%d) |I|=%zu\n",k,j,h,I.size()); } break; }
      }
    }
  }
  printf("punct=%d tested=%ld disconnected-slices=%ld\n",punct,tested,badconn);
}
