// Hole-freeness of integer flat sets R(D_N,1): generators = exponent vectors of p-free r in [2,N] (over primes != p).
// Primes that occur in exactly one generator (r=q) are decoupled and dropped. Facet normals of zonotope via (d-1)-subsets.
#include <bits/stdc++.h>
using namespace std;
typedef long long ll; typedef vector<ll> V;
ll det(vector<V> M){ int n=M.size(); if(n==0) return 1; ll sign=1, prev=1; for(int k=0;k<n-1;k++){ if(M[k][k]==0){ int s=-1; for(int i=k+1;i<n;i++) if(M[i][k]!=0){s=i;break;} if(s<0) return 0; swap(M[k],M[s]); sign=-sign; }
    for(int i=k+1;i<n;i++) for(int j=k+1;j<n;j++){ M[i][j]=(M[i][j]*M[k][k]-M[i][k]*M[k][j])/prev; } prev=M[k][k]; } return sign*M[n-1][n-1]; }
int main(int argc,char**argv){
  int N=atoi(argv[1]); int p=atoi(argv[2]); int mode=atoi(argv[3]); // mode 0: flat m=1; mode 1: final multiplicities m_r = floor(log_p(N/r))+1
  vector<int> pr; for(int q=2;q<=N;q++){bool ok=true; for(int d=2;d*d<=q;d++) if(q%d==0) ok=false; if(ok&&q!=p) pr.push_back(q);}
  vector<int> rs; for(int r=2;r<=N;r++) if(r%p) rs.push_back(r);
  // count occurrences of each prime among generators
  vector<int> occ(pr.size(),0); for(int r:rs) for(size_t i=0;i<pr.size();i++) if(r%pr[i]==0) occ[i]++;
  vector<int> keep; for(size_t i=0;i<pr.size();i++) if(occ[i]>1) keep.push_back(i);
  int d=keep.size();
  vector<V> G; vector<int> m;
  for(int r:rs){ V e(d,0); bool nz=false; int x=r; for(int k=0;k<d;k++){ int q=pr[keep[k]]; while(x%q==0){x/=q;e[k]++;nz=true;} } if(!nz) continue; G.push_back(e); int mm=1; if(mode==1){ long y=r; while(y*p<=N){y*=p;mm++;} } m.push_back(mm); }
  printf("N=%d p=%d mode=%d d=%d gens=%zu\n",N,p,mode,d,G.size());
  set<V> R; R.insert(V(d,0));
  for(size_t g=0;g<G.size();g++){ vector<V> add; for(auto&r:R){ V z=r; for(int k=1;k<=m[g];k++){ for(int i=0;i<d;i++) z[i]+=G[g][i]; add.push_back(z);} } for(auto&z:add) R.insert(z); }
  printf("|R|=%zu\n",R.size());
  // facet normals: (d-1)-subsets of distinct generator directions
  vector<V> dirs=G; sort(dirs.begin(),dirs.end()); dirs.erase(unique(dirs.begin(),dirs.end()),dirs.end());
  vector<V> normals; int n=dirs.size(); vector<int> idx(d-1);
  long cnt=0;
  function<void(int,int)> comb=[&](int pos,int start){ if(pos==d-1){ V c(d); for(int i=0;i<d;i++){ vector<V> M; for(int r=0;r<d-1;r++){ V row; for(int j=0;j<d;j++) if(j!=i) row.push_back(dirs[idx[r]][j]); M.push_back(row);} c[i]=((i%2)?-1:1)*det(M); }
      bool z=true; for(ll x:c) if(x) z=false; if(!z){ ll gg=0; for(ll x:c) gg=__gcd(gg,llabs(x)); for(auto&x:c) x/=gg; bool neg=false; for(ll x:c){ if(x<0){neg=true;break;} if(x>0) break; } if(neg) for(auto&x:c) x=-x; normals.push_back(c);} cnt++; return; }
    for(int s=start;s<n;s++){ idx[pos]=s; comb(pos+1,s+1);} };
  comb(0,0);
  sort(normals.begin(),normals.end()); normals.erase(unique(normals.begin(),normals.end()),normals.end());
  printf("subsets=%ld normals=%zu\n",cnt,normals.size());
  vector<pair<ll,ll>> lh; for(auto&c:normals){ ll lo=0,hi=0; for(size_t g=0;g<G.size();g++){ ll v=0; for(int i=0;i<d;i++) v+=c[i]*G[g][i]; v*=m[g]; if(v>0) hi+=v; else lo+=v; } lh.push_back({lo,hi}); }
  auto inZ=[&](const V&z){ for(size_t q=0;q<normals.size();q++){ ll v=0; for(int i=0;i<d;i++) v+=normals[q][i]*z[i]; if(v<lh[q].first||v>lh[q].second) return false; } return true; };
  long holes=0, cand=0;
  for(auto&r:R){ for(int i=0;i<d;i++) for(int s=-1;s<=1;s+=2){ V z=r; z[i]+=s; if(z[i]<0||R.count(z)) continue; cand++; if(inZ(z)){ holes++; if(holes<=5){ printf("HOLE: "); for(int k=0;k<d;k++) printf("%d^%lld ",pr[keep[k]],z[k]); printf("\n"); } } } }
  printf("candidates=%ld holes(adjacent)=%ld\n",cand,holes);
}
