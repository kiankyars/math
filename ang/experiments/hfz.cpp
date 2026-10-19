// HF1 test: D = threshold down-set (convex) in N^d (d=3..5) or integer p-free simplex; R = Sigma(D*) (each once) or with multiplicities m.
// Zonotope facets: normals = generalized cross products of (d-1) linearly independent generators. Check candidates R +- e_i (and full box if small).
#include <bits/stdc++.h>
using namespace std;
typedef long long ll; typedef vector<ll> V;
ll det(vector<V> M){ int n=M.size(); // integer det via fraction-free Bareiss
  ll sign=1, prev=1; for(int k=0;k<n-1;k++){ if(M[k][k]==0){ int s=-1; for(int i=k+1;i<n;i++) if(M[i][k]!=0){s=i;break;} if(s<0) return 0; swap(M[k],M[s]); sign=-sign; }
    for(int i=k+1;i<n;i++) for(int j=k+1;j<n;j++){ M[i][j]=(M[i][j]*M[k][k]-M[i][k]*M[k][j])/prev; } prev=M[k][k]; }
  return sign*M[n-1][n-1]; }
int main(int argc,char**argv){
  unsigned seed=atoi(argv[1]); int trials=atoi(argv[2]); int dmin=atoi(argv[3]); int dmax=atoi(argv[4]); int maxgen=atoi(argv[5]); int maxm=atoi(argv[6]); long maxR=atol(argv[7]); double amin=atof(argv[8]); long boxlim=atol(argv[9]);
  setvbuf(stdout,NULL,_IONBF,0); mt19937 rng(seed); long tested=0,holes=0;
  for(int t=0;t<trials;t++){
    int d=dmin+rng()%(dmax-dmin+1); vector<double> a(d); for(auto&x:a) x=amin+(0.7-amin)*(rng()%100000)/100000.0;
    vector<V> G; V e(d,0);
    function<void(int,double)> rec=[&](int i,double s){ if(i==d){ bool z=true; for(ll x:e) if(x) z=false; if(!z) G.push_back(e); return; } for(int k=0; s+k*a[i]<=1.0+1e-12; k++){ e[i]=k; rec(i+1,s+k*a[i]); } e[i]=0; };
    rec(0,0.0);
    if((int)G.size()<d||(int)G.size()>maxgen) continue;
    vector<int> m(G.size(),1); if(maxm>1) for(auto&x:m) x=1+rng()%maxm;
    // R
    set<V> R; R.insert(V(d,0));
    for(size_t g=0;g<G.size();g++){ vector<V> add; for(auto&r:R){ V z=r; for(int k=1;k<=m[g];k++){ for(int i=0;i<d;i++) z[i]+=G[g][i]; add.push_back(z);} } for(auto&z:add) R.insert(z); if((long)R.size()>maxR) break; }
    if((long)R.size()>maxR) continue;
    // facet normals
    vector<V> normals; int n=G.size();
    vector<int> idx(d-1); function<void(int,int)> comb=[&](int pos,int start){ if(pos==d-1){ // normal via cofactors
        V c(d); for(int i=0;i<d;i++){ vector<V> M; for(int r=0;r<d-1;r++){ V row; for(int j=0;j<d;j++) if(j!=i) row.push_back(G[idx[r]][j]); M.push_back(row);} ll dt=(d-1==0)?1:det(M); c[i]=((i%2)?-1:1)*dt; }
        bool z=true; for(ll x:c) if(x) z=false; if(!z){ ll gg=0; for(ll x:c) gg=__gcd(gg,llabs(x)); for(auto&x:c) x/=gg; normals.push_back(c);} return; }
      for(int s=start;s<n;s++){ idx[pos]=s; comb(pos+1,s+1);} };
    comb(0,0);
    sort(normals.begin(),normals.end()); normals.erase(unique(normals.begin(),normals.end()),normals.end());
    vector<pair<ll,ll>> rng2; for(auto&c:normals){ ll lo=0,hi=0; for(size_t g=0;g<G.size();g++){ ll v=0; for(int i=0;i<d;i++) v+=c[i]*G[g][i]; v*=m[g]; if(v>0) hi+=v; else lo+=v; } rng2.push_back({lo,hi}); }
    auto inZ=[&](const V&z){ for(size_t q=0;q<normals.size();q++){ ll v=0; for(int i=0;i<d;i++) v+=normals[q][i]*z[i]; if(v<rng2[q].first||v>rng2[q].second) return false; } return true; };
    tested++;
    bool found=false;
    for(auto&r:R){ for(int i=0;i<d&&!found;i++) for(int s=-1;s<=1;s+=2){ V z=r; z[i]+=s; if(R.count(z)) continue; if(inZ(z)){ found=true; holes++; if(holes<=3){ printf("HOLE d=%d |G|=%zu z=(",d,G.size()); for(ll x:z)printf("%lld,",x); printf(") gens:"); for(size_t g=0;g<G.size();g++){printf(" (");for(ll x:G[g])printf("%lld,",x);printf(")m%d",m[g]);} printf("\n"); } break; } } if(found) break; }
  }
  printf("tested=%ld systems-with-holes=%ld\n",tested,holes);
}
