// 2D hole-freeness: D = Young diagram (down-set in N^2), generators D* each once (or with random multiplicities).
#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
int main(int argc,char**argv){
  unsigned seed=atoi(argv[1]); int trials=atoi(argv[2]); int maxside=atoi(argv[3]); int maxm=atoi(argv[4]);
  mt19937 rng(seed); long tested=0,bad=0;
  for(int t=0;t<trials;t++){
    int K=1+rng()%maxside; vector<int> lam(K+1); lam[0]=1+rng()%maxside; for(int i=1;i<=K;i++) lam[i]=rng()%(lam[i-1]+1); // column heights (number of cells) decreasing
    vector<array<int,2>> G; vector<int> M;
    for(int a=0;a<=K;a++) for(int b=0;b<lam[a];b++) if(a||b){ G.push_back({a,b}); M.push_back(1+(maxm>1?rng()%maxm:0)); }
    if(G.size()<2) continue;
    int T0=0,T1=0; for(size_t g=0;g<G.size();g++){T0+=G[g][0]*M[g];T1+=G[g][1]*M[g];}
    vector<char> S((size_t)(T0+1)*(T1+1),0); S[0]=1; int c0=0,c1=0;
    for(size_t g=0;g<G.size();g++) for(int r=0;r<M[g];r++){ for(int x=c0;x>=0;x--) for(int y=c1;y>=0;y--) if(S[(size_t)x*(T1+1)+y]) S[(size_t)(x+G[g][0])*(T1+1)+y+G[g][1]]=1; c0+=G[g][0]; c1+=G[g][1]; }
    // zonotope facets: normals perpendicular to each generator direction
    vector<array<ll,2>> N; for(auto&g:G){ array<ll,2> c={-(ll)g[1],(ll)g[0]}; ll gg=__gcd(llabs(c[0]),llabs(c[1])); c[0]/=gg; c[1]/=gg; if(c[0]<0||(c[0]==0&&c[1]<0)){c[0]=-c[0];c[1]=-c[1];} N.push_back(c);} sort(N.begin(),N.end()); N.erase(unique(N.begin(),N.end()),N.end());
    vector<ll> lo(N.size(),0),hi(N.size(),0); for(size_t q=0;q<N.size();q++) for(size_t g=0;g<G.size();g++){ ll v=(N[q][0]*G[g][0]+N[q][1]*G[g][1])*M[g]; if(v>0) hi[q]+=v; else lo[q]+=v; }
    tested++; bool hole=false;
    for(int x=0;x<=T0&&!hole;x++) for(int y=0;y<=T1;y++){ bool in=true; for(size_t q=0;q<N.size();q++){ ll v=N[q][0]*x+N[q][1]*y; if(v<lo[q]||v>hi[q]){in=false;break;} } if(in && !S[(size_t)x*(T1+1)+y]){ hole=true; bad++; if(bad<=3){ printf("HOLE (%d,%d) lam:",x,y); for(int v:lam) printf(" %d",v); printf("\n"); } break; } }
  }
  printf("tested=%ld with-holes=%ld\n",tested,bad);
}
