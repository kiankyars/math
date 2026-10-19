// HF1 for D = lattice points of k*Delta_3 (x+y+z<=k). Compute all subset sums (bitset grid), check every lattice point of zonotope.
#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
int main(int argc,char**argv){
  int k=atoi(argv[1]);
  vector<array<int,3>> G; for(int x=0;x<=k;x++) for(int y=0;x+y<=k;y++) for(int z=0;x+y+z<=k;z++) if(x||y||z) G.push_back({x,y,z});
  int T[3]={0,0,0}; for(auto&g:G) for(int i=0;i<3;i++) T[i]+=g[i];
  int A=T[0]+1,B=T[1]+1,C=T[2]+1; printf("gens=%zu box=%d x %d x %d\n",G.size(),A,B,C);
  vector<char> S((size_t)A*B*C,0); S[0]=1; int cx=0,cy=0,cz=0;
  for(auto&g:G){ // process in decreasing index to avoid reuse
    for(int x=cx;x>=0;x--) for(int y=cy;y>=0;y--) for(int z=cz;z>=0;z--){ size_t id=((size_t)x*B+y)*C+z; if(S[id]){ size_t id2=((size_t)(x+g[0])*B+(y+g[1]))*C+(z+g[2]); S[id2]=1; } }
    cx+=g[0]; cy+=g[1]; cz+=g[2]; }
  // facet normals: cross products of pairs
  vector<array<ll,3>> N;
  for(size_t i=0;i<G.size();i++) for(size_t j=i+1;j<G.size();j++){ array<ll,3> c={ (ll)G[i][1]*G[j][2]-(ll)G[i][2]*G[j][1], (ll)G[i][2]*G[j][0]-(ll)G[i][0]*G[j][2], (ll)G[i][0]*G[j][1]-(ll)G[i][1]*G[j][0] };
    if(!c[0]&&!c[1]&&!c[2]) continue; ll gg=__gcd(llabs(c[0]),__gcd(llabs(c[1]),llabs(c[2]))); for(auto&x:c) x/=gg; if(c[0]<0||(c[0]==0&&(c[1]<0||(c[1]==0&&c[2]<0)))) for(auto&x:c) x=-x; N.push_back(c); }
  sort(N.begin(),N.end()); N.erase(unique(N.begin(),N.end()),N.end());
  vector<ll> lo(N.size(),0),hi(N.size(),0);
  for(size_t q=0;q<N.size();q++) for(auto&g:G){ ll v=N[q][0]*g[0]+N[q][1]*g[1]+N[q][2]*g[2]; if(v>0) hi[q]+=v; else lo[q]+=v; }
  printf("normals=%zu\n",N.size());
  long holes=0, inZ=0;
  for(int x=0;x<A;x++) for(int y=0;y<B;y++) for(int z=0;z<C;z++){
    bool in=true; for(size_t q=0;q<N.size();q++){ ll v=N[q][0]*x+N[q][1]*y+N[q][2]*z; if(v<lo[q]||v>hi[q]){in=false;break;} }
    if(!in) continue; inZ++;
    if(!S[((size_t)x*B+y)*C+z]){ holes++; if(holes<=10) printf("HOLE (%d,%d,%d)\n",x,y,z); } }
  printf("k=%d lattice points in Z: %ld holes: %ld\n",k,inZ,holes);
}
