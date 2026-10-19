// HF for D = {q1^a q2^b q3^c <= N} (3 primes), generators = nonzero points (each once). Exhaustive over the zonotope's lattice points.
#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
int main(int argc,char**argv){
  ll N=atoll(argv[1]); int q1=atoi(argv[2]),q2=atoi(argv[3]),q3=atoi(argv[4]); int mult=argc>5?atoi(argv[5]):0;
  vector<array<int,3>> G; vector<int> M;
  for(ll x=1;x<=N;x*=q1) for(ll y=x;y<=N;y*=q2) for(ll z=y;z<=N;z*=q3){ int a=0,b=0,c=0; ll t=z; while(t%q1==0){t/=q1;a++;} while(t%q2==0){t/=q2;b++;} while(t%q3==0){t/=q3;c++;} if(a||b||c){ G.push_back({a,b,c}); int m=1; if(mult){ ll w=z; while(w*2<=N){w*=2;m++;} } M.push_back(m);} }
  int T[3]={0,0,0}; for(size_t g=0;g<G.size();g++) for(int i=0;i<3;i++) T[i]+=G[g][i]*M[g];
  int A=T[0]+1,B=T[1]+1,C=T[2]+1; size_t tot=(size_t)A*B*C; if(tot>400000000ULL){printf("too big\n");return 0;}
  vector<char> S(tot,0); S[0]=1; int cx=0,cy=0,cz=0;
  for(size_t gi=0;gi<G.size();gi++){ auto g=G[gi]; for(int rep=0;rep<M[gi];rep++){ for(int x=cx;x>=0;x--) for(int y=cy;y>=0;y--) for(int z=cz;z>=0;z--){ size_t id=((size_t)x*B+y)*C+z; if(S[id]) S[((size_t)(x+g[0])*B+(y+g[1]))*C+(z+g[2])]=1; } cx+=g[0]; cy+=g[1]; cz+=g[2]; } }
  vector<array<ll,3>> Nn; for(size_t i=0;i<G.size();i++) for(size_t j=i+1;j<G.size();j++){ array<ll,3> c={ (ll)G[i][1]*G[j][2]-(ll)G[i][2]*G[j][1], (ll)G[i][2]*G[j][0]-(ll)G[i][0]*G[j][2], (ll)G[i][0]*G[j][1]-(ll)G[i][1]*G[j][0] };
    if(!c[0]&&!c[1]&&!c[2]) continue; ll gg=__gcd(llabs(c[0]),__gcd(llabs(c[1]),llabs(c[2]))); for(auto&x:c) x/=gg; if(c[0]<0||(c[0]==0&&(c[1]<0||(c[1]==0&&c[2]<0)))) for(auto&x:c) x=-x; Nn.push_back(c); }
  sort(Nn.begin(),Nn.end()); Nn.erase(unique(Nn.begin(),Nn.end()),Nn.end());
  vector<ll> lo(Nn.size(),0),hi(Nn.size(),0); for(size_t q=0;q<Nn.size();q++) for(size_t g=0;g<G.size();g++){ ll v=(Nn[q][0]*G[g][0]+Nn[q][1]*G[g][1]+Nn[q][2]*G[g][2])*M[g]; if(v>0) hi[q]+=v; else lo[q]+=v; }
  long holes=0,inZ=0;
  for(int x=0;x<A;x++) for(int y=0;y<B;y++) for(int z=0;z<C;z++){ bool in=true; for(size_t q=0;q<Nn.size();q++){ ll v=Nn[q][0]*x+Nn[q][1]*y+Nn[q][2]*z; if(v<lo[q]||v>hi[q]){in=false;break;} } if(!in) continue; inZ++; if(!S[((size_t)x*B+y)*C+z]){ holes++; if(holes<=3) printf("  HOLE (%d,%d,%d)\n",x,y,z);} }
  printf("N=%lld primes %d,%d,%d mult=%d gens=%zu latticeZ=%ld holes=%ld\n",N,q1,q2,q3,mult,G.size(),inZ,holes);
}
