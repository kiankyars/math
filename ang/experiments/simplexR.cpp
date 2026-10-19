// R1-R3 on R = Sigma(G) for G = nonzero lattice points of k*Delta_3 (each once).
#include <bits/stdc++.h>
using namespace std;
int main(int argc,char**argv){
  int k=atoi(argv[1]);
  vector<array<int,3>> G; for(int x=0;x<=k;x++) for(int y=0;x+y<=k;y++) for(int z=0;x+y+z<=k;z++) if(x||y||z) G.push_back({x,y,z});
  int T[3]={0,0,0}; for(auto&g:G) for(int i=0;i<3;i++) T[i]+=g[i];
  int A=T[0]+1,B=T[1]+1,C=T[2]+1;
  vector<char> S((size_t)A*B*C,0); S[0]=1; int cx=0,cy=0,cz=0;
  for(auto&g:G){ for(int x=cx;x>=0;x--) for(int y=cy;y>=0;y--) for(int z=cz;z>=0;z--){ size_t id=((size_t)x*B+y)*C+z; if(S[id]) S[((size_t)(x+g[0])*B+(y+g[1]))*C+(z+g[2])]=1; } cx+=g[0]; cy+=g[1]; cz+=g[2]; }
  auto in=[&](int x,int y,int z)->bool{ if(x<0||y<0||z<0||x>=A||y>=B||z>=C) return false; return S[((size_t)x*B+y)*C+z]; };
  long r1=0,r2=0,r3=0; int n=G.size();
  for(int x=0;x<A;x++) for(int y=0;y<B;y++) for(int z=0;z<C;z++){ if(!in(x,y,z)) continue;
    for(int a=0;a<n;a++){ auto&w=G[a];
      if(in(x-2*w[0],y-2*w[1],z-2*w[2]) && !in(x-w[0],y-w[1],z-w[2])) r1++;
      for(int b=a+1;b<n;b++){ auto&v=G[b];
        // R3: u, u-w-v in R => u-w or u-v
        if(in(x-w[0]-v[0],y-w[1]-v[1],z-w[2]-v[2]) && !in(x-w[0],y-w[1],z-w[2]) && !in(x-v[0],y-v[1],z-v[2])) r3++;
      }
      // R2 with u-w in R as "x+v" form: take a2=(x,y,z)=X+w in R, X+v in R => X or X+w+v in R
      for(int b=0;b<n;b++){ if(b==a) continue; auto&v=G[b];
        int X0=x-w[0],X1=y-w[1],X2=z-w[2];
        if(in(X0+v[0],X1+v[1],X2+v[2]) && !in(X0,X1,X2) && !in(x+v[0],y+v[1],z+v[2])) r2++; }
    } }
  printf("k=%d R1fail=%ld R2fail=%ld R3fail=%ld\n",k,r1,r2,r3);
}
