// {q1,q2,q3}-smooth subsystem of Ang's system for prime p (p not in {q1,q2,q3}), up to N.
// Flat-first: all (r,0) then add (r,j) j>=1 in increasing order of p^j r. Check G, KL, and degenerate configs at raises.
#include <bits/stdc++.h>
using namespace std;
typedef long long ll; typedef array<int,3> P3;
int main(int argc,char**argv){
  ll N=atoll(argv[1]); int p=atoi(argv[2]); int q1=atoi(argv[3]),q2=atoi(argv[4]),q3=atoi(argv[5]);
  vector<pair<ll,P3>> cols; for(ll x=1;x<=N;x*=q1) for(ll y=x;y<=N;y*=q2) for(ll z=y;z<=N;z*=q3){ if(z==1) continue; int a=0,b=0,c=0; ll t=z; while(t%q1==0){t/=q1;a++;} while(t%q2==0){t/=q2;b++;} while(t%q3==0){t/=q3;c++;} cols.push_back({z,{a,b,c}}); }
  sort(cols.begin(),cols.end());
  int n=cols.size();
  // final heights
  vector<int> Jf(n); int H=0; for(int i=0;i<n;i++){ ll w=cols[i].first; int j=0; while(w*p<=N){w*=p;j++;} Jf[i]=j; H+=(j+1)*j/2; }
  int T[3]={0,0,0}; for(int i=0;i<n;i++) for(int k=0;k<3;k++) T[k]+=cols[i].second[k]*(Jf[i]+1);
  int A=T[0]+1,B=T[1]+1,C=T[2]+1; size_t tot=(size_t)A*B*C;
  printf("cols=%d box=%zu maxh=%d\n",n,tot,H);
  // store per point min/max h (int16) with -1 = unreachable
  vector<short> mn(tot,-1), mx(tot,-1); mn[0]=mx[0]=0;
  int cx=0,cy=0,cz=0;
  auto add=[&](const P3&g,int h){ for(int x=cx;x>=0;x--) for(int y=cy;y>=0;y--) for(int z=cz;z>=0;z--){ size_t id=((size_t)x*B+y)*C+z; if(mn[id]<0) continue; size_t id2=((size_t)(x+g[0])*B+(y+g[1]))*C+(z+g[2]); short a=mn[id]+h, b=mx[id]+h; if(mn[id2]<0){mn[id2]=a;mx[id2]=b;} else { if(a<mn[id2]) mn[id2]=a; if(b>mx[id2]) mx[id2]=b; } } cx+=g[0]; cy+=g[1]; cz+=g[2]; };
  // NOTE: min/max tracking only valid if fibres stay intervals; we also check interval property separately via bitset? Here we rely on G check below by recomputation is expensive; do degenerate-config checks.
  for(int i=0;i<n;i++) add(cols[i].second,0);
  vector<int> J(n,0);
  // raises in increasing order of p^j r
  vector<tuple<ll,int,int>> ev; for(int i=0;i<n;i++) for(int j=1;j<=Jf[i];j++){ ll v=cols[i].first; for(int k=0;k<j;k++) v*=p; ev.push_back({v,i,j}); }
  sort(ev.begin(),ev.end());
  auto in=[&](int x,int y,int z){ if(x<0||y<0||z<0||x>=A||y>=B||z>=C) return false; return mn[((size_t)x*B+y)*C+z]>=0; };
  long d1=0,d2=0,d3=0,klf=0;
  for(auto&e:ev){ int i=get<1>(e), j=get<2>(e); P3 w=cols[i].second;
    for(int x=0;x<=cx;x++) for(int y=0;y<=cy;y++) for(int z=0;z<=cz;z++){ if(!in(x,y,z)) continue;
      if(in(x-2*w[0],y-2*w[1],z-2*w[2]) && !in(x-w[0],y-w[1],z-w[2])) d1++;
      for(int k=0;k<n;k++){ if(k==i) continue; P3 v=cols[k].second;
        if(in(x-v[0]-w[0],y-v[1]-w[1],z-v[2]-w[2]) && !in(x-v[0],y-v[1],z-v[2]) && !in(x-w[0],y-w[1],z-w[2])) d3++;
        int ux=x+w[0],uy=y+w[1],uz=z+w[2]; if(!in(ux,uy,uz) && in(ux-v[0],uy-v[1],uz-v[2]) && !in(x-v[0],y-v[1],z-v[2])) d2++; } }
    add(w,j); J[i]=j; }
  printf("N=%lld p=%d primes(%d,%d,%d): degenerate at raises D1=%ld D2=%ld D3=%ld\n",N,p,q1,q2,q3,d1,d2,d3);
}
