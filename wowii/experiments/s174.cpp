// Targeted search for WOWII 174 counterexamples: spider at v with mixed-parity legs + blockers.
#include <bits/stdc++.h>
using namespace std; typedef unsigned M;
int n; M adj[32]; M ALL; mt19937_64 rng;
inline int pc(M x){ return __builtin_popcount(x); }
M openN(M S){ M r=0; for(M t=S;t;t&=t-1) r|=adj[__builtin_ctz(t)]; return r; }
bool connectedM(M m){ if(!m) return true; M seen=m&(-m), fr=seen; while(fr){ M nf=openN(fr)&m&~seen; seen|=nf; fr=nf; } return seen==m; }
int alphaM(M m){ if(!m) return 0; int v=__builtin_ctz(m); M rest=m&~(1u<<v); int a=alphaM(rest&~adj[v])+1; if(!(adj[v]&rest)) return a; return max(a,alphaM(rest)); }
bool isBip(M m){ M left=m; while(left){ M c0=left&(-left),c1=0,fr0=c0,fr1=0; while(fr0||fr1){ M n1=openN(fr0)&m, n0=openN(fr1)&m; if((n1&c0)||(n0&c1)) return false; n1&=~c1; n0&=~c0; c1|=n1; c0|=n0; fr0=n0; fr1=n1; } left&=~(c0|c1);} return true; }
string g6(){ string s; s+=char(n+63); int val=0,k=0; for(int j=1;j<n;j++) for(int i=0;i<j;i++){ val=(val<<1)|((adj[i]>>j)&1); if(++k==6){ s+=char(val+63); val=0;k=0;} } if(k){ val<<=(6-k); s+=char(val+63);} return s; }
void addE(int a,int b){ if(a!=b){ adj[a]|=1u<<b; adj[b]|=1u<<a; } }
int main(int argc,char**argv){ long iters=atol(argv[1]); rng.seed(atol(argv[2])); long tested=0; int minslack=99;
  for(long it=0;it<iters;it++){
    for(int i=0;i<32;i++) adj[i]=0; int mu=3+rng()%4; int v=0; n=1; vector<int> I; vector<vector<int>> legs;
    for(int j=0;j<mu;j++){ int i=n++; addE(v,i); I.push_back(i); int len=rng()%3; vector<int> leg{i}; int prev=i; for(int k=0;k<len;k++){ int w=n++; addE(prev,w); leg.push_back(w); prev=w; } legs.push_back(leg); }
    int nb=1+rng()%4; for(int k=0;k<nb && n<17;k++){ int z=n++; int t=2+rng()%2; for(int q=0;q<t;q++){ int u=1+rng()%(z-1); addE(z,u);} }
    if(rng()%2){ int extra=rng()%4; for(int k=0;k<extra;k++){ int a=1+rng()%(n-1), b=1+rng()%(n-1); // avoid destroying I independence and v's neighbourhood
        if(a!=b && !((adj[0]>>a)&1 && (adj[0]>>b)&1)) addE(a,b);} }
    if(n>18) continue; ALL=(1u<<n)-1; if(!connectedM(ALL)) continue; tested++;
    int maxlam=0; for(int x=0;x<n;x++) maxlam=max(maxlam,alphaM(adj[x]));
    int b=0,gc=n; for(M S=1;S<=ALL;S++){ int c=pc(S); if(c>b && isBip(S)) b=c; if(c<gc && ((S|openN(S))==ALL) && connectedM(S)) gc=c; if(S==ALL) break; }
    int Ls=n-gc; int slack=Ls+b-(n+maxlam-1); minslack=min(minslack,slack);
    if(slack<0){ printf("FAIL174 %s n=%d Ls=%d b=%d mu=%d\n",g6().c_str(),n,Ls,b,maxlam); fflush(stdout); }
  }
  printf("tested=%ld minslack=%d\n",tested,minslack); }
