// Annealing search for WOWII 72a: tree(G) >= ceil(ecc_avg + lambda_max/3). Minimizes slack = tree - ceil(...).
// tree(G) computed exactly by branch and bound over connected induced acyclic sets (n <= 26).
#include <bits/stdc++.h>
using namespace std;
typedef unsigned M; int n; M adj[32];
static inline int pc(M x){ return __builtin_popcount(x); }
mt19937_64 rng(12345);
int best;
// grow induced trees: S current tree vertices, cand = vertices adjacent to exactly one vertex of S and not excluded
void grow(M S, M excl, int sz){
  if(sz>best) best=sz;
  // candidates: neighbors of S with exactly one neighbor in S, not in S, not excluded
  M nb=0; for(M t=S;t;t&=t-1) nb|=adj[__builtin_ctz(t)]; nb&=~S&~excl;
  // upper bound: sz + number of vertices not excluded and not in S that are reachable... crude
  M avail=((n==32)?~0u:((1u<<n)-1))&~S&~excl;
  if(sz+pc(avail)<=best) return;
  for(M t=nb;t;t&=t-1){ int v=__builtin_ctz(t); if(pc(adj[v]&S)==1){ grow(S|(1u<<v), excl, sz+1); excl|=1u<<v; if(sz+pc(((1u<<n)-1)&~S&~excl)<=best) return; } else { excl|=1u<<v; } }
}
int treeNum(){ best=1; M excl=0; for(int v=0;v<n;v++){ grow(1u<<v, excl, 1); excl|=1u<<v; } return best; }
int alphaM(M m){ if(!m) return 0; int v=__builtin_ctz(m); M rest=m&~(1u<<v); int a=alphaM(rest&~adj[v])+1; if(!(adj[v]&rest)) return a; return max(a,alphaM(rest)); }
bool connected(){ M seen=1,fr=1; while(fr){ M nf=0; for(M t=fr;t;t&=t-1) nf|=adj[__builtin_ctz(t)]; nf&=~seen; seen|=nf; fr=nf; } return seen==((1u<<n)-1); }
double eval(int &tr, double &rhs){
  double esum=0; for(int v=0;v<n;v++){ M seen=1u<<v,fr=seen; int d=0; while(fr){ M nf=0; for(M t=fr;t;t&=t-1) nf|=adj[__builtin_ctz(t)]; nf&=~seen; if(nf) d++; seen|=nf; fr=nf; } esum+=d; }
  int lmax=0; for(int v=0;v<n;v++) lmax=max(lmax,alphaM(adj[v]));
  rhs=ceil(esum/n+lmax/3.0-1e-9); tr=treeNum(); return tr-rhs + 0.001*(tr - (esum/n+lmax/3.0)); }
int main(int argc,char**argv){ n=atoi(argv[1]); long iters=atol(argv[2]); rng.seed(atoi(argv[3]));
  double p=atof(argv[4]);
  for(int i=0;i<n;i++) adj[i]=0;
  do { for(int i=0;i<n;i++) adj[i]=0; for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if((rng()%1000)<p*1000){ adj[i]|=1u<<j; adj[j]|=1u<<i; } } while(!connected());
  int tr; double rhs; double cur=eval(tr,rhs), bestv=cur; double T=1.0;
  for(long it=0;it<iters;it++){ int a=rng()%n,b=rng()%n; if(a==b) continue; adj[a]^=1u<<b; adj[b]^=1u<<a;
    if(!connected()){ adj[a]^=1u<<b; adj[b]^=1u<<a; continue; }
    int tr2; double rhs2; double v=eval(tr2,rhs2);
    if(v<=cur || exp((cur-v)/T) > (rng()%100000)/100000.0){ cur=v; if(v<bestv){ bestv=v; fprintf(stderr,"it=%ld best=%.3f tree=%d rhs=%.0f\n",it,v,tr2,rhs2); if(v<-0.5){ // print graph6
          string s; s+=char(n+63); int val=0,k=0; for(int j=1;j<n;j++) for(int i=0;i<j;i++){ val=(val<<1)|((adj[i]>>j)&1); if(++k==6){ s+=char(val+63); val=0; k=0; } } if(k){ val<<=(6-k); s+=char(val+63);} printf("CEX %s\n",s.c_str()); fflush(stdout); } } }
    else { adj[a]^=1u<<b; adj[b]^=1u<<a; }
    T=max(0.02,T*0.9995); }
  printf("done best=%.3f\n",bestv); }
