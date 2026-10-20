// SA over (3,B2) formulas with v vars: maximize i(G(f)) - v where G(f) is the cubic incidence graph (gamma_e(G)=v).
#include <bits/stdc++.h>
using namespace std; typedef unsigned long long u64;
int v,m,n; u64 adj[64]; mt19937_64 rng;
vector<array<int,3>> cl; // literals: +x / -x, x in 1..v
int bestI;
void idom(u64 und,int sz){ if(sz>=bestI) return; if(!und){ bestI=sz; return; }
  int lb=(__builtin_popcountll(und)+3)/4; if(sz+lb>=bestI) return;
  int bv=-1,bc=99; for(u64 t=und;t;t&=t-1){ int x=__builtin_ctzll(t); int c=__builtin_popcountll((adj[x]|(1ULL<<x))&und); if(c<bc){bc=c;bv=x; if(c<=1)break;} }
  u64 opts=(adj[bv]|(1ULL<<bv))&und;
  for(u64 t=opts;t;t&=t-1){ int w=__builtin_ctzll(t); u64 c2=adj[w]|(1ULL<<w); idom(und&~c2,sz+1); } }
int litv(int l){ int x=abs(l)-1; return 2*x+(l>0?0:1); }
void build(){ n=2*v+m; for(int i=0;i<n;i++) adj[i]=0; auto add=[&](int a,int b){ adj[a]|=1ULL<<b; adj[b]|=1ULL<<a; };
  for(int x=0;x<v;x++) add(2*x,2*x+1); for(int j=0;j<m;j++) for(int l:cl[j]) add(litv(l),2*v+j); }
int score(int ub){ build(); bestI=ub; idom((n==64)?~0ULL:((1ULL<<n)-1),0); return bestI-v; }
bool okClause(const array<int,3>& c){ return abs(c[0])!=abs(c[1]) && abs(c[0])!=abs(c[2]) && abs(c[1])!=abs(c[2]); }
int main(int argc,char**argv){ v=atoi(argv[1]); long iters=atol(argv[2]); rng.seed(atol(argv[3])); double T0=argc>4?atof(argv[4]):0.6;
  m=4*v/3; vector<int> slots; for(int x=1;x<=v;x++){ slots.push_back(x); slots.push_back(x); slots.push_back(-x); slots.push_back(-x); }
  do { shuffle(slots.begin(),slots.end(),rng); cl.assign(m,{}); bool ok=true; for(int j=0;j<m;j++){ cl[j]={slots[3*j],slots[3*j+1],slots[3*j+2]}; if(!okClause(cl[j])) ok=false; } if(ok) break; } while(true);
  int cur=score(v+5), best=cur;
  for(long it=0;it<iters;it++){
    int a=rng()%m,b=rng()%m; if(a==b) continue; int i=rng()%3,j=rng()%3;
    swap(cl[a][i],cl[b][j]); if(!okClause(cl[a])||!okClause(cl[b])){ swap(cl[a][i],cl[b][j]); continue; }
    int s=score(v+5); double T=T0*(1.0-(double)it/iters)+0.02;
    if(s>=cur || exp((s-cur)/T) > (rng()%1000000)/1e6){ cur=s; if(s>best){ best=s; printf("it=%ld new best i-v=%d\n",it,best); fflush(stdout);} 
      if(s>=1){ printf("FOUND v=%d:",v); for(auto&c:cl) printf(" (%d %d %d)",c[0],c[1],c[2]); printf("\n"); fflush(stdout); return 0; } }
    else swap(cl[a][i],cl[b][j]);
    if(it%20000==0){ printf("it=%ld cur=%d best=%d\n",it,cur,best); fflush(stdout); }
  }
  printf("done best=%d\n",best); }
