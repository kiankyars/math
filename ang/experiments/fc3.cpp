// Fiber connectivity for down-set configurations with bounds N>=1.
// mode 2: moves with |D_v|<=1 except one |D_v|=2 (FC2)
// mode 3: "quadratic" moves: sum of positive parts <=2 and sum of negative parts <=2 (multiset sizes), sigma(D)=0
#include <bits/stdc++.h>
using namespace std;
typedef vector<int> V;
int main(int argc,char**argv){
  unsigned seed=atoi(argv[1]); int trials=atoi(argv[2]); int dmax=atoi(argv[3]); int side=atoi(argv[4]); int maxN=atoi(argv[5]); int mode=atoi(argv[6]); long maxfib=atol(argv[7]); int maxcols=atoi(argv[8]);
  setvbuf(stdout,NULL,_IONBF,0); mt19937 rng(seed); long tested=0,bad=0,fibers=0;
  for(int t=0;t<trials;t++){
    int d=1+rng()%dmax; set<V> Ds; int ng=1+rng()%4;
    for(int g=0;g<ng;g++){ V gen(d); for(int i=0;i<d;i++) gen[i]=rng()%(side+1); V x(d,0);
      while(true){ Ds.insert(x); int i=0; while(i<d){ if(x[i]<gen[i]){x[i]++;break;} x[i]=0;i++;} if(i==d) break; } }
    Ds.erase(V(d,0)); if(Ds.empty()||(int)Ds.size()>maxcols) continue;
    vector<V> cols(Ds.begin(),Ds.end()); int n=cols.size(); V N(n); for(auto&x:N) x=1+rng()%maxN;
    // enumerate all t via DFS grouping by sigma
    double tot=1; for(int x:N) tot*=(x+1); if(tot>maxfib) continue;
    tested++;
    map<V,vector<V>> fib; V tt(n,0), y(d,0);
    function<void(int)> rec=[&](int i){ if(i==n){ fib[y].push_back(tt); return;} for(int k=0;k<=N[i];k++){ tt[i]=k; rec(i+1); for(int j=0;j<d;j++) y[j]+=cols[i][j]; } for(int j=0;j<d;j++) y[j]-=(N[i]+1)*cols[i][j]; tt[i]=0; };
    rec(0);
    for(auto&kv:fib){ auto&F=kv.second; if(F.size()<2) continue; fibers++;
      vector<char> seen(F.size(),0); vector<int> st={0}; seen[0]=1; size_t cnt=1;
      while(!st.empty()){ int a=st.back(); st.pop_back();
        for(size_t b=0;b<F.size();b++){ if(seen[b]) continue; bool ok;
          if(mode==2){ int big=0; ok=true; for(int i=0;i<n;i++){ int df=abs(F[a][i]-F[b][i]); if(df>2){ok=false;break;} if(df==2) big++; } if(big>1) ok=false; }
          else { int pos=0,neg=0; for(int i=0;i<n;i++){ int df=F[b][i]-F[a][i]; if(df>0) pos+=df; else neg-=df; } ok=(pos<=2&&neg<=2); }
          if(ok){ seen[b]=1; st.push_back(b); cnt++; } } }
      if(cnt!=F.size()){ bad++; if(bad<=3){ printf("FAIL mode%d d=%d D:",mode,d); for(int i=0;i<n;i++){printf(" (");for(int q:cols[i])printf("%d,",q);printf(")N%d",N[i]);} printf(" y=("); for(int q:kv.first)printf("%d,",q); printf(") fibsize=%zu comp=%zu\n",F.size(),cnt);} break; } }
  }
  printf("mode %d tested=%ld fibers=%ld bad=%ld\n",mode,tested,fibers,bad);
}
