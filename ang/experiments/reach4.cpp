// Faster R1-R3 test using hash set of encoded vectors. Includes negative x for R2.
#include <bits/stdc++.h>
using namespace std;
typedef vector<int> V;
int main(int argc,char**argv){
  unsigned seed=atoi(argv[1]); int trials=atoi(argv[2]); int dmax=atoi(argv[3]); int side=atoi(argv[4]); int maxm=atoi(argv[5]); int maxcols=atoi(argv[6]); long maxR=atol(argv[7]);
  setvbuf(stdout,NULL,_IONBF,0); mt19937 rng(seed); long tested=0,b1=0,b2=0,b3=0;
  const long OFF=512, B=2048;
  for(int t=0;t<trials;t++){
    int d=2+rng()%(dmax-1); set<V> Ds; int ng=1+rng()%5;
    for(int g=0;g<ng;g++){ V gen(d); for(int i=0;i<d;i++) gen[i]=rng()%(side+1); V x(d,0);
      while(true){ Ds.insert(x); int i=0; while(i<d){ if(x[i]<gen[i]){x[i]++;break;} x[i]=0;i++;} if(i==d) break; } }
    Ds.erase(V(d,0)); if(Ds.empty()||(int)Ds.size()>maxcols) continue;
    vector<V> cols(Ds.begin(),Ds.end()); sort(cols.begin(),cols.end(),[](const V&a,const V&b){int sa=0,sb=0; for(int x:a)sa+=x; for(int x:b)sb+=x; if(sa!=sb) return sa<sb; return a<b;});
    vector<int> m(cols.size());
    for(size_t c=0;c<cols.size();c++){ int ub=maxm; for(size_t c2=0;c2<c;c2++){ bool le=true; for(int i=0;i<d;i++) if(cols[c2][i]>cols[c][i]) le=false; if(le) ub=min(ub,m[c2]); } m[c]=1+rng()%ub; }
    auto enc=[&](const V&v){ long e=0; for(int i=0;i<d;i++){ e=e*B+(v[i]+OFF);} return e; };
    unordered_set<long> R; vector<V> Rl; R.insert(enc(V(d,0))); Rl.push_back(V(d,0));
    bool big=false;
    for(size_t c=0;c<cols.size()&&!big;c++){ vector<V> add; for(auto&y:Rl){ V z=y; for(int k=1;k<=m[c];k++){ for(int i=0;i<d;i++) z[i]+=cols[c][i]; long e=enc(z); if(!R.count(e)){ R.insert(e); add.push_back(z);} } } for(auto&z:add) Rl.push_back(z); if((long)Rl.size()>maxR) big=true; }
    if(big) continue; tested++;
    auto in=[&](const V&v){ return R.count(enc(v))>0; };
    for(auto&u:Rl) for(size_t a=0;a<cols.size();a++){
      const V&w=cols[a]; V u1=u,u2=u; for(int i=0;i<d;i++){u1[i]-=w[i];u2[i]-=2*w[i];}
      if(in(u2)&&!in(u1)) b1++;
      for(size_t b=a+1;b<cols.size();b++){ const V&w2=cols[b]; V uw2=u, uww=u1; for(int i=0;i<d;i++){uw2[i]-=w2[i];uww[i]-=w2[i];}
        if(in(uww)&&!in(u1)&&!in(uw2)){ b3++; if(b3<=3){printf("R3 FAIL\n");} }
        // R2 with x = u - w - w2 : x+w = u-w2, x+w2 = u-w  in R ; need x or x+w+w2=u
        if(in(uw2)&&in(u1)) {} 
      }
    }
    // R2: for a in R (a = x+w), b=x+w2 in R => x in R or x+w+w2 in R
    for(auto&a:Rl) for(size_t i1=0;i1<cols.size();i1++) for(size_t i2=0;i2<cols.size();i2++){ if(i1==i2) continue; const V&w=cols[i1]; const V&w2=cols[i2];
      V x=a, bb=a, c=a; for(int i=0;i<d;i++){ x[i]-=w[i]; bb[i]+=w2[i]-w[i]; c[i]+=w2[i]; }
      if(in(bb)&&!in(x)&&!in(c)){ b2++; if(b2<=3){ printf("R2 FAIL d=%d:",d); for(size_t q=0;q<cols.size();q++){printf(" (");for(int z:cols[q])printf("%d,",z);printf(")m%d",m[q]);} printf(" x=("); for(int z:x)printf("%d,",z); printf(") w=%zu w2=%zu\n",i1,i2);} } }
  }
  printf("tested=%ld R1fail=%ld R2fail=%ld R3fail=%ld\n",tested,b1,b2,b3);
}
