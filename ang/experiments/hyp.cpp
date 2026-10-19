// Test interval property for column systems under various hypotheses.
// variant 1: D arbitrary nonzero set, J(w) <= J0 arbitrary
// variant 2: D down-closed, J arbitrary <= J0
// variant 3: D arbitrary, J monotone w.r.t. present elements (u<=w => J(u)>=J(w)), J<=J0
// variant 4: D down-closed, J monotone (true model)
#include <bits/stdc++.h>
using namespace std;
typedef vector<int> V;
int main(int argc,char**argv){
  unsigned seed=atoi(argv[1]); int trials=atoi(argv[2]); int variant=atoi(argv[3]); int dmax=atoi(argv[4]); int side=atoi(argv[5]); int maxJ=atoi(argv[6]); int maxcols=atoi(argv[7]);
  mt19937 rng(seed); long tested=0,bad=0;
  for(int t=0;t<trials;t++){
    int d=1+rng()%dmax; int J0=rng()%(maxJ+1);
    set<V> Ds;
    if(variant==2||variant==4){ int ng=1+rng()%4; for(int g=0;g<ng;g++){ V gen(d); for(int i=0;i<d;i++) gen[i]=rng()%(side+1); V x(d,0);
      while(true){ Ds.insert(x); int i=0; while(i<d){ if(x[i]<gen[i]){x[i]++;break;} x[i]=0;i++;} if(i==d) break; } } }
    else { int m=1+rng()%maxcols; for(int g=0;g<m;g++){ V x(d); for(int i=0;i<d;i++) x[i]=rng()%(side+1); Ds.insert(x);} }
    Ds.erase(V(d,0)); if(Ds.empty()||(int)Ds.size()>maxcols) continue;
    vector<V> cols(Ds.begin(),Ds.end()); sort(cols.begin(),cols.end(),[](const V&a,const V&b){int sa=0,sb=0; for(int x:a)sa+=x; for(int x:b)sb+=x; return sa<sb;});
    map<V,int> J;
    for(auto&w:cols){ int ub=J0; if(variant>=3) for(auto&kv:J){ bool le=true; for(int i=0;i<d;i++) if(kv.first[i]>w[i]) le=false; if(le) ub=min(ub,kv.second);} J[w]=rng()%(ub+1); }
    int T=J0*(J0+1)/2; tested++;
    int maxh=0; for(auto&w:cols){int j=J[w]; maxh+=(j+1)*j/2;}
    map<V,vector<char>> D; D[V(d,0)]=vector<char>(maxh+1,0); D[V(d,0)][0]=1;
    for(auto&w:cols){ int Jr=J[w]; map<V,vector<char>> N2;
      for(auto&kv:D){ V y=kv.first; for(int k=0;k<=Jr+1;k++){ int L=k*(k-1)/2,H=k*Jr-k*(k-1)/2; auto&tg=N2[y]; if(tg.empty()) tg.assign(maxh+1,0);
          for(int h=0;h<=maxh;h++) if(kv.second[h]) for(int v=L;v<=H&&h+v<=maxh;v++) tg[h+v]=1;
          for(int i=0;i<d;i++) y[i]+=w[i]; } }
      D.swap(N2); }
    for(auto&kv:D){ int prev=-1; bool ok=true; for(int h=0;h<=maxh;h++) if(kv.second[h]){ if(prev>=0&&h-prev>T+1) ok=false; prev=h; }
      if(!ok){ bad++; if(bad<=2){ printf("FAIL v%d J0=%d:",variant,J0); for(auto&w:cols){printf(" (");for(int x:w)printf("%d,",x);printf(")J%d",J[w]);} printf(" R=("); for(int x:kv.first)printf("%d,",x); printf(")\n");} break; } }
  }
  printf("variant %d tested=%ld bad=%ld\n",variant,tested,bad);
}
