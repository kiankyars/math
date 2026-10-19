// G_ms: D down-closed in N^d; column v = multiset of heights with support {0..J(v)} (each mult>=1). Check intervals.
#include <bits/stdc++.h>
using namespace std;
typedef vector<int> V;
int main(int argc,char**argv){
  unsigned seed=atoi(argv[1]); int trials=atoi(argv[2]); int dmax=atoi(argv[3]); int side=atoi(argv[4]); int maxJ=atoi(argv[5]); int maxmult=atoi(argv[6]); int maxelts=atoi(argv[7]); int consecutive=atoi(argv[8]);
  setvbuf(stdout,NULL,_IONBF,0);
  mt19937 rng(seed); long tested=0,bad=0;
  for(int t=0;t<trials;t++){
    int d=1+rng()%dmax; set<V> Ds; int ng=1+rng()%4;
    for(int g=0;g<ng;g++){ V gen(d); for(int i=0;i<d;i++) gen[i]=rng()%(side+1); V x(d,0);
      while(true){ Ds.insert(x); int i=0; while(i<d){ if(x[i]<gen[i]){x[i]++;break;} x[i]=0;i++;} if(i==d) break; } }
    vector<V> cols(Ds.begin(),Ds.end());
    vector<pair<V,int>> elts;
    for(auto&w:cols){ int J=rng()%(maxJ+1); for(int h=0;h<=J;h++){ int mu=1+rng()%maxmult; if(!consecutive && h>0 && rng()%3==0) mu=0; for(int k=0;k<mu;k++) elts.push_back({w,h}); } }
    if((int)elts.size()>maxelts) continue;
    tested++;
    int maxh=0; for(auto&e:elts) maxh+=e.second;
    map<V,vector<char>> D; D[V(d,0)]=vector<char>(maxh+1,0); D[V(d,0)][0]=1;
    for(auto&e:elts){ map<V,vector<char>> N2=D; for(auto&kv:D){ V y=kv.first; for(int i=0;i<d;i++) y[i]+=e.first[i]; auto&tg=N2[y]; if(tg.empty()) tg.assign(maxh+1,0); for(int h=0;h+e.second<=maxh;h++) if(kv.second[h]) tg[h+e.second]=1; } D.swap(N2); }
    for(auto&kv:D){ int lo=-1,hi=-1,cnt=0; for(int h=0;h<=maxh;h++) if(kv.second[h]){ if(lo<0) lo=h; hi=h; cnt++; } if(cnt!=hi-lo+1){ bad++; if(bad<=3){ printf("FAIL d=%d elts:",d); for(auto&e:elts){printf(" (");for(int q:e.first)printf("%d,",q);printf(")h%d",e.second);} printf(" u=("); for(int q:kv.first)printf("%d,",q); printf(")\n"); } break; } }
  }
  printf("tested=%ld bad=%ld\n",tested,bad);
}
