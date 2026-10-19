// Theorem G with ARBITRARY heights on convex (threshold) down-sets D={e: sum a_i e_i <= 1}. Also KL and R1-R3.
#include <bits/stdc++.h>
using namespace std;
typedef vector<int> V;
int main(int argc,char**argv){
  unsigned seed=atoi(argv[1]); int trials=atoi(argv[2]); int dmax=atoi(argv[3]); int maxJ=atoi(argv[4]); int maxcols=atoi(argv[5]); int maxelts=atoi(argv[6]); double amin=atof(argv[7]);
  setvbuf(stdout,NULL,_IONBF,0); mt19937 rng(seed); long tested=0,badG=0,badKL=0;
  for(int t=0;t<trials;t++){
    int d=2+rng()%(dmax-1); vector<double> a(d); for(auto&x:a) x=amin+(0.6-amin)*(rng()%10000)/10000.0;
    vector<V> cols; V e(d,0);
    function<void(int,double)> rec=[&](int i,double s){ if(i==d){ bool z=true; for(int x:e) if(x) z=false; if(!z) cols.push_back(e); return; } for(int k=0; s+k*a[i]<=1.0+1e-12; k++){ e[i]=k; rec(i+1,s+k*a[i]); } e[i]=0; };
    rec(0,0.0);
    if(cols.empty()||(int)cols.size()>maxcols) continue;
    vector<int> J(cols.size()); for(auto&x:J) x=rng()%(maxJ+1);
    int ne=0; for(int j:J) ne+=j+1; if(ne>maxelts) continue; tested++;
    int maxh=0; for(int j:J) maxh+=(j+1)*j/2;
    map<V,vector<char>> Dm; Dm[V(d,0)]=vector<char>(maxh+1,0); Dm[V(d,0)][0]=1;
    for(size_t c=0;c<cols.size();c++){ int Jr=J[c]; map<V,vector<char>> N2;
      for(auto&kv:Dm){ V y=kv.first; for(int k=0;k<=Jr+1;k++){ int L=k*(k-1)/2,H=k*Jr-k*(k-1)/2; auto&tg=N2[y]; if(tg.empty()) tg.assign(maxh+1,0);
          for(int h=0;h<=maxh;h++) if(kv.second[h]) for(int v=L;v<=H&&h+v<=maxh;v++) tg[h+v]=1;
          for(int i=0;i<d;i++) y[i]+=cols[c][i]; } }
      Dm.swap(N2); }
    map<V,pair<int,int>> MM; bool okG=true;
    for(auto&kv:Dm){ int lo=-1,hi=-1,cnt=0; for(int h=0;h<=maxh;h++) if(kv.second[h]){ if(lo<0) lo=h; hi=h; cnt++; } if(cnt!=hi-lo+1) okG=false; MM[kv.first]={lo,hi}; }
    if(!okG){ badG++; if(badG<=3){ printf("G FAIL d=%d:",d); for(size_t c=0;c<cols.size();c++){printf(" (");for(int q:cols[c])printf("%d,",q);printf(")J%d",J[c]);} printf("\n"); } }
    for(size_t c=0;c<cols.size();c++) for(auto&kv:MM){ V z=kv.first; bool ok=true; for(int i=0;i<d;i++){ z[i]-=cols[c][i]; if(z[i]<0) ok=false;} if(!ok) continue; auto it=MM.find(z); if(it==MM.end()) continue;
      int lo=max(kv.second.first,it->second.first+J[c]), hi=min(kv.second.second,it->second.second+J[c]); if(lo>hi) badKL++; }
  }
  printf("tested=%ld Gfail=%ld KLfail=%ld\n",tested,badG,badKL);
}
