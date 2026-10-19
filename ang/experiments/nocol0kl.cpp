// Down-set I in N^(d+1) (columns over down-closed D with monotone heights). Remove column over 0. Check V(u) intervals.
// mode 0: random down-sets; mode 1: threshold down-sets {x : sum a_i x_i <= 1} with random weights.
#include <bits/stdc++.h>
using namespace std;
typedef vector<int> V;
int main(int argc,char**argv){
  unsigned seed=atoi(argv[1]); int trials=atoi(argv[2]); int dmax=atoi(argv[3]); int side=atoi(argv[4]); int maxJ=atoi(argv[5]); int maxelts=atoi(argv[6]); int mode=atoi(argv[7]);
  setvbuf(stdout,NULL,_IONBF,0); mt19937 rng(seed); long tested=0,bad=0,klall=0,klr=0; int worstgap=0;
  for(int t=0;t<trials;t++){
    int d=1+rng()%dmax; vector<pair<V,int>> cols;
    if(mode==0){
      set<V> Ds; int ng=1+rng()%4;
      for(int g=0;g<ng;g++){ V gen(d); for(int i=0;i<d;i++) gen[i]=rng()%(side+1); V x(d,0);
        while(true){ Ds.insert(x); int i=0; while(i<d){ if(x[i]<gen[i]){x[i]++;break;} x[i]=0;i++;} if(i==d) break; } }
      vector<V> cs(Ds.begin(),Ds.end()); sort(cs.begin(),cs.end(),[](const V&a,const V&b){int sa=0,sb=0; for(int x:a)sa+=x; for(int x:b)sb+=x; if(sa!=sb) return sa<sb; return a<b;});
      map<V,int> J; for(auto&w:cs){ int ub=maxJ; for(auto&kv:J){ bool le=true; for(int i=0;i<d;i++) if(kv.first[i]>w[i]) le=false; if(le) ub=min(ub,kv.second);} J[w]=rng()%(ub+1); }
      for(auto&w:cs){ bool z=true; for(int x:w) if(x) z=false; if(!z) cols.push_back({w,J[w]}); }
    } else {
      // weights: a_i in (0,1), a_p for height
      vector<double> a(d); for(auto&x:a) x=0.05+0.6*(rng()%1000)/1000.0; double ap=0.05+0.5*(rng()%1000)/1000.0;
      // enumerate e with sum a_i e_i <= 1
      V e(d,0);
      function<void(int,double)> rec=[&](int i,double s){ if(i==d){ bool z=true; for(int x:e) if(x) z=false; if(!z){ int J=(int)floor((1.0-s)/ap+1e-12); cols.push_back({e,J}); } return; } for(int k=0; s+k*a[i]<=1.0+1e-12; k++){ e[i]=k; rec(i+1,s+k*a[i]); } e[i]=0; };
      rec(0,0.0);
    }
    int ne=0; for(auto&c:cols) ne+=c.second+1; if(ne>maxelts||cols.empty()) continue;
    tested++;
    int maxh=0; for(auto&c:cols) maxh+=(c.second+1)*c.second/2;
    map<V,vector<char>> D; D[V(d,0)]=vector<char>(maxh+1,0); D[V(d,0)][0]=1;
    for(auto&c:cols){ int Jr=c.second; map<V,vector<char>> N2;
      for(auto&kv:D){ V y=kv.first; for(int k=0;k<=Jr+1;k++){ int L=k*(k-1)/2,H=k*Jr-k*(k-1)/2; auto&tg=N2[y]; if(tg.empty()) tg.assign(maxh+1,0);
          for(int h=0;h<=maxh;h++) if(kv.second[h]) for(int v=L;v<=H&&h+v<=maxh;v++) tg[h+v]=1;
          for(int i=0;i<d;i++) y[i]+=c.first[i]; } }
      D.swap(N2); }
    map<V,pair<int,int>> MM; for(auto&kv:D){ int lo=-1,hi=-1; for(int h=0;h<=maxh;h++) if(kv.second[h]){ if(lo<0) lo=h; hi=h; } MM[kv.first]={lo,hi}; }
    map<V,int> JJ; for(auto&c:cols) JJ[c.first]=c.second;
    for(auto&c:cols){ const V&v=c.first; int Jv=c.second;
      bool raisable=true; for(int i=0;i<d;i++) if(v[i]>0){ V w=v; w[i]--; bool z=true; for(int x:w) if(x) z=false; if(z) continue; if(JJ[w]<Jv+1) raisable=false; }
      for(auto&kv:MM){ V z=kv.first; bool ok=true; for(int i=0;i<d;i++){ z[i]-=v[i]; if(z[i]<0) ok=false; } if(!ok) continue; auto it=MM.find(z); if(it==MM.end()) continue;
        int lo=max(kv.second.first,it->second.first+Jv), hi=min(kv.second.second,it->second.second+Jv);
        if(lo>hi){ klall++; if(raisable) klr++; } } }
    bool any=false;
    for(auto&kv:D){ int prev=-1; for(int h=0;h<=maxh;h++) if(kv.second[h]){ if(prev>=0){ worstgap=max(worstgap,h-prev); if(h-prev>1) any=true; } prev=h; } }
    if(any) bad++;
  }
  printf("mode %d tested=%ld systems-with-gap=%ld worstgap=%d KLfail(all cols)=%ld KLfail(raisable)=%ld\n",mode,tested,bad,worstgap,klall,klr);
}
