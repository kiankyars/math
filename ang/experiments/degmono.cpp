// Monotone systems (no zero column). Reachable set R = R(D, m), m=J+1. For raisable w0 (all w<w0 in D* have J(w)>=J(w0)+1),
// count degenerate configs: D1(w0): u,u-2w0 in R, u-w0 notin R. D2(w0,v): u-w0,u-v in R; u,u-v-w0 notin R. D3(w0,v): u,u-v-w0 in R; u-v,u-w0 notin R.
#include <bits/stdc++.h>
using namespace std;
typedef vector<int> V;
int main(int argc,char**argv){
  unsigned seed=atoi(argv[1]); int trials=atoi(argv[2]); int dmax=atoi(argv[3]); int side=atoi(argv[4]); int maxJ=atoi(argv[5]); int maxcols=atoi(argv[6]); long maxR=atol(argv[7]); int mode=atoi(argv[8]);
  setvbuf(stdout,NULL,_IONBF,0); mt19937 rng(seed); long tested=0,d1=0,d2=0,d3=0,d1any=0;
  const long OFF=512,B=2048;
  for(int t=0;t<trials;t++){
    int d=2+rng()%(dmax-1); vector<V> cols; vector<int> J;
    if(mode==0){
      set<V> Ds; int ng=1+rng()%5;
      for(int g=0;g<ng;g++){ V gen(d); for(int i=0;i<d;i++) gen[i]=rng()%(side+1); V x(d,0);
        while(true){ Ds.insert(x); int i=0; while(i<d){ if(x[i]<gen[i]){x[i]++;break;} x[i]=0;i++;} if(i==d) break; } }
      Ds.erase(V(d,0)); cols.assign(Ds.begin(),Ds.end());
      sort(cols.begin(),cols.end(),[](const V&a,const V&b){int sa=0,sb=0; for(int x:a)sa+=x; for(int x:b)sb+=x; if(sa!=sb) return sa<sb; return a<b;});
      J.resize(cols.size()); for(size_t c=0;c<cols.size();c++){ int ub=maxJ; for(size_t c2=0;c2<c;c2++){ bool le=true; for(int i=0;i<d;i++) if(cols[c2][i]>cols[c][i]) le=false; if(le) ub=min(ub,J[c2]); } J[c]=rng()%(ub+1); }
    } else {
      vector<double> a(d); for(auto&x:a) x=0.04+0.5*(rng()%1000)/1000.0; double ap=0.04+0.5*(rng()%1000)/1000.0;
      V e(d,0);
      function<void(int,double)> rec=[&](int i,double s){ if(i==d){ bool z=true; for(int x:e) if(x) z=false; if(!z){ cols.push_back(e); J.push_back((int)floor((1.0-s)/ap+1e-12)); } return; } for(int k=0; s+k*a[i]<=1.0+1e-12; k++){ e[i]=k; rec(i+1,s+k*a[i]); } e[i]=0; };
      rec(0,0.0);
    }
    if(cols.empty()||(int)cols.size()>maxcols) continue;
    auto enc=[&](const V&v){ long e=0; for(int i=0;i<d;i++){ e=e*B+(v[i]+OFF);} return e; };
    unordered_set<long> R; vector<V> Rl; R.insert(enc(V(d,0))); Rl.push_back(V(d,0)); bool big=false;
    for(size_t c=0;c<cols.size()&&!big;c++){ vector<V> add; for(auto&y:Rl){ V z=y; for(int k=1;k<=J[c]+1;k++){ for(int i=0;i<d;i++) z[i]+=cols[c][i]; long e=enc(z); if(!R.count(e)){ R.insert(e); add.push_back(z);} } } for(auto&z:add) Rl.push_back(z); if((long)Rl.size()>maxR) big=true; }
    if(big) continue; tested++;
    auto in=[&](const V&v){ return R.count(enc(v))>0; };
    vector<char> rais(cols.size(),1);
    for(size_t c=0;c<cols.size();c++) for(size_t c2=0;c2<cols.size();c2++){ if(c2==c) continue; bool le=true; for(int i=0;i<d;i++) if(cols[c2][i]>cols[c][i]) le=false; if(le && J[c2]<J[c]+1) rais[c]=0; }
    for(size_t a=0;a<cols.size();a++){ const V&w0=cols[a];
      for(auto&u:Rl){ V u1=u,u2=u; for(int i=0;i<d;i++){u1[i]-=w0[i];u2[i]-=2*w0[i];}
        if(in(u2)&&!in(u1)){ d1any++; if(rais[a]) d1++; } }
      if(!rais[a]) continue;
      for(size_t b=0;b<cols.size();b++){ if(b==a) continue; const V&v=cols[b];
        for(auto&u:Rl){ // u in R : D3 check: u-v-w0 in R, u-v,u-w0 notin R
          V uv=u,uw=u,uvw=u; for(int i=0;i<d;i++){uv[i]-=v[i];uw[i]-=w0[i];uvw[i]-=v[i]+w0[i];}
          if(in(uvw)&&!in(uv)&&!in(uw)) d3++; }
        for(auto&a2:Rl){ // a2 = u-w0 in R; u = a2+w0; need u-v = a2+w0-v in R, u notin R, u-v-w0 = a2-v notin R
          V u=a2; for(int i=0;i<d;i++) u[i]+=w0[i]; V uv=u, uvw=a2; for(int i=0;i<d;i++){uv[i]-=v[i]; uvw[i]-=v[i];}
          if(in(uv)&&!in(u)&&!in(uvw)) d2++; }
      } }
  }
  printf("mode %d tested=%ld D1(any w0)=%ld D1(raisable)=%ld D2(raisable w0)=%ld D3(raisable w0)=%ld\n",mode,tested,d1any,d1,d2,d3);
}
