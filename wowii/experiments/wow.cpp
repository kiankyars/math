// Check WOWII conjectures 19, 40, 61, 100, 133 on graphs read in graph6 format from stdin.
#include <bits/stdc++.h>
using namespace std;
int n; unsigned adj[32];
bool parse(const string& s){ // graph6, n<=62
  int p=0; n=s[p++]-63; for(int i=0;i<n;i++) adj[i]=0;
  int bit=0; int val=0, k=6;
  for(int j=1;j<n;j++) for(int i=0;i<j;i++){ if(k==6){ val=s[p++]-63; k=0; } int b=(val>>(5-k))&1; k++; if(b){ adj[i]|=1u<<j; adj[j]|=1u<<i; } }
  return true; }
int alphaMask(unsigned m){ // independence number of induced subgraph on m
  if(!m) return 0; int v=__builtin_ctz(m); unsigned rest=m&~(1u<<v);
  int a=alphaMask(rest&~adj[v])+1; // include v
  if(!(adj[v]&rest)) return a; // v isolated in m => include
  int b=alphaMask(rest); return max(a,b); }
bool isForest(unsigned m){ // induced subgraph acyclic: edges == |m| - components
  int e=0; for(unsigned t=m;t;t&=t-1){ int v=__builtin_ctz(t); e+=__builtin_popcount(adj[v]&m); } e/=2;
  int comp=0; unsigned left=m; while(left){ int v=__builtin_ctz(left); unsigned c=1u<<v, fr=c; while(fr){ unsigned nf=0; for(unsigned t=fr;t;t&=t-1){ nf|=adj[__builtin_ctz(t)]&m; } nf&=~c; c|=nf; fr=nf; } left&=~c; comp++; }
  return e==__builtin_popcount(m)-comp; }
bool isBip(unsigned m){ unsigned col0=0,col1=0, left=m; while(left){ int v=__builtin_ctz(left); unsigned c0=1u<<v,c1=0,fr0=c0,fr1=0; bool ok=true;
    while(fr0||fr1){ unsigned n1=0,n0=0; for(unsigned t=fr0;t;t&=t-1) n1|=adj[__builtin_ctz(t)]&m; for(unsigned t=fr1;t;t&=t-1) n0|=adj[__builtin_ctz(t)]&m; if((n1&c0)||(n0&c1)) return false; n1&=~c1; n0&=~c0; c1|=n1; c0|=n0; fr0=n0; fr1=n1; }
    left&=~(c0|c1); } return true; }
int bestInducedPath;
void dfsPath(int v, unsigned used, unsigned forbid, int len){ // forbid: vertices adjacent to path except last
  bestInducedPath=max(bestInducedPath,len);
  unsigned cand=adj[v]&~used&~forbid;
  for(unsigned t=cand;t;t&=t-1){ int w=__builtin_ctz(t); dfsPath(w, used|(1u<<w), forbid|adj[v]|(1u<<v), len+1); }
}
int residueOf(vector<int> d){ sort(d.rbegin(),d.rend()); while(!d.empty() && d[0]>0){ int x=d[0]; d.erase(d.begin()); for(int i=0;i<x && i<(int)d.size();i++) d[i]--; sort(d.rbegin(),d.rend()); } return d.size(); }
int main(int argc,char**argv){
  int doPC=argc>1?atoi(argv[1]):1;
  string s; long cnt=0; long fail[5]={0}; double minslack[5]={1e9,1e9,1e9,1e9,1e9};
  vector<int> isPathMask; vector<int> cover;
  while(getline(cin,s)){ if(s.empty()) continue; parse(s); cnt++; unsigned all=(n==32)?~0u:((1u<<n)-1);
    // eccentricities
    vector<int> ecc(n); for(int v=0;v<n;v++){ unsigned seen=1u<<v, fr=seen; int d=0; while(seen!=all){ unsigned nf=0; for(unsigned t=fr;t;t&=t-1) nf|=adj[__builtin_ctz(t)]; nf&=~seen; if(!nf) break; seen|=nf; fr=nf; d++; } ecc[v]=d; }
    int rad=*min_element(ecc.begin(),ecc.end()), diam=*max_element(ecc.begin(),ecc.end()); long sumecc=0; for(int e:ecc) sumecc+=e;
    int alpha=alphaMask(all); vector<int> l(n); int maxl=0; long suml=0; for(int v=0;v<n;v++){ l[v]=alphaMask(adj[v]); maxl=max(maxl,l[v]); suml+=l[v]; }
    vector<int> deg(n); for(int v=0;v<n;v++) deg[v]=__builtin_popcount(adj[v]);
    int f=0,b=0; for(unsigned m=0;m<=all;m++){ int c=__builtin_popcount(m); if(c>f && isForest(m)) f=c; if(c>b && isBip(m)) b=c; if(m==all) break; }
    bestInducedPath=0; for(int v=0;v<n;v++) dfsPath(v,1u<<v,0,1);
    int path=bestInducedPath;
    // C4
    bool hasC4=false; for(int a=0;a<n&&!hasC4;a++) for(int c=a+1;c<n&&!hasC4;c++){ unsigned common=adj[a]&adj[c]; if(__builtin_popcount(common)>=2) hasC4=true; }
    int res=residueOf(deg);
    // C19: floor(sumecc/n + maxl) <= b
    { long lhs=(sumecc + (long)maxl*n)/n; double slack=b-lhs; if(lhs>b){ fail[0]++; if(fail[0]<=3) cout<<"C19 FAIL "<<s<<" n="<<n<<" lhs="<<lhs<<" b="<<b<<"\n"; } minslack[0]=min(minslack[0],slack); }
    // C61: res + ceil(diam/3) <= f
    { int lhs=res+(diam+2)/3; if(lhs>f){ fail[2]++; if(fail[2]<=3) cout<<"C61 FAIL "<<s<<" n="<<n<<" res="<<res<<" diam="<<diam<<" f="<<f<<"\n"; } minslack[2]=min(minslack[2],(double)(f-lhs)); }
    // C100: alpha <= ceil((maxl + 0.5 sqrt(sum degc^2))/2)
    { long S=0; for(int v=0;v<n;v++){ long dc=n-1-deg[v]; S+=dc*dc; } double val=(maxl+0.5*sqrt((double)S))/2; long rhs=(long)ceil(val-1e-9); if(alpha>rhs){ fail[3]++; if(fail[3]<=3) cout<<"C100 FAIL "<<s<<" n="<<n<<" alpha="<<alpha<<" rhs="<<rhs<<" val="<<val<<"\n"; } minslack[3]=min(minslack[3],(double)(rhs-alpha)); }
    // C133: rad + l^{cC4} <= path ; if hasC4 exponent 0 -> rad+1
    { double lhs = hasC4 ? rad+1 : rad + (double)suml/n; if(lhs>path+1e-9){ fail[4]++; if(fail[4]<=3) cout<<"C133 FAIL "<<s<<" n="<<n<<" rad="<<rad<<" avgl="<<(double)suml/n<<" path="<<path<<" C4="<<hasC4<<"\n"; } minslack[4]=min(minslack[4],path-lhs); }
    // C40: ceil((pc + b + 1)/2) <= f   (path cover number)
    if(doPC){ int N=1<<n; isPathMask.assign(N,0); vector<unsigned> endset(N,0); // endset[m] = vertices v such that m has a Ham path ending at v
      for(int v=0;v<n;v++) endset[1<<v]=1u<<v;
      for(int m=1;m<N;m++){ if(!endset[m]) continue; for(unsigned t=endset[m];t;t&=t-1){ int v=__builtin_ctz(t); unsigned nb=adj[v]&~m; for(unsigned u=nb;u;u&=u-1){ int w=__builtin_ctz(u); endset[m|(1<<w)]|=1u<<w; } } }
      cover.assign(N,99); cover[0]=0; for(int m=1;m<N;m++){ int low=m&-m; for(int sub=m; sub; sub=(sub-1)&m){ if(!(sub&low)) continue; if(endset[sub]&&cover[m^sub]+1<cover[m]) cover[m]=cover[m^sub]+1; } }
      int pc=cover[N-1]; int lhs=(pc+b+1+1)/2; if(lhs>f){ fail[1]++; if(fail[1]<=3) cout<<"C40 FAIL "<<s<<" n="<<n<<" pc="<<pc<<" b="<<b<<" f="<<f<<"\n"; } minslack[1]=min(minslack[1],(double)(f-lhs)); }
  }
  printf("graphs=%ld fails: C19=%ld C40=%ld C61=%ld C100=%ld C133=%ld | minslack C19=%.2f C40=%.2f C61=%.2f C100=%.2f C133=%.3f\n",cnt,fail[0],fail[1],fail[2],fail[3],fail[4],minslack[0],minslack[1],minslack[2],minslack[3],minslack[4]);
}
