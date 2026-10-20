// C133 on C4-free graphs: slack = path - rad - avg l. Reports min slack and tight graphs.
#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64;
int n; u64 adj[64];
void parse(const string& s){ int p=0; n=s[p++]-63; for(int i=0;i<n;i++) adj[i]=0; int val=0,k=6;
  for(int j=1;j<n;j++) for(int i=0;i<j;i++){ if(k==6){ val=s[p++]-63; k=0; } int b=(val>>(5-k))&1; k++; if(b){ adj[i]|=1ULL<<j; adj[j]|=1ULL<<i; } } }
int alphaMask(u64 m){ if(!m) return 0; int v=__builtin_ctzll(m); u64 rest=m&~(1ULL<<v); int a=alphaMask(rest&~adj[v])+1; if(!(adj[v]&rest)) return a; return max(a,alphaMask(rest)); }
int best;
void dfs(int v,u64 used,u64 forbid,int len){ if(len>best) best=len; u64 c=adj[v]&~used&~forbid; for(u64 t=c;t;t&=t-1){ int w=__builtin_ctzll(t); dfs(w,used|(1ULL<<w),forbid|adj[v]|(1ULL<<v),len+1);} }
int main(int argc,char**argv){ string s; long cnt=0; double mins=1e9; vector<string> tight; double thr=argc>1?atof(argv[1]):0.5;
  while(getline(cin,s)){ if(s.empty()) continue; parse(s); cnt++; u64 all=(n==64)?~0ULL:((1ULL<<n)-1);
    int rad=1e9; for(int v=0;v<n;v++){ u64 seen=1ULL<<v,fr=seen; int d=0; while(seen!=all){ u64 nf=0; for(u64 t=fr;t;t&=t-1) nf|=adj[__builtin_ctzll(t)]; nf&=~seen; seen|=nf; fr=nf; d++; } rad=min(rad,d); }
    long suml=0; for(int v=0;v<n;v++) suml+=alphaMask(adj[v]);
    best=0; for(int v=0;v<n;v++) dfs(v,1ULL<<v,0,1);
    double sl=best-rad-(double)suml/n; if(sl<mins-1e-12) mins=sl;
    if(sl<thr+1e-9){ char buf[200]; snprintf(buf,200," n=%d rad=%d avgl=%.3f path=%d slack=%.3f",n,rad,(double)suml/n,best,sl); cout<<s<<buf<<"\n"; }
  }
  fprintf(stderr,"graphs=%ld minslack=%.4f\n",cnt,mins); }
