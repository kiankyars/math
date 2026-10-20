// TxGraffiti conj 3: r-regular G => i(G) <= mu*(G) (min maximal matching). graph6 input, n<=62.
#include <bits/stdc++.h>
using namespace std; typedef unsigned long long u64;
int n; u64 adj[64]; vector<pair<int,int>> E;
void parse(const string& s){ int p=0; n=s[p++]-63; for(int i=0;i<n;i++) adj[i]=0; E.clear(); int val=0,k=6;
  for(int j=1;j<n;j++) for(int i=0;i<j;i++){ if(k==6){ val=s[p++]-63; k=0; } int b=(val>>(5-k))&1; k++; if(b){ adj[i]|=1ULL<<j; adj[j]|=1ULL<<i; E.push_back({i,j}); } } }
int bestI;
// min independent dominating set: choose vertices; undominated set 'und'; candidates must be non-adjacent to chosen.
void idom(u64 chosen,u64 dom,u64 allowed,int sz){ // dom = closed nbhd of chosen
  if(sz>=bestI) return; u64 und=~dom & ((n==64)?~0ULL:((1ULL<<n)-1)); if(!und){ bestI=sz; return; }
  int v=__builtin_ctzll(und); // v must be dominated: choose v or a neighbour of v that is allowed
  u64 opts=(adj[v]|(1ULL<<v))&allowed;
  for(u64 t=opts;t;t&=t-1){ int w=__builtin_ctzll(t); u64 cl=adj[w]|(1ULL<<w); idom(chosen|(1ULL<<w),dom|cl,allowed&~cl,sz+1); }
}
int bestM;
// min maximal matching: every edge must be dominated (share endpoint with matched edge). pick first undominated edge uv: match u-x or v-y for some x,y free.
void mm(u64 matched,int sz){ if(sz>=bestM) return; int ue=-1; for(int i=0;i<(int)E.size();i++){ auto [a,b]=E[i]; if(!((matched>>a)&1) && !((matched>>b)&1)){ ue=i; break; } }
  if(ue<0){ bestM=sz; return; } auto [a,b]=E[ue];
  for(int end=0;end<2;end++){ int u= end? b:a; u64 fr=adj[u]&~matched; for(u64 t=fr;t;t&=t-1){ int w=__builtin_ctzll(t); if(end==1 && w==a) continue; // avoid double counting edge ab
      mm(matched|(1ULL<<u)|(1ULL<<w),sz+1);} }
}
int main(){ string s; long cnt=0,fails=0; int minsl=1e9;
  while(getline(cin,s)){ if(s.empty()) continue; parse(s); cnt++;
    bestI=n+1; idom(0,0,(n==64)?~0ULL:((1ULL<<n)-1),0); bestM=n; mm(0,0);
    int sl=bestM-bestI; if(sl<minsl) minsl=sl; if(sl<0){ fails++; if(fails<=10) printf("FAIL %s n=%d i=%d mu*=%d\n",s.c_str(),n,bestI,bestM); }
    if(sl==0 && cnt<0) printf("tight %s\n",s.c_str());
  }
  printf("graphs=%ld fails=%ld min(mu*-i)=%d\n",cnt,fails,minsl); }
