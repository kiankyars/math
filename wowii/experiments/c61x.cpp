// For each connected graph: does there exist X (3-packing: pairwise dist>=3), |X| >= ceil(D/3), with
//  (a) |X| + alpha(G-X) >= R(G) + ceil(D/3)   [suffices for C61]
//  (b) |X| + R(G-X) >= R(G) + ceil(D/3)
//  restricted to X on a diametral (shortest) path, and general X.
#include <bits/stdc++.h>
using namespace std;
int n; unsigned adj[32]; int dist[32][32];
void parse(const string& s){ int p=0; n=s[p++]-63; for(int i=0;i<n;i++) adj[i]=0; int val=0,k=6;
  for(int j=1;j<n;j++) for(int i=0;i<j;i++){ if(k==6){ val=s[p++]-63; k=0; } int b=(val>>(5-k))&1; k++; if(b){ adj[i]|=1u<<j; adj[j]|=1u<<i; } } }
int alphaMask(unsigned m){ if(!m) return 0; int v=__builtin_ctz(m); unsigned rest=m&~(1u<<v); int a=alphaMask(rest&~adj[v])+1; if(!(adj[v]&rest)) return a; return max(a,alphaMask(rest)); }
int residueOf(vector<int> d){ sort(d.rbegin(),d.rend()); while(!d.empty()&&d[0]>0){ int x=d[0]; d.erase(d.begin()); for(int i=0;i<x&&i<(int)d.size();i++) d[i]--; sort(d.rbegin(),d.rend()); } return d.size(); }
int resMask(unsigned m){ vector<int> d; for(unsigned t=m;t;t&=t-1){ int v=__builtin_ctz(t); d.push_back(__builtin_popcount(adj[v]&m)); } return residueOf(d); }
int main(){ string s; long cnt=0, failAgen=0, failApath=0, failBgen=0, failBpath=0;
  while(getline(cin,s)){ if(s.empty()) continue; parse(s); cnt++; unsigned ALL=(1u<<n)-1;
    for(int v=0;v<n;v++){ for(int u=0;u<n;u++) dist[v][u]=-1; dist[v][v]=0; deque<int> q{v}; while(!q.empty()){ int x=q.front(); q.pop_front(); for(unsigned t=adj[x];t;t&=t-1){ int y=__builtin_ctz(t); if(dist[v][y]<0){ dist[v][y]=dist[v][x]+1; q.push_back(y);} } } }
    int D=0; for(int a=0;a<n;a++) for(int b=0;b<n;b++) D=max(D,dist[a][b]);
    int R=resMask(ALL); int need=R+(D+2)/3; int c3=(D+2)/3;
    // general X: enumerate subsets with pairwise dist>=3, size>=c3
    bool okAg=false, okBg=false;
    for(unsigned X=1;X<=ALL && !(okAg&&okBg);X++){ int sz=__builtin_popcount(X); if(sz<c3) continue; bool pk=true; for(unsigned t=X;t&&pk;t&=t-1){ int a=__builtin_ctz(t); for(unsigned u=t&(t-1);u;u&=u-1){ int b=__builtin_ctz(u); if(dist[a][b]<3){pk=false;break;} } } if(!pk) continue;
      if(!okAg && sz+alphaMask(ALL&~X)>=need) okAg=true; if(!okBg && sz+resMask(ALL&~X)>=need) okBg=true; }
    if(!okAg){ failAgen++; if(failAgen<=3) printf("A-general FAIL %s\n",s.c_str()); }
    if(!okBg){ failBgen++; if(failBgen<=5) printf("B-general FAIL %s n=%d R=%d D=%d\n",s.c_str(),n,R,D); }
  }
  printf("graphs=%ld failA_general=%ld failB_general=%ld\n",cnt,failAgen,failBgen); }
