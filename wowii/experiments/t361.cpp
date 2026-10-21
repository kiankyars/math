// Trees: WOWII 361 (gamma_t >= iso<S> + |C|) and 376 (gamma_t >= iso<M> + |median|). Input: sparse6 or graph6 trees.
#include <bits/stdc++.h>
using namespace std;
int n; vector<vector<int>> g;
bool parse(const string& s){
  g.clear();
  if(s[0]==':'){ // sparse6
    int p=1; n=s[p++]-63; g.assign(n,{}); int k=1; while((1<<k)<n) k++;
    vector<int> bits; for(size_t i=p;i<s.size();i++){ int x=s[i]-63; for(int b=5;b>=0;b--) bits.push_back((x>>b)&1); }
    int v=0; size_t i=0; while(i+1+k<=bits.size()){ int b=bits[i++]; int x=0; for(int j=0;j<k;j++) x=(x<<1)|bits[i++]; if(b) v++; if(x>v){ v=x; } else if(v<n){ if(x<n && v<n){ g[x].push_back(v); g[v].push_back(x);} } }
  } else { int p=0; n=s[p++]-63; g.assign(n,{}); int val=0,k=6; for(int j=1;j<n;j++) for(int i=0;i<j;i++){ if(k==6){ val=s[p++]-63; k=0; } if((val>>(5-k))&1){ g[i].push_back(j); g[j].push_back(i);} k++; } }
  return true; }
const int INF=1e9;
int gammaT(){ // tree DP
  vector<int> par(n,-1), order; order.push_back(0); par[0]=0; for(size_t i=0;i<order.size();i++){ int v=order[i]; for(int w:g[v]) if(par[w]<0){ par[w]=v; order.push_back(w);} }
  vector<array<long,4>> st(n);
  for(int i=n-1;i>=0;i--){ int v=order[i]; long sumAll=0,sumCD=0,sumAC=0,sumC=0, bestIn=INF, bestA=INF; bool hasCh=false;
    for(int w:g[v]) if(w!=par[v] || (v==0 && false)) { if(v!=0 && w==par[v]) continue; hasCh=true; auto&c=st[w]; long all=min({c[0],c[1],c[2],c[3]}); sumAll+=all; bestIn=min(bestIn,min(c[0],c[1])-all); sumCD+=min(c[2],c[3]); long ac=min(c[0],c[2]); sumAC+=ac; bestA=min(bestA,c[0]-ac); sumC+=c[2]; }
    array<long,4> r; r[0]= hasCh? 1+sumAll+bestIn : INF; r[1]=1+sumCD; r[2]= hasCh? sumAC+bestA : INF; r[3]=sumC; for(auto&x:r) x=min(x,(long)INF); st[v]=r; }
  return min(st[0][0],st[0][2]); }
int main(){ string s; long cnt=0; map<string,long> fails; map<string,long> minsl; map<string,string> first;
  auto F=[&](const string&k,long lhs,long rhs){ long sl=lhs-rhs; if(!minsl.count(k)||sl<minsl[k]) minsl[k]=sl; if(sl<0){ if(fails[k]++==0) first[k]=s; } else fails[k]+=0; };
  while(getline(cin,s)){ if(s.empty()) continue; parse(s); if(n<3) continue; cnt++;
    vector<int> deg(n); for(int v=0;v<n;v++) deg[v]=g[v].size(); int D=*max_element(deg.begin(),deg.end());
    vector<vector<int>> dist(n, vector<int>(n,-1)); for(int v=0;v<n;v++){ deque<int> q{v}; dist[v][v]=0; while(!q.empty()){ int x=q.front(); q.pop_front(); for(int y:g[x]) if(dist[v][y]<0){ dist[v][y]=dist[v][x]+1; q.push_back(y);} } }
    vector<int> ecc(n), td(n); for(int v=0;v<n;v++){ ecc[v]=*max_element(dist[v].begin(),dist[v].end()); td[v]=accumulate(dist[v].begin(),dist[v].end(),0); }
    int rad=*min_element(ecc.begin(),ecc.end()), mtd=*min_element(td.begin(),td.end()); int C=0, Md=0; for(int v=0;v<n;v++){ C+=ecc[v]==rad; Md+=td[v]==mtd; }
    vector<char> sup(n,0), mx(n,0); for(int v=0;v<n;v++){ if(deg[v]==D) mx[v]=1; for(int w:g[v]) if(deg[w]==1) sup[v]=1; }
    int isoS=0, isoM=0; for(int v=0;v<n;v++){ if(sup[v]){ bool iso=true; for(int w:g[v]) if(sup[w]) iso=false; isoS+=iso; } if(mx[v]){ bool iso=true; for(int w:g[v]) if(mx[w]) iso=false; isoM+=iso; } }
    int gt=gammaT(); F("361",gt,isoS+C); F("376",gt,isoM+Md); }
  printf("trees=%ld\n",cnt); for(auto&[k,v]:minsl) printf("%-4s fails=%-8ld minslack=%ld %s\n",k.c_str(),fails[k],v,first[k].c_str()); }
