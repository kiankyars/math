#include <bits/stdc++.h>
using namespace std;
int n; vector<vector<int>> g;
void parse(const string& s){ int p=0; n=s[p++]-63; if(n==63){ n=0; for(int k=0;k<3;k++) n=n*64+(s[p++]-63);} g.assign(n,{}); int val=0,k=6;
  for(int j=1;j<n;j++) for(int i=0;i<j;i++){ if(k==6){ val=s[p++]-63; k=0; } int b=(val>>(5-k))&1; k++; if(b){ g[i].push_back(j); g[j].push_back(i);} } }
const int INF=1e9; vector<int> order,par;
void root(){ order.clear(); par.assign(n,-1); vector<int> st{0}; vector<bool> vis(n,false); vis[0]=true; while(!st.empty()){ int v=st.back(); st.pop_back(); order.push_back(v); for(int w:g[v]) if(!vis[w]){ vis[w]=true; par[w]=v; st.push_back(w);} } }
int gammaT(){ // states: v in S & has S-child / v in S & no S-child yet (needs parent in S) / v not in S & dominated by child / v not in S & not dominated (needs parent in S)
  vector<array<int,4>> dp(n); for(int i=n-1;i>=0;i--){ int v=order[i];
    // A: in S, dominated by child; B: in S, not yet dominated; C: not in S, dominated; D: not in S, not dominated
    long sumIn=0; int bestGainIn=INF; // children if v in S: child may be (A),(C) or (B? child in S not dominated -> dominated by v ok), (D-> dominated by v ok)
    long sumOut=0; int bestGainOut=INF; bool anyChild=false;
    for(int w:g[v]) if(w!=par[v]){ anyChild=true;
      int inS=min(dp[w][0],dp[w][1]); int any=min({dp[w][0],dp[w][1],dp[w][2],dp[w][3]});
      // v in S: child arbitrary state; v gets dominated if some child in S
      sumIn+=any; bestGainIn=min(bestGainIn, inS-any);
      // v not in S: child must be dominated already (A or C) since v not in S cannot dominate it
      int okc=min(dp[w][0],dp[w][2]); int okcIn=dp[w][0];
      sumOut+=okc; bestGainOut=min(bestGainOut, okcIn-okc); }
    dp[v][0]= anyChild? (int)min((long)INF,1+sumIn+bestGainIn):INF; // in S with S-child
    dp[v][1]= (int)min((long)INF,1+sumIn); // in S, possibly no S child (counts as needing parent) - pessimistic ok
    dp[v][2]= anyChild? (int)min((long)INF,sumOut+bestGainOut):INF;
    dp[v][3]= (int)min((long)INF,sumOut); }
  return min(dp[0][0],dp[0][2]); }
int vcover(){ vector<array<int,2>> dp(n); for(int i=n-1;i>=0;i--){ int v=order[i]; dp[v][1]=1; dp[v][0]=0; for(int w:g[v]) if(w!=par[v]){ dp[v][1]+=min(dp[w][0],dp[w][1]); dp[v][0]+=dp[w][1]; } } return min(dp[0][0],dp[0][1]); }
int pathcover(){ // greedy: number of paths = n - max path-forest edges; max edges in a subforest with max degree 2 (linear forest) via DP
  vector<array<int,3>> dp(n); // dp[v][d] = max edges in subtree with v having d chosen child-edges (d<=2)
  for(int i=n-1;i>=0;i--){ int v=order[i]; int b0=0; int g1=-INF,g2=-INF; for(int w:g[v]) if(w!=par[v]){ int f=max({dp[w][0],dp[w][1],dp[w][2]}); int e=max(dp[w][0],dp[w][1])+1; b0+=f; int gain=e-f; if(gain>g1){ g2=g1; g1=gain; } else if(gain>g2) g2=gain; }
    dp[v][0]=b0; dp[v][1]= g1>-INF? b0+g1 : -INF; dp[v][2]= g2>-INF? b0+g1+g2 : -INF; }
  int e=max({dp[0][0],dp[0][1],dp[0][2]}); return n-e; }
int main(){ string s; map<int,int> mx; map<int,int> mxp; map<int,int> minHalf;
  while(getline(cin,s)){ if(s.empty()) continue; parse(s); root(); int gt=gammaT(), vc=vcover(), p=pathcover(); int l=0; for(int v=0;v<n;v++) if(g[v].size()==1) l++;
    if(!mx.count(l)) mx[l]=-99; mx[l]=max(mx[l],vc-gt); if(!mxp.count(p)) mxp[p]=-99; mxp[p]=max(mxp[p],vc-gt);
    int d=gt-n/2; if(!minHalf.count(l)) minHalf[l]=99; minHalf[l]=min(minHalf[l],d); }
  for(auto [l,v]:mx) printf("leaves=%d max(vc-gt)=%d   min(gt-floor(n/2))=%d\n",l,v,minHalf[l]);
  for(auto [p,v]:mxp) printf("pcover=%d max(vc-gt)=%d\n",p,v); }
