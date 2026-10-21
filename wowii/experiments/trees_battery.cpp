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
vector<vector<int>> D;
void apsp(){ D.assign(n, vector<int>(n,-1)); for(int s=0;s<n;s++){ deque<int> q{s}; D[s][s]=0; while(!q.empty()){ int v=q.front(); q.pop_front(); for(int w:g[v]) if(D[s][w]<0){ D[s][w]=D[s][v]+1; q.push_back(w);} } } }
int dset(int v,const vector<int>&S){ int m=INF; for(int s:S) m=min(m,D[v][s]); return m; }
double distAvgPairs(const vector<int>&S){ if(S.size()<2) return 0; double t=0; long c=0; for(int a:S) for(int b:S) if(a!=b){ t+=D[a][b]; c++; } return t/c; }
double distAvgToSet(const vector<int>&S){ if(S.empty()) return 0; double t=0; for(int v=0;v<n;v++) t+=dset(v,S); return t/n; }
double distAvgSV(const vector<int>&S){ double t=0; long c=0; for(int s:S) for(int v=0;v<n;v++) if(v!=s){ t+=D[s][v]; c++; } return c? t/c:0; }
int eccSet(const vector<int>&S){ if(S.empty()) return 0; int m=0; for(int v=0;v<n;v++) m=max(m,dset(v,S)); return m; }
int eccMaxMember(const vector<int>&S){ int m=0; for(int s:S) for(int v=0;v<n;v++) m=max(m,D[s][v]); return m; }
int ncomp(const vector<int>&S, bool isoOnly){ vector<char> in(n,0); for(int s:S) in[s]=1; vector<char> vis(n,0); int c=0,iso=0; for(int s:S) if(!vis[s]){ c++; int sz=0; vector<int> st{s}; vis[s]=1; while(!st.empty()){ int v=st.back(); st.pop_back(); sz++; for(int w:g[v]) if(in[w]&&!vis[w]){ vis[w]=1; st.push_back(w);} } if(sz==1) iso++; } return isoOnly? iso:c; }
int annih(const vector<int>& deg){ vector<int> d=deg; sort(d.begin(),d.end()); long m=0; for(int x:d) m+=x; m/=2; long s=0; int k=0; for(int x:d){ if(s+x<=m){ s+=x; k++; } else break; } return k; }
struct Res{ long fails=0; double minsl=1e18; string ex; int firstn=0; };
map<string,Res> R;
void rec(const string& name,double lhs,double rhs,const string& g6){ Res& r=R[name]; double sl=lhs-rhs; if(sl<r.minsl){ r.minsl=sl; if(sl<-1e-9) {} } if(sl<-1e-9){ if(r.fails==0){ r.ex=g6; r.firstn=n;} r.fails++; } }
int main(){ string s;
  while(getline(cin,s)){ if(s.empty()) continue; parse(s); if(n<3) continue; root(); apsp(); double gt=gammaT();
    vector<int> deg(n); for(int v=0;v<n;v++) deg[v]=g[v].size();
    vector<int> ecc(n); int rad=INF,diam=0; for(int v=0;v<n;v++){ ecc[v]=*max_element(D[v].begin(),D[v].end()); rad=min(rad,ecc[v]); diam=max(diam,ecc[v]); }
    vector<int> C,B,M,L,Sup,D2,Dev,ND2c; int Delta=*max_element(deg.begin(),deg.end());
    for(int v=0;v<n;v++){ if(ecc[v]==rad) C.push_back(v); if(ecc[v]==diam) B.push_back(v); if(deg[v]==Delta) M.push_back(v); if(deg[v]==1) L.push_back(v); if(deg[v]==2) D2.push_back(v); if(deg[v]%2==0) Dev.push_back(v); }
    for(int v=0;v<n;v++){ bool sp=false; for(int w:g[v]) if(deg[w]==1) sp=true; if(sp) Sup.push_back(v); }
    for(int v=0;v<n;v++){ bool in=deg[v]==2; for(int w:g[v]) if(deg[w]==2) in=true; if(in) ND2c.push_back(v); }
    vector<int> SL=Sup; for(int l:L) SL.push_back(l); sort(SL.begin(),SL.end()); SL.erase(unique(SL.begin(),SL.end()),SL.end());
    double eccavg=0; for(int v=0;v<n;v++) eccavg+=ecc[v]; eccavg/=n;
    vector<int> sd=deg; sort(sd.begin(),sd.end()); double lowmed=sd[(n-1)/2], upmed=sd[n/2], med=(lowmed+upmed)/2;
    int compND2=ncomp(ND2c,false);
    // 241
    rec("241", gt, floor(compND2+distAvgPairs(C)+1e-9), s);
    rec("241_toSet", gt, floor(compND2+distAvgToSet(C)+1e-9), s);
    rec("241_SV", gt, floor(compND2+distAvgSV(C)+1e-9), s);
    rec("242", gt, 0.5*(compND2+eccavg), s);
    // 356
    rec("356_pairs", gt, C.size()*distAvgPairs(L), s);
    rec("356_toSet", gt, C.size()*distAvgToSet(L), s);
    rec("356_SV", gt, C.size()*distAvgSV(L), s);
    // 358/359: ecc(C)
    int isoS=ncomp(Sup,true), compSL=ncomp(SL,false);
    for(int r=0;r<2;r++){ double e = r==0? eccSet(C): eccMaxMember(C); string t= r==0? "_eccSet":"_eccMember";
      rec("358"+t, gt, 0.5*e+isoS, s); rec("359"+t, gt, 0.5*e+compSL, s);
      double eb = r==0? eccSet(B): eccMaxMember(B);
      rec("375"+t, gt, eb+lowmed, s);
      double ec=e; rec("380"+t, gt*(ec-1>0?ec-1:1), ec-1>0? (double)Dev.size(): -1e9, s);
      if(ec-1<=0) rec("380"+t+"_ecc1", 1, 0, s);
    }
    rec("374_pairs", gt, distAvgPairs(B)+med, s); rec("374_toSet", gt, distAvgToSet(B)+med, s); rec("374_SV", gt, distAvgSV(B)+med, s);
    rec("377", gt, ncomp(M,true)+upmed, s);
    rec("378_pairs", gt, ncomp(M,false)+distAvgPairs(D2), s); rec("378_toSet", gt, ncomp(M,false)+distAvgToSet(D2), s); rec("378_SV", gt, ncomp(M,false)+distAvgSV(D2), s);
    // 341-344 annihilation readings
    int A=annih(deg); vector<int> cdeg(n); for(int v=0;v<n;v++) cdeg[v]=n-1-deg[v]; int Ab=annih(cdeg);
    int sigma=sd[1];
    rec("341", ceil(A/2.0)*sigma, gt, s);
    rec("342", Ab+ceil(ncomp(Sup,true)/2.0), gt, s);
    if(!D2.empty()) rec("343", Ab+ceil(ncomp(D2,false)/2.0), gt, s);
    vector<int> NL=L; for(int v:Sup) NL.push_back(v); sort(NL.begin(),NL.end()); NL.erase(unique(NL.begin(),NL.end()),NL.end());
    rec("344", Ab-1+ncomp(NL,false), gt, s);
  }
  for(auto&[k,r]:R) printf("%-22s fails=%-8ld minslack=%-8.3f firstfail_n=%d ex=%s\n",k.c_str(),r.fails,r.minsl,r.firstn,r.ex.c_str());
}
