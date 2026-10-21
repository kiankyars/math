#include <bits/stdc++.h>
using namespace std; typedef unsigned M; int n; M adj[32]; M ALL; mt19937_64 rng(1); string which;
inline int pc(M x){ return __builtin_popcount(x); }
M openN(M S){ M r=0; for(M t=S;t;t&=t-1) r|=adj[__builtin_ctz(t)]; return r; }
M closedN(M S){ return S|openN(S); }
bool connM(M m){ if(!m) return true; M seen=m&(-m),fr=seen; while(fr){ M nf=openN(fr)&m&~seen; seen|=nf; fr=nf; } return seen==m; }
int matchA(const M* A, M m){ if(!m) return 0; int v=__builtin_ctz(m); M rest=m&~(1u<<v); int best=matchA(A,rest); for(M t=A[v]&rest;t;t&=t-1){ int w=__builtin_ctz(t); best=max(best,1+matchA(A,rest&~(1u<<w))); if(best*2>=pc(m)) break; } return best; }
int residueOf(vector<int> d){ sort(d.rbegin(),d.rend()); while(!d.empty()&&d[0]>0){ int x=d[0]; d.erase(d.begin()); for(int i=0;i<x&&i<(int)d.size();i++) d[i]--; sort(d.rbegin(),d.rend()); } return d.size(); }
// returns number of distinct minimal TDS sizes (>1 means not WTD)
int wtdSizes(){ set<int> sz; for(M S=1;S<=ALL;S++){ if(openN(S)==ALL){ bool minimal=true; for(M t=S;t;t&=t-1){ M S2=S&~(t&-t); if(openN(S2)==ALL){minimal=false;break;} } if(minimal) sz.insert(pc(S)); } if(S==ALL) break; } return sz.size(); }
double score(){ if(!connM(ALL)) return -1e9; M cadj[32]; for(int v=0;v<n;v++) cadj[v]=ALL&~adj[v]&~(1u<<v);
  vector<int> deg(n); for(int v=0;v<n;v++) deg[v]=pc(adj[v]);
  double slack; // hypothesis slack: >=0 means hypothesis holds
  if(which=="328"){ vector<int> k4(n); for(int v=0;v<n;v++){ int c=0; M N=adj[v]; for(M t=N;t;t&=t-1){ int a=__builtin_ctz(t); for(M u=N&adj[a]&~((2u<<a)-1);u;u&=u-1){ int b=__builtin_ctz(u); c+=pc(N&adj[a]&adj[b]&~((2u<<b)-1)); } } k4[v]=c; } int km=*max_element(k4.begin(),k4.end()); int f=0; for(int v=0;v<n;v++) if(k4[v]==km) f++; slack=f-4.0*matchA(cadj,ALL); }
  else { int mx=-1,mn=99; for(int u=0;u<n;u++) for(int v=u+1;v<n;v++) if(!(adj[u]>>v&1)){ int x=pc(cadj[u]|cadj[v]); mx=max(mx,x); mn=min(mn,x);} if(mx<0) return -1e9;
    if(which=="324") slack=1+residueOf(deg)-mx;
    else { M S=0; for(int v=0;v<n;v++) if(deg[v]==2) S|=1u<<v; M NS=closedN(S); int comp=0; M left=NS; while(left){ M c=left&(-left),fr=c; while(fr){ M nf=openN(fr)&NS&~c; c|=nf; fr=nf; } left&=~c; comp++; } slack=1+comp-mn; } }
  if(slack<0) return slack-1;
  return wtdSizes()>1 ? 1 : -0.5; }
int main(int argc,char**argv){ which=argv[1]; n=atoi(argv[2]); long iters=atol(argv[3]); rng.seed(atoi(argv[4])); double p=atof(argv[5]); ALL=(1u<<n)-1;
  for(int v=0;v<n;v++) adj[v]=0; for(int i=1;i<n;i++){ int j=rng()%i; adj[i]|=1u<<j; adj[j]|=1u<<i; } for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if((rng()%1000)/1000.0<p){ adj[i]|=1u<<j; adj[j]|=1u<<i; }
  double cur=score(),best=cur; M bestA[32]; memcpy(bestA,adj,sizeof adj); double T=1.0;
  for(long it=0;it<iters;it++){ int i=rng()%n,j=rng()%n; if(i==j) continue; adj[i]^=1u<<j; adj[j]^=1u<<i; double s=score();
    if(s>=cur || exp((s-cur)/T)>(rng()%1000000)/1e6){ cur=s; if(s>best){best=s; memcpy(bestA,adj,sizeof adj);} } else { adj[i]^=1u<<j; adj[j]^=1u<<i; } T=max(0.05,T*0.999); }
  memcpy(adj,bestA,sizeof adj); printf("%s n=%d best=%.3f edges:",which.c_str(),n,best); for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if(adj[i]>>j&1) printf(" %d-%d",i,j); printf("\n"); }
