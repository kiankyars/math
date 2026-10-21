#include <bits/stdc++.h>
using namespace std; typedef unsigned M; int n; M adj[32]; M ALL; mt19937_64 rng(1); string which;
inline int pc(M x){ return __builtin_popcount(x); }
M openN(M S){ M r=0; for(M t=S;t;t&=t-1) r|=adj[__builtin_ctz(t)]; return r; }
bool connM(M m){ if(!m) return true; M seen=m&(-m),fr=seen; while(fr){ M nf=openN(fr)&m&~seen; seen|=nf; fr=nf; } return seen==m; }
int edgesIn(M m){ int e=0; for(M t=m;t;t&=t-1) e+=pc(adj[__builtin_ctz(t)]&m); return e/2; }
int bestA2; void recA2(M S, M C){ int s=pc(S); if(s>bestA2) bestA2=s; if(s+pc(C)<=bestA2||!C) return; int v=__builtin_ctz(C); M C2=C&~(1u<<v); M S2=S|(1u<<v); M full=0; for(M t=S2;t;t&=t-1){ int x=__builtin_ctz(t); if(adj[x]&S2) full|=1u<<x; } M nc=0; for(M t=C2;t;t&=t-1){ int w=__builtin_ctz(t); M nw=adj[w]&S2; if(pc(nw)>=2||(nw&full)) continue; nc|=1u<<w; } recA2(S2,nc); recA2(S,C2); }
int alpha2(){ bestA2=0; recA2(0,ALL); return bestA2; }
// path cover number of G[X] via DP over subsets of X (X small)
int pathCoverIn(M X){ if(!X) return 0; vector<int> idx; for(M t=X;t;t&=t-1) idx.push_back(__builtin_ctz(t)); int k=idx.size(); int N=1<<k; vector<M> endset(N,0); vector<M> ladj(k,0); for(int i=0;i<k;i++) for(int j=0;j<k;j++) if(adj[idx[i]]>>idx[j]&1) ladj[i]|=1u<<j;
  for(int i=0;i<k;i++) endset[1<<i]=1u<<i; for(int m=1;m<N;m++){ if(!endset[m]) continue; for(M t=endset[m];t;t&=t-1){ int v=__builtin_ctz(t); for(M u=ladj[v]&~m;u;u&=u-1){ int w=__builtin_ctz(u); endset[m|(1<<w)]|=1u<<w; } } }
  vector<int> cover(N,99); cover[0]=0; for(int m=1;m<N;m++){ int low=m&-m; for(int sub=m;sub;sub=(sub-1)&m){ if(!(sub&low)) continue; if(endset[sub] && cover[m^sub]+1<cover[m]) cover[m]=cover[m^sub]+1; } } return cover[N-1]; }
// longest induced path (vertex count)
int bestP; void recP(M S, int last, M forb){ int s=pc(S); if(s>bestP) bestP=s; M cand=adj[last]&~S&~forb; for(M t=cand;t;t&=t-1){ int w=__builtin_ctz(t); // w adjacent only to last in S
    if((adj[w]&S)!=(1u<<last)) continue; recP(S|(1u<<w), w, forb); } }
int indPath(){ bestP=1; for(int v=0;v<n;v++) recP(1u<<v,v,0); return bestP; }
double score(){ if(!connM(ALL)) return -1e9; vector<int> deg(n); for(int v=0;v<n;v++) deg[v]=pc(adj[v]); int delta=*min_element(deg.begin(),deg.end());
  M A=0,A2=0,H3=0,P=0,Hh=0; for(int v=0;v<n;v++){ if(deg[v]==delta) A|=1u<<v; if(deg[v]==2) A2|=1u<<v; if(deg[v]>=3) H3|=1u<<v; if(deg[v]==1) P|=1u<<v; if(2*deg[v]>n) Hh|=1u<<v; }
  M S=openN(P);
  if(which=="446") return alpha2()-(pathCoverIn(openN(A))+pc(ALL&~S));
  if(which=="450") return alpha2()-(pathCoverIn(openN(A2))+pc(ALL&~S)+pathCoverIn(ALL&~H3));
  if(which=="448a_ip") return alpha2()-(pc(Hh)+edgesIn(ALL&~Hh)+indPath());
  if(which=="448b_ip") return alpha2()-(pc(ALL&~A)+edgesIn(openN(S))+indPath());
  if(which=="448a_pc") return alpha2()-(pc(Hh)+edgesIn(ALL&~Hh)+pathCoverIn(ALL));
  if(which=="448b_pc") return alpha2()-(pc(ALL&~A)+edgesIn(openN(S))+pathCoverIn(ALL));
  return 0; }
void parse(const string& s){ int p=0; n=s[p++]-63; for(int i=0;i<n;i++) adj[i]=0; int val=0,k=6; for(int j=1;j<n;j++) for(int i=0;i<j;i++){ if(k==6){ val=s[p++]-63; k=0;} if(val>>(5-k)&1){ adj[i]|=1u<<j; adj[j]|=1u<<i;} k++; } }
int main(int argc,char**argv){ which=argv[1]; n=atoi(argv[2]); long iters=atol(argv[3]); rng.seed(atoi(argv[4])); double p=atof(argv[5]); ALL=(1u<<n)-1;
  if(iters==0){ string s; long cnt=0,tot=0; double mx=-1e9; while(getline(cin,s)){ parse(s); ALL=(1u<<n)-1; double sc=score(); tot++; mx=max(mx,sc); if(sc>1e-9){ cnt++; if(cnt<=3) printf("CE %s %s %.1f\n",which.c_str(),s.c_str(),sc);} } printf("%s n=%d tot=%ld ce=%ld max=%.1f\n",which.c_str(),n,tot,cnt,mx); return 0; }
  for(int v=0;v<n;v++) adj[v]=0; for(int i=1;i<n;i++){ int j=rng()%i; adj[i]|=1u<<j; adj[j]|=1u<<i; } for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if((rng()%1000)/1000.0<p){ adj[i]|=1u<<j; adj[j]|=1u<<i; }
  double cur=score(),best=cur; M bestA[32]; memcpy(bestA,adj,sizeof adj); double T=1.0;
  for(long it=0;it<iters;it++){ int i=rng()%n,j=rng()%n; if(i==j) continue; adj[i]^=1u<<j; adj[j]^=1u<<i; double s=score();
    if(s>=cur || exp((s-cur)/T)>(rng()%1000000)/1e6){ cur=s; if(s>best){best=s; memcpy(bestA,adj,sizeof adj);} } else { adj[i]^=1u<<j; adj[j]^=1u<<i; } T=max(0.05,T*0.9995); }
  memcpy(adj,bestA,sizeof adj); printf("%s n=%d best=%.1f edges:",which.c_str(),n,best); for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if(adj[i]>>j&1) printf(" %d-%d",i,j); printf("\n"); }
