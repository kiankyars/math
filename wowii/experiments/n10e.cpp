// Exhaustive battery, part 5: 171, 427 (C the centre, and C = M), 432a (absolute reading) and 432b (graph6 on stdin, n <= 12).
#include <bits/stdc++.h>
using namespace std;
typedef unsigned M;
int n; M adj[16], ALL;
static inline int pc(M x){ return __builtin_popcount(x); }
void parse(const string& s){ int p=0; n=s[p++]-63; for(int i=0;i<n;i++) adj[i]=0; int val=0,k=6;
  for(int j=1;j<n;j++) for(int i=0;i<j;i++){ if(k==6){ val=s[p++]-63; k=0; } if((val>>(5-k))&1){ adj[i]|=1u<<j; adj[j]|=1u<<i; } k++; }
  ALL=(1u<<n)-1; }
static inline M openN(M S){ M r=0; for(M t=S;t;t&=t-1) r|=adj[__builtin_ctz(t)]; return r; }
bool connM(M m){ if(!m) return true; M seen=m&(-m),fr=seen; while(fr){ M nf=openN(fr)&m&~seen; seen|=nf; fr=nf; } return seen==m; }
int edgesIn(M m){ int e=0; for(M t=m;t;t&=t-1) e+=pc(adj[__builtin_ctz(t)]&m); return e/2; }
bool isBip(){ int col[16]; for(int i=0;i<n;i++) col[i]=-1; for(int s=0;s<n;s++){ if(col[s]>=0) continue; col[s]=0; deque<int> q{s}; while(!q.empty()){ int x=q.front(); q.pop_front(); for(M t=adj[x];t;t&=t-1){ int y=__builtin_ctz(t); if(col[y]<0){ col[y]=1-col[x]; q.push_back(y);} else if(col[y]==col[x]) return false; } } } return true; }
int main(){ string s; map<string,long> fails; map<string,double> minsl; map<string,string> first; long cnt=0;
  auto F=[&](const string& k,double lhs,double rhs){ double sl=lhs-rhs; if(!minsl.count(k)||sl<minsl[k]) minsl[k]=sl; if(sl<-1e-9){ if(fails[k]++==0) first[k]=s; } else fails[k]+=0; };
  while(getline(cin,s)){ if(s.empty()) continue; parse(s); if(n<4) continue; cnt++;
    int D[16][16], ecc[16];
    for(int v=0;v<n;v++){ for(int w=0;w<n;w++) D[v][w]=99; D[v][v]=0; M seen=1u<<v,fr=seen; int d=0; while(fr){ M nf=openN(fr)&~seen; d++; for(M t=nf;t;t&=t-1) D[v][__builtin_ctz(t)]=d; seen|=nf; fr=nf; } ecc[v]=0; for(int w=0;w<n;w++) ecc[v]=max(ecc[v],D[v][w]); }
    int rad=99; for(int v=0;v<n;v++) rad=min(rad,ecc[v]);
    vector<int> deg(n); int m=0; for(int v=0;v<n;v++){ deg[v]=pc(adj[v]); m+=deg[v]; } m/=2;
    vector<int> sd=deg; sort(sd.begin(),sd.end());
    int idom=n, gc=n;
    for(M S=1;S<=ALL;S++){ int c=pc(S); M on=openN(S);
      if(c<idom && ((on|S)==ALL) && !(on&S)) idom=c;
      if(c<gc && ((on|S)==ALL) && connM(S)) gc=c;
      if(S==ALL) break; }
    int Ls=n-gc;
    int mind=99, demax=0; for(int v=0;v<n;v++){ int e=0,o=0; for(int w=0;w<n;w++){ if(D[v][w]%2==0) e++; else o++; } mind=min(mind,abs(e-o)); demax=max(demax,e); }
    int a=0,sm=0; for(int i=0;i<n;i++){ sm+=sd[i]; if(sm<=m) a=i+1; else break; }
    M P=0, C=0; for(int v=0;v<n;v++){ if(deg[v]==1) P|=1u<<v; if(ecc[v]==rad) C|=1u<<v; }
    M NP=openN(P);
    F("432a abs", a+mind, idom);
    F("432b", n-pc(NP)+(isBip()?mind:0), idom);
    { int cut=0; for(M t=C;t;t&=t-1) cut+=pc(adj[__builtin_ctz(t)]&~C); F("427", cut+(2*edgesIn(ALL&~NP))/3, idom);
      int Dl=0; for(int v=0;v<n;v++) Dl=max(Dl,deg[v]); M Mx=0; for(int v=0;v<n;v++) if(deg[v]==Dl) Mx|=1u<<v;
      int cut2=0; for(M t=Mx;t;t&=t-1) cut2+=pc(adj[__builtin_ctz(t)]&~Mx); F("427 M", cut2+(2*edgesIn(ALL&~NP))/3, idom); }
    // 171: B = boundary vertices; dist_avg(B) = mean distance over pairs of distinct boundary vertices
    { M B=0; for(int v=0;v<n;v++){ bool isb=false; for(int u=0;u<n&&!isb;u++){ if(u==v) continue; bool ok=true; for(M t=adj[v];t;t&=t-1) if(D[u][__builtin_ctz(t)]>D[u][v]) ok=false; if(ok) isb=true; } if(isb) B|=1u<<v; }
      double sum=0,c=0; for(int x=0;x<n;x++) if(B>>x&1) for(int y=x+1;y<n;y++) if(B>>y&1){ sum+=D[x][y]; c++; }
      if(c>0) F("171", Ls, (demax-1)/(sum/c)); }
  }
  printf("graphs=%ld\n",cnt); for(auto&[k,v]:minsl) printf("%-9s fails=%-8ld minslack=%.3f %s\n",k.c_str(),fails[k],v,first[k].c_str()); }
