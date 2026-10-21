#include <bits/stdc++.h>
using namespace std; typedef unsigned M; int n; M adj[32]; M ALL; mt19937_64 rng(1); string which;
inline int pc(M x){ return __builtin_popcount(x); }
M openN(M S){ M r=0; for(M t=S;t;t&=t-1) r|=adj[__builtin_ctz(t)]; return r; }
M closedN(M S){ return S|openN(S); }
bool connM(M m){ if(!m) return true; M seen=m&(-m),fr=seen; while(fr){ M nf=openN(fr)&m&~seen; seen|=nf; fr=nf; } return seen==m; }
int edgesIn(M m){ int e=0; for(M t=m;t;t&=t-1) e+=pc(adj[__builtin_ctz(t)]&m); return e/2; }
int alphaM(M m){ if(!m) return 0; int v=__builtin_ctz(m); M rest=m&~(1u<<v); int a=alphaM(rest&~adj[v])+1; if(!(adj[v]&rest)) return a; return max(a,alphaM(rest)); }
#include "fastinv.h"
int bestT; void recT(M S, M X){ if(pc(S)>=bestT) return; int w=-1; for(int v=0;v<n;v++) if(!(adj[v]&S)){ w=v; break; } if(w<0){ bestT=pc(S); return; }
  M cand=adj[w]&~S&~X; M X2=X; for(M t=cand;t;t&=t-1){ int u=__builtin_ctz(t); recT(S|(1u<<u),X2); X2|=1u<<u; } }
int gammat(){ bestT=n+1; recT(0,0); return bestT; }
bool isForest(M m){ int e=edgesIn(m); int comp=0; M left=m; while(left){ M c=left&(-left),fr=c; while(fr){ M nf=openN(fr)&m&~c; c|=nf; fr=nf; } left&=~c; comp++; } return e==pc(m)-comp; }
bool isBip(M m){ M left=m; while(left){ M c0=left&(-left),c1=0,fr0=c0,fr1=0; while(fr0||fr1){ M n1=openN(fr0)&m, n0=openN(fr1)&m; if((n1&c0)||(n0&c1)) return false; n1&=~c1; n0&=~c0; c1|=n1; c0|=n0; fr0=n0; fr1=n1; } left&=~(c0|c1);} return true; }
double score(){ if(!connM(ALL)) return -1e9;
  int D[32][32]; for(int v=0;v<n;v++){ for(int w=0;w<n;w++) D[v][w]=99; D[v][v]=0; M seen=1u<<v,fr=seen; int d=0; while(fr){ M nf=openN(fr)&~seen; d++; for(M t=nf;t;t&=t-1) D[v][__builtin_ctz(t)]=d; seen|=nf; fr=nf; } }
  vector<int> deg(n),ecc(n); for(int v=0;v<n;v++){ deg[v]=pc(adj[v]); ecc[v]=0; for(int w=0;w<n;w++) ecc[v]=max(ecc[v],D[v][w]); }
  int rad=*min_element(ecc.begin(),ecc.end()); int delta=*min_element(deg.begin(),deg.end()), Delta=*max_element(deg.begin(),deg.end());
  M Mx=0; for(int v=0;v<n;v++) if(deg[v]==Delta) Mx|=1u<<v;
  vector<int> lam(n); auto lamC=[&](){ for(int v=0;v<n;v++) lam[v]=alphaM(adj[v]); };
  int maxDE=0; for(int v=0;v<n;v++){ int c=0; for(int w=0;w<n;w++) if(D[v][w]%2==0) c++; maxDE=max(maxDE,c); }
  // G^2
  vector<int> d2(n),ecc2(n); double s2=0; for(int v=0;v<n;v++){ int c=0; ecc2[v]=0; for(int w=0;w<n;w++){ if(w!=v&&D[v][w]<=2) c++; int dd=(D[v][w]+1)/2; ecc2[v]=max(ecc2[v],dd); s2+=dd; } d2[v]=c; }
  int D2=*max_element(d2.begin(),d2.end()), rad2=*min_element(ecc2.begin(),ecc2.end()); double avg2=s2/(n*(n-1.0));
  if(which=="chk"){ int b=1,tr=1,gc=n; for(M S=1;S<=ALL;S++){ int c=pc(S); if(c>b&&isBip(S)) b=c; if(c>tr&&connM(S)&&edgesIn(S)==c-1) tr=c; if(c<gc&&closedN(S)==ALL&&connM(S)) gc=c; if(S==ALL) break; } return abs(b-bipB())+abs(tr-treeN())+abs(gc-gammaC()); }
  if(which.substr(0,3)=="182"||which.substr(0,3)=="184"||which.substr(0,3)=="186"){
    int D2m[32][32]; for(int u=0;u<n;u++) for(int v=0;v<n;v++) D2m[u][v]=(D[u][v]+1)/2;
    M A2[32]; for(int v=0;v<n;v++){ A2[v]=0; for(int w=0;w<n;w++) if(w!=v&&D[v][w]<=2) A2[v]|=1u<<w; }
    int dm2=*max_element(ecc2.begin(),ecc2.end()); M B2=0,C2=0; for(int v=0;v<n;v++){ if(ecc2[v]==dm2) B2|=1u<<v; if(ecc2[v]==rad2) C2|=1u<<v; }
    int diam=*max_element(ecc.begin(),ecc.end());
    double rhs=0;
    if(which=="182a"){ int mx=0; for(M t=B2;t;t&=t-1) mx=max(mx,pc(A2[__builtin_ctz(t)])); rhs=mx+diam; }
    if(which=="182b"){ int mx=0; for(M t=B2;t;t&=t-1) mx=max(mx,pc(A2[__builtin_ctz(t)]&B2)); rhs=mx+diam; }
    if(which=="184a"){ double s=0; int c=0; for(M t=B2;t;t&=t-1){ int b=__builtin_ctz(t); for(int v=0;v<n;v++){ s+=D2m[b][v]; c++; } } rhs=D2+2*s/c; }
    if(which=="184b"){ double s=0; for(int v=0;v<n;v++){ int mn=99; for(M t=B2;t;t&=t-1) mn=min(mn,D2m[v][__builtin_ctz(t)]); s+=mn; } rhs=D2+2*s/n; }
    if(which=="184c"){ double s=0; int c=0; for(M t=B2;t;t&=t-1){ int b=__builtin_ctz(t); for(int v=0;v<n;v++) if(v!=b){ s+=D2m[b][v]; c++; } } rhs=D2+2*s/c; }
    int eC=0; for(int v=0;v<n;v++){ int mn=99; for(M t=C2;t;t&=t-1) mn=min(mn,D2m[v][__builtin_ctz(t)]); eC=max(eC,mn); }
    M NC2=0; for(M t=C2;t;t&=t-1) NC2|=A2[__builtin_ctz(t)];
    if(which=="186a") rhs=pc(NC2)+2*eC;
    if(which=="186b") rhs=pc(openN(C2))+2*eC;
    if(which=="186c") rhs=pc(NC2&~C2)+2*eC;
    return rhs-(Ls()+bipB()); }
  if(which=="258") return 2.0*maxDE/Ls()-gammat();
  if(which=="259") return 2.0*pc(openN(Mx)&~Mx)/Ls()-gammat();
  if(which=="260"){ int dm=*max_element(ecc.begin(),ecc.end()); M B=0; for(int v=0;v<n;v++) if(ecc[v]==dm) B|=1u<<v; return 2.0*pc(openN(B)&~B)/Ls()-gammat(); }
  if(which=="261"){ M S=0; for(int v=0;v<n;v++) if(deg[v]==2) S|=1u<<v; return 2.0*pc(openN(S)&~S)/Ls()-gammat(); }
  if(which=="72"){ lamC(); double ea=0; for(int v=0;v<n;v++) ea+=ecc[v]; ea/=n; int lm=*max_element(lam.begin(),lam.end()); return ceil(ea+lm/3.0-1e-9)-treeN(); }
  if(which=="76"){ vector<int> tri(n); for(int v=0;v<n;v++) tri[v]=edgesIn(adj[v]); int tm=*max_element(tri.begin(),tri.end()); int f=0; for(int v=0;v<n;v++) if(tri[v]==tm) f++; int m=edgesIn(ALL); int fd=(2*m)/n; return (double)f/fd-treeN(); }
  if(which=="84") return 2.0*rad/delta-treeN();
  if(which=="108"){ int al=alphaM(ALL); int core=0; for(int v=0;v<n;v++) if(alphaM(ALL&~(1u<<v))<al) core++; return al-(maxDE+2*(core/3)); }
  if(which=="111"){ lamC(); double la=0; for(int v=0;v<n;v++) la+=lam[v]; la/=n; int cmax=0; for(int v=0;v<n;v++) cmax=max(cmax,n-1-deg[v]); if(cmax==0) return -1e9; M S=0; for(int v=0;v<n;v++) if(n-1-deg[v]==cmax) S|=1u<<v; M NS=0; for(M t=S;t;t&=t-1){ int v=__builtin_ctz(t); NS|=ALL&~adj[v]&~(1u<<v); } return alphaM(ALL)-ceil(1+pc(NS)*(la-1)-1e-9); }
  if(which=="165"){ int k=pc(openN(Mx)&~Mx); return ceil(sqrt(2.0*k)-1e-9)-Ls(); }
  if(which=="166"){ int k=pc(openN(Mx)&~Mx); return k/sqrt((double)rad)-Ls(); }
  if(which=="174"){ lamC(); int lm=*max_element(lam.begin(),lam.end()); return (n+lm-1)-(Ls()+bipB()); }
  if(which=="180"){ return (1+alphaM(ALL)+maxDE)-(Ls()+bipB()); }
  if(which=="183"){ return (D2+2*rad2)-(Ls()+bipB()); }
  if(which=="185"){ return (D2+2*avg2)-(Ls()+bipB()); }
  return 0; }
void parse(const string& s){ int p=0; n=s[p++]-63; for(int i=0;i<n;i++) adj[i]=0; int val=0,k=6;
  for(int j=1;j<n;j++) for(int i=0;i<j;i++){ if(k==6){ val=s[p++]-63; k=0;} if(val>>(5-k)&1){ adj[i]|=1u<<j; adj[j]|=1u<<i;} k++; } }
int main(int argc,char**argv){ which=argv[1]; n=atoi(argv[2]); long iters=atol(argv[3]); rng.seed(atoi(argv[4])); double p=atof(argv[5]); ALL=(1u<<n)-1;
  if(iters==0){ string s; long cnt=0,tot=0; double mx=-1e9; while(getline(cin,s)){ parse(s); ALL=(1u<<n)-1; double sc=score(); tot++; mx=max(mx,sc); if(sc>1e-9){ cnt++; if(cnt<=3) printf("CE %s %s %.3f\n",which.c_str(),s.c_str(),sc);} } printf("%s n=%d tot=%ld ce=%ld max=%.3f\n",which.c_str(),n,tot,cnt,mx); return 0; }
  for(int v=0;v<n;v++) adj[v]=0; for(int i=1;i<n;i++){ int j=rng()%i; adj[i]|=1u<<j; adj[j]|=1u<<i; } for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if((rng()%1000)/1000.0<p){ adj[i]|=1u<<j; adj[j]|=1u<<i; }
  double cur=score(),best=cur; M bestA[32]; memcpy(bestA,adj,sizeof adj); double T=1.0;
  for(long it=0;it<iters;it++){ int i=rng()%n,j=rng()%n; if(i==j) continue; adj[i]^=1u<<j; adj[j]^=1u<<i; double s=score();
    if(s>=cur || exp((s-cur)/T)>(rng()%1000000)/1e6){ cur=s; if(s>best){best=s; memcpy(bestA,adj,sizeof adj);} } else { adj[i]^=1u<<j; adj[j]^=1u<<i; } T=max(0.05,T*0.9995); }
  memcpy(adj,bestA,sizeof adj); printf("%s n=%d best=%.3f edges:",which.c_str(),n,best); for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if(adj[i]>>j&1) printf(" %d-%d",i,j); printf("\n"); }
