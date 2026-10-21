#include <bits/stdc++.h>
using namespace std; typedef unsigned M; int n; M adj[32]; M ALL; mt19937_64 rng(1); string which;
inline int pc(M x){ return __builtin_popcount(x); }
M openN(M S){ M r=0; for(M t=S;t;t&=t-1) r|=adj[__builtin_ctz(t)]; return r; }
bool connM(M m){ if(!m) return true; M seen=m&(-m),fr=seen; while(fr){ M nf=openN(fr)&m&~seen; seen|=nf; fr=nf; } return seen==m; }
int comps(M m){ int c=0; M left=m; while(left){ M s=left&(-left),fr=s; while(fr){ M nf=openN(fr)&m&~s; s|=nf; fr=nf; } left&=~s; c++; } return c; }
int matchM(M m){ if(!m) return 0; int v=__builtin_ctz(m); M rest=m&~(1u<<v); if(!(adj[v]&rest)) return matchM(rest); int best=matchM(rest); for(M t=adj[v]&rest;t;t&=t-1){ int w=__builtin_ctz(t); best=max(best,1+matchM(rest&~(1u<<w))); if(best*2>=pc(m)-1) break; } return best; }
bool isBip(M m){ M left=m; while(left){ M c0=left&(-left),c1=0,fr0=c0,fr1=0; while(fr0||fr1){ M n1=openN(fr0)&m, n0=openN(fr1)&m; if((n1&c0)||(n0&c1)) return false; n1&=~c1; n0&=~c0; c1|=n1; c0|=n0; fr0=n0; fr1=n1; } left&=~(c0|c1);} return true; }
int maxd, maxs; M Hu;
void recI(int v, M I, M forb){ if(v==n){ int d=pc(I)-pc(openN(I)); int s=pc(I); if(d>maxd||(d==maxd&&s>maxs)){ maxd=d; maxs=s; Hu=I; } else if(d==maxd&&s==maxs) Hu|=I; return; }
  recI(v+1,I,forb); if(!(forb>>v&1)) recI(v+1,I|(1u<<v),forb|adj[v]); }
int Hsize(){ maxd=-100; maxs=-1; Hu=0; recI(0,0,0); return pc(Hu); }
double score(){ if(!connM(ALL)) return -1e9; M P=0; for(int v=0;v<n;v++) if(pc(adj[v])==1) P|=1u<<v; M R=ALL&~openN(P); int h=Hsize(); int mu=matchM(R);
  if(which=="412f") return mu-h;
  if(which=="412fb"){ if(!isBip(ALL)) return -1e9; return comps(R)+mu-h; }
  return 0; }
void parse(const string& s){ int p=0; n=s[p++]-63; for(int i=0;i<n;i++) adj[i]=0; int val=0,k=6; for(int j=1;j<n;j++) for(int i=0;i<j;i++){ if(k==6){ val=s[p++]-63; k=0;} if(val>>(5-k)&1){ adj[i]|=1u<<j; adj[j]|=1u<<i;} k++; } }
int main(int argc,char**argv){ which=argv[1]; n=atoi(argv[2]); long iters=atol(argv[3]); rng.seed(atoi(argv[4])); double p=atof(argv[5]); ALL=(1u<<n)-1;
  if(iters==0){ string s; long cnt=0,tot=0; double mx=-1e9; while(getline(cin,s)){ parse(s); ALL=(1u<<n)-1; double sc=score(); if(sc<-1e8) continue; tot++; mx=max(mx,sc); if(sc>1e-9){ cnt++; if(cnt<=3) printf("CE %s %s %.1f\n",which.c_str(),s.c_str(),sc);} } printf("%s n=%d tot=%ld ce=%ld max=%.1f\n",which.c_str(),n,tot,cnt,mx); return 0; }
  for(int v=0;v<n;v++) adj[v]=0; for(int i=1;i<n;i++){ int j=rng()%i; adj[i]|=1u<<j; adj[j]|=1u<<i; } for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if((rng()%1000)/1000.0<p){ adj[i]|=1u<<j; adj[j]|=1u<<i; }
  double cur=score(),best=cur; M bestA[32]; memcpy(bestA,adj,sizeof adj); double T=1.0;
  for(long it=0;it<iters;it++){ int i=rng()%n,j=rng()%n; if(i==j) continue; adj[i]^=1u<<j; adj[j]^=1u<<i; double s=score();
    if(s>=cur || exp((s-cur)/T)>(rng()%1000000)/1e6){ cur=s; if(s>best){best=s; memcpy(bestA,adj,sizeof adj);} } else { adj[i]^=1u<<j; adj[j]^=1u<<i; } T=max(0.05,T*0.9995); }
  memcpy(adj,bestA,sizeof adj); printf("%s n=%d best=%.1f edges:",which.c_str(),n,best); for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if(adj[i]>>j&1) printf(" %d-%d",i,j); printf("\n"); }
