#include <bits/stdc++.h>
using namespace std; typedef unsigned M; int n; M adj[32]; M ALL; mt19937_64 rng(1); string which;
inline int pc(M x){ return __builtin_popcount(x); }
M openN(M S){ M r=0; for(M t=S;t;t&=t-1) r|=adj[__builtin_ctz(t)]; return r; }
M closedN(M S){ return S|openN(S); }
bool connM(M m){ if(!m) return true; M seen=m&(-m),fr=seen; while(fr){ M nf=openN(fr)&m&~seen; seen|=nf; fr=nf; } return seen==m; }
int edgesIn(M m){ int e=0; for(M t=m;t;t&=t-1) e+=pc(adj[__builtin_ctz(t)]&m); return e/2; }
int alphaM(M m){ if(!m) return 0; int v=__builtin_ctz(m); M rest=m&~(1u<<v); int a=alphaM(rest&~adj[v])+1; if(!(adj[v]&rest)) return a; return max(a,alphaM(rest)); }
double score(){ if(!connM(ALL)) return -1e9;
  int D[32][32]; for(int v=0;v<n;v++){ for(int w=0;w<n;w++) D[v][w]=99; D[v][v]=0; M seen=1u<<v,fr=seen; int d=0; while(fr){ M nf=openN(fr)&~seen; d++; for(M t=nf;t;t&=t-1) D[v][__builtin_ctz(t)]=d; seen|=nf; fr=nf; } }
  vector<int> deg(n),ecc(n); for(int v=0;v<n;v++){ deg[v]=pc(adj[v]); ecc[v]=0; for(int w=0;w<n;w++) ecc[v]=max(ecc[v],D[v][w]); }
  int rad=*min_element(ecc.begin(),ecc.end());
  int delta=*min_element(deg.begin(),deg.end()), Delta=*max_element(deg.begin(),deg.end());
  M A=0,Mx=0,P=0,C=0; for(int v=0;v<n;v++){ if(deg[v]==delta) A|=1u<<v; if(deg[v]==Delta) Mx|=1u<<v; if(deg[v]==1) P|=1u<<v; if(ecc[v]==rad) C|=1u<<v; }
  M S=openN(P); // support vertices
  vector<int> tri(n); for(int v=0;v<n;v++) tri[v]=edgesIn(adj[v]); int tm=*min_element(tri.begin(),tri.end()); int Tm=0; for(int v=0;v<n;v++) if(tri[v]==tm) Tm++;
  M Dd=0; for(int v=0;v<n;v++) for(int u=0;u<n;u++) if(u!=v && ((closedN(1u<<u)&~closedN(1u<<v))==0)) { Dd|=1u<<v; break; }
  double CW=0; for(int v=0;v<n;v++) CW+=1.0/(deg[v]+1);
  bool needI = which[0]=='4' && which!="439" ; bool needA2 = which=="439"; bool needG2 = which=="397c"||which=="399c";
  int id=n,g2=n,a2=0; if(needI||needA2||needG2) for(M T=1;T<=ALL;T++){ int c=pc(T);
    if(needI && c<id && closedN(T)==ALL && !(openN(T)&T)) id=c;
    if(needG2 && c<g2){ bool ok=true; for(int v=0;v<n&&ok;v++) if(!(T>>v&1) && pc(adj[v]&T)<2) ok=false; if(ok) g2=c; }
    if(needA2 && c>a2){ bool ok=true; for(M t=T;t;t&=t-1) if(pc(adj[__builtin_ctz(t)]&T)>1){ok=false;break;} if(ok) a2=c; }
    if(T==ALL) break; }
  if(which=="420b") return id-(alphaM(ALL&~openN(S))+4.0*(edgesIn(closedN(A))-1));
  if(which=="420c") return id-(alphaM(ALL&~openN(S))+4.0*(Tm-1));
  if(which=="422d") return id-(alphaM(ALL&~Dd)+floor((edgesIn(Dd)+1)/3.0));
  if(which=="423") return id-(edgesIn(Mx)+1.0*alphaM(closedN(A))*alphaM(ALL&~A));
  if(which=="425e") return id-(4.0*Tm+edgesIn(Dd));
  if(which=="430a") return id-(alphaM(openN(C))+2*floor(CW-1+1e-9));
  if(which=="433"){ double s=0; for(int v=0;v<n;v++){ int c=0; for(int w=0;w<n;w++) if(w!=v&&D[v][w]<=2) c++; s+=1.0/c; } return id-(0.5*pc(openN(Mx))*floor(2*s+1e-9)); }
  if(which=="439") return a2-(pc(openN(Mx))+floor(2*(CW-1)+1e-9));
  if(which=="397c"){ M a2m[32]; for(int v=0;v<n;v++){ a2m[v]=0; for(int w=0;w<n;w++) if(w!=v&&D[v][w]<=2) a2m[v]|=1u<<w; }
    int gs=n; for(M T=1;T<=ALL;T++){ int c=pc(T); if(c<gs){ M cn=T; for(M t=T;t;t&=t-1) cn|=a2m[__builtin_ctz(t)]; if(cn==ALL) gs=c; } if(T==ALL) break; }
    return g2-(pc(ALL&~openN(P))+gs); }
  if(which=="399c"){ vector<int> cd(n); for(int v=0;v<n;v++) cd[v]=n-1-deg[v]; sort(cd.rbegin(),cd.rend()); int WP=0; for(int i=0;i<n;i++) WP=max(WP,min(cd[i]+1,i+1));
    vector<int> lam(n); for(int v=0;v<n;v++) lam[v]=alphaM(adj[v]); int lm=*min_element(lam.begin(),lam.end()); int Ml=0; for(int v=0;v<n;v++) if(lam[v]==lm) Ml++;
    return g2-(2.0/3*WP+2*Ml); }
  return 0; }
void parse(const string& s){ int p=0; n=s[p++]-63; for(int i=0;i<n;i++) adj[i]=0; int val=0,k=6;
  for(int j=1;j<n;j++) for(int i=0;i<j;i++){ if(k==6){ val=s[p++]-63; k=0;} if(val>>(5-k)&1){ adj[i]|=1u<<j; adj[j]|=1u<<i;} k++; } }
int main(int argc,char**argv){ which=argv[1]; n=atoi(argv[2]); long iters=atol(argv[3]);
  if(iters==0){ string s; long cnt=0,tot=0; double mx=-1e9; while(getline(cin,s)){ parse(s); ALL=(1u<<n)-1; double sc=score(); tot++; mx=max(mx,sc); if(sc>1e-9){ cnt++; if(cnt<=3) printf("CE %s %s %.3f\n",which.c_str(),s.c_str(),sc);} } printf("%s n=%d tot=%ld ce=%ld max=%.3f\n",which.c_str(),n,tot,cnt,mx); return 0; } rng.seed(atoi(argv[4])); double p=atof(argv[5]); ALL=(1u<<n)-1;
  for(int v=0;v<n;v++) adj[v]=0; for(int i=1;i<n;i++){ int j=rng()%i; adj[i]|=1u<<j; adj[j]|=1u<<i; } for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if((rng()%1000)/1000.0<p){ adj[i]|=1u<<j; adj[j]|=1u<<i; }
  double cur=score(),best=cur; M bestA[32]; memcpy(bestA,adj,sizeof adj); double T=1.0;
  for(long it=0;it<iters;it++){ int i=rng()%n,j=rng()%n; if(i==j) continue; adj[i]^=1u<<j; adj[j]^=1u<<i; double s=score();
    if(s>=cur || exp((s-cur)/T)>(rng()%1000000)/1e6){ cur=s; if(s>best){best=s; memcpy(bestA,adj,sizeof adj);} } else { adj[i]^=1u<<j; adj[j]^=1u<<i; } T=max(0.05,T*0.999); }
  memcpy(adj,bestA,sizeof adj); printf("%s n=%d best=%.3f edges:",which.c_str(),n,best); for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if(adj[i]>>j&1) printf(" %d-%d",i,j); printf("\n"); }
