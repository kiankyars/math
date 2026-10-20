// Random/structured search for counterexamples to clean open WOWII conjectures, n <= 20.
#include <bits/stdc++.h>
using namespace std; typedef unsigned M;
int n; M adj[32]; M ALL; mt19937_64 rng;
inline int pc(M x){ return __builtin_popcount(x); }
M openN(M S){ M r=0; for(M t=S;t;t&=t-1) r|=adj[__builtin_ctz(t)]; return r; }
M closedN(M S){ return S|openN(S); }
bool connectedM(M m){ if(!m) return true; M seen=m&(-m), fr=seen; while(fr){ M nf=openN(fr)&m&~seen; seen|=nf; fr=nf; } return seen==m; }
int edgesIn(M m){ int e=0; for(M t=m;t;t&=t-1) e+=pc(adj[__builtin_ctz(t)]&m); return e/2; }
int alphaM(M m){ if(!m) return 0; int v=__builtin_ctz(m); M rest=m&~(1u<<v); int a=alphaM(rest&~adj[v])+1; if(!(adj[v]&rest)) return a; return max(a,alphaM(rest)); }
int matchM(M m){ if(!m) return 0; int v=__builtin_ctz(m); M rest=m&~(1u<<v); int best=matchM(rest); for(M t=adj[v]&rest;t;t&=t-1){ int w=__builtin_ctz(t); best=max(best,1+matchM(rest&~(1u<<w))); if(best*2>=pc(m)) break; } return best; }
int gammaM(M m){ if(!m) return 0; vector<int> el; for(M t=m;t;t&=t-1) el.push_back(__builtin_ctz(t)); int k=el.size(); int best=k;
  for(long s=1;s<(1L<<k);s++){ int c=__builtin_popcountl(s); if(c>=best) continue; M S=0; for(int i=0;i<k;i++) if(s>>i&1) S|=1u<<el[i]; if((closedN(S)&m)==m) best=c; } return best; }
bool isBip(M m){ M left=m; while(left){ M c0=left&(-left),c1=0,fr0=c0,fr1=0; while(fr0||fr1){ M n1=openN(fr0)&m, n0=openN(fr1)&m; if((n1&c0)||(n0&c1)) return false; n1&=~c1; n0&=~c0; c1|=n1; c0|=n0; fr0=n0; fr1=n1; } left&=~(c0|c1);} return true; }
int residueOf(vector<int> d){ sort(d.rbegin(),d.rend()); while(!d.empty()&&d[0]>0){ int x=d[0]; d.erase(d.begin()); for(int i=0;i<x&&i<(int)d.size();i++) d[i]--; sort(d.rbegin(),d.rend()); } return d.size(); }
map<string,long> fails; map<string,string> ex; long tested=0;
string g6(){ string s; s+=char(n+63); int val=0,k=0; for(int j=1;j<n;j++) for(int i=0;i<j;i++){ val=(val<<1)|((adj[i]>>j)&1); if(++k==6){ s+=char(val+63); val=0;k=0;} } if(k){ val<<=(6-k); s+=char(val+63);} return s; }
void F(const string& name,bool ok,const string& info){ if(!ok){ if(fails[name]++==0){ ex[name]=g6()+" "+info; printf("NEWFAIL %s : %s %s\n",name.c_str(),g6().c_str(),info.c_str()); fflush(stdout);} } }
void testGraph(){ if(!connectedM(ALL)||n<4) return; tested++;
  vector<int> deg(n); int m=0; for(int v=0;v<n;v++){ deg[v]=pc(adj[v]); m+=deg[v]; } m/=2;
  int delta=*min_element(deg.begin(),deg.end()), Delta=*max_element(deg.begin(),deg.end());
  vector<int> ecc(n); vector<vector<int>> dist(n,vector<int>(n,0)); for(int v=0;v<n;v++){ M seen=1u<<v,fr=seen; int d=0; while(seen!=ALL){ M nf=openN(fr)&~seen; d++; for(M t=nf;t;t&=t-1) dist[v][__builtin_ctz(t)]=d; seen|=nf; fr=nf; } ecc[v]=d; }
  int rad=*min_element(ecc.begin(),ecc.end());
  vector<int> lam(n),lamc(n); for(int v=0;v<n;v++){ lam[v]=alphaM(adj[v]); }
  int maxlam=*max_element(lam.begin(),lam.end());
  // subset invariants
  int gamma=n,gammat=n,gamma2=n,idom=n,tree=1,b=1,gc=n;
  for(M S=1;S<=ALL;S++){ int c=pc(S); M on=openN(S), cn=S|on;
    if(c<gamma && cn==ALL) gamma=c;
    if(c<gammat && on==ALL) gammat=c;
    if(c<idom && cn==ALL && !(on&S)) idom=c;
    if(c<gamma2){ bool ok=true; M out=ALL&~S; for(M t=out;t&&ok;t&=t-1){ int v=__builtin_ctz(t); if(pc(adj[v]&S)<2) ok=false; } if(ok) gamma2=c; }
    if(c>tree && edgesIn(S)==c-1 && connectedM(S)) tree=c;
    if(c>b && isBip(S)) b=c;
    if(c<gc && cn==ALL && connectedM(S)) gc=c;
    if(S==ALL) break; }
  int Ls=n-gc; int alpha=alphaM(ALL); int mu=matchM(ALL);
  char buf[400]; snprintf(buf,400,"n=%d m=%d delta=%d Delta=%d rad=%d tree=%d Ls=%d b=%d maxlam=%d gamma=%d gt=%d g2=%d i=%d alpha=%d mu=%d",n,m,delta,Delta,rad,tree,Ls,b,maxlam,gamma,gammat,gamma2,idom,alpha,mu); string info=buf;
  F("84", tree*delta >= 2*rad, info);
  F("174", Ls+b >= n+maxlam-1, info);
  int maxNe=0; for(int u=0;u<n;u++) for(M t=adj[u];t;t&=t-1){ int v=__builtin_ctz(t); maxNe=max(maxNe,pc(adj[u]|adj[v])); }
  F("178", Ls+b >= maxlam+maxNe, info);
  F("179", Ls+b >= Delta+gamma+maxlam, info);
  { M Mset=0; for(int v=0;v<n;v++) if(deg[v]==Delta) Mset|=1u<<v; int x=pc(openN(Mset)&~Mset); F("165", Ls*Ls >= 2*x || (Ls+0.0) >= ceil(sqrt(2.0*x))-1e-9, info); }
  // 247 regular
  // 255: gt >= 2|C|/maxNe ; 256: gt >= 2|N(A)|/maxNe
  { int C=0; for(int v=0;v<n;v++) if(ecc[v]==rad) C++; F("255", gammat*maxNe >= 2*C, info);
    M A=0; for(int v=0;v<n;v++) if(deg[v]==delta) A|=1u<<v; F("256", gammat*maxNe >= 2*pc(openN(A)), info); }
  // 384b, 387
  { vector<int> tri(n); for(int v=0;v<n;v++) tri[v]=edgesIn(adj[v]); set<int> T(tri.begin(),tri.end()); F("384b", 2*gamma2 <= 2*n-(int)T.size(), info);
    vector<int> d=deg; sort(d.begin(),d.end()); int um=d[n/2]; F("387", gamma2 <= n-um+1, info); }
  // 392b,c ; 394
  { M Ad=0,A2=0,Ml=0; int minl=*min_element(lam.begin(),lam.end()); for(int v=0;v<n;v++){ if(deg[v]==delta) Ad|=1u<<v; if(deg[v]==2) A2|=1u<<v; if(lam[v]==minl) Ml|=1u<<v; }
    int cnt1=0; for(int v=0;v<n;v++) if(pc(adj[v]&A2)==1) cnt1++; int base=matchM(ALL&~Ad)+pc(Ad);
    F("392b", gamma2 <= base+cnt1, info); int cutv=0; for(int v=0;v<n;v++){ M r=ALL&~(1u<<v); if(!connectedM(r)) cutv++; } F("392c", gamma2 <= base+cutv, info);
    F("394", gamma2 <= mu+edgesIn(A2)+pc(Ml), info); }
  // 422a,b,c ; 426
  { M Mset=0; for(int v=0;v<n;v++) if(deg[v]==Delta) Mset|=1u<<v;
    F("422a", idom <= alphaM(ALL&~Mset)+2*(edgesIn(Mset)/3), info);
    int g=gammaM(ALL&~Mset); F("422b", idom <= alphaM(Mset)+g*g, info);
    M A=0; for(int v=0;v<n;v++) if(2*deg[v]<=n) A|=1u<<v; int DVA=0; for(int v=0;v<n;v++) if(!(A>>v&1)) DVA=max(DVA,pc(adj[v]&~A&ALL)); F("422c", idom <= alphaM(A)+2*(DVA/3), info);
    F("426", idom <= n-gammaM(openN(Mset)), info); }
  // 434e: i <= SW(G^c) - ecc(C) + 2 ; SW = 1 + max over subgraphs min degree (degeneracy+1), ecc(C) = max_v dist(v,C)
  { M cadj[32]; for(int v=0;v<n;v++) cadj[v]=ALL&~adj[v]&~(1u<<v); // degeneracy of complement
    M rem=ALL; int degen=0; while(rem){ int bv=-1,bd=99; for(M t=rem;t;t&=t-1){ int v=__builtin_ctz(t); int d=pc(cadj[v]&rem); if(d<bd){bd=d;bv=v;} } degen=max(degen,bd); rem&=~(1u<<bv); }
    int SW=degen+1; int eccC=0; for(int v=0;v<n;v++){ int dm=99; for(int c=0;c<n;c++) if(ecc[c]==rad) dm=min(dm,dist[v][c]); eccC=max(eccC,dm); }
    F("434e", idom <= SW-eccC+2, info); }
  // 281/300: frequency of lambda_min of complement
  { vector<int> lc(n); M cadj[32]; for(int v=0;v<n;v++) cadj[v]=ALL&~adj[v]&~(1u<<v);
    // alpha in complement of the complement-neighbourhood = clique number in G of non-neighbours
    for(int v=0;v<n;v++){ // lambda_bar(v) = alpha_{bar G}(N_bar(v)) = omega_G(N_bar(v))
      M S=cadj[v]; // compute max clique in G on S via alpha in complement: alphaM uses adj; emulate by swapping
      M save[32]; memcpy(save,adj,sizeof(adj)); for(int u=0;u<n;u++) adj[u]=cadj[u]; lc[v]=alphaM(S); memcpy(adj,save,sizeof(adj)); }
    int mn=*min_element(lc.begin(),lc.end()); int fr=0; for(int v=0;v<n;v++) if(lc[v]==mn) fr++;
    F("281", gammat <= fr+mu, info); F("300", 2*gammat <= n+fr, info);
    int mx=*max_element(lc.begin(),lc.end()); F("161", Ls >= mx, info); }
  // 199: tree-2 <= kappa => ham path (n<=20 DP)
  if(n<=18){ int kappa=n-1; for(M S=0;S<ALL;S++){ int c=pc(S); if(c>=kappa) continue; M rest=ALL&~S; if(pc(rest)>=2 && !connectedM(rest)) kappa=c; }
    if(tree-2<=kappa){ int N=1<<n; vector<M> es(N,0); for(int v=0;v<n;v++) es[1<<v]=1u<<v; bool ham=false;
      for(int mm=1;mm<N;mm++){ if(!es[mm]) continue; for(M t=es[mm];t;t&=t-1){ int v=__builtin_ctz(t); for(M u=adj[v]&~mm;u;u&=u-1){ int w=__builtin_ctz(u); es[mm|(1<<w)]|=1u<<w; } } }
      ham=es[N-1]!=0; F("199", ham, info+" kappa="+to_string(kappa)); } }
}
void addE(int a,int b){ if(a==b) return; adj[a]|=1u<<b; adj[b]|=1u<<a; }
int main(int argc,char**argv){ long iters=atol(argv[1]); rng.seed(atol(argv[2])); int nmin=argc>3?atoi(argv[3]):10, nmax=argc>4?atoi(argv[4]):16;
  for(long it=0;it<iters;it++){ n=nmin+rng()%(nmax-nmin+1); ALL=(1u<<n)-1; for(int i=0;i<n;i++) adj[i]=0; int type=rng()%6;
    if(type==0){ double p=0.1+0.6*(rng()%1000)/1000.0; for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if((rng()%1000)/1000.0<p) addE(i,j); }
    else if(type==1){ for(int i=1;i<n;i++) addE(i,rng()%i); int extra=rng()%(2*n); for(int k=0;k<extra;k++) addE(rng()%n,rng()%n); }
    else if(type==2){ // cycle blow-up with random clique sizes plus pendants
      int c=3+rng()%6; vector<int> part(n); for(int v=0;v<n;v++) part[v]=v%c; for(int i=0;i<n;i++) for(int j=i+1;j<n;j++){ int d=abs(part[i]-part[j]); d=min(d,c-d); if(d==0||d==1) addE(i,j); }
      int pend=rng()%3; for(int k=0;k<pend && k<n;k++){ int v=n-1-k; for(int u=0;u<n;u++) if(u!=v){ adj[u]&=~(1u<<v);} adj[v]=0; addE(v,rng()%(n-1-k)); } }
    else if(type==3){ // random bipartite
      int a=1+rng()%(n-1); double p=0.2+0.6*(rng()%1000)/1000.0; for(int i=0;i<a;i++) for(int j=a;j<n;j++) if((rng()%1000)/1000.0<p) addE(i,j); }
    else if(type==4){ // random geometric-ish: circular distance threshold
      vector<double> x(n); for(auto& t:x) t=(rng()%100000)/100000.0; double r=0.05+0.3*(rng()%1000)/1000.0; for(int i=0;i<n;i++) for(int j=i+1;j<n;j++){ double d=fabs(x[i]-x[j]); d=min(d,1-d); if(d<r) addE(i,j);} }
    else { // sparse random with degree cap
      int cap=2+rng()%3; for(int k=0;k<3*n;k++){ int a=rng()%n,b=rng()%n; if(a!=b && pc(adj[a])<cap && pc(adj[b])<cap) addE(a,b);} }
    testGraph(); }
  printf("tested=%ld\n",tested); for(auto& [k,v]:fails) printf("FAIL %s count=%ld e.g. %s\n",k.c_str(),v,ex[k].c_str()); }
