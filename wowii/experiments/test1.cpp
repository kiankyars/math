#include "inv.h"
int main(){ string s; long cnt=0; map<string,long> fails; map<string,string> ex;
  auto F=[&](const string& name,bool ok,const string& info){ if(!ok){ if(fails[name]++==0) ex[name]=info; } };
  while(getline(cin,s)){ if(s.empty()) continue; parse(s); cnt++; Inv I=compute(); char buf[300];
    int maxlam=*max_element(I.lam.begin(),I.lam.end());
    snprintf(buf,300,"%s n=%d rad=%d delta=%d tree=%d Ls=%d b=%d maxlam=%d Delta=%d gamma=%d alpha=%d kappa=%d ham=%d gt=%d pcov=%d",s.c_str(),n,I.rad,I.delta,I.tree,I.Ls,I.b,maxlam,I.Delta,I.gamma,I.alpha,I.kappa,(int)I.hampath,I.gammat,I.pcov);
    string info=buf;
    if(n>=2){
    F("84 tree>=2rad/delta", (double)I.tree >= 2.0*I.rad/I.delta - 1e-9, info);
    F("174 Ls+b>=n+maxlam-1", I.Ls+I.b >= n+maxlam-1, info);
    F("179 Ls+b>=Delta+gamma+maxlam", I.Ls+I.b >= I.Delta+I.gamma+maxlam, info);
    F("199 tree-2<=kappa => hampath", !(I.tree-2<=I.kappa) || I.hampath, info);
    // 252: C4-free => gamma_t >= mode_min (smallest most frequent degree)
    { map<int,int> fr; for(int d:I.deg) fr[d]++; int best=-1,md=0; for(auto [d,c]:fr) if(c>best){best=c;md=d;} F("252 C4free=>gt>=modemin", I.c4 || I.gammat>=md, info); }
    // 247: regular => gamma_t >= 2 pcov
    F("247 regular=>gt>=2p", I.delta!=I.Delta || I.gammat>=2*I.pcov, info);
    // 387: gamma2 <= n - m + 1, m upper median of degree sequence
    { vector<int> d=I.deg; sort(d.begin(),d.end()); int um=d[n/2]; F("387 g2<=n-uppermedian+1", I.gamma2<=n-um+1, info); }
    // 384b: gamma2 <= floor(n - |T|/2), T = set of distinct triangle counts
    { set<int> T(I.tri.begin(),I.tri.end()); F("384b g2<=floor(n-|T|/2)", 2*I.gamma2 <= 2*n-(int)T.size(), info); }
    // 426: i <= n - gamma(G[N(M)])
    { M Mset=0; for(int v=0;v<n;v++) if(I.deg[v]==I.Delta) Mset|=1u<<v; M NM=openN(Mset); F("426 i<=n-gamma(G[N(M)])", I.idom <= n-gammaM(NM), info); }
    // 422a: i <= alpha(G[V-M]) + 2 floor(|E(G[M])|/3)
    { M Mset=0; for(int v=0;v<n;v++) if(I.deg[v]==I.Delta) Mset|=1u<<v; F("422a", I.idom <= alphaM(ALL&~Mset)+2*(edgesIn(Mset)/3), info);
      F("422b", I.idom <= alphaM(Mset)+gammaM(ALL&~Mset)*gammaM(ALL&~Mset), info);
      M A=0; for(int v=0;v<n;v++) if(2*I.deg[v]<=n) A|=1u<<v; int DeltaVA=0; for(int v=0;v<n;v++) if(!(A>>v&1)) DeltaVA=max(DeltaVA,pc(adj[v]&~A&ALL)); F("422c", I.idom <= alphaM(A)+2*(DeltaVA/3), info);
      M Amin=0; for(int v=0;v<n;v++) if(I.deg[v]==I.delta) Amin|=1u<<v; F("423", I.idom <= edgesIn(Mset)+alphaM(closedN(Amin))*alphaM(ALL&~Amin), info); }
    // 397c: gamma2 <= |V - N(P)| + gamma(G^2), P pendants
    { M P=0; for(int v=0;v<n;v++) if(I.deg[v]==1) P|=1u<<v; // gamma(G^2)
      M adj2[32]; for(int v=0;v<n;v++){ adj2[v]=adj[v]; for(M t=adj[v];t;t&=t-1) adj2[v]|=adj[__builtin_ctz(t)]; adj2[v]&=~(1u<<v); }
      int g2sq=n; for(M S=1;S<=ALL;S++){ int c=pc(S); if(c>=g2sq) continue; M r=S; for(M t=S;t;t&=t-1) r|=adj2[__builtin_ctz(t)]; if(r==ALL) g2sq=c; if(S==ALL) break; }
      F("397c", I.gamma2 <= pc(ALL&~openN(P)) + g2sq, info); }
    // 394: gamma2 <= mu + |E(G[A2])| + |M_lam| (vertices of min local independence)
    { M A2=0,Ml=0; int minl=*min_element(I.lam.begin(),I.lam.end()); for(int v=0;v<n;v++){ if(I.deg[v]==2) A2|=1u<<v; if(I.lam[v]==minl) Ml|=1u<<v; } F("394", I.gamma2 <= I.mu+edgesIn(A2)+pc(Ml), info); }
    // 392b: gamma2 <= mu(G[V-Adelta]) + |Adelta| + |{v: |N(v) ∩ A2|=1}|
    { M Ad=0,A2=0; for(int v=0;v<n;v++){ if(I.deg[v]==I.delta) Ad|=1u<<v; if(I.deg[v]==2) A2|=1u<<v; } int cnt1=0; for(int v=0;v<n;v++) if(pc(adj[v]&A2)==1) cnt1++;
      int base=matchM(ALL&~Ad)+pc(Ad); F("392b", I.gamma2 <= base+cnt1, info);
      int cutv=0; for(int v=0;v<n;v++){ M r=ALL&~(1u<<v); if(pc(r)>=2 && !connectedM(r)) cutv++; } F("392c", I.gamma2 <= base+cutv, info); }
    }
  }
  printf("graphs=%ld\n",cnt); for(auto& [k,v]:fails) printf("FAIL %-28s count=%ld  e.g. %s\n",k.c_str(),v,ex[k].c_str());
}
