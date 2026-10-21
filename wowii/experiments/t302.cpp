#include "inv.h"
int omegaM(M m){ if(!m) return 0; int v=__builtin_ctz(m); M rest=m&~(1u<<v); int a=omegaM(rest&adj[v])+1; if((adj[v]&rest)==rest) return a; return max(a,omegaM(rest)); }
int main(){ string s; map<string,pair<long,string>> fails; map<string,double> minsl; long cnt=0;
  auto F=[&](const string& k,double lhs,double rhs){ double sl=lhs-rhs; if(!minsl.count(k)||sl<minsl[k]) minsl[k]=sl; if(sl<-1e-9){ auto& f=fails[k]; if(f.first++==0) f.second=s; } };
  while(getline(cin,s)){ if(s.empty()) continue; parse(s); if(n<3) continue; cnt++;
    int D[32][32]; for(int v=0;v<n;v++){ for(int w=0;w<n;w++) D[v][w]=-1; D[v][v]=0; M seen=1u<<v,fr=seen; int d=0; while(fr){ M nf=openN(fr)&~seen; d++; for(M t=nf;t;t&=t-1) D[v][__builtin_ctz(t)]=d; seen|=nf; fr=nf; } }
    Inv I=compute(); int gt=I.gammat;
    M cadj[32]; for(int v=0;v<n;v++) cadj[v]=ALL&~adj[v]&~(1u<<v);
    int lc[32],lcmax=0,lcmin=99; for(int v=0;v<n;v++){ lc[v]=omegaM(cadj[v]); lcmax=max(lcmax,lc[v]); lcmin=min(lcmin,lc[v]); }
    int fmax=0,fmin=0; for(int v=0;v<n;v++){ if(lc[v]==lcmax) fmax++; if(lc[v]==lcmin) fmin++; }
    int demin=99,demax=0; for(int v=0;v<n;v++){ int e=0; for(int w=0;w<n;w++) if(D[v][w]%2==0) e++; demin=min(demin,e); demax=max(demax,e); }
    F("302", demin+fmax, gt);
    F("281", fmin+I.mu, gt);
    F("300", 0.5*(n+fmin), gt);
    int nemax=-1,nemin=99; for(int u=0;u<n;u++) for(int v=u+1;v<n;v++) if(!(adj[u]>>v&1)){ int x=pc(cadj[u]|cadj[v]); nemax=max(nemax,x); nemin=min(nemin,x); }
    if(nemax>=0){ F("304", 0.5*(fmax+nemax), gt); F("305", ceil(2.0*nemax/3-1e-9), gt); }
    // annihilation
    vector<int> dd=I.deg; sort(dd.begin(),dd.end()); int a=0,sm=0; for(int i=0;i<n;i++){ sm+=dd[i]; if(sm<=I.m) a=i+1; else break; }
    int S2=0; for(int v=0;v<n;v++) if(I.deg[v]==2) S2++;
    F("299", a+S2, gt);
    // C4 indicator: subgraph / induced
    bool c4i=false; for(int x=0;x<n&&!c4i;x++) for(int y=x+1;y<n&&!c4i;y++) if(!(adj[x]>>y&1)){ M cn=adj[x]&adj[y]; for(M t=cn;t;t&=t-1){ int p=__builtin_ctz(t); if(cn&~adj[p]&~(1u<<p)&~((1u<<(p+1))-1)) {c4i=true;break;} } }
    F("298 sub", a+(I.c4?0:1), gt); F("298 ind", a+(c4i?0:1), gt);
    // Havel-Hakimi first zero step
    { vector<int> d=I.deg; int k=0; bool z=false; for(int x:d) if(x==0) z=true; while(!z){ sort(d.rbegin(),d.rend()); int x=d[0]; d.erase(d.begin()); for(int i=0;i<x&&i<(int)d.size();i++) d[i]--; k++; for(int y:d) if(y==0) z=true; if(d.empty()) break; }
      // complement matching
      M sadj[32]; for(int v=0;v<n;v++){ sadj[v]=adj[v]; adj[v]=cadj[v]; } int muc=matchM(ALL); for(int v=0;v<n;v++) adj[v]=sadj[v];
      F("287", k+muc, gt); F("290", k*I.Delta, gt); }
    // girth
    int girth=99; for(int v=0;v<n;v++){ int dist[32],par[32]; for(int i=0;i<n;i++) dist[i]=-1; dist[v]=0; par[v]=-1; deque<int> q{v}; while(!q.empty()){ int x=q.front(); q.pop_front(); for(M t=adj[x];t;t&=t-1){ int y=__builtin_ctz(t); if(dist[y]<0){ dist[y]=dist[x]+1; par[y]=x; q.push_back(y);} else if(par[x]!=y) girth=min(girth,dist[x]+dist[y]+1); } } }
    // 267: girth>=5 -> gt >= ceil(dist_avg(A,V))
    if(girth>=5 && girth<99){ double s1=0,c1=0,s2=0,c2=0; for(int x=0;x<n;x++) if(I.deg[x]==I.delta){ for(int y=0;y<n;y++){ s1+=D[x][y]; c1++; if(y!=x){ s2+=D[x][y]; c2++; } } }
      F("267 incl0", gt, ceil(s1/c1-1e-9)); F("267 excl0", gt, ceil(s2/c2-1e-9)); }
    // 268/269 centers
    { vector<int> C; for(int v=0;v<n;v++) if(I.ecc[v]==I.rad) C.push_back(v); double s=0,c=0; for(int i=0;i<(int)C.size();i++) for(int j=i+1;j<(int)C.size();j++){ s+=D[C[i]][C[j]]; c++; } double da=c?s/c:0;
      double s3=0,c3=0; for(int x:C) for(int y=0;y<n;y++) if(y!=x){ s3+=D[x][y]; c3++; } double dcv=s3/c3;
      F("268 pairs", gt, floor(1+da+1e-9)); F("268 CV", gt, floor(1+dcv+1e-9));
      if(!I.c4){ F("269 pairs", gt, ceil(1+da-1e-9)); F("269 CV", gt, ceil(1+dcv-1e-9)); } }
    // 232/233/235: B = periphery / boundary; ecc(B) = max_v d(v,B)
    { M per=0; for(int v=0;v<n;v++) if(I.ecc[v]==I.diam) per|=1u<<v;
      M bnd=0; for(int v=0;v<n;v++){ bool isb=false; for(int u=0;u<n&&!isb;u++){ if(u==v) continue; bool ok=true; for(M t=adj[v];t;t&=t-1) if(D[u][__builtin_ctz(t)]>D[u][v]) ok=false; if(ok) isb=true; } if(isb) bnd|=1u<<v; }
      for(int r=0;r<2;r++){ M B=r?bnd:per; int eB=0; for(int v=0;v<n;v++){ int mn=99; for(M t=B;t;t&=t-1) mn=min(mn,D[v][__builtin_ctz(t)]); eB=max(eB,mn);} 
        int eB2=0; for(M t=B;t;t&=t-1) eB2=max(eB2,I.ecc[__builtin_ctz(t)]);
        string tag=r?" bnd":" per"; bool bip=isBip(ALL);
        F("232 setecc"+tag, gt, 0.5*(I.rad+eB)); F("233 setecc"+tag, gt, 2.0/3*(1+eB)); F("235 setecc"+tag, gt, 2.0/3*eB+(bip?1:0));
        F("233 maxecc"+tag, gt, 2.0/3*(1+eB2)); } }
  }
  printf("graphs=%ld\n",cnt); for(auto&[k,v]:minsl) printf("%-26s fails=%-7ld minslack=%.3f %s\n",k.c_str(),fails[k].first,v,fails[k].second.c_str()); }
