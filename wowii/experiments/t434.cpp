#include "inv.h"
int degeneracy(const M* A, M m){ int best=0; M left=m; while(left){ int mn=99,v=-1; for(M t=left;t;t&=t-1){ int x=__builtin_ctz(t); int d=pc(A[x]&left); if(d<mn){mn=d;v=x;} } best=max(best,mn); left&=~(1u<<v); } return best; }
int main(){ string s; map<string,pair<long,string>> fails; map<string,double> minsl; long cnt=0;
  auto F=[&](const string& k,double lhs,double rhs){ double sl=lhs-rhs; if(!minsl.count(k)||sl<minsl[k]) minsl[k]=sl; if(sl<-1e-9){ auto& f=fails[k]; if(f.first++==0) f.second=s; } };
  while(getline(cin,s)){ if(s.empty()) continue; parse(s); if(n<4) continue; cnt++;
    Inv I=compute(); int id=I.idom;
    M cadj[32]; for(int v=0;v<n;v++) cadj[v]=ALL&~adj[v]&~(1u<<v);
    int SW=degeneracy(cadj,ALL)+1;
    M Mx=0; for(int v=0;v<n;v++) if(I.deg[v]==I.Delta) Mx|=1u<<v;
    int dM=99; for(M t=Mx;t;t&=t-1) dM=min(dM,pc(adj[__builtin_ctz(t)]&Mx));
    M R=ALL&~Mx; int dR=99; for(M t=R;t;t&=t-1) dR=min(dR,pc(adj[__builtin_ctz(t)]&R)); if(!R) dR=0;
    F("434b", dM+1+SW, id); if(I.diam>2) F("434b diam>2", dM+SW, id);
    F("434c", dR+1+SW, id); if(I.delta==1) F("434c delta=1", dR+SW, id);
    int D[32][32]; for(int v=0;v<n;v++){ for(int w=0;w<n;w++) D[v][w]=-1; D[v][v]=0; M seen=1u<<v,fr=seen; int d=0; while(fr){ M nf=openN(fr)&~seen; d++; for(M t=nf;t;t&=t-1) D[v][__builtin_ctz(t)]=d; seen|=nf; fr=nf; } }
    M B=0; for(int v=0;v<n;v++) if(I.ecc[v]==I.diam) B|=1u<<v; M NB=closedN(B); int comp=0; M left=NB; while(left){ M c=left&(-left),fr=c; while(fr){ M nf=openN(fr)&NB&~c; c|=nf; fr=nf; } left&=~c; comp++; }
    F("434d", SW-comp+2, id);
    M C=0; for(int v=0;v<n;v++) if(I.ecc[v]==I.rad) C|=1u<<v; int eC=0; for(int v=0;v<n;v++){ int mn=99; for(M t=C;t;t&=t-1) mn=min(mn,D[v][__builtin_ctz(t)]); eC=max(eC,mn); }
    F("434e", SW-eC+2, id);
    F("434a M", pc(Mx)+2*(SW/2), id);
  }
  printf("graphs=%ld\n",cnt); for(auto&[k,v]:minsl) printf("%-26s fails=%-7ld minslack=%.3f %s\n",k.c_str(),fails[k].first,v,fails[k].second.c_str()); }
