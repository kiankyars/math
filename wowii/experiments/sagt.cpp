#include <bits/stdc++.h>
using namespace std; typedef unsigned M; int n; M adj[32]; M ALL; mt19937_64 rng(1); string which;
inline int pc(M x){ return __builtin_popcount(x); }
M openN(M S){ M r=0; for(M t=S;t;t&=t-1) r|=adj[__builtin_ctz(t)]; return r; }
bool connected(){ M seen=1,fr=1; while(fr){ M nf=openN(fr)&~seen; seen|=nf; fr=nf; } return seen==ALL; }
int gammat(){ int best=n; function<void(M,int)> rec=[&](M S,int sz){ if(sz>=best) return; M dom=openN(S); if(dom==ALL){ best=sz; return; } M und=~dom&ALL; int v=-1,bd=99; for(M t=und;t;t&=t-1){ int x=__builtin_ctz(t); int d=pc(adj[x]&~S); if(d<bd){bd=d;v=x;} } if(sz+1>=best) return; for(M t=adj[v]&~S;t;t&=t-1){ int u=__builtin_ctz(t); rec(S|(1u<<u),sz+1);} }; rec(0,0); return best; }
int omegaA(const M* A, M m){ if(!m) return 0; int v=__builtin_ctz(m); M rest=m&~(1u<<v); int a=omegaA(A,rest&A[v])+1; if((A[v]&rest)==rest) return a; return max(a,omegaA(A,rest)); }
// Edmonds blossom
int matching(const M* A){ vector<int> match(n,-1),p(n),base(n); vector<char> used(n),blossom(n); vector<int> q;
  auto lca=[&](int a,int b){ vector<char> u(n,0); while(1){ a=base[a]; u[a]=1; if(match[a]==-1) break; a=p[match[a]]; } while(1){ b=base[b]; if(u[b]) return b; b=p[match[b]]; } };
  auto markPath=[&](int v,int b,int ch){ while(base[v]!=b){ blossom[base[v]]=blossom[base[match[v]]]=1; p[v]=ch; ch=match[v]; v=p[match[v]]; } };
  auto findPath=[&](int root)->int{ fill(used.begin(),used.end(),0); fill(p.begin(),p.end(),-1); for(int i=0;i<n;i++) base[i]=i; used[root]=1; q.assign(1,root); size_t qh=0;
    while(qh<q.size()){ int v=q[qh++]; for(M t=A[v];t;t&=t-1){ int to=__builtin_ctz(t); if(base[v]==base[to]||match[v]==to) continue; if(to==root||(match[to]!=-1&&p[match[to]]!=-1)){ int cb=lca(v,to); fill(blossom.begin(),blossom.end(),0); markPath(v,cb,to); markPath(to,cb,v); for(int i=0;i<n;i++) if(blossom[base[i]]){ base[i]=cb; if(!used[i]){ used[i]=1; q.push_back(i);} } } else if(p[to]==-1){ p[to]=v; if(match[to]==-1) return to; used[match[to]]=1; q.push_back(match[to]); } } } return -1; };
  int res=0; for(int i=0;i<n;i++) if(match[i]==-1){ int v=findPath(i); if(v!=-1){ res++; while(v!=-1){ int pv=p[v],ppv=match[pv]; match[v]=pv; match[pv]=v; v=ppv; } } } return res; }
double score(){ if(!connected()) return -1e9; int gt=gammat(); vector<int> deg(n); int m=0; for(int v=0;v<n;v++){ deg[v]=pc(adj[v]); m+=deg[v]; } m/=2;
  M cadj[32]; for(int v=0;v<n;v++) cadj[v]=ALL&~adj[v]&~(1u<<v);
  if(which=="298"||which=="299"){ vector<int> dd=deg; sort(dd.begin(),dd.end()); int a=0,sm=0; for(int i=0;i<n;i++){ sm+=dd[i]; if(sm<=m) a=i+1; else break; }
    if(which=="298"){ bool c4=false; for(int x=0;x<n&&!c4;x++) for(int y=x+1;y<n;y++) if(pc(adj[x]&adj[y])>=2){c4=true;break;} return gt-(a+(c4?0:1)); }
    int D2=0; for(int v=0;v<n;v++) if(deg[v]==2) D2++; return gt-(a+D2); }
  if(which=="290"||which=="287"){ vector<int> d=deg; int k=0; bool z=false; while(!z){ sort(d.rbegin(),d.rend()); int x=d[0]; d.erase(d.begin()); for(int i=0;i<x&&i<(int)d.size();i++) d[i]--; k++; for(int y:d) if(y==0) z=true; if(d.empty()) break; }
    if(which=="290") return gt-k*(*max_element(deg.begin(),deg.end())); return gt-(k+matching(cadj)); }
  int lc[32],lmax=0,lmin=99; for(int v=0;v<n;v++){ lc[v]=omegaA(adj,cadj[v]); lmax=max(lmax,lc[v]); lmin=min(lmin,lc[v]); } int fmax=0,fmin=0; for(int v=0;v<n;v++){ if(lc[v]==lmax) fmax++; if(lc[v]==lmin) fmin++; }
  if(which=="281") return gt-(fmin+matching(adj));
  if(which=="300") return gt-0.5*(n+fmin);
  if(which=="302"){ int D[32][32]; for(int v=0;v<n;v++){ for(int w=0;w<n;w++) D[v][w]=-1; D[v][v]=0; M seen=1u<<v,fr=seen; int d=0; while(fr){ M nf=openN(fr)&~seen; d++; for(M t=nf;t;t&=t-1) D[v][__builtin_ctz(t)]=d; seen|=nf; fr=nf; } }
    int demin=99; for(int v=0;v<n;v++){ int e=0; for(int w=0;w<n;w++) if(D[v][w]%2==0) e++; demin=min(demin,e); } return gt-(demin+fmax); }
  if(which=="304"){ int nemax=-1; for(int u=0;u<n;u++) for(int v=u+1;v<n;v++) if(!(adj[u]>>v&1)) nemax=max(nemax,pc(cadj[u]|cadj[v])); if(nemax<0) return -1e9; return gt-0.5*(fmax+nemax); }
  return 0; }
int main(int argc,char**argv){ which=argv[1]; n=atoi(argv[2]); long iters=atol(argv[3]); rng.seed(atoi(argv[4])); double p=atof(argv[5]); ALL=(1u<<n)-1;
  for(int v=0;v<n;v++) adj[v]=0; for(int i=1;i<n;i++){ int j=rng()%i; adj[i]|=1u<<j; adj[j]|=1u<<i; } for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if((rng()%1000)/1000.0<p){ adj[i]|=1u<<j; adj[j]|=1u<<i; }
  double cur=score(),best=cur; M bestA[32]; memcpy(bestA,adj,sizeof adj); double T=1.0;
  for(long it=0;it<iters;it++){ int i=rng()%n,j=rng()%n; if(i==j) continue; adj[i]^=1u<<j; adj[j]^=1u<<i; double s=score();
    if(s>=cur || exp((s-cur)/T)>(rng()%1000000)/1e6){ cur=s; if(s>best){best=s; memcpy(bestA,adj,sizeof adj);} } else { adj[i]^=1u<<j; adj[j]^=1u<<i; } T=max(0.05,T*0.9997); }
  memcpy(adj,bestA,sizeof adj); printf("%s n=%d best=%.3f edges:",which.c_str(),n,best); for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if(adj[i]>>j&1) printf(" %d-%d",i,j); printf("\n"); }
