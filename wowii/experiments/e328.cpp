#include <bits/stdc++.h>
using namespace std; typedef unsigned M; int n; M adj[32]; M ALL;
inline int pc(M x){ return __builtin_popcount(x); }
void parse(const string& s){ int p=0; n=s[p++]-63; for(int i=0;i<n;i++) adj[i]=0; int val=0,k=6;
  for(int j=1;j<n;j++) for(int i=0;i<j;i++){ if(k==6){ val=s[p++]-63; k=0;} if(val>>(5-k)&1){ adj[i]|=1u<<j; adj[j]|=1u<<i;} k++; } }
M openN(M S){ M r=0; for(M t=S;t;t&=t-1) r|=adj[__builtin_ctz(t)]; return r; }
int matchA(const M* A, M m){ if(!m) return 0; int v=__builtin_ctz(m); M rest=m&~(1u<<v); int best=matchA(A,rest); for(M t=A[v]&rest;t;t&=t-1){ int w=__builtin_ctz(t); best=max(best,1+matchA(A,rest&~(1u<<w))); if(best*2>=pc(m)) break; } return best; }
int main(){ string s; long cnt=0; while(getline(cin,s)){ parse(s); ALL=(1u<<n)-1; M cadj[32]; for(int v=0;v<n;v++) cadj[v]=ALL&~adj[v]&~(1u<<v);
  vector<int> k4(n); for(int v=0;v<n;v++){ int c=0; M N=adj[v]; for(M t=N;t;t&=t-1){ int a=__builtin_ctz(t); for(M u=N&adj[a]&~((2u<<a)-1);u;u&=u-1){ int b=__builtin_ctz(u); c+=pc(N&adj[a]&adj[b]&~((2u<<b)-1)); } } k4[v]=c; }
  int km=*max_element(k4.begin(),k4.end()); int f=0; for(int v=0;v<n;v++) if(k4[v]==km) f++;
  if(4*matchA(cadj,ALL)>f) continue;
  set<int> sz; for(M S=1;S<=ALL;S++){ if(openN(S)==ALL){ bool minimal=true; for(M t=S;t;t&=t-1){ if(openN(S&~(t&-t))==ALL){minimal=false;break;} } if(minimal) sz.insert(pc(S)); } if(S==ALL) break; }
  if(sz.size()>1){ cnt++; if(cnt<=5){ printf("%s m=%d km=%d f=%d sizes:",s.c_str(),pc(0),km,f); for(int x:sz) printf(" %d",x); printf(" edges:"); for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if(adj[i]>>j&1) printf(" %d-%d",i,j); printf("\n"); } } }
  printf("count=%ld\n",cnt); }
