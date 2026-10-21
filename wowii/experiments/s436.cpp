#include <bits/stdc++.h>
using namespace std; typedef unsigned M; int n; M adj[32]; M ALL;
inline int pc(M x){ return __builtin_popcount(x); }
M openN(M S){ M r=0; for(M t=S;t;t&=t-1) r|=adj[__builtin_ctz(t)]; return r; }
M closedN(M S){ return S|openN(S); }
int bestA2; void recA2(M S, M C){ int s=pc(S); if(s>bestA2) bestA2=s; if(s+pc(C)<=bestA2||!C) return; int v=__builtin_ctz(C); M C2=C&~(1u<<v); M S2=S|(1u<<v); M full=0; for(M t=S2;t;t&=t-1){ int x=__builtin_ctz(t); if(adj[x]&S2) full|=1u<<x; } M nc=0; for(M t=C2;t;t&=t-1){ int w=__builtin_ctz(t); M nw=adj[w]&S2; if(pc(nw)>=2||(nw&full)) continue; nc|=1u<<w; } recA2(S2,nc); recA2(S,C2); }
int alpha2(){ bestA2=0; recA2(0,ALL); return bestA2; }
int h; M hadj[8];
long cnt=0, tested=0; int worst=-99;
void evalG(){ ALL=(n==32)?~0u:((1u<<n)-1); vector<int> deg(n); for(int v=0;v<n;v++) deg[v]=pc(adj[v]);
  vector<int> d=deg; sort(d.rbegin(),d.rend()); int k=0; { vector<int> L=d; int step=0; while(true){ bool z=false; for(int x:L) if(x==0) z=true; if(z||L.empty()){ k=step; break; } int x=L[0]; L.erase(L.begin()); for(int i=0;i<x&&i<(int)L.size();i++) L[i]--; sort(L.rbegin(),L.rend()); step++; } }
  if(k!=1) return;
  M Dd=0; for(int v=0;v<n;v++) for(int u=0;u<n;u++) if(u!=v && ((closedN(1u<<u)&~closedN(1u<<v))==0)) { Dd|=1u<<v; break; }
  for(M t=Dd;t;t&=t-1) if(adj[__builtin_ctz(t)]&Dd) return;
  vector<int> cd(n); for(int v=0;v<n;v++) cd[v]=n-1-deg[v]; sort(cd.rbegin(),cd.rend()); int WP=0; for(int i=0;i<n;i++) WP=max(WP,min(cd[i]+1,i+1));
  int a=alpha2(); tested++; int sc=a-WP; if(sc>worst){ worst=sc; } if(sc>0){ cnt++; if(cnt<=5){ printf("CE n=%d a2=%d WP=%d edges:",n,a,WP); for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if(adj[i]>>j&1) printf(" %d-%d",i,j); printf("\n"); } } }
int main(int argc,char**argv){ int maxLeaf=atoi(argv[1]); string s; while(getline(cin,s)){ int p=0; h=s[p++]-63; for(int i=0;i<h;i++) hadj[i]=0; int val=0,kk=6; for(int j=1;j<h;j++) for(int i=0;i<j;i++){ if(kk==6){ val=s[p++]-63; kk=0;} if(val>>(5-kk)&1){ hadj[i]|=1u<<j; hadj[j]|=1u<<i;} kk++; }
    for(M Sup=1;Sup<(1u<<h);Sup++){ bool ind=true; for(M t=Sup;t;t&=t-1) if(hadj[__builtin_ctz(t)]&Sup) ind=false; if(!ind) continue;
      // non-support H vertices need H-degree>=2
      bool ok=true; for(int v=0;v<h;v++) if(!(Sup>>v&1) && pc(hadj[v])<2) ok=false; if(!ok) continue;
      vector<int> sv; for(M t=Sup;t;t&=t-1) sv.push_back(__builtin_ctz(t)); int m=sv.size(); vector<int> c(m,1);
      while(true){ int tot=h; for(int x:c) tot+=x; if(tot<=31){ n=tot; for(int i=0;i<h;i++) adj[i]=hadj[i]; int idx=h; for(int i=0;i<m;i++) for(int j=0;j<c[i];j++){ adj[idx]=1u<<sv[i]; adj[sv[i]]|=1u<<idx; idx++; } evalG(); }
        int i=0; while(i<m && c[i]==maxLeaf){ c[i]=1; i++; } if(i==m) break; c[i]++; } } }
  printf("tested=%ld ce=%ld worst=%d\n",tested,cnt,worst); }
