// Polarity graph ER_q (q prime): vertices = points of PG(2,q), x~y iff x.y=0 (x != y).
// Compute rad, avg l, and search induced path (DFS with time limit); report vs threshold rad+avg l.
#include <bits/stdc++.h>
using namespace std;
int n; vector<vector<int>> A; vector<bitset<512>> adj;
int best; long nodes; long LIM;
void dfs(int v, bitset<512>& used, bitset<512>& forbid, int len, vector<int>& path, vector<int>& bestPath){
  if(len>best){ best=len; bestPath=path; }
  if(++nodes>LIM) return;
  bitset<512> cand=adj[v]&~used&~forbid;
  for(int w=cand._Find_first(); w<512; w=cand._Find_next(w)){
    bitset<512> u2=used; u2.set(w); bitset<512> f2=forbid|adj[v]; f2.set(v);
    path.push_back(w); dfs(w,u2,f2,len+1,path,bestPath); path.pop_back(); if(nodes>LIM) return; }
}
int main(int argc,char**argv){ int q=atoi(argv[1]); LIM=argc>2?atol(argv[2]):100000000;
  vector<array<int,3>> P; for(int a=0;a<q;a++)for(int b=0;b<q;b++)for(int c=0;c<q;c++){ if(a==0&&b==0&&c==0) continue; int f = a?a:(b?b:c); if(f!=1) continue; P.push_back({a,b,c}); }
  n=P.size(); adj.assign(n,{});
  for(int i=0;i<n;i++)for(int j=0;j<n;j++) if(i!=j){ int d=(P[i][0]*P[j][0]+P[i][1]*P[j][1]+P[i][2]*P[j][2])%q; if(d==0) adj[i].set(j); }
  // C4 check
  bool c4=false; for(int i=0;i<n;i++)for(int j=i+1;j<n;j++) if((adj[i]&adj[j]).count()>=2) c4=true;
  // ecc
  int rad=1e9; for(int s=0;s<n;s++){ vector<int> d(n,-1); d[s]=0; queue<int> Q; Q.push(s); int mx=0; while(!Q.empty()){int x=Q.front();Q.pop(); for(int y=0;y<n;y++) if(adj[x][y]&&d[y]<0){d[y]=d[x]+1; mx=max(mx,d[y]); Q.push(y);} } rad=min(rad,mx); }
  // l(v): N(v) induces matching (C4-free) -> l = deg - edges in N(v)
  long suml=0; for(int v=0;v<n;v++){ int deg=adj[v].count(); int e=0; for(int x=0;x<n;x++) if(adj[v][x]) e+=(adj[x]&adj[v]).count(); suml+=deg-e/2; }
  double thr=rad+(double)suml/n;
  printf("q=%d n=%d C4=%d rad=%d avgl=%.4f threshold=%.4f need path>=%d\n",q,n,c4,rad,(double)suml/n,thr,(int)ceil(thr-1e-9));
  best=0; vector<int> path, bestPath; nodes=0;
  for(int s=0;s<n && nodes<=LIM;s++){ bitset<512> u; u.set(s); bitset<512> f; path={s}; dfs(s,u,f,1,path,bestPath); }
  printf("best induced path found=%d (nodes=%ld, %s)\n",best,nodes,nodes>LIM?"truncated":"exhaustive");
  for(int x:bestPath) printf("%d ",x); printf("\n");
}
