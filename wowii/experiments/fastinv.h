// fast exact invariants by branch and bound; requires n, adj[], ALL, pc, openN, closedN, connM
int bestB; void recB(int v, M C0, M C1, int cnt){ if(cnt+(n-v)<=bestB) return; if(v==n){ bestB=cnt; return; }
  if(!(adj[v]&C0)) recB(v+1,C0|(1u<<v),C1,cnt+1); if(C0 && !(adj[v]&C1)) recB(v+1,C0,C1|(1u<<v),cnt+1); recB(v+1,C0,C1,cnt); }
int bipB(){ bestB=0; recB(0,0,0,0); return bestB; }
// max induced tree: S current tree, cand = vertices adjacent to exactly one of S and not excluded
int bestTr; void recTr(M S, M X){ int s=pc(S); if(s>bestTr) bestTr=s; M fr=openN(S)&~S&~X; M cand=0; for(M t=fr;t;t&=t-1){ int w=__builtin_ctz(t); if(pc(adj[w]&S)==1) cand|=1u<<w; }
  // upper bound: s + vertices reachable via non-excluded non-S vertices
  M avail=ALL&~X&~S; M reach=cand, f=cand; while(f){ M nf=openN(f)&avail&~reach; reach|=nf; f=nf; } if(s+pc(reach)<=bestTr) return; if(!cand) return;
  int w=__builtin_ctz(cand); recTr(S|(1u<<w),X); recTr(S,X|(1u<<w)); }
int treeN(){ bestTr=1; for(int v=0;v<n;v++){ M X=(1u<<v)-1; recTr(1u<<v,X); } return bestTr; }
// connected domination number via B&B on include/exclude in vertex order
int bestC; void recC(int v, M S, M X){ if(pc(S)>=bestC) return;
  // infeasible if some vertex has closed nbhd fully excluded
  for(int u=0;u<n;u++){ M cn=adj[u]|(1u<<u); if((cn&X)==cn) return; }
  if(closedN(S)==ALL && connM(S) && S){ bestC=pc(S); return; }
  if(v==n) return;
  recC(v+1,S|(1u<<v),X); recC(v+1,S,X|(1u<<v)); }
int gammaC(){ bestC=n; recC(0,0,0); return bestC; }
int Ls(){ if(n<=2) return n-1; int g=gammaC(); return n-g; }
