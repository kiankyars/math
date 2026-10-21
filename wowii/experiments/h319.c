// read graph6, test 319 hypothesis: dist_even(v) constant k and gamma == k; print graphs
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
int n; unsigned adj[32];
int parse(char*s){ int p=0; n=s[p++]-63; for(int i=0;i<n;i++)adj[i]=0; int val=0,k=6; for(int j=1;j<n;j++)for(int i=0;i<j;i++){ if(k==6){val=s[p++]-63;k=0;} if(val>>(5-k)&1){adj[i]|=1u<<j;adj[j]|=1u<<i;} k++;} return n;}
int best; unsigned ALL;
void dom(unsigned S, unsigned covered, int sz, int start){
  if(sz>=best) return;
  if(covered==ALL){ best=sz; return; }
  // pick lowest uncovered vertex u; one of N[u] must be in S
  int u=__builtin_ctz(~covered & ALL);
  unsigned cand=adj[u]|(1u<<u);
  for(unsigned t=cand;t;t&=t-1){ int w=__builtin_ctz(t); dom(S|(1u<<w), covered|adj[w]|(1u<<w), sz+1, 0); }
}
int main(){ char s[256]; long cnt=0;
  while(fgets(s,sizeof s,stdin)){ s[strcspn(s,"\n")]=0; parse(s); ALL=(n==32)?~0u:((1u<<n)-1);
    int k=-1, ok=1;
    for(int v=0;v<n&&ok;v++){ unsigned seen=1u<<v, fr=1u<<v; int d=0, ev=1;
      while(fr){ unsigned nf=0; for(unsigned t=fr;t;t&=t-1) nf|=adj[__builtin_ctz(t)]; nf&=~seen; seen|=nf; fr=nf; d++; if(d%2==0) ev+=__builtin_popcount(nf); }
      if(k<0)k=ev; else if(k!=ev) ok=0; }
    if(!ok) continue;
    best=n+1; dom(0,0,0,0);
    if(best==k){ cnt++; printf("%s n=%d k=%d\n", s, n, k); }
  }
  fprintf(stderr,"count %ld\n",cnt); }
