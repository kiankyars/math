// Read graphs as edge lists: "n m" then m lines "u v"; multiple graphs, each preceded by a name line "# name".
// Report C4, rad, diam, avg l, threshold, best induced path found (DFS with node limit).
#include <bits/stdc++.h>
using namespace std;
const int MX=1024; typedef bitset<MX> B;
int n; vector<B> adj; int best; long nodes, LIM; int target;
void dfs(int v,const B& used,const B& forbid,int len){ if(len>best) best=len; if(best>=target) return; if(++nodes>LIM) return;
  B cand=adj[v]&~used&~forbid; B f2=forbid|adj[v]; f2.set(v);
  for(int w=cand._Find_first(); w<MX; w=cand._Find_next(w)){ B u2=used; u2.set(w); dfs(w,u2,f2,len+1); if(nodes>LIM||best>=target) return; } }
int alphaSet(vector<int> vs){ // small brute force max independent set among vs
  int k=vs.size(); if(k==0) return 0; int v=vs[0]; vector<int> r1,r2; for(int i=1;i<k;i++){ r2.push_back(vs[i]); if(!adj[v][vs[i]]) r1.push_back(vs[i]); }
  int a=1+alphaSet(r1); if((int)r1.size()==k-1) return a; return max(a,alphaSet(r2)); }
int main(int argc,char**argv){ LIM=argc>1?atol(argv[1]):50000000; string name; 
  while(true){ string line; if(!getline(cin,line)) break; if(line.empty()) continue; if(line[0]=='#'){ name=line.substr(2); continue; }
    int m; { stringstream ss(line); ss>>n>>m; } adj.assign(n,B());
    for(int i=0;i<m;i++){ int a,b; cin>>a>>b; adj[a].set(b); adj[b].set(a);} getline(cin,line);
    bool c4=false; for(int i=0;i<n&&!c4;i++)for(int j=i+1;j<n;j++) if((adj[i]&adj[j]).count()>=2){c4=true;break;}
    int rad=1e9,diam=0; for(int s=0;s<n;s++){ vector<int> d(n,-1); d[s]=0; deque<int> Q{s}; int mx=0; while(!Q.empty()){int x=Q.front();Q.pop_front(); for(int y=adj[x]._Find_first();y<MX;y=adj[x]._Find_next(y)) if(d[y]<0){d[y]=d[x]+1;mx=max(mx,d[y]);Q.push_back(y);} } rad=min(rad,mx); diam=max(diam,mx);} 
    long suml=0; for(int v=0;v<n;v++){ vector<int> vs; for(int y=adj[v]._Find_first();y<MX;y=adj[v]._Find_next(y)) vs.push_back(y); suml+=alphaSet(vs);} 
    double thr= c4? rad+1 : rad+(double)suml/n; target=(int)ceil(thr-1e-9)+0; // stop once threshold reached? search a bit beyond
    int stopAt=argc>2? target+atoi(argv[2]) : 1<<30; target=stopAt;
    best=0; nodes=0; for(int s=0;s<n&&nodes<=LIM&&best<target;s++){ B u; u.set(s); dfs(s,u,B(),1);} 
    printf("%-28s n=%d C4=%d rad=%d diam=%d avgl=%.3f thr=%.3f path>=%d %s slack>=%.3f\n",name.c_str(),n,c4,rad,diam,(double)suml/n,thr,best,(nodes>LIM||best>=target)?"(partial)":"(exact)",best-thr); fflush(stdout);
  }
}
