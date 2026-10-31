// Independent finite-certificate verifier for three-uniform Berge-C5 saturation.
// It regenerates every incidence profile itself and does not share code with the search.
// Forbidden cycles are detected by five HYPEREDGES in a cyclic order, their consecutive
// intersections, and an injective assignment of five core vertices to those intersections.
#include <algorithm>
#include <array>
#include <fstream>
#include <iostream>
#include <numeric>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>
using namespace std;
using Edges=vector<array<int,3>>;
int m,minimum,maximum,maxisolates;ifstream input;
long long records=0,dc=0,cc=0,ac=0,sc=0;
struct Cls{int z;vector<int> f;long long seen=0;};
vector<Cls> classes;
vector<int>degrees,high;
void require(bool okay,const char*why){if(!okay)throw runtime_error(why);}
bool member(const array<int,3>&e,int x){return find(e.begin(),e.end(),x)!=e.end();}
bool five_intersections(const Edges&edges,const array<int,5>&order){
 array<array<int,3>,5> common;array<int,5> count={0,0,0,0,0};
 for(int i=0;i<5;++i){for(int x:edges[order[i]])if(member(edges[order[(i+1)%5]],x))common[i][count[i]++]=x;if(count[i]==0)return false;}
 array<int,5> pick;
 auto rec=[&](auto&&self,int i)->bool{
  if(i==5)return true;
  for(int k=0;k<count[i];++k){int x=common[i][k];bool fresh=true;for(int j=0;j<i;++j)if(pick[j]==x)fresh=false;
   if(fresh){pick[i]=x;if(self(self,i+1))return true;}}
  return false;
 };
 return rec(rec,0);
}
bool forbidden(const Edges&edges){
 int q=edges.size();
 for(int a=0;a<q;++a)for(int b=a+1;b<q;++b)for(int c=b+1;c<q;++c)for(int d=c+1;d<q;++d)for(int e=d+1;e<q;++e){
  array<int,4> rest={b,c,d,e};
  do{ if(rest[0]>rest[3])continue; if(five_intersections(edges,{a,rest[0],rest[1],rest[2],rest[3]}))return true;}
  while(next_permutation(rest.begin(),rest.end()));
 }
 return false;
}
Edges rows(const vector<int>&profile,int n){
 Edges edges(m);for(int i=0;i<m;++i){int pos=0;for(int v=0;v<(int)profile.size();++v)if(profile[v]&(1<<i)){require(pos<3,"row with more than three vertices");edges[i][pos++]=v;}require(pos==3,"row without three vertices");}
 (void)n;return edges;
}
bool saturated(const Edges&edges,int n){
 if(forbidden(edges))return false;
 for(int a=0;a<n;++a)for(int b=a+1;b<n;++b)for(int c=b+1;c<n;++c){array<int,3>t={a,b,c};
  bool present=false;for(auto e:edges){sort(e.begin(),e.end());if(e==t)present=true;}if(present)continue;
  auto aug=edges;aug.push_back(t);if(!forbidden(aug))return false;}
 return true;
}
vector<int> canonical(const vector<int>&profile){
 vector<int>p(m);iota(p.begin(),p.end(),0);vector<int>best;
 do{vector<int>f;for(int mask:profile){int out=0;for(int i=0;i<m;++i)if(mask&(1<<i))out|=1<<p[i];f.push_back(out);}sort(f.begin(),f.end());if(best.empty()||f<best)best=f;}while(next_permutation(p.begin(),p.end()));
 return best;
}
void record(const vector<int>&profile,const Edges&edges,int isolates){
 char tag;require(bool(input>>tag),"missing record");int n=profile.size()+isolates;++records;
 if(tag=='D'){
  array<int,3>v;for(int&i:v)require(bool(input>>i)&&i>=0&&i<n,"invalid component vertex");
  vector<int>component(n,-1);int label=0;
  for(int s=0;s<n;++s)if(component[s]<0){vector<int>queue={s};component[s]=label;for(size_t k=0;k<queue.size();++k)for(auto e:edges)if(member(e,queue[k]))for(int w:e)if(component[w]<0){component[w]=label;queue.push_back(w);}++label;}
  require(component[v[0]]!=component[v[1]]&&component[v[0]]!=component[v[2]]&&component[v[1]]!=component[v[2]],"component certificate false");++dc;
 }else if(tag=='C'){
  array<int,5>v,e;for(int&i:v)require(bool(input>>i)&&i>=0&&i<n,"invalid cycle vertex");for(int&i:e)require(bool(input>>i)&&i>=0&&i<m,"invalid cycle edge");
  require(set<int>(v.begin(),v.end()).size()==5&&set<int>(e.begin(),e.end()).size()==5,"cycle assignment not injective");
  for(int i=0;i<5;++i)require(member(edges[e[i]],v[i])&&member(edges[e[i]],v[(i+1)%5]),"unsupported cycle pair");++cc;
 }else if(tag=='A'){
  array<int,3>t;for(int&i:t)require(bool(input>>i)&&i>=0&&i<n,"invalid added triple");
  sort(t.begin(),t.end());require(t[0]<t[1]&&t[1]<t[2],"repeated added vertex");
  for(auto e:edges){sort(e.begin(),e.end());require(e!=t,"added triple already present");}
  auto augmented=edges;augmented.push_back(t);require(!forbidden(augmented),"claimed free augmentation has a cycle");++ac;
 }else if(tag=='S'){
  int id;require(bool(input>>id)&&id>=1&&id<=(int)classes.size(),"invalid class index");
  require(classes[id-1].z==isolates&&classes[id-1].f==canonical(profile),"survivor not isomorphic to its class");
  ++classes[id-1].seen;++sc;
 }else throw runtime_error("certificate does not exclude saturation");
}
void enumerate(int firstmask,int nonisolated){
 if(nonisolated+maxisolates<minimum)return;
 vector<int>p=high;for(int i=0;i<m;++i)for(int k=degrees[i];k<3;++k)p.push_back(1<<i);
 Edges edges=rows(p,p.size());
 set<array<int,3>> distinct;for(auto e:edges){sort(e.begin(),e.end());distinct.insert(e);}
 if(distinct.size()==(size_t)m)for(int z=0;z<=maxisolates;++z)if((int)p.size()+z>=minimum&&(int)p.size()+z<=maximum)record(p,edges,z);
 int fullrows=0;for(int i=0;i<m;++i)if(degrees[i]==3)fullrows|=1<<i;
 for(int mask=firstmask;mask<(1<<m);++mask){if(mask&fullrows)continue;int count=__builtin_popcount((unsigned)mask);
  if(count<2||nonisolated-count+1+maxisolates<minimum)continue;
  for(int bits=mask;bits;bits&=bits-1)++degrees[__builtin_ctz((unsigned)bits)];high.push_back(mask);enumerate(mask,nonisolated-count+1);high.pop_back();for(int bits=mask;bits;bits&=bits-1)--degrees[__builtin_ctz((unsigned)bits)];
 }
}
int main(int argc,char**argv){try{
 require(argc==6||argc==7,"usage: verify_profiles m min_n max_n max_isolates certificate [classes]");
 m=stoi(argv[1]);minimum=stoi(argv[2]);maximum=stoi(argv[3]);maxisolates=stoi(argv[4]);
 require(m>=1&&m<=8&&maxisolates>=0&&maxisolates<=1&&maximum<=3*m+maxisolates,"unsupported range");
 if(argc==7){ifstream cl(argv[6]);require(bool(cl),"cannot open class list");int z,k;
  while(cl>>z>>k){require(z>=0&&z<=1&&k>0,"bad class header");Cls c;c.z=z;c.f.resize(k);for(int&i:c.f)require(bool(cl>>i),"truncated class");
   require(c.f==canonical(c.f),"class not in canonical form");
   for(const auto&o:classes)require(!(o.z==c.z&&o.f==c.f),"duplicate class");
   Edges edges=rows(c.f,k);require(saturated(edges,k+z),"listed class is not Berge-C5-saturated");
   classes.push_back(c);}}
 input.open(argv[5]);require(bool(input),"cannot open certificate");
 string magic;int a,b,c,d;require(bool(input>>magic>>a>>b>>c>>d)&&magic=="COMPACT"&&a==m&&b==minimum&&c==maximum&&d==maxisolates,"invalid header");
 degrees.assign(m,0);enumerate(1,3*m);string extra;require(!(input>>extra),"surplus certificate records");
 for(const auto&cl:classes)require(cl.seen>0,"listed class never occurs");
 cout<<"{\"passed\":true,\"m\":"<<m<<",\"min_n\":"<<minimum<<",\"max_n\":"<<maximum<<",\"max_isolates\":"<<maxisolates<<",\"records\":"<<records<<",\"component_certificates\":"<<dc<<",\"cycle_certificates\":"<<cc<<",\"free_augmentations\":"<<ac<<",\"accepted_survivors\":"<<sc<<",\"classes\":"<<classes.size()<<"}\n";return 0;
 }catch(const exception&e){cerr<<"FAIL at record "<<records<<": "<<e.what()<<'\n';return 1;}}
