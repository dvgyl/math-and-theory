// Independent finite-certificate verifier. Does not share code with search.
// Forbidden cycles are detected by four HYPEREDGES, cyclic intersections,
// and an injective assignment of four core vertices to those intersections.
#include <algorithm>
#include <array>
#include <fstream>
#include <iostream>
#include <numeric>
#include <set>
#include <stdexcept>
#include <vector>
using namespace std;
int m,minimum,maximum,maxisolates;ifstream input;long long records=0,dc=0,cc=0,ac=0,sc=0;bool compact=false;
vector<pair<int,vector<int>>> accepted_classes;
vector<int>degrees,high;
void require(bool okay,const char*why){if(!okay)throw runtime_error(why);}
bool member(const array<int,3>&e,int x){return find(e.begin(),e.end(),x)!=e.end();}
bool four_intersections(const vector<array<int,3>>&edges,const array<int,4>&order){
 array<array<int,3>,4> common;array<int,4> count={0,0,0,0};
 for(int i=0;i<4;++i){for(int x:edges[order[i]])if(member(edges[order[(i+1)%4]],x))common[i][count[i]++]=x;if(count[i]==0)return false;}
 for(int ia=0;ia<count[0];++ia)for(int ib=0;ib<count[1];++ib){int a=common[0][ia],b=common[1][ib];if(a==b)continue;
  for(int ic=0;ic<count[2];++ic){int c=common[2][ic];if(c==a||c==b)continue;for(int id=0;id<count[3];++id){int d=common[3][id];if(d!=a&&d!=b&&d!=c)return true;}}}
 return false;
}
bool forbidden(const vector<array<int,3>>&edges){
 int q=edges.size();for(int a=0;a<q;++a)for(int b=a+1;b<q;++b)for(int c=b+1;c<q;++c)for(int d=c+1;d<q;++d)
  if(four_intersections(edges,{a,b,c,d})||four_intersections(edges,{a,b,d,c})||four_intersections(edges,{a,c,b,d}))return true;
 return false;
}
void record(const vector<int>&profile,const vector<array<int,3>>&edges,int isolates){
 int z=isolates,n0=profile.size();if(!compact){require(bool(input>>z>>n0),"missing certificate record");require(z==isolates&&n0==(int)profile.size(),"profile order or size mismatch");
 for(int a:profile){int b;require(bool(input>>b)&&a==b,"incidence profile mismatch");}}
 char tag;require(bool(input>>tag),"missing status");int n=n0+isolates;++records;
 if(tag=='D'){
  array<int,3>v;for(int&i:v)require(bool(input>>i)&&i>=0&&i<n,"invalid component vertex");
  vector<int>component(n,-1);int label=0;
  for(int s=0;s<n;++s)if(component[s]<0){vector<int>queue={s};component[s]=label;for(size_t k=0;k<queue.size();++k)for(auto e:edges)if(member(e,queue[k]))for(int w:e)if(component[w]<0){component[w]=label;queue.push_back(w);}++label;}
  require(component[v[0]]!=component[v[1]]&&component[v[0]]!=component[v[2]]&&component[v[1]]!=component[v[2]],"component certificate false");++dc;
 }else if(tag=='C'){
  array<int,4>v,e;for(int&i:v)require(bool(input>>i)&&i>=0&&i<n,"invalid cycle vertex");for(int&i:e)require(bool(input>>i)&&i>=0&&i<m,"invalid cycle edge");
  require(set<int>(v.begin(),v.end()).size()==4&&set<int>(e.begin(),e.end()).size()==4,"cycle assignment not injective");
  for(int i=0;i<4;++i)require(member(edges[e[i]],v[i])&&member(edges[e[i]],v[(i+1)%4]),"unsupported cycle pair");++cc;
 }else if(tag=='A'){
  array<int,3>t;for(int&i:t)require(bool(input>>i)&&i>=0&&i<n,"invalid added triple");
  sort(t.begin(),t.end());require(t[0]<t[1]&&t[1]<t[2],"repeated added vertex");require(find(edges.begin(),edges.end(),t)==edges.end(),"added triple already present");
  auto augmented=edges;augmented.push_back(t);require(!forbidden(augmented),"claimed free augmentation has a cycle");++ac;
 }else if(tag=='S'){
  bool matched=false;vector<int>p(m);iota(p.begin(),p.end(),0);
  do{vector<int>f;for(int mask:profile){int out=0;for(int i=0;i<m;++i)if(mask&(1<<i))out|=1<<p[i];f.push_back(out);}sort(f.begin(),f.end());
   for(const auto&entry:accepted_classes)if(entry.first==isolates&&entry.second==f){matched=true;break;}
   if(matched)break;
  }while(next_permutation(p.begin(),p.end()));
  require(matched,"survivor not isomorphic to an accepted class");++sc;
 }else throw runtime_error("certificate does not exclude saturation");
}
void enumerate(int firstmask,int nonisolated){
 if(nonisolated+maxisolates<minimum)return;
 vector<int>p=high;for(int i=0;i<m;++i)for(int k=degrees[i];k<3;++k)p.push_back(1<<i);
 vector<array<int,3>>edges(m);for(int i=0;i<m;++i){int pos=0;for(int v=0;v<(int)p.size();++v)if(p[v]&(1<<i))edges[i][pos++]=v;require(pos==3,"internal capacity error");}
 if(set<array<int,3>>(edges.begin(),edges.end()).size()==(size_t)m)for(int z=0;z<=maxisolates;++z)if((int)p.size()+z>=minimum&&(int)p.size()+z<=maximum)record(p,edges,z);
 int fullrows=0;for(int i=0;i<m;++i)if(degrees[i]==3)fullrows|=1<<i;
 for(int mask=firstmask;mask<(1<<m);++mask){if(mask&fullrows)continue;int count=__builtin_popcount((unsigned)mask);
  if(count<2||nonisolated-count+1+maxisolates<minimum)continue;
  for(int bits=mask;bits;bits&=bits-1)++degrees[__builtin_ctz((unsigned)bits)];high.push_back(mask);enumerate(mask,nonisolated-count+1);high.pop_back();for(int bits=mask;bits;bits&=bits-1)--degrees[__builtin_ctz((unsigned)bits)];
 }
}
int main(int argc,char**argv){try{
 require(argc==6||argc==7,"usage: verify_profiles m min_n max_n max_isolates certificate [accepted_classes]");m=stoi(argv[1]);minimum=stoi(argv[2]);maximum=stoi(argv[3]);maxisolates=stoi(argv[4]);
 if(argc==7){ifstream cl(argv[6]);require(bool(cl),"cannot open accepted class list");int z,n;while(cl>>z>>n){require(z>=0&&n>=0,"bad class size");vector<int>f(n);for(int&i:f)require(bool(cl>>i),"truncated class");sort(f.begin(),f.end());accepted_classes.push_back({z,f});}}
 input.open(argv[5]);require(bool(input),"cannot open input");if(input.peek()=='C'){string magic;int a,b,c,d;input>>magic>>a>>b>>c>>d;require(magic=="COMPACT"&&a==m&&b==minimum&&c==maximum&&d==maxisolates,"invalid compact header");compact=true;}degrees.assign(m,0);enumerate(1,3*m);string extra;require(!(input>>extra),"surplus certificate records");
 cout<<"{\"passed\":true,\"m\":"<<m<<",\"min_n\":"<<minimum<<",\"max_n\":"<<maximum<<",\"max_isolates\":"<<maxisolates<<",\"records\":"<<records<<",\"component_certificates\":"<<dc<<",\"cycle_certificates\":"<<cc<<",\"free_augmentations\":"<<ac<<",\"accepted_survivors\":"<<sc<<"}\n";return 0;
 }catch(const exception&e){cerr<<"FAIL at record "<<records<<": "<<e.what()<<'\n';return 1;}}
