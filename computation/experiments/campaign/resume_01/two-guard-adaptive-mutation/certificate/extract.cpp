// Same fixed minimum-two/unit-deficit counterexample only; existing cutoff DAG extractor.
#include "../../../../seven_pairs/slots.hpp"
#include <functional>
#include <iostream>
#include <map>
#include <sys/resource.h>
struct Edge{int pick,child,child_value;bool switches;};
struct Node{int id,mask,deficit,value,card;bool terminal,alias;std::vector<Edge>edges;};
static std::string labels(const ExactSlots&v,int m){std::string z;for(int x:v.xs)if(m&v.bit(x))z+=std::to_string(x)+",";return z.empty()?"empty":z;}
int main(int argc,char**argv){auto start=std::chrono::steady_clock::now();try{
 const int cutoff=argc>1?std::stoi(argv[1]):7;if(cutoff<5||cutoff>7)throw std::runtime_error("unsupported cutoff"); std::vector<int>S={2,4,7,13,15,19,35,36,50,57,60,99};ExactSlots v(S,1);std::map<std::pair<int,int>,int>ids;std::vector<Node>nodes;

 std::function<int(int,int)>visit=[&](int m,int d){auto key=std::make_pair(m,d);if(ids.count(key))return ids.at(key);int value=v.value(m,d),card=__builtin_popcount((unsigned)m);bool alias=false;Node n{0,m,d,value,card,m==0||v.sums[m]<d,alias,{}};
  if(alias&&value!=-1)throw std::runtime_error("alias is not expected LOSS");
  if(card>cutoff&&!n.terminal&&!alias){for(int x:v.xs)if(m&v.bit(x)){int cm=m^v.bit(x),cd=std::abs(x-d),cv=v.value(cm,cd),move=x>=d?-cv:cv;if(value==1&&move!=1)continue;if(value==-1&&move!=-1)throw std::runtime_error("loss has nonloss move");int child=visit(cm,cd);n.edges.push_back({x,child,cv,x>=d});if(value==1)break;}
   if(value==0||n.edges.empty()||(value==-1&&(int)n.edges.size()!=card))throw std::runtime_error("unexpected proof node");}
  n.id=(int)nodes.size()+1;nodes.push_back(n);ids.emplace(key,n.id);return n.id;};
 int root=visit(v.full,1);if(nodes[root-1].value!=-1)throw std::runtime_error("root is not LOSS");
 unsigned leaves=0,aliases=0,edges=0;for(const auto&n:nodes){leaves+=n.edges.empty()&&!n.alias;aliases+=n.alias;edges+=n.edges.size();std::cout<<"NODE id "<<n.id<<" deficit "<<n.deficit<<" value "<<n.value<<" card "<<n.card<<" kind "<<(n.alias?"alias":n.edges.empty()?"leaf":(n.value==1?"win":"loss"))<<" terminal "<<n.terminal<<" remaining "<<labels(v,n.mask)<<'\n';for(const auto&e:n.edges)std::cout<<"EDGE parent "<<n.id<<" pick "<<e.pick<<" switches "<<e.switches<<" child "<<e.child<<" child_value "<<e.child_value<<'\n';}
 std::cout<<"ROOT label G1 node "<<root<<" value -1\n";rusage u{};getrusage(RUSAGE_SELF,&u);std::cout<<"CERTIFICATE_DATA_COMPLETE cutoff "+std::to_string(cutoff)+" nodes "<<nodes.size()<<" leaves "<<leaves<<" aliases "<<aliases<<" edges "<<edges<<" slot_states "<<v.states<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<" max_rss_bytes "<<u.ru_maxrss<<'\n';
 }catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 2;}return 0;}
