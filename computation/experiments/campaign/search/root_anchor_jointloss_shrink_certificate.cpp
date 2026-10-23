// Export only proof obligations inside the finalized witness, using the frozen recurrence.
#include "../../seven_pairs/slots.hpp"
#include <iostream>
#include <map>
#include <functional>
#include <sys/resource.h>
struct Edge{int pick,child,child_value;bool switches;};
struct Node{int id,mask,deficit,value,card;bool terminal;std::vector<Edge>edges;};
static std::string labels(const ExactSlots&v,int m){std::string z;for(int x:v.xs)if(m&v.bit(x))z+=std::to_string(x)+",";return z.empty()?"empty":z;}
int main(){auto start=std::chrono::steady_clock::now();try{
 ExactSlots v({2,3,4,7,18,33,35,36,52,56,62,74,100},8);std::map<std::pair<int,int>,int>ids;std::vector<Node>nodes;
 std::function<int(int,int)>visit=[&](int m,int d){auto key=std::make_pair(m,d);if(ids.count(key))return ids.at(key);int value=v.value(m,d),card=__builtin_popcount((unsigned)m);Node n{0,m,d,value,card,m==0||v.sums[m]<d,{}};
  if(card>8){for(int x:v.xs)if(m&v.bit(x)){int childmask=m^v.bit(x),cd=std::abs(x-d),cv=v.value(childmask,cd),move=x>=d?-cv:cv;if(value==1 && move!=1)continue;if(value==-1 && move!=-1)throw std::runtime_error("loss node has nonloss move");int child=visit(childmask,cd);n.edges.push_back({x,child,cv,x>=d});if(value==1)break;}
   if(value==0 || n.edges.empty() || (value==-1 && (int)n.edges.size()!=card))throw std::runtime_error("unexpected proof node");}
  n.id=(int)nodes.size()+1;nodes.push_back(n);ids.emplace(key,n.id);return n.id;};
 int E=v.full^v.bit(2)^v.bit(3);int r1=visit(E,1),r3=visit(E,3),r8=visit(v.full,8);if(nodes[r1-1].value!=-1||nodes[r3-1].value!=-1||nodes[r8-1].value!=1)throw std::runtime_error("root value mismatch");
 unsigned leaves=0,edges=0;for(const auto&n:nodes){leaves+=n.edges.empty();edges+=n.edges.size();std::cout<<"NODE id "<<n.id<<" deficit "<<n.deficit<<" value "<<n.value<<" card "<<n.card<<" kind "<<(n.edges.empty()?"leaf":(n.value==1?"win":"loss"))<<" terminal "<<n.terminal<<" remaining "<<labels(v,n.mask)<<'\n';for(const auto&e:n.edges)std::cout<<"EDGE parent "<<n.id<<" pick "<<e.pick<<" switches "<<e.switches<<" child "<<e.child<<" child_value "<<e.child_value<<'\n';}
 std::cout<<"ROOT label E1 node "<<r1<<" value -1\nROOT label E3 node "<<r3<<" value -1\nROOT label C8 node "<<r8<<" value 1\n";
 rusage u{};getrusage(RUSAGE_SELF,&u);std::cout<<"CERTIFICATE_DATA_COMPLETE cutoff 8 nodes "<<nodes.size()<<" leaves "<<leaves<<" edges "<<edges<<" slot_states "<<v.states<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<" max_rss_bytes "<<u.ru_maxrss<<'\n';
 }catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 2;}}
