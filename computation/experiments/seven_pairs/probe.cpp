#include "slots.hpp"
#include <fstream>
#include <iostream>
#include <sstream>
int main(int argc,char**argv){
 if(argc!=3)return 2;std::ifstream in(argv[1]);std::ofstream out(argv[2]);
 if(!in || !out)return 3;
 std::string line;int shapes=0;std::uint64_t states=0;auto t=std::chrono::steady_clock::now();
 while(std::getline(in,line)){
  if(std::chrono::duration<double>(std::chrono::steady_clock::now()-t).count()>20){
   std::cout<<"TIME_LIMIT completed "<<shapes<<"\n";return 4;}
  std::istringstream row(line);std::vector<int> starts,labels;int x;
  while(row>>x)starts.push_back(x);
  if(starts.size()!=7 || starts[0]!=4)return 5;
  for(int i=0;i<7;i++){
   x=starts[i];if(x<4 || x%2 || (i && x<starts[i-1]+2))return 6;
   labels.push_back(x);labels.push_back(x+1);
  }
  ExactSlots s(labels);int root=s.value(s.full,3);
  out<<"ROOT "<<line<<" VALUE "<<root<<"\n";
  for(int x:labels){
   int m=s.full^s.bit(x),d=x-3;
   std::vector<int> replies;
   if(x%2)replies={x-1};
   else if(x>=8 && (m&s.bit(4)))replies={4,x+1};
   else replies={x+1};
   int opening=s.move(s.full,3,x),policy=1;
   for(int y:replies){int v=s.move(m,d,y);policy=std::min(policy,v);m^=s.bit(y);
    bool catching=y>=d;d=std::abs(y-d);
    if(catching){if(y!=replies.back())return 7;break;}
   }
   out<<"PICK "<<x<<" exact "<<opening<<" reply";for(int y:replies)out<<' '<<y;
   out<<" move_value "<<policy<<"\n";
  }
  ++shapes;states+=s.states;out.flush();
 }
 std::cout<<"COMPLETE shapes "<<shapes<<" memo_states "<<states<<"\n";
}
