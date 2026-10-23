#include "slots.hpp"
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
std::vector<int> canonicalReply(const std::vector<int>& starts,int x){
 if(x%2)return {x-1};
 std::vector<int> rest;for(int a:starts)if(a!=x)rest.push_back(a);
 if(rest!=std::vector<int>{6,10,20,40})return {x+1};
 if(x>=42)return {6,10,20,x+1};
 if(x==8)return {6};
 return {6,x==22?20:10}; // The inherited bounded sparse repair.
}
int main(int argc,char**argv){
 if(argc!=3)return 2;std::ifstream in(argv[1]);std::ofstream out(argv[2]);
 if(!in || !out)return 3;
 std::string line;auto begin=std::chrono::steady_clock::now();
 std::uint64_t shapes=0,turns=0,failures=0,states=0;
 while(std::getline(in,line)){
  if(std::chrono::duration<double>(std::chrono::steady_clock::now()-begin).count()>20){
   std::cout<<"TIME_LIMIT completed "<<shapes<<"\n";return 4;}
  std::istringstream row(line);std::vector<int> starts,labels{5};int a;
  while(row>>a)starts.push_back(a);
  if(starts.size()!=3 && starts.size()!=5)return 5;
  for(int i=0;i<(int)starts.size();i++){
   a=starts[i];if(a<6 || a==8 || a%2 || (i && a<starts[i-1]+2))return 6;
   labels.push_back(a);labels.push_back(a+1);
  }
  ExactSlots s(labels,8);out<<"STATE "<<line<<" VALUE "<<s.value(s.full,8)<<"\n";
  for(int x:labels){
   std::vector<std::vector<int>> paths;
   if(x>=8)paths.push_back({x});
   else for(int y:labels)if(y!=x)paths.push_back({x,y});
   for(auto path:paths){
    int m=s.full,d=8;for(int z:path){
     if(z!=path.back() && z>=d)return 7;
     m^=s.bit(z);bool catches=z>=d;d=std::abs(z-d);
     if(z==path.back() && !catches)return 8;
    }
    std::vector<int> reply;
    if(x>=8)reply={x%2?x-1:x+1};
    else if(x==5)reply=canonicalReply(starts,path.back());
    else if(x==6){int y=path.back();reply={y==5?7:y==7?5:y%2?y-1:y+1};}
    else if(x==7){int y=path.back();reply={y==5?6:y==6?5:y%2?y-1:y+1};}
    else return 9;
    int worst=1;
    for(int z:reply){
     worst=std::min(worst,s.move(m,d,z));m^=s.bit(z);
     bool catches=z>=d;d=std::abs(z-d);
     if(catches && z!=reply.back())return 10;
     if(!catches && z==reply.back())return 11;
    }
    ++turns;failures+=worst<0;
    out<<"TURN";for(int z:path)out<<' '<<z;
    out<<" REPLY";for(int z:reply)out<<' '<<z;
    out<<" GUARANTEE "<<worst<<"\n";
   }
  }
  ++shapes;states+=s.states;out.flush();
 }
 std::cout<<"COMPLETE shapes "<<shapes<<" opponent_turns "<<turns<<" failed_responses "<<failures<<" memo_states "<<states<<"\n";
}
