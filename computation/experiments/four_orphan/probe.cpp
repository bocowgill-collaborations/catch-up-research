// Bounded tests of both four-pair orphan reserves; exact recurrence reused.
#include "../seven_pairs/slots.hpp"
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
int main(int argc,char**argv){
 if(argc!=3)return 2;
 std::ifstream in(argv[1]);std::ofstream out(argv[2]);if(!in || !out)return 3;
 std::string line;auto begin=std::chrono::steady_clock::now();
 std::uint64_t supports=0,roots=0,turns=0,wins=0,matefails=0,states=0;
 while(std::getline(in,line)){
  if(std::chrono::duration<double>(std::chrono::steady_clock::now()-begin).count()>20){
   std::cout<<"TIME_LIMIT completed "<<supports<<'\n';return 4;}
  std::istringstream row(line);int a;std::vector<int>B;
  while(row>>a)B.push_back(a);if(B.size()!=4)return 5;
  for(int i=0;i<4;i++)if(B[i]<10 || B[i]==12 || B[i]%2 || (i && B[i]<=B[i-1]))return 6;
  for(int z:{6,7}){
   std::vector<int>R{z};for(int b:B){R.push_back(b);R.push_back(b+1);}
   ExactSlots s(R,z+2);
   for(int d:{z,z+2}){
    int v=s.value(s.full,d);++roots;wins+=v==1;
    out<<"ROOT "<<z<<' '<<d<<' '<<line<<" VALUE "<<v<<'\n';
    for(int x:R){
     std::vector<std::vector<int>> paths;
     if(x>=d)paths.push_back({x});
     else for(int y:R)if(y!=x)paths.push_back({x,y});
     for(auto path:paths){
      int m=s.full,def=d;
      for(int i=0;i<(int)path.size();i++){
       int y=path[i];if(!(m&s.bit(y)))return 7;
       if((y>=def)!=(i==(int)path.size()-1))return 8;
       m^=s.bit(y);def=std::abs(y-def);
      }
      out<<"TURN";for(int y:path)out<<' '<<y;
      out<<" CHILD "<<s.value(m,def)<<" SAFE_FIRST";
      for(int y:R)if((m&s.bit(y)) && s.move(m,def,y)>=0)out<<' '<<y;
      if(path.size()==1 && x!=z){
       int mate=x%2?x-1:x+1;
       int mv=s.move(m,def,mate);matefails+=mv<0;
       out<<" MATE "<<mate<<" GUARANTEE "<<mv;
      }
      out<<'\n';++turns;
     }
    }
   }
   states+=s.states;
  }
  ++supports;out.flush();
 }
 std::cout<<"COMPLETE supports "<<supports<<" roots "<<roots<<" opponent_turns "<<turns
          <<" winning_roots "<<wins<<" mate_failures "<<matefails<<" memo_states "<<states<<'\n';
}
