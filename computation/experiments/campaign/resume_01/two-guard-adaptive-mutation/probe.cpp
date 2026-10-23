#include "../../../seven_pairs/slots.hpp"
#include <iostream>
#include <ctime>
int main(){const auto start=std::clock();int id,n;
 while(std::cin>>id>>n){std::vector<int>s(n);for(auto&x:s)std::cin>>x;
  if(double(std::clock()-start)/CLOCKS_PER_SEC>14){std::cout<<"{\"status\":\"CPU_CAP\"}\n";return 3;}
  ExactSlots e(s,1);int v=e.value(e.full,1);
  std::cout<<"{\"id\":"<<id<<",\"value\":"<<v<<",\"moves\":{";bool first=true;
  for(int x:s){if(!first)std::cout<<",";first=false;std::cout<<"\""<<x<<"\":"<<e.move(e.full,1,x);}
  std::cout<<"},\"states\":"<<e.states<<",\"cpu_seconds\":"<<double(std::clock()-start)/CLOCKS_PER_SEC<<"}\n"<<std::flush;
  if(v==-1)return 0;
 }
}
