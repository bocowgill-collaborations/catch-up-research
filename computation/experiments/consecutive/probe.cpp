#include "../seven_pairs/slots.hpp"
#include <iostream>
#include <ctime>
int main(){int id,n,d;const auto start=std::clock();
 while(std::cin>>id>>n>>d){std::vector<int>s(n);for(auto&x:s)std::cin>>x;
  if(double(std::clock()-start)/CLOCKS_PER_SEC>14){std::cout<<"{\"status\":\"CPU_CAP\"}\n";return 3;}
  if(n>15)return 4;
  // Frozen ExactSlots accepts up to14 counters. At15, evaluate all first
  // children (each14) and take their exact maximum; do not change its code.
  std::vector<int> moves;int best=-1;std::uint64_t states=0;
  if(n<=14){ExactSlots e(s,d);best=e.value(e.full,d);for(int x:s)moves.push_back(e.move(e.full,d,x));states=e.states;}
  else for(int x:s){std::vector<int>r;for(int y:s)if(y!=x)r.push_back(y);ExactSlots e(r,std::abs(x-d));int v=e.value(e.full,std::abs(x-d));if(x>=d)v=-v;moves.push_back(v);best=std::max(best,v);states+=e.states;}
  std::cout<<"{\"id\":"<<id<<",\"deficit\":"<<d<<",\"value\":"<<best<<",\"moves\":{";
  for(int i=0;i<n;i++){if(i)std::cout<<",";std::cout<<"\""<<s[i]<<"\":"<<moves[i];}
  std::cout<<"},\"states\":"<<states<<",\"cpu_seconds\":"<<double(std::clock()-start)/CLOCKS_PER_SEC<<"}\n"<<std::flush;
 }
}
