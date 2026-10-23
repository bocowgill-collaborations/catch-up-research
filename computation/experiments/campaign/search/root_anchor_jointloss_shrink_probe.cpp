// Exhaust only subsets of the verified nine-label witness; no global minimum claim.
#include "../../seven_pairs/slots.hpp"
#include <iostream>
#include <numeric>
#include <tuple>
#include <sys/resource.h>
static std::string labels(const ExactSlots&v,int m){std::string z;for(int x:v.xs)if(m&v.bit(x))z+=std::to_string(x)+",";return z;}
static std::string moves(ExactSlots&v,int m,int d){std::string z;for(int x:v.xs)if(m&v.bit(x))z+=std::to_string(x)+":"+std::to_string(v.move(m,d,x))+",";return z;}
static void detail(const char*label,ExactSlots&v,int m,int d){std::cout<<"STATE label "<<label<<" deficit "<<d<<" value "<<v.value(m,d)<<" remaining "<<labels(v,m)<<" moves "<<moves(v,m,d)<<'\n';}
int main(){auto start=std::chrono::steady_clock::now();try{
 const std::vector<int>source={18,33,35,36,52,56,62,74,100};std::vector<int>best;bool found=false;unsigned evens=0,odds=0,witnesses=0,bestmask=0;
 for(unsigned mask=0;mask<(1U<<source.size());++mask){std::vector<int>T,E={4,7};for(unsigned i=0;i<source.size();++i)if(mask&(1U<<i))T.push_back(source[i]);int sum=std::accumulate(T.begin(),T.end(),0);
  if(sum%2){++odds;std::cout<<"ODD_SKIPPED mask "<<mask<<" tail_sum "<<sum<<'\n';continue;}++evens;E.insert(E.end(),T.begin(),T.end());ExactSlots v(E,3);int one=v.value(v.full,1),three=v.value(v.full,3);bool both=one==-1&&three==-1;
  std::cout<<"CASE mask "<<mask<<" tail_card "<<T.size()<<" tail_sum "<<sum<<" E1 "<<one<<" E3 "<<three<<" E "<<labels(v,v.full)<<'\n';if(both){++witnesses;auto objective=std::make_tuple(T.size(),T.empty()?0:T.back(),sum,T);auto old=std::make_tuple(best.size(),best.empty()?0:best.back(),std::accumulate(best.begin(),best.end(),0),best);if(!found||objective<old){found=true;best=T;bestmask=mask;}}
  if(std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>8)throw std::runtime_error("INCOMPLETE8s shrink cap");
 }
 if(!found)throw std::runtime_error("verified source witness missing");std::vector<int>E={4,7};E.insert(E.end(),best.begin(),best.end());ExactSlots e(E,3);detail("E1",e,e.full,1);detail("E3",e,e.full,3);std::vector<int>C={2,3,4,7};C.insert(C.end(),best.begin(),best.end());ExactSlots c(C,8);detail("C8",c,c.full,8);detail("C2",c,c.full,2);detail("Cerase2_4",c,c.full^c.bit(2),4);
 rusage u{};getrusage(RUSAGE_SELF,&u);std::cout<<"COMPLETE_FIXED_SUPPORT_SHRINK total_subsets 512 even_subsets "<<evens<<" odd_skipped "<<odds<<" doubleloss_subsets "<<witnesses<<" minimum_mask "<<bestmask<<" minimum_tail_card "<<best.size()<<" minimum_max "<<best.back()<<" minimum_sum "<<std::accumulate(best.begin(),best.end(),0)<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<" max_rss_bytes "<<u.ru_maxrss<<'\n';
 }catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 2;}}
