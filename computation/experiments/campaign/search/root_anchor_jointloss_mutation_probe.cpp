// One radius-two mutation discriminator, with a hard 19.5s search stop.
#include "../../seven_pairs/slots.hpp"
#include <fstream>
#include <iostream>
#include <sys/resource.h>
static std::string labels(const ExactSlots&v,int m){std::string z;for(int x:v.xs)if(m&v.bit(x))z+=std::to_string(x)+",";return z;}
static std::string moves(ExactSlots&v,int m,int d){std::string z;for(int x:v.xs)if(m&v.bit(x))z+=std::to_string(x)+":"+std::to_string(v.move(m,d,x))+",";return z;}
static void detail(int id,const char*label,ExactSlots&v,int m,int d){std::cout<<"STATE id "<<id<<" label "<<label<<" deficit "<<d<<" value "<<v.value(m,d)<<" remaining "<<labels(v,m)<<" moves "<<moves(v,m,d)<<'\n';}
int main(int argc,char**argv){auto start=std::chrono::steady_clock::now();try{
 if(argc!=2)throw std::runtime_error("seed file required");std::ifstream in(argv[1]);if(!in)throw std::runtime_error("seed read failed");
 ExactSlots namedR({2,3,4,9,10,12,15},1);detail(0,"NAMED_R1",namedR,namedR.full,1);
 unsigned completed=0;std::uint64_t visited=0;bool found=false,cap=false;int id,parent,root,depth,control,expected1,expected3,r,last=0;
 while(in>>id>>parent>>root>>depth>>control>>expected1>>expected3>>r){std::vector<int>T(r),E={4,7};for(int&i:T)in>>i;E.insert(E.end(),T.begin(),T.end());ExactSlots v(E,3);int one=v.value(v.full,1),three=v.value(v.full,3);++completed;last=id;
  if(control && (one!=expected1 || three!=expected3))throw std::runtime_error("source control mismatch");
  std::cout<<"CASE id "<<id<<" parent "<<parent<<" root_source "<<root<<" depth "<<depth<<" E1 "<<one<<" E3 "<<three<<" E "<<labels(v,v.full)<<'\n';
  found=one==-1 && three==-1;if(found){detail(id,"E1",v,v.full,1);detail(id,"E3",v,v.full,3);std::vector<int>C={2,3,4,7};C.insert(C.end(),T.begin(),T.end());if(C.size()>14)throw std::runtime_error("witness contexts exceed frozen bound");ExactSlots cv(C,8);detail(id,"C8",cv,cv.full,8);detail(id,"C2",cv,cv.full,2);detail(id,"Cerase2_4",cv,cv.full^cv.bit(2),4);}
  visited+=v.states;if(found)break;if((completed&63)==0)std::cout<<std::flush;
  if(std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>19.5){cap=true;break;}
 }
 rusage u{};getrusage(RUSAGE_SELF,&u);std::cout<<(found?"STOP_FIRST_DOUBLELOSS":(cap?"STOP_SEARCH_19_5S_CAP":"COMPLETE_FIXED_RADIUS_TWO"))<<" completed "<<completed<<" last_completed_id "<<last<<" slot_states_visited "<<visited<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<" max_rss_bytes "<<u.ru_maxrss<<'\n';
 }catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 2;}}
