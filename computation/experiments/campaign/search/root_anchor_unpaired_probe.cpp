// One deterministic unpaired-tail discriminator, stopping at the first anchor LOSS.
#include "../../seven_pairs/slots.hpp"
#include <fstream>
#include <iostream>
#include <sys/resource.h>
static std::string labels(const ExactSlots&v,int m){std::string z;for(int x:v.xs)if(m&v.bit(x))z+=std::to_string(x)+",";return z;}
static std::string moves(ExactSlots&v,int m,int d){std::string z;for(int x:v.xs)if(m&v.bit(x))z+=std::to_string(x)+":"+std::to_string(v.move(m,d,x))+",";return z;}
int main(int argc,char**argv){auto start=std::chrono::steady_clock::now();try{
 if(argc<2)throw std::runtime_error("seed file required");std::ifstream in(argv[1]);if(!in)throw std::runtime_error("seed read failed");const int first=argc>2?std::stoi(argv[2]):1;unsigned completed=0;std::uint64_t visited=0;int id,r;char family;bool loss=false,cap=false;int last=0;
 while(in>>id>>family>>r){std::vector<int>T(r),U={2,3,4};for(int&i:T)in>>i;if(id<first)continue;if(family=='B')U.push_back(7);U.insert(U.end(),T.begin(),T.end());int d=family=='A'?7:8;ExactSlots v(U,d);int value=v.value(v.full,d);++completed;last=id;
  std::cout<<"CASE id "<<id<<" family "<<family<<" shadow_def "<<d<<" shadow_value "<<value<<" support_size "<<U.size()<<" U "<<labels(v,v.full)<<'\n';
  if(value==-1){loss=true;std::cout<<"ANCHOR_LOSS id "<<id<<" family "<<family<<" deficit "<<d<<" value "<<value<<" remaining "<<labels(v,v.full)<<" moves "<<moves(v,v.full,d)<<'\n';
   int td=family=='A'?3:2;std::cout<<"TARGET id "<<id<<" label "<<(family=='A'?"A3":"B2")<<" deficit "<<td<<" value "<<v.value(v.full,td)<<" remaining "<<labels(v,v.full)<<" moves "<<moves(v,v.full,td)<<'\n';if(family=='B'){int m=v.full^v.bit(2);std::cout<<"TARGET id "<<id<<" label B_erase2_4 deficit 4 value "<<v.value(m,4)<<" remaining "<<labels(v,m)<<" moves "<<moves(v,m,4)<<'\n';}}
  visited+=v.states;std::cout<<std::flush;if(loss)break;if(std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>8){cap=true;break;}
 }
 rusage u{};getrusage(RUSAGE_SELF,&u);std::cout<<(loss?"STOP_ANCHOR_LOSS":(cap?"STOP_PROBE_8S_CAP":"COMPLETE_PLANNED_BATCH"))<<" first_id "<<first<<" last_completed_id "<<last<<" completed "<<completed<<" slot_states_visited "<<visited<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<" max_rss_bytes "<<u.ru_maxrss<<'\n';
 }catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 2;}}
