// Same saved B tails, plus one named prior control; stop on the first double LOSS.
#include "../../seven_pairs/slots.hpp"
#include <fstream>
#include <iostream>
#include <sys/resource.h>
static std::string labels(const ExactSlots&v,int m){std::string z;for(int x:v.xs)if(m&v.bit(x))z+=std::to_string(x)+",";return z;}
static std::string moves(ExactSlots&v,int m,int d){std::string z;for(int x:v.xs)if(m&v.bit(x))z+=std::to_string(x)+":"+std::to_string(v.move(m,d,x))+",";return z;}
static void state(int id,const char*label,ExactSlots&v,int m,int d){std::cout<<"STATE id "<<id<<" label "<<label<<" deficit "<<d<<" value "<<v.value(m,d)<<" remaining "<<labels(v,m)<<" moves "<<moves(v,m,d)<<'\n';}
int main(int argc,char**argv){auto start=std::chrono::steady_clock::now();try{
 if(argc!=2)throw std::runtime_error("seed file required");std::ifstream in(argv[1]);int id,source,control,saved,r;unsigned count=0;bool found=false,cap=false;
 while(in>>id>>source>>control>>saved>>r){std::vector<int>T(r),E={4,7};for(int&i:T)in>>i;E.insert(E.end(),T.begin(),T.end());ExactSlots v(E,3);int one=v.value(v.full,1),three=v.value(v.full,3);++count;
  std::cout<<"CASE id "<<id<<" source_id "<<source<<" is_control "<<control<<" E1 "<<one<<" E3 "<<three<<" saved_C8 "<<saved<<" E "<<labels(v,v.full)<<'\n';found=one==-1 && three==-1;
  if(found || control){std::vector<int>C={2,3,4,7};C.insert(C.end(),T.begin(),T.end());ExactSlots cv(C,8);int C8=cv.value(cv.full,8);if(C8!=saved)throw std::runtime_error("savedC8 mismatch");state(id,"C8",cv,cv.full,8);state(id,"C2",cv,cv.full,2);state(id,"Cerase2_4",cv,cv.full^cv.bit(2),4);}
  if(found){state(id,"E1",v,v.full,1);state(id,"E3",v,v.full,3);break;}
  std::cout<<std::flush;if(std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>8){cap=true;break;}
 }
 rusage u{};getrusage(RUSAGE_SELF,&u);std::cout<<(found?"STOP_FIRST_DOUBLELOSS":(cap?"STOP_8S_CAP":"COMPLETE_NO_DOUBLELOSS"))<<" completed "<<count<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<" max_rss_bytes "<<u.ru_maxrss<<'\n';
 }catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 2;}}
