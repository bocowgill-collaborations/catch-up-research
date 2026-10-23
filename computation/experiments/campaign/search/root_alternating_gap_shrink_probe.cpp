// Fixed witness compression only: all16 admissible deletions, then greedy -2.
#include "../../seven_pairs/slots.hpp"
#include <fstream>
#include <iostream>
#include <numeric>
#include <string>
#include <tuple>
#include <sys/resource.h>
static void arr(const std::vector<int>&a){std::cout<<'[';bool c=false;for(int x:a){if(c)std::cout<<',';std::cout<<x;c=true;}std::cout<<']';}
static std::vector<int> support(const std::vector<int>&T){std::vector<int>S={4,7};S.insert(S.end(),T.begin(),T.end());return S;}
static bool valid(const std::vector<int>&T){if(T.empty()||T[0]<9)return false;int p=0,sum=0;for(int i=0;i<(int)T.size();i++){if(T[i]<=p||T[i]%2!=(i%2==0?1:0))return false;p=T[i];sum+=p;}return sum%2==0;}
static bool less(const std::vector<int>&a,const std::vector<int>&b){return std::make_tuple(a.size(),a.back(),std::accumulate(a.begin(),a.end(),0),a)<std::make_tuple(b.size(),b.back(),std::accumulate(b.begin(),b.end(),0),b);}
static void evaluate(const char*kind,const std::vector<int>&S,int d){ExactSlots v(S,d);std::cout<<"{\"kind\":\""<<kind<<"\",\"support\":";arr(v.xs);std::cout<<",\"deficit\":"<<d<<",\"value\":"<<v.value(v.full,d)<<",\"moves\":{";bool comma=false;for(int x:v.xs){if(comma)std::cout<<',';std::cout<<'"'<<x<<"\":"<<v.move(v.full,d,x);comma=true;}std::cout<<"}}"<<std::endl;}
int main(int argc,char**argv){try{
 if(argc!=2)throw std::runtime_error("authorized admissible input required");auto start=std::chrono::steady_clock::now();auto elapsed=[&](){return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();};
 std::ifstream in(argv[1]);std::vector<std::pair<int,std::vector<int>>>cases;int mask,k;while(in>>mask>>k){std::vector<int>T(k);for(int&x:T)in>>x;if(!valid(T))throw std::runtime_error("invalid predicate");cases.push_back({mask,T});}if(cases.size()!=16)throw std::runtime_error("expected16");
 std::vector<int>best;int phase1queries=0,phase2queries=0,accepted=0,sweeps=0;bool cap=false;
 for(const auto&[m,T]:cases){if(elapsed()>=20){cap=true;break;}ExactSlots v(support(T),1);int value=v.value(v.full,1);++phase1queries;std::cout<<"{\"kind\":\"deletion\",\"mask\":"<<m<<",\"T\":";arr(T);std::cout<<",\"value\":"<<value<<",\"states\":"<<v.states<<"}"<<std::endl;if(value==-1&&(best.empty()||less(T,best)))best=T;}
 if(!best.empty()){std::cout<<"{\"kind\":\"selected_deletion_loss\",\"T\":";arr(best);std::cout<<"}"<<std::endl;}
 bool fixed=false;
 while(!best.empty()&&!cap&&!fixed){++sweeps;bool changed=false;for(int i=0;i<(int)best.size();++i){if(elapsed()>=20){cap=true;break;}auto before=best,candidate=best;candidate[i]-=2;bool admissible=valid(candidate);int value=2;bool accept=false;if(admissible){ExactSlots v(support(candidate),1);value=v.value(v.full,1);++phase2queries;accept=value==-1;if(accept){best=candidate;changed=true;++accepted;}}
 std::cout<<"{\"kind\":\"numeric_trial\",\"sweep\":"<<sweeps<<",\"coordinate_zero_based\":"<<i<<",\"before\":";arr(before);std::cout<<",\"candidate\":";arr(candidate);std::cout<<",\"admissible\":"<<(admissible?"true":"false")<<",\"queried\":"<<(admissible?"true":"false")<<",\"value\":";if(admissible)std::cout<<value;else std::cout<<"null";std::cout<<",\"accepted\":"<<(accept?"true":"false")<<",\"current_best\":";arr(best);std::cout<<"}"<<std::endl;}
 if(!cap&&!changed)fixed=true;}
 if(!best.empty()){std::cout<<"{\"kind\":\"frozen_best\",\"T\":";arr(best);std::cout<<",\"one_step_fixed_point\":"<<(fixed?"true":"false")<<"}"<<std::endl;evaluate("final_E1",support(best),1);evaluate("final_E3",support(best),3);std::vector<int>C={2,3,4,7};C.insert(C.end(),best.begin(),best.end());evaluate("final_C8",C,8);}
 rusage u{};getrusage(RUSAGE_SELF,&u);std::cout<<"{\"kind\":\"checkpoint\",\"phase1_queries\":"<<phase1queries<<",\"phase1_unprocessed\":"<<16-phase1queries<<",\"phase2_queries\":"<<phase2queries<<",\"accepted_numeric_trials\":"<<accepted<<",\"sweeps\":"<<sweeps<<",\"one_step_fixed_point\":"<<(fixed?"true":"false")<<",\"time_cap\":"<<(cap?"true":"false")<<",\"seconds\":"<<elapsed()<<",\"max_rss_bytes\":"<<u.ru_maxrss<<"}"<<std::endl;
 }catch(const std::exception&e){std::cerr<<e.what()<<std::endl;return 2;}return 0;}
