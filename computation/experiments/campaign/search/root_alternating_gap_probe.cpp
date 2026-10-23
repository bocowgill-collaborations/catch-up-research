// One approved fixed alternating-tail batch; unmodified supplied-label solver.
#include "../../seven_pairs/slots.hpp"
#include <fstream>
#include <iostream>
#include <string>
#include <sys/resource.h>

struct Case { int id; std::vector<int> tail; };
static void arr(const std::vector<int>& a) {
  std::cout << '['; bool comma=false;
  for(int x:a) { if(comma)std::cout<<','; std::cout<<x; comma=true; }
  std::cout << ']';
}
static void map(ExactSlots& v,int d) {
  std::cout << '{'; bool comma=false;
  for(int x:v.xs) {
    if(comma)std::cout<<',';
    std::cout << '"' << x << "\":" << v.move(v.full,d,x); comma=true;
  }
  std::cout << '}';
}
static void evaluate(const char* kind,const Case& c,const std::vector<int>& S,
                     int d,bool all_moves) {
  ExactSlots v(S,d); int value=v.value(v.full,d);
  std::cout << "{\"kind\":\"" << kind << "\",\"id\":" << c.id
            << ",\"T\":"; arr(c.tail);
  std::cout << ",\"support\":"; arr(v.xs);
  std::cout << ",\"deficit\":" << d << ",\"value\":" << value;
  if(all_moves) {std::cout << ",\"moves\":"; map(v,d);}
  std::cout << ",\"states\":" << v.states << "}" << std::endl;
}
int main(int argc,char**argv) { try {
  if(argc!=3)throw std::runtime_error("seed and control ID files required");
  auto start=std::chrono::steady_clock::now();
  auto elapsed=[&](){return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();};
  std::ifstream in(argv[1]); std::vector<Case> cs; int id,k;
  while(in>>id>>k) {Case c{id,std::vector<int>(k)};for(int&x:c.tail)in>>x;cs.push_back(c);}
  if(cs.size()!=229)throw std::runtime_error("expected exactly229 authorized tails");
  for(const auto&c:cs) {
    if(c.tail.size()!=3 && c.tail.size()!=4 && c.tail.size()!=7 && c.tail.size()!=8)
      throw std::runtime_error("wrong cardinality");
    int sum=0,previous=8;
    for(int i=0;i<(int)c.tail.size();++i) {
      int x=c.tail[i]; if(x<=previous || x%2!=(i%2==0?1:0))throw std::runtime_error("rank predicate failed");
      previous=x;sum+=x;
    }
    if(sum%2 || c.tail.size()+2>10)throw std::runtime_error("even sum/label limit failed");
  }
  int completed=0,witness_id=0;std::string reason="all_229_completed";
  for(const auto&c:cs) {
    if(elapsed()>=20) {reason="search_time_cap";break;}
    std::vector<int>S={4,7};S.insert(S.end(),c.tail.begin(),c.tail.end());
    ExactSlots v(S,1);int val=v.value(v.full,1);++completed;
    std::cout << "{\"kind\":\"primary\",\"id\":" << c.id << ",\"T\":";arr(c.tail);
    std::cout << ",\"support\":";arr(v.xs);
    std::cout << ",\"deficit\":1,\"value\":" << val << ",\"states\":" << v.states;
    if(val==-1) {std::cout << ",\"moves\":";map(v,1);}
    std::cout << "}" << std::endl;
    if(val==-1) {witness_id=c.id;reason="first_loss";break;}
  }
  // These are exactly the eight requested provenance controls (six supports).
  // Querying them after a stop is diagnostic replay, not further search.
  std::ifstream controls(argv[2]);int control_id;
  while(controls>>control_id) {
    if(control_id<1 || control_id>(int)cs.size())throw std::runtime_error("badcontrolid");
    const auto&c=cs.at(control_id-1);std::vector<int>S={4,7};S.insert(S.end(),c.tail.begin(),c.tail.end());
    evaluate("control",c,S,1,true);
  }
  if(witness_id) {
    const auto&c=cs.at(witness_id-1);std::vector<int>E={4,7},C={2,3,4,7},Cerase2={3,4,7};
    E.insert(E.end(),c.tail.begin(),c.tail.end());C.insert(C.end(),c.tail.begin(),c.tail.end());
    Cerase2.insert(Cerase2.end(),c.tail.begin(),c.tail.end());
    evaluate("witness_E3",c,E,3,true);
    evaluate("witness_C8",c,C,8,true);
    evaluate("witness_C2",c,C,2,true);
    evaluate("witness_Cerase2_d4",c,Cerase2,4,true);
  }
  rusage u{};getrusage(RUSAGE_SELF,&u);
  std::cout << "{\"kind\":\"checkpoint\",\"authorized_cases\":229,\"completed_primary\":" << completed
            << ",\"unprocessed_primary\":" << 229-completed << ",\"witness_id\":" << witness_id
            << ",\"stop_reason\":\"" << reason << "\",\"seconds\":" << elapsed()
            << ",\"max_rss_bytes\":" << u.ru_maxrss << "}" << std::endl;
  return 0;
} catch(const std::exception&e) {std::cerr<<e.what()<<std::endl;return 2;}}
