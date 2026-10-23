// Bounded discovery for the reached ten-counter defender decision.
// Uses the existing exact recurrence; this output is experimental, not a proof.
#include "../seven_pairs/slots.hpp"
#include <fstream>
#include <iostream>
#include <tuple>

int main(int argc,char**argv){
 if(argc!=2)return 2;
 std::ofstream out(argv[1]);if(!out)return 3;
 auto begin=std::chrono::steady_clock::now();
 for(int q=42;q<=100;q+=2){
  if(std::chrono::duration<double>(std::chrono::steady_clock::now()-begin).count()>20)return 4;
  ExactSlots s({7,10,11,18,19,20,21,40,41,q},q-7);
  int d=q-7;
  out<<"ROOT "<<q<<" VALUE "<<s.value(s.full,d)<<" FIRST";
  for(int x:s.xs)out<<' '<<x<<':'<<s.move(s.full,d,x);
  out<<'\n';
  for(int a=1;a<=s.full;a++)for(int f:s.xs)if((a&s.bit(f)) && s.sums[a]>=d &&
        (a==s.bit(f) || s.sums[a^s.bit(f)]<d)){
   int v=-s.value(s.full^a,s.sums[a]-d);
   if(v>=0){
    out<<"TURN "<<q<<" VALUE "<<v<<" PREP";
    for(int x:s.xs)if(x!=f && (a&s.bit(x)))out<<' '<<x;
    out<<" FINAL "<<f<<" ENDDEF "<<s.sums[a]-d<<" ENDSET";
    for(int x:s.xs)if(!(a&s.bit(x)))out<<' '<<x;
    out<<'\n';
   }
  }
 }
 std::cout<<"COMPLETE 30 q values including100 control\n";
}
