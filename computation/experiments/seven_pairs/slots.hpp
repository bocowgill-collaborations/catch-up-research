// Extension of canonical_five3/probe.cpp's exact recurrence to supplied slots.
// Experimental only. Actual labels are retained; a timeout is never an outcome.
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <stdexcept>
#include <vector>
struct ExactSlots {
  std::vector<int> xs,sums;
  int width,full;
  std::vector<std::int8_t> cache;
  std::uint64_t states=0;
  explicit ExactSlots(std::vector<int> labels,int initial_d=3):xs(std::move(labels)) {
    if(xs.empty() || xs.size()>14 || initial_d<0 || initial_d>10000)
      throw std::runtime_error("unsupported explicit bounded input");
    std::sort(xs.begin(),xs.end());
    if(xs.front()<=0 || xs.back()>10000 || std::adjacent_find(xs.begin(),xs.end())!=xs.end())
      throw std::runtime_error("invalid counter labels");
    width=std::max(xs.back(),initial_d)+1;full=(1<<xs.size())-1;
    sums.resize(full+1);cache.assign((full+1)*width,2);
    for(int m=1;m<=full;m++){int i=__builtin_ctz((unsigned)m);sums[m]=sums[m^(1<<i)]+xs[i];}
  }
  int bit(int x)const {
    auto it=std::lower_bound(xs.begin(),xs.end(),x);
    if(it==xs.end() || *it!=x)throw std::runtime_error("missing counter");
    return 1<<(it-xs.begin());
  }
  int value(int m,int d) {
    if(d<0 || d>=width)throw std::runtime_error("deficit out of range");
    auto& z=cache[m*width+d];if(z!=2)return z;++states;
    if(!m)return z=d==0?0:-1;
    if(sums[m]<d)return z=-1;
    int best=-1;
    for(int i=0;i<(int)xs.size();i++)if(m&(1<<i)){
      int v=value(m^(1<<i),std::abs(xs[i]-d));if(xs[i]>=d)v=-v;
      best=std::max(best,v);if(best==1)break;
    }
    return z=best;
  }
  int move(int m,int d,int x){
    int b=bit(x);if(!(m&b))throw std::runtime_error("illegal move");
    int v=value(m^b,std::abs(x-d));return x>=d?-v:v;
  }
};
