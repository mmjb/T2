// #include "ctl.h"

// Property: G F WItemsNum >= 1

int WItemsNum;
unsigned int pc;
int __rho_1_;
int __rho_2_;
 inline int __phi() { return CAG(CAF(CAP(WItemsNum>=1))); }

 inline void init() { WItemsNum = nondet(); }

 inline void callback1() {}
 inline void callback2() {}
#define MoreWItems() nondet()

inline void body() {
  __rho_1_ = nondet();
    WItemsNum = __rho_1_;
    while(1) {
      while(1) { 
	__rho_2_ = MoreWItems();
	if (WItemsNum<=5) { if (__rho_2_>0) break; }
               if (WItemsNum<=5) {
                   callback1();
                   WItemsNum++;
    
               } else {
                   WItemsNum++;
               }
        }
    
      while(1) { 
	if (!(WItemsNum>2)) break;
             callback2();
             WItemsNum--;
        }
    }
  while(1) { dummy=dummy; } L_return: return 0;
}
    
 int main() { init(); body(); }
