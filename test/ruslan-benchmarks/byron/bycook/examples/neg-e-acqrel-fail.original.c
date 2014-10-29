// #include "ctl.h"

int n; int A; int R;
unsigned int pc;
int __phi() { return CEF(CAND(CAP(A==1),CAG(CAP(R!=1)))); }

int init() { A=0; R=0; }
int dobreak;
int __rho_1_;
int __rho_2_;

int body() {
  __rho_1_ = nondet();
  dobreak = __rho_1_;
  while(1) {
    if (dobreak > 0) break;
    A = 1;
    A = 0;
    __rho_2_ = nondet();
    n = __rho_2_;
    //assume(n>0);
    while(1) {
      if (!(n>0)) break;
      // should loop forever here
      n = n + 0;
    }
    R = 1;
    R = 0;
    __rho_1_ = nondet();
    dobreak = __rho_1_;
  }
  while(1) { dummy=dummy; } L_return: return 0;  
}

int main() { }

