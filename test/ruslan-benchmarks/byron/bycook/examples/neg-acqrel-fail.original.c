// #include "ctl.h"

int n; int A; int R;
unsigned int pc;
int __phi() { return CEF(CAND(CAP(A==1),CEG(CAP(R!=1)))); }
int __rho_1_;

int init() { A=0; R=0; }
int dobreak;

int body() {
  dobreak = nondet();
  while(1) {
    if (dobreak > 0) break;
    A = 1;
    A = 0;
    __rho_1_ = nondet();
    n = __rho_1_;
    while(1) {
      if (!(n>0)) break;
      /*  ((n___old2 > loc_n)&&(loc_n>=0)) */
      n--;
    }
    R = 1;
    R=0;
    dobreak = nondet();
  }
  while(1) { dummy=dummy; } L_return: return 0;
}

int main() { }
