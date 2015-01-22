// #include "ctl.h"

int n; int A; int R;
unsigned int pc;
int __phi() { return CAG(CIMP(CAP(A==1),CEF(CAP(R==1)))); }

int init() { A=0; R=0; }
int dobreak;

int body() {
  dobreak = nondet();
  while(1) {
    if (dobreak > 0) break;
    A = 1;
    A = 0;
    n = nondet();
    assume(n>0);
    while(1) {
      if (!(n>0)) break;
      // should loop forever here
      n = n + 0;
    }
    R = 1;
    R = 0;
    dobreak = nondet();
  }
  while(1) { dummy=dummy; } L_return: return 0;  
}

int main() { }

