// #include "ctl.h"
// Property: c > 5 => F(resp > 5)

int c;
int servers ;
int resp;
int curr_serv;

int __rho_1_;
unsigned int pc;
int __phi() { return CAND(CAP(c>5),CEG(CAP(resp<=5))); }

void init() {
  c = nondet(); assume(c>0);
  servers = 8;
  resp = 0;
  curr_serv = servers;
}

int body() {
  c = c;
  while(1) {
    if (!(curr_serv > 0)) break;
    __rho_1_ = nondet();
    if(__rho_1_>0) {
      c--; curr_serv--;
      resp++;
    } else {
      assume(c < curr_serv);
      curr_serv--;
    }
  }
  while(1) { dummy=dummy; } L_return: return 0;
}

int main() {}

