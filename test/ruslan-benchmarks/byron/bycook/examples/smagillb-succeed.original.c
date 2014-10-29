// #include "ctl.h"
// Property: c > servers / 2 => F(resp > servers / 2)

unsigned int c;
int servers ;
int resp;
int curr_serv;
int serversdiv2;

unsigned int pc;
int __rho_1_;
int __phi() { return CIMP(CAP(c>serversdiv2),CAF(CAP(resp>serversdiv2))); }

void init() {
  c = nondet(); assume(c>0);
  servers = nondet(); assume(servers>0);
  serversdiv2 = nondet();
  dummy = nondet();
  if(dummy>0) {
    assume(serversdiv2+serversdiv2==servers);
  } else { 
    assume(serversdiv2+serversdiv2+1==servers);
  }
  resp = 0;
  curr_serv = servers;
}

int body() {
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
