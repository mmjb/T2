// #include "ctl.h"
// Property: c > 5 => F(resp > 5)

int c;
int servers ;
int resp;
int curr_serv;

int __rho_1_;
int __rho_2_;
unsigned int pc;
 inline int __phi() { return CAND(CAP(c>5),CAG(CAP(resp<=5))); }

 inline void init() {
  __rho_2_ = nondet();
  c = __rho_2_; assume(c>0);
  servers = 4;
  resp = 0;
  curr_serv = servers;
}

inline int body() {
  if(c<=5) {
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
  }
  while(1) { dummy=dummy; } L_return: return 0;
}

 int main() { init(); body(); }





// c=6, servers=4, curr = 4, resp=0
// c=5, servers=4, curr = 3, resp=1
// c=4, servers=4, curr = 2, resp=2
// c=3, servers=4, curr = 1, resp=2
// c=2, servers=4, curr = 0, resp=3
