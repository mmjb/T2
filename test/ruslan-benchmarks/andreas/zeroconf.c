/*

Zeroconf protocol adapted from Kattenbelt et al.

*/

#include "assume.h"
#include "patterns.h"


/*
 USED PATTERN: 000 * 0000 * 00000 * ...
*/

void main() {

  int NONDET;
  int b_ip;
  int b_probe;
  int b_arp;
  int b_configured;
  int N;
  int k;
  
  int seq = 1;
  int i = seq+3;

  __INITPATTERN

  N = NONDET;
  assume (N >= 0);


  b_ip = 0;
  b_probe = 0;
  b_arp = 0;
  b_configured = 0;
  k = 0;




  while (b_configured == 0) 
    { // exit loop if b_configured
      
      b_arp = 0; // no b_arp received
      b_probe = 0; // no b_probe sent
      k = 0; // number of b_probes sent is 0
   
      

      b_ip = NONDET; // b_ip = coin();
      assume (b_ip >= 0);
      assume (b_ip <= 1);
      

      /// Instrumentation
      if (z <= 0) {
	if (i > 0) {
	  __FIRSTP0(b_ip)
	  __WEND
	}
	else {
	  seq++;
	  i = seq+3;
	  z = NONDET; assume (z >= 0); pos = 0;
	}
      }
      else z--;
      /// end Instrumentation
      

      while ((b_arp <= 0) && k<=N) 
	{ 
	  b_probe = NONDET; // b_probe = coin()
	  assume (b_probe >= 0);
	  assume (b_probe <= 1);

     /// Instrumentation
      if (z <= 0) {
	if (i > 0) {
	  __FIRSTP0(b_probe)
	  __WEND
	}
	else {
	  seq++;
	  i = seq+3;
	  z = NONDET; assume (z >= 0); pos = 0;
	}
      }
      else z--;
      /// end Instrumentation

	  if (b_probe >= 1 && b_ip <= 0) 
	    { 
	      b_arp = NONDET; 
	      assume (b_arp >= 0);
	      assume (b_arp <= 1);

     /// Instrumentation
      if (z <= 0) {
	if (i > 0) {
	  __FIRSTP0(b_arp)
	  __WEND
	}
	else {
	  seq++;
	  i = seq+3;
	  z = NONDET; assume (z >= 0); pos = 0;
	}
      }
      else z--;
      assume (seq <= N+1);
      /// end Instrumentation
    }
  k = k+1; // move onto next b_probe
  
  //assume (seq <= N+1); // for preorcessing phase
  //if (seq > N+1) {ERROR:} // invariant from preprocessing

}
     
      if (b_arp <= 0) {b_configured = 1;} // sent all b_probes and no b_arps received so presume b_ip address is fresh
      //assume (seq <= N+1); // invariant from preprocessing
    //if (seq > N+1) {ERROR: } // for preorcessing phase  
  }

}
