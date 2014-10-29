#include "assume.h"
#include "patterns.h"


void main() {

  int NONDET;
  int n; // # processes
  int m; // # minimal distance
  int max; 
  int c1,c2;

  int seq = 1;
  int wpos = 0;
  int pi = seq;

  __INITPATTERN

  n = NONDET;
  assume (n >= 0);

    
  // abstract max = n/k  
  max = NONDET;
  assume (max >= 0);
  assume (max <= n);
 
  m = NONDET;
  assume (m <= max);
  assume (m >= 0);
    
  while (m > 0) {
    
    //assume (seq <= n+1); // {ERROR: }
    //if (seq > n+1) {ERROR: }
    // COIN TOSS
    c1 = NONDET;
    assume (c1 >= 0);
    assume (c1 <= 1);
      
    ///
    if (z <= 0) {
      if (pos <= 0) {
	assume (c1 <= 0); pos++;
      }
      else if (pos <= 1) {
	if (wpos <= 0) {
	  assume (c1 >= 1);
	  wpos++;
	}
	else if (wpos <= 1 && pi > 0) {
	  assume (c1 <= 0);
	  wpos = 0;
	  pi--;
	}
	else {
	  seq++;
	  wpos = 0;
	  pos = 0;
	  pi = seq;
	  z = NONDET;
	  assume (z >= 0);
	}
      }
    }
    else {z--;}
    ///

    if (c1 >= 1) {

      // COIN TOSS
      c2 = NONDET;
      assume (c2 >= 0);
      assume (c2 <= 1);
      ///
      if (z <= 0) {
	if (pos <= 0) {
	  assume (c2 <= 0); pos++;
	}
	else if (pos <= 1) {
	  if (wpos <= 0) {
	    assume (c2 >= 1);
	    wpos++;
	  }
	  else if (wpos <= 1 && pi > 0) {
	    assume (c2 <= 0);
	    wpos = 0;
	    pi--;
	  }
	  else {
	    seq++;
	    wpos = 0;
	    pos = 0;
	    pi = seq;
	    z = NONDET;
	    assume (z >= 0);
	  }
	}
      }
      else {z--;}
      ///

      if (c2 >= 1) {
	if (m < max) m++;
      }
      else {
	m = m-1;
      }
    }
    // if (seq > n+1) {ERROR: } // for preprocessing phase 
    //assume (seq <= n+1); // {ERROR: }
 

  }
}





