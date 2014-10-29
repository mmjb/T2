#include "assume.h"

// Example from "Probabilistic termination in B", McIver et al.
// Symmetry breaking in FireWire protocol

void main() {

  int xx, yy;
  int c1, c2;
  int NONDET;
  int z;
  int pattern = 0;
  int buffer;
  int seqlen = 1;
  int it = seqlen;

  xx = 0;
  yy = 0;

  z = NONDET;
  assume (z >= 1);

  /*
    pattern can take the values 0,1,2,3; 
    these represent the values (c2, c1) in binary ( (0,0), (0,1), (1,0), (1,1) )
    we enforce the pattern (0,0)...(0,1)...(1,0)...(1,1)...(0,0)...(0,1)...
    Of course, if the pattern (0,1) is chosen the first time, we will terminate :-)
  */


  while (xx == yy) {


    /* if z==0, insert pattern */
    if (z == 0) {
      
      if (it > 0) {
	it--;
	// Set (c2, c1) to the pattern in binary representation
	buffer = pattern;
	if (buffer > 2) {
	  c2 = 1;
	  buffer = buffer-2;
	}
	else c2 = 0;
	c1 = buffer;
      }
      else {
	// pattern = pattern + 1 mod 4
	if (pattern >= 3) { pattern = 0; }
	else { pattern++; }
	
	// reinit counter
	z = NONDET;
	assume (z >= 1);
	seqlen++;
	it = seqlen;
      }
    } 
    else {
      z--;
      c1 = NONDET;
      c2 = NONDET;
    }
 
    if (c1 == 0) {
      xx = 0;
    }
    else {
      xx = 1;
    }
    
    if (c2 == 0) {
      yy = 0; 
    }
    else {
      yy = 1;
    }
  }
}
