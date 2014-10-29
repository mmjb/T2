#include "assume.h"
#include "patterns.h"

void main() {
  int NONDET;
  int N;
  int walker;
  int choice;

  int seq = 1;
  int i = seq;
  __INITPATTERN
    

  N = NONDET;
  assume (N == 2);

  walker = 1;

  while ((walker <= N) && (walker >= 1)) {
    
    choice = NONDET;
    assume (choice >= 0);
    assume (choice <= 1);

    /* Instrumentation */
    if (z <= 0) {
      if (i > 0) {assume (choice <= 0); i--;}
      else {seq++; i = seq; z = NONDET; assume (z >= 0); }
    } 
    else {z--;}
    
    if (choice <= 0) walker--; else walker++;
 
    //if (seq > N+1) { ERROR: } // for preprocessing
    //assume (seq <= N+1);
  }
}
  
  
 
