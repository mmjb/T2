#include "assume.h"
#include "brp.h"
#include "patterns.h"
// model of bounded retransmission protocol 
// dxp/gxn/mxk 30/06/08
// file for property 4: probability that eventually the receiver does not receive any chunk and the sender tried to send a chunk

// variables for the sender
int NONDET;
int i; // number of chunks sent
int bs;
int s_ab = 0;
int fs; // first chunk
int ls; // last chunk


// variables for the receiver
int br;
int r_ab = 0;
int fr; // first chunk
int lr; // last chunk
int recv = 0; // has reveived something
int rrep = RREP_INIT; // 1 = FST, 2 = INC, 3 =OK

int c1 = 0; 
int c2 = 0;


int main() {  

  int N = NONDET;
  __INITPATTERNP
  assume (N >= 1);
  
  i = 0; // start with first chunk
  while (i<N) { // try to send all N chunks

    if (i <= 0) fs = 1; else fs = 0;
    if (i >=N-1) ls = 1; else ls = 0;
    bs = s_ab; // set bit for current chunk
    //nrtr = 0; // current number of retransmissions of chunk 

    while (1==1) { // maximum number of retransmissions is UNBOUNDED
       c1 = NONDET;
       assume (c1 >= 0);
       assume (c1 <= 1);

       __BEGINPP
	 __FIRSTP1(c1)
	 __P1(1, c1)
       __ENDPP
        
      if (c1 >= 1) { // message sent correctly
        fr = fs; // is it the first chunk
        lr = ls; // is it the last chunk
        br = bs; // set bit for current message
        if (recv <= 0) { // if it is the first chunk received then
          r_ab = br; // set bit for first chunk
        }
        recv = 1; // have received something chunk
        if (r_ab == br) { // if bit was correct
          // set rrep
          if (fr != 0 && lr==0) 
            rrep = RREP_FST;
          else if (fr<=0 && lr<=0) 
            rrep = RREP_INC;
          else if (lr >= 1) 
            rrep = RREP_OK;
          // change bit
	  if (r_ab >= 1) r_ab = 0; else r_ab = 1;
        } 
	c2 = NONDET;
	assume (c2 >= 0);
	assume (c2 <= 1);

       __BEGINPP
	 __FIRSTP1(c2)
	 __P1(1, c2)
       __ENDPP

        if (c2 == 1) { // ack arrives correctly
	  if (s_ab >= 1) s_ab = 0; else s_ab = 1;
	  i++; // move onto next chunk            
	  break; // leave loop and move onto next chunk
        }
      }
       //assume (next < N+1);
       //if (next >= N+1) {ERROR:}
       // if (next >= N+1) return;
    }
     //if (srep==SREP_NOK) break;
     //if (srep==SREP_DK) break; // if failed to send chunk then stop (error)
    //if (next >= N+1) {ERROR:}
    //assume (next < N+1);
    //    If (next >= N+1) return;
  }
 
}
