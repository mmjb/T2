// Property: F G Stored==0

// #include "ctl.h"

int Stored;

 inline void init() { Stored = 0; }



 inline void callback() {}
 inline void IoQueueWorkItem() {}

inline void body() {
    while(nondet()) {


           if (nondet()) {
               //
               // We are safely at PASSIVE_LEVEL, call callback directly
               // to perform
               // this operation immediately.
               //
               callback ();

           } else {
	       IoQueueWorkItem ();
               Stored = 1;
               break;
           }
    }

    // Lower Irql and process

    if (Stored==1) {
        callback ();
        Stored = 0;
    }
}

 int main() { init(); body(); }
