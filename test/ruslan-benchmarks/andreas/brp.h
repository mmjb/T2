#ifndef __BRP_H
#define __BRP_H

//#include "qprover.h"

#define SREP_INIT 0
#define SREP_OK   1
#define SREP_NOK  2
#define SREP_DK   3

#define RREP_INIT 0
#define RREP_FST  1
#define RREP_INC  2
#define RREP_OK   3

#ifndef __PROP1__  // prop 4 probability that eventually the receiver does not receive any chunk and the sender tried to send a chunk
#ifndef __PROP2__  // prop 2 probability that eventually the sender reports an uncertainty on the success of the transmission
#ifndef __PROP3__  // prop 1
#ifndef __COST__
#define __PROP1__
#endif
#endif
#endif
#endif

//#ifndef N
//#define N 64
//#endif 

//#ifndef MAX
//#define MAX 5
//#endif

#endif
