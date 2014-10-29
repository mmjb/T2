#include "necla.h"
/*
   An array with constant-time reset.
*/

/* #include <stdlib.h> */
#define NULL 0

typedef int data_t;
typedef size_t idx_t;
typedef int bool_t;

typedef struct {
  data_t resetVal;
  data_t *data;
  idx_t numData;
  idx_t maxNumData;
  idx_t *dataIdx;
  idx_t *dataWriteEvidence;
} buf_t;

inline buf_t *bufAlloc(size_t n) {
  size_t i;
  buf_t *b = (buf_t *)malloc(sizeof(buf_t));
  b->data = (data_t *)malloc(sizeof(data_t) * n);
  b->maxNumData = n;
  b->numData = 0;
  for (i=0; i<n; i++)
     b->dataWriteEvidence[i] = n;
  return b;
}

inline bool_t bufIdxWritten(const buf_t *buf_, idx_t idx_) {
  ASSUME(buf_ != NULL );
  /*ASSUME(0 <= idx_ );*/
  ASSUME(idx_ < buf_->maxNumData);
  return /*buf_->dataWriteEvidence[idx_] >= 0 &&*/
    buf_->dataWriteEvidence[idx_] < buf_->numData &&
    buf_->dataIdx[buf_->dataWriteEvidence[idx_]] == idx_;
}

inline data_t bufRead(const buf_t *buf_, idx_t idx_) {
  ASSUME(buf_ != NULL );
  /*ASSUME(0 <= idx_ );*/
  ASSUME( idx_ < buf_->maxNumData);
  return bufIdxWritten(buf_, idx_) ? buf_->data[buf_->dataWriteEvidence[idx_]] : buf_->resetVal;
}

inline void bufReset(buf_t *buf_, data_t resetVal_) {
  ASSUME(buf_ != NULL);
  buf_->resetVal = resetVal_;
  buf_->numData = 0;
}

inline void bufWrite(buf_t *buf_, idx_t idx_, data_t val_) {
   ASSUME(buf_!=NULL);
   /*ASSUME(0 <= idx_);*/
   ASSUME(idx_ < buf_->maxNumData);
   idx_t writeDataTo = buf_->dataWriteEvidence[idx_];
   if (!bufIdxWritten(buf_, idx_)) {
    ASSERT(buf_->numData < buf_->maxNumData);
    buf_->dataIdx[buf_->numData] = idx_;
    buf_->dataWriteEvidence[idx_] = buf_->numData;
    writeDataTo = buf_->numData;
    buf_->numData++;
  }
  buf_->data[writeDataTo] = val_;
}

inline idx_t randomIdx(const buf_t *buf_) {
  ASSUME(buf_ != NULL);
  idx_t idx = __NONDET__();
  /*ASSUME(0 <= idx);*/
  ASSUME(idx < buf_->maxNumData);
  return idx;
}

int main(int argc, char *argv[]) {
  const int numWrites = 4, numReads = 10, numBufs = 3, maxN = 20;
  int i,j;
  data_t datum;
  bool_t shouldReset;
  bool_t datumOut;
  
  buf_t **bufs = (buf_t **)malloc(numBufs * sizeof(buf_t *));
  for (i=0; i<numBufs; i++)
     bufs[i] = bufAlloc(maxN);
  
  for (i=0; i<numWrites; i++) {
     for (j=0; j<numBufs; j++)
        bufWrite(bufs[j], randomIdx(bufs[j]), (data_t)__NONDET__());
     
  }
  
  for (i=0; i<numReads; i++) {
     for (j=0; j<numBufs; j++) {
        datum = (data_t)__NONDET__();
        shouldReset = __NONDET__();
        datumOut = (data_t)0;
        if (shouldReset)
           bufReset(bufs[j], datum);
        else
           datumOut = bufRead(bufs[j], randomIdx(bufs[j]));
        
        
     }
  }
  return 1;
}
