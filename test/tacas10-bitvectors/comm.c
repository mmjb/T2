
#define LINESTAT_XMIT_HOLDING_REG_EMPTY ((UCHAR) 1<<5)
#define REG_TIMEOUT_LOOPS 1000000

typedef unsigned int UINT;
typedef unsigned char UCHAR;

int main(void)
{
  UINT i = 0;
  UINT maxLoops = REG_TIMEOUT_LOOPS;
  UCHAR lineStatReg;

  do {
    lineStatReg = nondet();
  } while (!(lineStatReg & LINESTAT_XMIT_HOLDING_REG_EMPTY) && (++i < maxLoops));

  return 0;
}

