
#define IR_SAMPLE_PERIOD                 50

typedef long LONG;
typedef unsigned long ULONG;

int main(void)
{
  LONG numSamplesThisPacket;
  ULONG bitPos = 0;

  if(numSamplesThisPacket>0)
  {

  numSamplesThisPacket /= IR_SAMPLE_PERIOD;


  while (numSamplesThisPacket > 0) {

    ;

    if ((numSamplesThisPacket + bitPos) < 8) {

        bitPos += numSamplesThisPacket;
        break;

    } else {

        numSamplesThisPacket -= (8-bitPos);

        ;

        bitPos = 0;

        ;

    }

  }

  }

  return 0;
}
