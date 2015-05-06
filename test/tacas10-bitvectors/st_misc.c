
#define DOT11_RATE_SET_MAX_LENGTH               126 // 126 bytes

typedef unsigned long ULONG;
typedef unsigned char UCHAR;

typedef struct _DOT11_RATE_SET {
    ULONG uRateSetLength;
    /*__field_ecount_part(DOT11_RATE_SET_MAX_LENGTH, uRateSetLength) */
    UCHAR ucRateSet[DOT11_RATE_SET_MAX_LENGTH];
} DOT11_RATE_SET, * PDOT11_RATE_SET;

int main(void)
{
  ULONG i,j;
  DOT11_RATE_SET rateSet;
  DOT11_RATE_SET APRateSet;

  ULONG rateSet_uRateSetLength=rateSet.uRateSetLength;
  ULONG APRateSet_uRateSetLength=APRateSet.uRateSetLength;

  i = 0;
  while (i < rateSet_uRateSetLength)
  {
    for (j = 0; j < APRateSet_uRateSetLength; j++)
    {
        if (nondet())
            break;
    }

    //
    // remove the rate if it is not in AP's rate set
    //
    if (j == APRateSet_uRateSetLength)
    {
        rateSet_uRateSetLength--;
        ;
    }
    else
    {
        i++;
    }
  }

  return 0;
}
