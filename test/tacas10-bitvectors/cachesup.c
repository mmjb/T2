#define REPINNED_BCBS_ARRAY_SIZE (4)

typedef unsigned long ULONG;

int main(void)
{
  ULONG i;

  for (i = 0; i < REPINNED_BCBS_ARRAY_SIZE; i += 1) {
    ULONG j;

    for (j = i + 1; j < REPINNED_BCBS_ARRAY_SIZE; j++) {

        ;
    }
  }

  return 0;
}
