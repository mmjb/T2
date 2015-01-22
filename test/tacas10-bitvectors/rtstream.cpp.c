
typedef unsigned long ULONG;
typedef char BOOL;
#define TRUE 1
#define FALSE 0

int nondet();

int main(void)
{
  ULONG count = 0;
  BOOL bTimedOut = TRUE;

  do
  {
      if (nondet())
      {
          bTimedOut = FALSE;
          break;
      }

      ;

  } while (count++ < 10);

  return 0;
}
