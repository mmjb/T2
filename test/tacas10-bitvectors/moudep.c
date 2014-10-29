
typedef unsigned long ULONG;

int nondet();

int main(void)
{
  ULONG Attempts;
  ULONG i;

  // a proper capped read-from-device loop

  for(i = 0; i < Attempts; i++) {

    if(nondet()) // device responded...
      break;

  }

  return 0;
}
