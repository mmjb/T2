typedef unsigned long ULONG;

int nondet();

int main(void)
{
  ULONG context_Length;
  ULONG context_BytesRead;

  assume(context_Length);
  assume(context_BytesRead);

  while (  (context_BytesRead < context_Length)
        && (  nondet()
           || (context_BytesRead%3)
        )  )
  {
      if (nondet())
      {
        ;
        context_BytesRead = context_BytesRead + 1;
      }
      else
      {
        ;
        break;
      }
  }

  return 0;
}
