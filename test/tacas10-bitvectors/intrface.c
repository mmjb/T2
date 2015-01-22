
typedef unsigned long ULONG_PTR;

typedef ULONG_PTR KAFFINITY;

int main(void)
{
  KAFFINITY Processors;

  assume(Processors!=1);

  while (Processors) {
      if (Processors & 1) {

          ;

      }
      Processors = Processors >> 1;
      ;
  }

  return 0;
}
