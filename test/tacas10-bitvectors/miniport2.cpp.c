
#define NUM2VOICES 18

typedef unsigned short      WORD;

int nondet();

int main(void)
{
  WORD i, found;

  found = 0 ;

  for (i = (found + 1); i < NUM2VOICES; i++)
    if (nondet())
    {
       found = i ;
    }

  return 0;
}
