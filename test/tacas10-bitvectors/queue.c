
typedef long LONG;

int nondet();

int main(void)
{
  LONG ix;

  assume(ix>=0);

  // if last char isn't digit, decrement it.
  while((ix > -1) && nondet()) {
    ix--;
  }

  return 0;
}
