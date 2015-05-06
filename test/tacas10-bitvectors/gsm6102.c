
typedef long LONG;

int main(void)
{
  LONG l_var;

  assume(l_var > 0);

  while (l_var < 1073741824)
  {
    ;
    l_var = l_var << 1;
  }

  return 0;
}
