
int nondet();

int main(void)
{
  short nCount, nOld;

  if(nCount <= nOld)
  {

  short nNew = nOld - nCount;
  for (;nNew > 0; nNew--)
  {
      if (nondet())
      {
          ;
      }
      else
      {
          nCount += nNew;
          break;
      }
  }

  }

  return 0;
}
