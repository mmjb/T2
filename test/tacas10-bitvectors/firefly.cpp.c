
int main(void)
{
  int i, j;
  j=1;

  for(i = 500; (i>0)&&(j>0); i-=j) {

      j = (i*9/100);

      ;
  }

  for(i = 12; i<500; i+=j) {

      j = (i*9/100);

      ;
  }

  return 0;
}
