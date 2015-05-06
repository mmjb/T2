
typedef unsigned char UCHAR;

int main(void)
{
  UCHAR i; // nondet

  while(i)
  {
     ;
     i = i & (i-1);
  }

  return 0;
}
