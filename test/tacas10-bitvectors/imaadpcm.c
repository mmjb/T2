
typedef unsigned int UINT;

int main(void)
{
  UINT cbBlockLength; //nondet

  if( 0 == cbBlockLength%8 )
  {

  while( 0 != cbBlockLength )
  {
      cbBlockLength -= 8;
      ;
  }
  
  }

  return 0;
}
