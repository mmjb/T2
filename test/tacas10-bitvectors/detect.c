

int main(void)
{
  // Unfolded array to make it easier for Rankfinder/Seneschal
  // Obviously, this could be done automatically.
  
  //unsigned statusBits[] = {1,2,0};
  unsigned long s_0 = 1;
  unsigned long s_1 = 2;
  unsigned long s_2 = 0;

  //for (int i = 0; statusBits[i] != 0; i++) ;
  int i;
  while(1)
  {
    if(i==0) { if(s_0==0) break; }
    else if(i==1) { if(s_1==0) break; }
    else if(i==2) { if(s_2==0) break; }
    i++;
  }

  return 0;
}
