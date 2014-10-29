
#define NETBIOS_NAME_LEN 16

int nondet();

int main(void)
{
  int      len, fieldLen;

  while(len < NETBIOS_NAME_LEN)
  {
      fieldLen=0;

      while (fieldLen < 4 && (len + fieldLen) < NETBIOS_NAME_LEN)
      {
          ;

          len++;
          fieldLen++;

          if (nondet())
              break;
      }

      if (nondet())
      {
//          return(Status);
        break;
      }

      ;
  }

  return 0;
}
