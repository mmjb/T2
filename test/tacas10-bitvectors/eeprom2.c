
#define EEDO                        0x08    // EEPROM data out
#define EEDI                        0x04    // EEPROM data in (set for writing data)

typedef unsigned short USHORT;

USHORT nondet();

int main(void)
{
  USHORT data; // nondet
  USHORT count; // nondet
  USHORT x,mask; // nondet

  mask = 0x01 << (count - 1);
  x &= ~(EEDO | EEDI);

  do
  {
      x &= ~EEDI;
      if(data & mask)
          x |= EEDI;

      ;

      mask = mask >> 1;
  } while(mask);

  return 0;
}
