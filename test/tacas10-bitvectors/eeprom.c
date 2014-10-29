
#define EEDO                        0x08    // EEPROM data out
#define EEDI                        0x04    // EEPROM data in (set for writing data)
#define EEPROM_MAX_SIZE        256

typedef unsigned short USHORT;

USHORT nondet();

int main(void)
{
  USHORT x;
  USHORT size = 1;

  do
  {
    size *= 2;          // each bit of address doubles eeprom size
    x |= EEDO;          // set bit to detect "dummy zero"
    x &= ~EEDI;         // address consists of all zeros

    ;

    // check for "dummy zero"
    x = nondet();
    if (size > EEPROM_MAX_SIZE)
    {
        size = 0;
        break;
    }
  }
  while (x & EEDO);

  return 0;
}
