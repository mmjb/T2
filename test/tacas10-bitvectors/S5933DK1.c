
typedef unsigned int    size_t;
typedef unsigned long ULONG;

int main(void)
{
  ULONG numxfer;
  size_t Item_u_DmaWork_nbytes;

  while (Item_u_DmaWork_nbytes) {

    ;

    switch (Item_u_DmaWork_nbytes) {

        case 1:
        ;
        numxfer = 1;
        break;

        case 2:
        ;
        numxfer = 2;
        break;

        case 3:
        ;
        numxfer = 3;
        break;

        default:
        ;
        numxfer = 4;
        break;
    }

    ;
    Item_u_DmaWork_nbytes  -= numxfer;

    ;
  }

  return 0;
}
