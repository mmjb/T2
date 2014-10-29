int count = 0;
int fair_nondet()
{
   if (count < 5) {
       count++;
       return 0;
   } else {
       count = 0;
       return 1;
   }
}


void main()
{
    int x;
    int y;
    int z;

    while(x<y) {
        while(y<z) {
            if (fair_nondet()) {
                y++;
            }
        }
        x++;
    }
}
