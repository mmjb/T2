void main()
{
    int x;

    for(;;) {
       x--;
       if (x < 0) return; /* AR: used to be x > 0 */
    }
}
