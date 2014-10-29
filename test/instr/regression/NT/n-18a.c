void main()
{
    int x;
    int y;

    for(;;) {
       x = y + x;
       if (x < 0) return; /* AR: used to be x > 0 */
    }
}
