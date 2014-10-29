int x;
int y;

int nondet() { int x; return x;}

void main()
{

    x = nondet();
    y = nondet();

    while(x<y) {
        x++;
    }
}
