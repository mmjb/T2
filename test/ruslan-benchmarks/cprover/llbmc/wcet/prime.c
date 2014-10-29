/*
 * MDH WCET BENCHMARK SUITE. File version $Id: prime.c,v 1.2 2005/12/09
 * 14:52:02 jgn Exp $
 */

/*
 * Changes:
 JG 2005/12/08: Prototypes added, and changed exit to retun in
 * main.
 */

typedef unsigned char bool;
typedef unsigned int uint;

bool divides(uint n, uint m);
bool even(uint n);
bool prime(uint n);
void            swap(uint * a, uint * b);

inline
bool divides(uint n, uint m)
{
        return (m % n == 0);
}

inline
bool even(uint n)
{
        return (divides(2, n));
}

inline
bool prime(uint n)
{
        uint i;

        if (even(n))
            return (n == 2);

        for (i = 3; i * i <= n; i += 2) {
            if (divides(i, n))    /* ai: loop here min 0 max 357 end; */
                return 0;
        }
        return (n > 1);
}

inline
void
swap(uint * a, uint * b)
{
    uint tmp = *a;
    *a = *b;
    *b = tmp;
}

int
main()
{
    uint x = 21649;
    uint y = 513239;

    swap(&x, &y);

    return (!(prime(x) && prime(y)));
}
