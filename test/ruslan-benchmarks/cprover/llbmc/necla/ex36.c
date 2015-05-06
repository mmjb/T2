#include "necla.h"
/* #include <stdlib.h> */

/*** bigint.c ***/

/*  This is a very crude large integer package.  The purpose is to teach, not to
be efficient.  See freelip or miracl for very efficient code or check out the
commercial packages like Macsyma, Maple or the other similar products.  The basis
of these routines come from J.W. Crenshaw and several articles in his "Programmers
Toolbox" in Embedded Systems Programming magazine from Dec. 1996 thru Sept. 1997

http://www.eskimo.com/~eresrch/fast_onb/bigint.c
*/


/**
  Sriram Sankaranarayanan:

   There are two bugs in this code.
   One is in the very end where I
   made a blunder with the free.

   The other I leave it as a challenge to the
   person going through this to try and
   crack with their tool.
   ;-)

--*/

   

#include <stdio.h>
#include "ex36.h"

/*  clear all bits in a large integer storage block.  */

inline void int_null( a)
BIGINT *a;
{
	INDEX i;
	
	INTLOOP (i) a->hw[i] = 0;
}

/*  copy one BIGINT block to another  */

inline void int_copy( a, b)
BIGINT *a, *b;
{
	INDEX i;
	
	INTLOOP (i) b->hw[i] = a->hw[i];
}

/*  for use in the far distant future, convert a packed field to a large
	integer.  Does a simple expansion.  The large integer is 4 times bigger
	to accomodate multiplication (once!).
*/

inline void field_to_int( a, b)
FIELD2N *a;
BIGINT *b;
{
	INDEX	i, j;
	
	int_null( b);
	for (i=NUMWORD; i>=0; i--)
	{
		j = INTMAX - ((NUMWORD - i)<<1);
		b->hw[j] = a->e[i] & LOMASK;
		j--;
		b->hw[j] = (a->e[i] & HIMASK) >> HALFSIZE;
	}
}

/*  Pack a BIGINT variable back into a FIELD2N size one.  */

inline void int_to_field( a, b)
BIGINT *a;
FIELD2N *b;
{
	INDEX i, j;
	
	SUMLOOP(i)
	{
		j = (i + MAXLONG) << 1;
		b->e[i] = a->hw[j+1] | (a->hw[j] << HALFSIZE);
	}
}

/*  Negate a BIGINT in place.  Each half word is complemented, then we add 1  */

inline void int_neg( a)
BIGINT *a;
{
	INDEX i;
	
	INTLOOP(i) a->hw[i] = ~a->hw[i] & LOMASK;
	INTLOOP(i)
	{
		a->hw[i]++;
		if (a->hw[i] & LOMASK) break;
		a->hw[i] &= LOMASK;
	}
}

/*  add two BIGINTS to get a third.  c = a + b  
	Unlike the polynomial or ONB math, c can be one of a or b
*/

inline void int_add( a, b, c)
BIGINT *a, *b, *c;
{
	INDEX i;
	ELEMENT ec;
	
	ec = 0;
	INTLOOP (i)
	{
	/* add previous carry bit to each term  */
		ec = a->hw[i] + b->hw[i] + (ec >> HALFSIZE);	
		c->hw[i] = ec & LOMASK;
	}
}

/*  subtract two BIGINTS, c = a - b == a + (-b).  
	as in addition, c can point to a or b and still works
*/

inline void int_sub( a, b, c)
BIGINT *a, *b, *c;
{
	BIGINT negb;
	
	int_copy( b, &negb);
	int_neg( &negb);
	int_add( a, &negb, c);
}

/*  multiply two BIGINTs to get a third.
	Do NOT attempt to do 2 multiplies in a row without a division in between.
	You may get an overflow and there is no provision in this code to return
	an error condition for that.  See more advanced packages for correct way
	to do this.  c can *not* be one of a or b, it must be a separate storage
	location.
*/

inline void int_mul( a, b, c)
BIGINT *a, *b, *c;
{
	ELEMENT		ea, eb, mul;
	INDEX		i, j, k;
	BIGINT		sum;
	
	int_null(c);
	
	for ( i = INTMAX; i > INTMAX/2; i--)
	{
		ea = a->hw[i];
		int_null( &sum);
		for ( j = INTMAX; j > INTMAX/2; j--)
		{
			eb = b->hw[j];
			k = i + j - INTMAX;
			mul = ea * eb + sum.hw[k];
			sum.hw[k] = mul & LOMASK;
			sum.hw[k-1] = mul >> HALFSIZE;
		}
		int_add( &sum, c, c);
	}
}

/*  unsigned divide.  Input full sized numerator (top), 
	half sized denominator (bottom).
	Output half sized quotient and half sized remainder.
	Exceptionally crude but works ok for basics, error
	conditions return zero results.
*/

inline void int_div( top, bottom, quotient, remainder)
BIGINT *top, *bottom, *quotient, *remainder;
{
	BIGINT d, e;
	ELEMENT mask;
	INDEX	l, m, n, i, j;
	
/*  first step, initialize counters to most significant
	bit position in top and bottom.
*/
	int_copy( top, &d);
	int_copy( bottom, &e);
	l = (INTMAX + 1) * HALFSIZE;
	for( i=0; i<=INTMAX; i++)
	{
		if (!d.hw[i]) l -= HALFSIZE;
		else break;
	}
	mask = 1L << (HALFSIZE-1);
	for ( j=0; j<HALFSIZE; j++)
	{
		if ( !(d.hw[i] & mask))
		{
			l--;
			mask >>= 1;
		}
		else break;
	}

/*  same thing for bottom, compute msb position  */

	m = (INTMAX + 1) * HALFSIZE;
	for( i=0; i<=INTMAX; i++)
	{
		if (!e.hw[i]) m -= HALFSIZE;
		else break;
	}
	mask = 1L << (HALFSIZE-1);
	for ( j=0; j<HALFSIZE; j++)
	{
		if ( !(e.hw[i] & mask))
		{
			m--;
			mask >>= 1;
		}
		else break;
	}
	
/*  check for error inputs, does not check for zero, so is 
	actually incorrect.
*/
	if (!m)			/*  x/1 = x */
	{
		int_copy( top, quotient);
		int_null( remainder);
	}
	if (!l | (l<m))			/*  1/x = 0 */
	{
		int_null( quotient);
		int_copy( bottom, remainder);
	}

/*  next step, shift bottom over to align msb with top msb  */

	n = l - m;
	i = n;
	while ( i > HALFSIZE )
	{
		for (j=0; j<INTMAX; j++) e.hw[j] = e.hw[j+1];
		i -= HALFSIZE;
		e.hw[INTMAX] = 0;
	}
	mask = 0;
	while ( i > 0 )
	{
		INTLOOP (j)
		{
			e.hw[j] = (e.hw[j] << 1) | mask;
			mask = e.hw[j] & CARRY ? 1 : 0;
			e.hw[j] &= LOMASK;
		}
		i--;
	}

/*  main division loop.  check to see if we can subtract shifted bottom
	from what's left on top.  If we can, set that bit in quotient and do
	subtract.  if we can't, just shift bottom right and repeat until only
	remainder is left.
*/

	int_null( quotient);
	while ( n>=0)
	{
		i = INTMAX - l/HALFSIZE;
		j = INTMAX - n/HALFSIZE;
		while ( (d.hw[i] == e.hw[i]) && ( i<INTMAX) ) i++;
		if ( d.hw[i] >= e.hw[i] )
		{
			int_sub( &d, &e, &d);
			mask = 1L << ( n%HALFSIZE );
			quotient->hw[j] |= mask;
		}
		INTLOOP(j)
		{
			if (j) mask = ( e.hw[j-1] & 1) ? CARRY : 0;
			else mask = 0;
			e.hw[j] = (e.hw[j] | mask) >> 1;
		}
		n--;
		l--;
	}
	int_copy ( &d, remainder);
}

/*  Convert ascii string of decimal digits into BIGINT binary.
	Ignores out of range characters.  This is very crude, 'a' = '1',
	so watch out for input errors!
*/

inline void ascii_to_bigint( instring, outhex)
char *instring;
BIGINT *outhex;
{
	ELEMENT	ch;
	BIGINT	ten, digit, temp;
	INDEX	i=0;
	
	int_null( &ten);		/* create decimal multiplier */
	ten.hw[INTMAX] = 0xA;
	int_null( &digit);
	int_null( outhex);
	
	while ((ch = *instring++))
	{
		digit.hw[INTMAX] = ch & 0xF;
		int_mul( outhex, &ten, &temp);
		if (digit.hw[INTMAX] > 9) continue;
		int_add( &temp, &digit, outhex);
	}
}

/*  Convert binary BIGINT to ascii string.  Assumes destination has 
	enough characters to hold result.  This is 4*HALFSIZE*MAXLONG bits
	= Log(2)*4*HALFSIZE*MAXLONG = 1.20412*HALFSIZE*MAXLONG characters
	or about 5/4*HALFSIZE*MAXLONG chars.  Works backwards and blank
	fills destination string.
*/

inline void bigint_to_ascii( inhex, outstring)
BIGINT *inhex;
char *outstring;
{
	BIGINT	top, ten, quotient, remainder;
	ELEMENT	check;
	INDEX	i;

	int_copy( inhex, &top);
	int_null( &ten);		/*  create constant 10 */
	ten.hw[INTMAX] = 0xA;
	for (i=0; i<MAXSTRING; i++) *outstring++ = ' ';  /*  blank fill and null string */
	outstring--;
	*outstring-- = 0;
	
	check = 1;
	while (check)
	{
		int_div( &top, &ten, &quotient, &remainder);
		*outstring-- = remainder.hw[INTMAX] | '0';
		check = 0;
		INTLOOP(i) check |= quotient.hw[i];
		int_copy( &quotient, &top);
	}
}


/*--
  SS:  The harness function. Initialize two
  bigints in some way and carry out some function
  on them based on the input specification. After that,
  free them.
  --*/

#define ALLOC_INIT 1132
#define ALIAS_INIT 12
#define COPY_INIT 1872
#define ADD_CMD 12
#define SUB_CMD 15
#define MUL_CMD 123
#define DIV_CMD 19846

/* int __llbmc_main(int cmd1, int zer, int cmd2){ */
int main(int cmd1, int zer, int cmd2){

   BIGINT *a, *b, *c, *d;
   c= (BIGINT *) malloc(1 * sizeof(BIGINT));
   d= (BIGINT *) malloc(1 * sizeof(BIGINT));
   int_null(c);
   int_null(d);
   switch (cmd1){
      case ALLOC_INIT:
         a= (BIGINT *) malloc(1 * sizeof(BIGINT));
         if (zer > 0) int_null(a);
         b= (BIGINT *) malloc(1 * sizeof(BIGINT));
         if (zer > 0)  int_null(b);
         break;
      case COPY_INIT:
         a= (BIGINT *) malloc(1 * sizeof(BIGINT));
         if (zer > 0) int_null(a);
         b= (BIGINT *) malloc(1 * sizeof(BIGINT));
         int_copy(a,b);
      case ALIAS_INIT:
         a=b= (BIGINT *) malloc(1 * sizeof(BIGINT));
         if (zer > 0) int_null(a);
         break;
      default:
         return -1;
   }

   switch(cmd2){
      case ADD_CMD:
         int_add(a,b,b);
         int_add(a,b,b);
         int_add(a,b,c);
         break;
      case SUB_CMD:
         int_sub(a,b,c);
         break;
      case MUL_CMD:
         int_mul(a,b,c);
         break;
      case DIV_CMD:
         int_div(a,b,c,d);
         
   }

   free(a);
   free(b); /*-- SS:possible bug here, esp. if we chose to alias a to b --*/
   free(c);
   free(d);

   return 0;
}
