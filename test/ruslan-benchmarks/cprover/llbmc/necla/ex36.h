/*** bigint.h ***/

#include "field2n.h"

/*  The following are used by the multiprecision integer package.
	This really is very crude.  See J. W. Crenshaw "Programmers
	Toolbox", Embedded Systems Programming Dec. 1996 for why you
	want to do this in assembler.
*/

#define	HALFSIZE	(WORDSIZE/2)
#define	HIMASK		(-1L<<HALFSIZE)
#define LOMASK		(~HIMASK)
#define CARRY		(1L<<HALFSIZE)
#define MSB_HW		(CARRY>>1)
#define	INTMAX		(4*MAXLONG-1)
#define MAXSTRING	(MAXLONG*WORDSIZE/3)

#define	INTLOOP(i)	for(i=INTMAX;i>=0;i--)

typedef struct {
	ELEMENT		hw[4*MAXLONG];
}  BIGINT;

void int_null();
void int_copy();
void field_to_int();
void int_to_field();
void int_neg();
void int_add();
void int_sub();
void int_mul();
void int_div();
void ascii_to_bigint();
void bigint_to_ascii();
void int_gcd();
void mod_exp();
void mod_inv();
void int_div2();


