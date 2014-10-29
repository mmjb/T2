/*
  Separation logic assertions.
*/

/*
   How this works in the toolchain:

   1. Add a function (SL_pto, for instance) for the separation logic
   connectives you want. If the logic connective takes arbitrary arguments
   (like PTo), use varargs. (Care: slam fe's treatment of varargs changes from
   time to time.)

   2. Declare the name of this function in SIL.AssertionNames.

   3. Use frontend_slam to parse this function into an Exp.Fun(sl_fun,args).

   4. Extend ReconstructSpecs.sh_of_exp by adding a case to convert this
   function into a symbolic heap.


 */
#ifndef _SLAYER_SPECIFICATIONS_H_
#define _SLAYER_SPECIFICATIONS_H_


#ifdef SLAyer

// Pretenders of basic domains.
typedef void* SL_Tsep_logic;
typedef void* SL_Texp;
typedef void* SL_TPatn;

#define SL_EMPTY_BODY {}

// Greenspun's law.
SL_Texp SL_nil(void) { SL_EMPTY_BODY } // []
SL_Texp SL_cons(SL_Texp hd, SL_Texp tl) { SL_EMPTY_BODY } // ht::tl

// Atomic propositions
SL_Tsep_logic SL_ff(void) {} // ff
SL_Tsep_logic SL_tt(void) {} // tt
SL_Tsep_logic SL_exp(int e) {} // inject a pure atomic expr into SH. Only vars, ==, != allowed in e.
//// Useful macros for pto.
#define SL_FIELD(x) SL_cons(x,SL_nil())
#define SL_FIELD2(x,y) SL_cons(x,SL_cons(y,SL_nil()))
SL_Tsep_logic SL_pto(SL_Texp p, ...) {}  // PointsTo(p,fld_seq0,e0,fld_seq1,e1,...).

// emp, \/, *, exists.
SL_Tsep_logic SL_emp(void) { SL_EMPTY_BODY }
SL_Tsep_logic SL_or(SL_Tsep_logic p, SL_Tsep_logic q) { SL_EMPTY_BODY }
SL_Tsep_logic SL_star(SL_Tsep_logic p, SL_Tsep_logic q) { SL_EMPTY_BODY }

//// You have to declare "long x" yourself. MSVC doesn't have a
//// "Statements and Declarations in Expressions" extension, so this:
////       #define SL_exists(x,body) ({long x; SL_exists(x,body)})
//// doesn't work.
SL_Tsep_logic SL_exists(SL_Texp x,SL_Tsep_logic body) { }
#define SL_exists2(x,y,body) SL_exists(x,SL_exists(y,body))
#define SL_exists3(x,y,z,body) SL_exists(x,SL_exists(y,SL_exists(z,body)))

// Generic list predicates.
SL_TPatn SL_sll_Flink(void) { SL_EMPTY_BODY }       // Same name as used by SIL/Discovery.
SL_TPatn SL_dll_Flink_Blink(void) { SL_EMPTY_BODY } //
// SL_ls params:
//    Patn p          - name of Discovery-exported patn
//    len             - length of list (expr).
//    fnt,prv,nxt,bck - pointer sequences (list of vars).
//    of,ob           - offset of fnt and bck (list of fields).
SL_Tsep_logic SL_ls(SL_TPatn p, SL_Texp len, SL_Texp prv, SL_Texp fnt, SL_Texp of, SL_Texp bck, SL_Texp ob, SL_Texp nxt) { };
//// Short-cuts for ls:
//#define SL_SLL(len,x,o,y) SL_ls(SL_sll_Flink(),len,x,0,y,0)
//#define SL_DLL(len,x,o,y) SL_ls(SL_dll_Flink_Blink(),len,x,0,y,0)

void SL_pre(SL_Tsep_logic p,...) { SL_EMPTY_BODY } // SL_pre(pre,ghosts)
void SL_post(SL_Tsep_logic q) { SL_EMPTY_BODY }

#define SL_NO_GHOSTS
#define SL_NO_CMNDS

/*
  SL_triple(pre,cc,post,ghosts),
    where
    - pre, post are predicates constructed using the SL_* functions.
    - cc is a ";"-separated list of Cmnds (not Conts). Optional.
    - ghosts: "," separated identifiers. Optional.

  Style Cop: write your specs like this:
  <code>
  void SL_triple_MyAssertionName(...)
  {
    SL_triple(pre,
              commands,
              post,
	      ghosts);
  }
  </code>

  The prefix SL_triple is essential for ReconstuctSpecs to convert these C
  constructs into SH ones.

  Style Guide: When you don't have commands/ghosts, use the
  SL_NO_{GHOSTS,CMNDS} macros make this explicit in the SL_triple assertion.

*/
#define SL_triple(pre,cc,post,...)		\
  {						\
    long SL_dummy_var,__VA_ARGS__;		\
    SL_pre(pre,__VA_ARGS__);			\
    cc;						\
    SL_post(post);				\
  }


#define SL_ASSUME(q) SL_triple(SL_tt(),SL_NO_CMNDS,q) // {tt}_{q};
#define SL_ASSERT(q)  SL_triple(q,SL_NO_CMNDS,q)       // {q}_{q};
#define SL_ENTAIL(lhs,rhs) ASSUMPTION(lhs); ASSERTION(rhs); // {tt}_{lhs};{rhs}_{rhs};





#define SL_DIVERGE ASSUMPTION(SL_ff())

// If an entailment holds, then NONENTAILMENT will return.
#define SL_NONENTAIL(q) if(nondet()) { ASSUMPTION(q); ASSERTION(q); return; }


/*
   Separation logic assertions --- end.
*/
#endif // #ifdef SLAyer

#endif // #ifndef _SLAYER_SPECIFICATIONS_H_
