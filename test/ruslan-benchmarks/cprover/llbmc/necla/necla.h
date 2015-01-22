#define ASSERT(b) __llbmc_assert(b)
#define ASSUME(b) __llbmc_assume(b)
#define __NONDET__ __llbmc_nondef_int

#include "llbmc.h"
