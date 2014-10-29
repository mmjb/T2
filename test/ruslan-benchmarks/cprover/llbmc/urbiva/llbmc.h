#ifndef LLBMC_H
#define LLBMC_H

#ifdef __cplusplus
extern "C" {
#endif

#include <stdint.h>

// assume/assert
void __llbmc_assert(int);
void __llbmc_assume(int);

// requires/ensures
void __llbmc_requires(int);
void __llbmc_ensures(int);

// uint_.../int_... nondefs
uint8_t __llbmc_nondef_uint8_t(void);
int8_t __llbmc_nondef_int8_t(void);
uint16_t __llbmc_nondef_uint16_t(void);
int16_t __llbmc_nondef_int16_t(void);
uint32_t __llbmc_nondef_uint32_t(void);
int32_t __llbmc_nondef_int32_t(void);
uint64_t __llbmc_nondef_uint64_t(void);
int64_t __llbmc_nondef_int64_t(void);

// other more nondefs
char __llbmc_nondef_char(void);
signed char __llbmc_nondef_signed_char(void);
unsigned char __llbmc_nondef_unsigned_char(void);
short __llbmc_nondef_short(void);
short int __llbmc_nondef_short_int(void);
signed short int __llbmc_nondef_signed_short_int(void);
unsigned short int __llbmc_nondef_unsigned_short_int(void);
int __llbmc_nondef_int(void);
signed int __llbmc_nondef_signed_int(void);
unsigned int __llbmc_nondef_unsigned_int(void);
long __llbmc_nondef_long(void);
long int __llbmc_nondef_long_int(void);
signed long int __llbmc_nondef_signed_long_int(void);
unsigned long int __llbmc_nondef_unsigned_long_int(void);
long long __llbmc_nondef_long_long(void);
long long int __llbmc_nondef_long_long_int(void);
signed long long int __llbmc_nondef_signed_long_long_int(void);
unsigned long long int __llbmc_nondef_unsigned_long_long_int(void);

// macros
#define assert(x) __llbmc_assert(x)
#define assume(x) __llbmc_assume(x)

#define requires(x) __llbmc_requires(x)
#define ensures(x) __llbmc_ensures(x)

#ifdef __cplusplus
}
#endif

#endif

