
#ifndef STDINT_INC
#define STDINT_INC

/* This file will get picked up when stdint.h does not appear in the default
include path (which it doesn't seem to be - even though the file exists). */

typedef signed char int8_t;
typedef unsigned char uint8_t;
typedef short int16_t;
typedef unsigned short uint16_t;
typedef long int32_t;
typedef unsigned long uint32_t;

#endif /* STDINT_INC */
