/*----------------------------------------------------------------------------*/
/* sys_types.h                                              10/20/10 15:19:19 */
/*                                                                            */
/* (c) Texas Instruments 2003-2010, All rights reserved.                      */
/*                                                                            */


#ifndef __sys_types_h__
#define __sys_types_h__

/*----------------------------------------------------------------------------*/
/* Standard Types                                                             */

typedef signed char T_S8;
#define MAX_S8 (127)
#define MIN_S8 (-128)

typedef unsigned char T_U8;
#define MAX_U8 (255)
#define MIN_U8 (0)

typedef signed short T_S16;
#define MAX_S16 (32767)
#define MIN_S16 (-32767-1)

typedef unsigned short T_U16;
#define MAX_U16 (0xFFFFU)
#define MIN_U16 (0)

typedef signed int T_S32;
#define MAX_S32 (2147483647L)
#define MIN_S32 (-2147483647L-1)

typedef unsigned int T_U32;
#define MAX_U32 (0xFFFFFFFFU)
#define MIN_U32 (0)

typedef float T_F32;
#define MAX_F32 (3.39e+38)
#define MIN_F32 (1.18e-38)

typedef double T_F64;
#define MAX_F64 (1.79e+308)
#define MIN_F64 (2.23e-308)


#endif
/*----------------------------------------------------------------------------*/

