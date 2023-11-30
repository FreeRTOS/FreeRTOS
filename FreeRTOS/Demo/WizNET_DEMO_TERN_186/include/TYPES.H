/*
********************************************************************************
* Wiznet.
* 5F Simmtech Bldg., 228-3, Nonhyun-dong, Kangnam-gu,
* Seoul, Korea
*
* (c) Copyright 2002, Wiznet, Seoul, Korea
*
* Filename : types.h
* Programmer(s): 
* Created : 2002/01/
* Modified :
* Description : Define of data type.
********************************************************************************
*/

#ifndef _TYPES_H_
#define _TYPES_H_

#ifndef NULL
# define NULL		((void *) 0)
#endif

typedef enum { false, true } bool;

#ifndef _SIZE_T
#define _SIZE_T
typedef unsigned int size_t;
#endif

typedef	unsigned char	BYTE;		// 8-bit value
typedef	unsigned char	UCHAR;		// 8-bit value
typedef	         int	INT;		// 16-bit value
typedef	unsigned int	UINT;		// 16-bit value
typedef	unsigned short	USHORT;		// 16-bit value
typedef	unsigned short	WORD;		// 16-bit value
typedef	unsigned long	ULONG;		// 32-bit value
typedef	unsigned long	DWORD;		// 32-bit value

// bsd
typedef unsigned char	u_char;		// 8-bit value
typedef unsigned short	u_short;	// 16-bit value
typedef unsigned int		u_int;		// 16-bit value
typedef unsigned long	u_long;		// 32-bit value

typedef UCHAR	SOCKET;


/* Type for treating 4 byte variables with byte by byte */
typedef union un_l2cval
  {
  u_long	lVal;
  u_char	cVal[4];
  };

/* Type for treating 2 byte variables with byte by byte */
typedef union un_i2cval
  {
  u_int	iVal;
  u_char	cVal[2];
  };

#endif		// _TYPES_H_

