/******************************************************************************
* File Name    : types.h
* Version      : 1.0
* Device(s)    : Renesas
* Tool-Chain   : Renesas SH2A V9+
* OS           : None
* H/W Platform : SH2A
* Description  : User Defined Type Definition File
*******************************************************************************
* History      : DD.MM.YYYY Ver. Description
*              : 01.08.2009 1.00 MAB First Release
******************************************************************************/

/******************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Technology Corp. and is only
* intended for use with Renesas products. No other uses are authorized.
* This software is owned by Renesas Technology Corp. and is protected under
* all applicable laws, including copyright laws.
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES
* REGARDING THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY,
* INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A
* PARTICULAR PURPOSE AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY
* DISCLAIMED.
* TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS
* TECHNOLOGY CORP. NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE
* FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES
* FOR ANY REASON RELATED TO THE THIS SOFTWARE, EVEN IF RENESAS OR ITS
* AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this
* software and to discontinue the availability of this software.
* By using this software, you agree to the additional terms and
* conditions found by accessing the following link:
* http://www.renesas.com/disclaimer
******************************************************************************/
/* Copyright (C) 2008. Renesas Technology Corp.,       All Rights Reserved.  */
/* Copyright (C) 2009. Renesas Technology Europe Ltd., All Rights Reserved.  */
/*****************************************************************************/

#ifndef TYPES_H_INCLUDED
#define TYPES_H_INCLUDED

/******************************************************************************
User Includes
******************************************************************************/

#include "Compiler.h"

/******************************************************************************
Function Macros
******************************************************************************/

#ifndef SWAPWORD
#define SWAPWORD(x)           (WORD)((((x) & 0xFF) << 8) | (((x) >> 8) & 0xFF))
#endif

#ifndef LOBYTE
#define LOBYTE(x)             (BYTE)(x)
#endif

#ifndef HIBYTE
#define HIBYTE(x)             (BYTE)((x) >> 8)
#endif

#ifndef MAKEWORD
#define MAKEWORD(a, b)        ((WORD) (((BYTE) (a)) |\
                              ((WORD) ((BYTE) (b))) << 8))
#endif

/******************************************************************************
Typedefs
******************************************************************************/

/* Generic definitions */
#ifndef NULL                        /* set null ((void *)0) */
#define NULL                        0
#endif

#ifndef PNULL
#define PNULL                       ((PVOID)0)
#endif

#ifndef BIT_0                       /* set bits */
#define BIT_0                       0x1
#define BIT_1                       0x2
#define BIT_2                       0x4
#define BIT_3                       0x8
#define BIT_4                       0x10
#define BIT_5                       0x20
#define BIT_6                       0x40
#define BIT_7                       0x80

#define BIT_8                       0x100
#define BIT_9                       0x200
#define BIT_10                      0x400
#define BIT_11                      0x800
#define BIT_12                      0x1000
#define BIT_13                      0x2000
#define BIT_14                      0x4000
#define BIT_15                      0x8000

#define BIT_16                      0x10000L
#define BIT_17                      0x20000L
#define BIT_18                      0x40000L
#define BIT_19                      0x80000L
#define BIT_20                      0x100000L
#define BIT_21                      0x200000L
#define BIT_22                      0x400000L
#define BIT_23                      0x800000L

#define BIT_24                      0x1000000L
#define BIT_25                      0x2000000L
#define BIT_26                      0x4000000L
#define BIT_27                      0x8000000L
#define BIT_28                      0x10000000L
#define BIT_29                      0x20000000L
#define BIT_30                      0x40000000L
#define BIT_31                      0x80000000L
#endif

#ifndef TRUE                        /* true and false */
#define TRUE                        (BOOL)1
#endif

#ifndef FALSE
#define FALSE                       (BOOL)0
#endif

#if defined(WIN32_SH4) && defined(__cplusplus)
#define _SIZE_T
#else
#ifndef _SIZE_T
#define _SIZE_T
typedef unsigned long size_t;
#endif
#endif

#ifndef BOOL
#define BOOL                        BOOL
typedef unsigned char BOOL;
#endif

#ifndef PBOOL
#define PBOOL                       PBOOL
typedef unsigned char *PBOOL;
#endif

#ifndef TCHAR
#define TCHAR                       TCHAR
typedef char    TCHAR;
#endif

#ifndef PTCHAR
#define PTCHAR                      PTCHAR
typedef char   *PTCHAR;
#endif

#ifndef PCTCHAR
#define PCTCHAR                     PCTCHAR
typedef char   *const PCTCHAR;
#endif

#ifndef CPCTCHAR
#define CPCTCHAR                    CPCTCHAR
typedef const char *const CPCTCHAR;
#endif

#ifndef CHAR
#define CHAR                        CHAR
typedef char    CHAR;
#endif

#ifndef CCHAR
#define CCHAR                       CCHAR
typedef const char CCHAR;
#endif

#ifndef PCHAR
#define PCHAR                       PCHAR
typedef char    *PCHAR;
#endif

#ifndef CPCHAR
#define CPCHAR                      CPCHAR
typedef const char *CPCHAR;
#endif

#ifndef PCCHAR
#define PCCHAR                      PCCHAR
typedef char *const PCCHAR;
#endif

#ifndef CPCCHAR
#define CPCCHAR                     CPCCHAR
typedef const char *const CPCCHAR;
#endif

#ifndef PTSTR
#define PTSTR                       PTSTR
typedef const char *PTSTR;
#endif

#ifndef PCTSTR
#define PCTSTR                      PCTSTR
typedef char *const PCTSTR;
#endif

#ifndef PCTSTR
#define PCTSTR                      PCTSTR
typedef const char *PCTSTR;
#endif

#ifndef PTSTR
#define PTSTR                       PTSTR
typedef char *PTSTR;
#endif

#ifndef BYTE
#define BYTE                        BYTE
typedef unsigned char BYTE;
#endif

#ifndef PBYTE
#define PBYTE                       PBYTE
typedef unsigned char *PBYTE;
#endif

#ifndef PCBYTE
#define PCBYTE                      PCBYTE
typedef unsigned char *const PCBYTE;
#endif

#ifndef CPBYTE
#define CPBYTE                      CPBYTE
typedef const unsigned char *CPBYTE;
#endif

#ifndef SHORT
#define SHORT                       SHORT
typedef short   SHORT;
#endif

#ifndef PSHORT
#define PSHORT                      PSHORT
typedef short *PSHORT;
#endif

#ifndef PCSHORT
#define PCSHORT                     PCSHORT
typedef short *const PCSHORT;
#endif

#ifndef CPSHORT
#define CPSHORT                     CPSHORT
typedef const short *CPSHORT;
#endif

#ifndef USHORT
#define USHORT                      USHORT
typedef unsigned short USHORT;
#endif

#ifndef PUSHORT
#define PUSHORT                     PUSHORT
typedef unsigned short *PUSHORT;
#endif

#ifndef PCUSHORT
#define PCUSHORT                    PCUSHORT
typedef unsigned short *const PCUSHORT;
#endif

#ifndef CPUSHORT
#define CPUSHORT                    CPUSHORT
typedef const unsigned short *CPUSHORT;
#endif

#ifndef WORD
#define WORD                        WORD
typedef unsigned short WORD;
#endif

#ifndef PWORD
#define PWORD                       PWORD
typedef unsigned short *PWORD;
#endif

#ifndef PCWORD
#define PCWORD                      PCWORD
typedef unsigned short *const PCWORD;
#endif

#ifndef INT
#define INT                         INT
typedef int INT;
#endif

#ifndef CINT
#define CINT                        CINT
typedef const int CINT;
#endif

#ifndef PINT
#define PINT                        PINT
typedef int *PINT;
#endif

#ifndef PCINT
#define PCINT                       PCINT
typedef int *const PCINT;
#endif

#ifndef CPINT
#define CPINT                       CPINT
typedef const int *CPINT;
#endif

#ifndef UINT
#define UINT                        UINT
typedef unsigned int UINT;
#endif

#ifndef PUINT
#define PUINT                       PUINT
typedef unsigned int *PUINT;
#endif

#ifndef PCUINT
#define PCUINT                      PCUINT
typedef unsigned int *const PCUINT;
#endif

#ifndef CPUINT
#define CPUINT                      CPUINT
typedef const unsigned int *CPUINT;
#endif

#ifndef DWORD
#define DWORD                       DWORD
typedef unsigned long DWORD;
#endif

#ifndef PDWORD
#define PDWORD                      PDWORD
typedef unsigned long *PDWORD;
#endif

#ifndef PCDWORD
#define PCDWORD                     PCDWORD
typedef unsigned long *const PCDWORD;
#endif

#ifndef CPDWORD
#define CPDWORD                     CPDWORD
typedef const unsigned long *CPDWORD;
#endif

#ifndef LONG
#define LONG                        LONG
typedef long LONG;
#endif

#ifndef PLONG
#define PLONG                       PLONG
typedef long *PLONG;
#endif

#ifndef PCLONG
#define PCLONG                      PCLONG
typedef long *const PCLONG;
#endif

#ifndef CPLONG
#define CPLONG                      CPLONG
typedef const long *CPLONG;
#endif

#ifndef ULONG
#define ULONG                       ULONG
typedef unsigned long ULONG;
#endif

#ifndef PULONG
#define PULONG                      PULONG
typedef unsigned long *PULONG;
#endif

#ifndef PCULONG
#define PCULONG   PCULONG
typedef unsigned long *const        PCULONG;
#endif

#ifndef CPULONG
#define CPULONG                     CPULONG
typedef const unsigned long *CPULONG;
#endif

#ifndef FLOAT
#define FLOAT                       FLOAT
typedef float FLOAT;
#endif

#ifndef DOUBLE
#define DOUBLE                      DOUBLE
typedef long double DOUBLE;
#endif

#ifndef PDOUBLE
#define PDOUBLE                     PDOUBLE
typedef long double *PDOUBLE;
#endif

#ifndef CPDOUBLE
#define CPDOUBLE                    CPDOUBLE
typedef const long double *CPDOUBLE;
#endif

#ifndef PCDOUBLE
#define PCDOUBLE                    PCDOUBLE
typedef long double *const PCDOUBLE;
#endif

#ifndef PVOID
#define PVOID   PVOID
typedef void *PVOID;
#endif

#ifndef VOID
#define VOID                        VOID
typedef void VOID;
#endif

#ifndef IOID
#define IOID                        IOID
typedef unsigned short IOID;
#endif

#ifndef PIOID
#define PIOID                       PIOID
typedef unsigned short *PIOID;
#endif

#ifndef BBYTE
#define BBYTE   BBYTE
typedef union {
    unsigned char   BYTE;       /*lint -e46 */
                                /* this is correct */
    struct {
        #ifdef _BITFIELDS_MSB_FIRST_
        unsigned char B7:1;
        unsigned char B6:1;
        unsigned char B5:1;
        unsigned char B4:1;
        unsigned char B3:1;
        unsigned char B2:1;
        unsigned char B1:1;
        unsigned char B0:1;
        #else
        unsigned char B0:1;
        unsigned char B1:1;
        unsigned char B2:1;
        unsigned char B3:1;
        unsigned char B4:1;
        unsigned char B5:1;
        unsigned char B6:1;
        unsigned char B7:1;
        #endif
    } BIT;
} BBYTE;
#endif

#endif /* TYPES_H_INCLUDED */

/******************************************************************************
End  Of File
******************************************************************************/
