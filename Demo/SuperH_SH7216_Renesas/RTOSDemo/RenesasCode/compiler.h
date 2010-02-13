/******************************************************************************
* File Name    : compiler.h
* Version      : 1.0
* Device(s)    : Renesas
* Tool-Chain   : Renesas SH2A V9+
* OS           : None
* H/W Platform : SH2A
* Description  : Compiler specific defines for abstraction
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

#ifndef COMPILER_H_INCLUDED
#define COMPILER_H_INCLUDED

/******************************************************************************
Defines
******************************************************************************/

/* Embedded CPU data type definitions */

/* Set a few #defines for potential compilers used */
#define                 MCS      0  /* Hitachi */
#define                 GNU      1  /* Hitachi + many other devices */
#define                 IAR      2  /* Hitachi + some other devices */
#define                 MSV      3  /* Microsoft Visual C */

/* Test the compiler intrinisic defs */
#ifdef __GNUC__                     /* GNU compiler - C mode   */
#define COMPILER    GNU

#elif defined(__GNUG__)             /* GNU compiler - C++ mode */
#define COMPILER    GNU

#elif defined __IAR_SYSTEMS_ICC     /* IAR compiler */
#define COMPILER    IAR

#elif defined _MSC_VER              /* Microsoft c compiler */
#define COMPILER    MSV
#else
                                    
#define COMPILER    MCS             /* MCS compiler */
                                    /* MCS compiler has MSB first even in little
                                       endian mode unless #pragma or command
                                       line switch used to change it */
#define _BITFIELDS_MSB_FIRST_
#endif

/******************************************************************************
Pragma macros
******************************************************************************/
                                    /* Visual Cpp */
#if COMPILER == MSV
#define PACK1                       pack(1)
#define UNPACK                      pack()
#else
                                    /* MCS SH & H8S series recently got unified
                                       pragma syntax */
#define PACK1                       # ## pragma pack 1
#define UNPACK                      # ## pragma unpack
#endif

#endif /* COMPILER_H_INCLUDED */

/******************************************************************************
End  Of File
******************************************************************************/
