/******************************************************************************
*
* Copyright (C) 2007 - 2014 Xilinx, Inc.  All rights reserved.
*
* Permission is hereby granted, free of charge, to any person obtaining a copy
* of this software and associated documentation files (the "Software"), to deal
* in the Software without restriction, including without limitation the rights
* to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
* copies of the Software, and to permit persons to whom the Software is
* furnished to do so, subject to the following conditions:
*
* The above copyright notice and this permission notice shall be included in
* all copies or substantial portions of the Software.
*
* Use of the Software is limited solely to applications:
* (a) running on a Xilinx device, or
* (b) that interact with a Xilinx device through a bus or interconnect.
*
* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
* XILINX  BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
* WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
* OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
* SOFTWARE.
*
* Except as contained in this notice, the name of the Xilinx shall not be used
* in advertising or otherwise to promote the sale, use or other dealings in
* this Software without prior written authorization from Xilinx.
*
******************************************************************************/
/*****************************************************************************/
/**
* @file fsl.h
*
* This file contains macros for interfacing to the Fast Simplex Link (FSL)
* interface..
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- ---------------------------------------------------
* 1.00a ecm  06/20/07 Initial version, moved over from bsp area
* 1.11c ecm  08/26/08 Fixed the missing 'FSL_DEFAULT' define that was causing
*					  assembly errors.
* </pre>
*
* @note
*
* None.
*
******************************************************************************/


#ifndef _FSL_H
#define _FSL_H

/***************************** Include Files *********************************/


#ifdef __cplusplus
extern "C" {
#endif
/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/


/* if these have not been defined already, define here */
#ifndef stringify

/* necessary for pre-processor */
#define stringify(s)    tostring(s)
#define tostring(s)     #s

#endif /* stringify */

/* Extended FSL macros. These now replace all of the previous FSL macros */
#define FSL_DEFAULT
#define FSL_NONBLOCKING                          n
#define FSL_EXCEPTION                            e
#define FSL_CONTROL                              c
#define FSL_ATOMIC                               a

#define FSL_NONBLOCKING_EXCEPTION                ne
#define FSL_NONBLOCKING_CONTROL                  nc
#define FSL_NONBLOCKING_ATOMIC                   na
#define FSL_EXCEPTION_CONTROL                    ec
#define FSL_EXCEPTION_ATOMIC                     ea
#define FSL_CONTROL_ATOMIC                       ca

#define FSL_NONBLOCKING_EXCEPTION_CONTROL        nec
#define FSL_NONBLOCKING_EXCEPTION_ATOMIC         nea
#define FSL_NONBLOCKING_CONTROL_ATOMIC           nca
#define FSL_EXCEPTION_CONTROL_ATOMIC             eca

#define FSL_NONBLOCKING_EXCEPTION_CONTROL_ATOMIC neca

#define getfslx(val, id, flags)      asm volatile (stringify(flags) "get\t%0,rfsl" stringify(id) : "=d" (val))
#define putfslx(val, id, flags)      asm volatile (stringify(flags) "put\t%0,rfsl" stringify(id) :: "d" (val))

#define tgetfslx(val, id, flags)     asm volatile ("t" stringify(flags) "get\t%0,rfsl" stringify(id) : "=d" (val))
#define tputfslx(id, flags)          asm volatile ("t" stringify(flags) "put\trfsl" stringify(id))

#define getdfslx(val, var, flags)    asm volatile (stringify(flags) "getd\t%0,%1" : "=d" (val) : "d" (var))
#define putdfslx(val, var, flags)    asm volatile (stringify(flags) "putd\t%0,%1" :: "d" (val), "d" (var))

#define tgetdfslx(val, var, flags)   asm volatile ("t" stringify(flags) "getd\t%0,%1" : "=d" (val) : "d" (var))
#define tputdfslx(var, flags)        asm volatile ("t" stringify(flags) "putd\t%0" :: "d" (var))

/* if the mb_interface.h file has been included already, the following are not needed and will not be defined */

/* Legacy FSL Access Macros */

#ifndef getfsl

/* Blocking Data Read and Write to FSL no. id */
#define getfsl(val, id)         asm volatile ("get\t%0,rfsl" stringify(id) : "=d" (val))
#define putfsl(val, id)         asm volatile ("put\t%0,rfsl" stringify(id) :: "d" (val))

/* Non-blocking Data Read and Write to FSL no. id */
#define ngetfsl(val, id)        asm volatile ("nget\t%0,rfsl" stringify(id) : "=d" (val))
#define nputfsl(val, id)        asm volatile ("nput\t%0,rfsl" stringify(id) :: "d" (val))

/* Blocking Control Read and Write to FSL no. id */
#define cgetfsl(val, id)        asm volatile ("cget\t%0,rfsl" stringify(id) : "=d" (val))
#define cputfsl(val, id)        asm volatile ("cput\t%0,rfsl" stringify(id) :: "d" (val))

/* Non-blocking Control Read and Write to FSL no. id */
#define ncgetfsl(val, id)       asm volatile ("ncget\t%0,rfsl" stringify(id) : "=d" (val))
#define ncputfsl(val, id)       asm volatile ("ncput\t%0,rfsl" stringify(id) :: "d" (val))

/* Polling versions of FSL access macros. This makes the FSL access interruptible */
#define getfsl_interruptible(val, id)       asm volatile ("\n1:\n\tnget\t%0,rfsl" stringify(id) "\n\t"   \
                                                          "addic\tr18,r0,0\n\t"                \
                                                          "bnei\tr18,1b\n"                     \
                                                           : "=d" (val) :: "r18")

#define putfsl_interruptible(val, id)       asm volatile ("\n1:\n\tnput\t%0,rfsl" stringify(id) "\n\t"   \
                                                          "addic\tr18,r0,0\n\t"                \
                                                          "bnei\tr18,1b\n"                     \
                                                          :: "d" (val) : "r18")

#define cgetfsl_interruptible(val, id)      asm volatile ("\n1:\n\tncget\t%0,rfsl" stringify(id) "\n\t"  \
                                                          "addic\tr18,r0,0\n\t"                \
                                                          "bnei\tr18,1b\n"                     \
                                                          : "=d" (val) :: "r18")

#define cputfsl_interruptible(val, id)      asm volatile ("\n1:\n\tncput\t%0,rfsl" stringify(id) "\n\t"  \
                                                          "addic\tr18,r0,0\n\t"                \
                                                          "bnei\tr18,1b\n"                     \
                                                          :: "d" (val) : "r18")
/* FSL valid and error check macros. */
#define fsl_isinvalid(result)               asm volatile ("addic\t%0,r0,0"  : "=d" (result))
#define fsl_iserror(error)                  asm volatile ("mfs\t%0,rmsr\n\t"  \
                                                              "andi\t%0,%0,0x10" : "=d" (error))

#endif /* legacy FSL defines */
/************************** Function Prototypes ******************************/

/************************** Variable Definitions *****************************/

#ifdef __cplusplus
}
#endif
#endif /* _FSL_H */

