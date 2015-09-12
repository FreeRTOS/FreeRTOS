/*****************************************************************************
* Copyright 2014 Microchip Technology Inc. and its subsidiaries.
* You may use this software and any derivatives exclusively with
* Microchip products.
* THIS SOFTWARE IS SUPPLIED BY MICROCHIP "AS IS".
* NO WARRANTIES, WHETHER EXPRESS, IMPLIED OR STATUTORY, APPLY TO THIS SOFTWARE,
* INCLUDING ANY IMPLIED WARRANTIES OF NON-INFRINGEMENT, MERCHANTABILITY,
* AND FITNESS FOR A PARTICULAR PURPOSE, OR ITS INTERACTION WITH MICROCHIP
* PRODUCTS, COMBINATION WITH ANY OTHER PRODUCTS, OR USE IN ANY APPLICATION.
* IN NO EVENT WILL MICROCHIP BE LIABLE FOR ANY INDIRECT, SPECIAL, PUNITIVE,
* INCIDENTAL OR CONSEQUENTIAL LOSS, DAMAGE, COST OR EXPENSE OF ANY KIND
* WHATSOEVER RELATED TO THE SOFTWARE, HOWEVER CAUSED, EVEN IF MICROCHIP HAS
* BEEN ADVISED OF THE POSSIBILITY OR THE DAMAGES ARE FORESEEABLE.
* TO THE FULLEST EXTENT ALLOWED BY LAW, MICROCHIP'S TOTAL LIABILITY ON ALL
* CLAIMS IN ANY WAY RELATED TO THIS SOFTWARE WILL NOT EXCEED THE AMOUNT OF
* FEES, IF ANY, THAT YOU HAVE PAID DIRECTLY TO MICROCHIP FOR THIS SOFTWARE.
* MICROCHIP PROVIDES THIS SOFTWARE CONDITIONALLY UPON YOUR ACCEPTANCE
* OF THESE TERMS.
*****************************************************************************/


/** @file mec14xx_trace_inline.h
 *MEC14xx Inline TRACE macros
 */
/** @defgroup MEC14xx TRACE
 */

#ifndef _MEC14XX_TRACE_INLINE_H
#define _MEC14XX_TRACE_INLINE_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

#define INLINE_TRACE_ENABLE

#ifdef INLINE_TRACE_ENABLE


#define TRDA (0xA0008c00ul)

#define TRHDR() *(volatile uint8_t *)(TRDA)=0xFDu
#define TRB0(v) *(volatile uint8_t *)(TRDA)=(uint8_t)v
#define TRB1(v) *(volatile uint8_t *)(TRDA)=(uint8_t)(v>>8)
#define TRB2(v) *(volatile uint8_t *)(TRDA)=(uint8_t)(v>>16)
#define TRB3(v) *(volatile uint8_t *)(TRDA)=(uint8_t)(v>>24)

#define TRACE0(nbr,cat,b,str) TRHDR();TRB0(nbr);TRB1(nbr);
#define TRACE1(nbr,cat,b,str,p1) TRHDR();TRB0(nbr);TRB1(nbr);TRB0(p1);TRB1(p1);
#define TRACE2(nbr,cat,b,str,p1,p2) TRHDR();TRB0(nbr);TRB1(nbr);TRB0(p1);TRB1(p1);TRB0(p2);TRB1(p2);
#define TRACE3(nbr,cat,b,str,p1,p2,p3) TRHDR();TRB0(nbr);TRB1(nbr);TRB0(p1);TRB1(p1);TRB0(p2);TRB1(p2);TRB0(p3);TRB1(p3);
#define TRACE4(nbr,cat,b,str,p1,p2,p3,p4) TRHDR();TRB0(nbr);TRB1(nbr);TRB0(p1);TRB1(p1);TRB0(p2);TRB1(p2);TRB0(p3);TRB1(p3);TRB0(p4);TRB1(p4);
#define TRACE11(nbr,cat,b,str,p1) TRHDR();TRB0(nbr);TRB1(nbr);TRB0(p1);TRB1(p1);TRB2(p1);TRB3(p1);
#define TRACE12(nbr,cat,b,str,p1,p2) TRHDR();TRB0(nbr);TRB1(nbr);TRB0(p1);TRB1(p1);TRB2(p1);TRB3(p1);TRB0(p2);TRB1(p2);TRB2(p2);TRB3(p2);

#else // #ifdef INLINE_TRACE_ENABLE

#define TRACE0(nbr,cat,b,str) 
#define TRACE1(nbr,cat,b,str,p1) 
#define TRACE2(nbr,cat,b,str,p1,p2) 
#define TRACE3(nbr,cat,b,str,p1,p2,p3) 
#define TRACE4(nbr,cat,b,str,p1,p2,p3,p4) 
#define TRACE11(nbr,cat,b,str,p1) 
#define TRACE12(nbr,cat,b,str,p1,p2) 
#define trace0(nbr,cat,b,str) 
#define trace1(nbr,cat,b,str,p1) 
#define trace2(nbr,cat,b,str,p1,p2) 
#define trace3(nbr,cat,b,str,p1,p2,p3) 
#define trace4(nbr,cat,b,str,p1,p2,p3,p4) 
#define trace11(nbr,cat,b,str,p1) 
#define trace12(nbr,cat,b,str,p1,p2) 

#endif // #ifdef PLIB_TRACE_ENABLE

#define trace0(nbr,cat,b,str) 
#define trace1(nbr,cat,b,str,p1) 
#define trace2(nbr,cat,b,str,p1,p2) 
#define trace3(nbr,cat,b,str,p1,p2,p3) 
#define trace4(nbr,cat,b,str,p1,p2,p3,p4) 
#define trace11(nbr,cat,b,str,p1) 
#define trace12(nbr,cat,b,str,p1,p2) 

#ifdef __cplusplus
}
#endif

#endif // #ifndef _MEC14XX_TRACE_INLINE_H
/* end mec14xx_trace_inline.h */
/**   @}
 */
