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

/** @file mec14xx_trace_func.h
 *MEC14xx TFDP Peripheral Library API
 */
/** @defgroup MEC14xx Peripherals Trace
 */

#ifndef _MEC14XX_TRACE_FUNC_H
#define _MEC14XX_TRACE_FUNC_H

#include "appcfg.h"
#include "mec14xx.h"
#include "mec14xx_tfdp.h"

#ifdef __cplusplus
extern "C" {
#endif

#ifdef ENABLE_TFDP_TRACE

#ifdef ENABLE_TRACE_HOST_LINK
#include <stdio.h>
#include <stdlib.h>
#endif

#define TFDP_SLEEP_EN       (1u)
#define TFDP_SLEEP_DIS      (0u)
#define TFDP_EN             (1u)
#define TFDP_DIS            (0u)
#define TFDP_CFG_PINS       (1u)
#define TFDP_NO_CFG_PINS    (0u)

void tfdp_sleep_en(uint8_t sleep_en);
void tfdp_enable(uint8_t en, uint8_t pin_cfg);
void TFDPTrace0( uint16_t nbr, uint8_t b );
void TFDPTrace1( uint16_t nbr, uint8_t b, uint32_t p1 );
void TFDPTrace2( uint16_t nbr, uint8_t b, uint32_t p1, uint32_t p2 );
void TFDPTrace3( uint16_t nbr, uint8_t b, uint32_t p1, uint32_t p2, uint32_t p3);
void TFDPTrace4( uint16_t nbr, uint8_t b, uint32_t p1, uint32_t p2, uint32_t p3, uint32_t p4);
void TFDPTrace11( uint16_t nbr, uint8_t b, uint32_t p1);
void TFDPTrace12( uint16_t nbr, uint8_t b, uint32_t p1, uint32_t p2);

#if defined(ENABLE_TRACE_HOST_LINK)
#define TRACE0(nbr,cat,b,str) printf(str)
#define TRACE1(nbr,cat,b,str,p1) printf(str,p1)
#define TRACE2(nbr,cat,b,str,p1,p2) printf(str,p1,p2)
#define TRACE3(nbr,cat,b,str,p1,p2,p3) printf(str,p1,p2,p3)
#define TRACE4(nbr,cat,b,str,p1,p2,p3,p4) printf(str,p1,p2,p3,p4)
#define TRACE11(nbr,cat,b,str,p1) printf(str,p1)
#define TRACE12(nbr,cat,b,str,p1,p2) printf(str,p1,p2)
#elif defined(TRACE_NO_PREPROC)
/* C pre-processor - don't substitute TRACE macros */
#else // not ENABLE_TRACE_HOST_LINK
#define TRACE0(nbr,cat,b,str) TFDPTrace0(nbr,b)
#define TRACE1(nbr,cat,b,str,p1) TFDPTrace1(nbr,b,p1)
#define TRACE2(nbr,cat,b,str,p1,p2) TFDPTrace2(nbr,b,p1,p2)
#define TRACE3(nbr,cat,b,str,p1,p2,p3) TFDPTrace3(nbr,b,p1,p2,p3)
#define TRACE4(nbr,cat,b,str,p1,p2,p3,p4) TFDPTrace4(nbr,b,p1,p2,p3,p4)
#define TRACE11(nbr,cat,b,str,p1) TFDPTrace11(nbr,b,p1)
#define TRACE12(nbr,cat,b,str,p1,p2) TFDPTrace12(nbr,b,p1,p2)
#endif

#else // #ifdef ENABLE_TFDP_TRACE

#define tfdp_sleep_en(sleep_en)
#define tfdp_enable(en,pin_cfg) 
#define TRACE0(nbr,cat,b,str) 
#define TRACE1(nbr,cat,b,str,p1) 
#define TRACE2(nbr,cat,b,str,p1,p2) 
#define TRACE3(nbr,cat,b,str,p1,p2,p3) 
#define TRACE4(nbr,cat,b,str,p1,p2,p3,p4) 
#define TRACE11(nbr,cat,b,str,p1) 
#define TRACE12(nbr,cat,b,str,p1,p2) 

#endif // #ifdef ENABLE_TFDP_TRACE

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

#endif // #ifndef _MEC14XX_TRACE_FUNC_H
/* end mec14xx_trace_func.h */
/**   @}
 */
