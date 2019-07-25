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

/** @file girq08.c
 *Interrupt service routines for MIPS using vanilla GCC and MCHP XC32
 */
/** @defgroup MEC14xx ISR
 *  @{
 */

#include "appcfg.h"
#include "platform.h"
#include "MEC14xx/mec14xx.h"
#include "MEC14xx/mec14xx_girqs.h"
#include "MEC14xx/mec14xx_gpio.h"
#include "MEC14xx/mec14xx_trace_func.h"



#if GIRQ08_DISAGG == 0

/*
 * Aggregated mode handler, must handle all enabled 
 * GIRQ08 sources. 
*/
void __attribute__((weak, interrupt, nomips16, section(".girqs")))
girq08_isr( void )
{
    JTVIC_GROUP_EN_CLR->w = (1ul<<0);
}

#else

/*
 * Disaggregated GIRQ08 subhandlers, one for each 
 * source.  Called by assembly language wrapper. 
*/


void __attribute__((weak, interrupt, nomips16))
girq08_b0(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ08_ID, 0);
}


void __attribute__((weak, interrupt, nomips16))
girq08_b1(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ08_ID, 1);
}


void __attribute__((weak, interrupt, nomips16))
girq08_b2(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ08_ID, 2);
}


void __attribute__((weak, interrupt, nomips16))
girq08_b3(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ08_ID, 3);
}


void __attribute__((weak, interrupt, nomips16))
girq08_b4(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ08_ID, 4);
}


void __attribute__((weak, interrupt, nomips16))
girq08_b5(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ08_ID, 5);
}


void __attribute__((weak, interrupt, nomips16))
girq08_b6(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ08_ID, 6);
}


void __attribute__((weak, interrupt, nomips16))
girq08_b7(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ08_ID, 7);
}


void __attribute__((weak, interrupt, nomips16))
girq08_b8(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ08_ID, 8);
}


void __attribute__((weak, interrupt, nomips16))
girq08_b9(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ08_ID, 9);
}


void __attribute__((weak, interrupt, nomips16))
girq08_b10(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ08_ID, 10);
}


void __attribute__((weak, interrupt, nomips16))
girq08_b11(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ08_ID, 11);
}


void __attribute__((weak, interrupt, nomips16))
girq08_b12(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ08_ID, 12);
}


void __attribute__((weak, interrupt, nomips16))
girq08_b13(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ08_ID, 13);
}


void __attribute__((weak, interrupt, nomips16))
girq08_b14(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ08_ID, 14);
}


void __attribute__((weak, interrupt, nomips16))
girq08_b15(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ08_ID, 15);
}


void __attribute__((weak, interrupt, nomips16))
girq08_b16(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ08_ID, 16);
}


void __attribute__((weak, interrupt, nomips16))
girq08_b17(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ08_ID, 17);
}


void __attribute__((weak, interrupt, nomips16))
girq08_b18(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ08_ID, 18);
}


void __attribute__((weak, interrupt, nomips16))
girq08_b19(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ08_ID, 19);
}


void __attribute__((weak, interrupt, nomips16))
girq08_b20(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ08_ID, 20);
}


void __attribute__((weak, interrupt, nomips16))
girq08_b21(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ08_ID, 21);
}


void __attribute__((weak, interrupt, nomips16))
girq08_b22(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ08_ID, 22);
}


#endif


/* end girq08.c */
/**   @}
 */

