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

/** @file girq10.c
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


#if GIRQ10_DISAGG == 0

void __attribute__((weak, interrupt, nomips16, section(".girqs")))
girq10_isr(void)
{
    JTVIC_GROUP_EN_CLR->w = (1ul<<2);
}

#else

void __attribute__((weak, interrupt, nomips16))
girq10_b0(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ10_ID, 0, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq10_b1(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ10_ID, 1, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq10_b2(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ10_ID, 2, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq10_b3(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ10_ID, 3, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq10_b4(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ10_ID, 4, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq10_b5(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ10_ID, 5, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq10_b6(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ10_ID, 6, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq10_b7(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ10_ID, 7, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq10_b8(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ10_ID, 8, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq10_b9(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ10_ID, 9, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq10_b10(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ10_ID, 10, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq10_b11(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ10_ID, 11, JTVIC_CLR_SRC);
}


void __attribute__((weak, interrupt, nomips16))
girq10_b12(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ10_ID, 12, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq10_b13(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ10_ID, 13, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq10_b14(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ10_ID, 14, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq10_b15(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ10_ID, 15, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq10_b16(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ10_ID, 16, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq10_b17(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ10_ID, 17, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq10_b18(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ10_ID, 18, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq10_b19(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ10_ID, 19, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq10_b20(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ10_ID, 20, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq10_b21(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ10_ID, 21, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq10_b22(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ10_ID, 22, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq10_b23(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ10_ID, 23, JTVIC_CLR_SRC);
}

#endif

/* end girq10.c */
/**   @}
 */

