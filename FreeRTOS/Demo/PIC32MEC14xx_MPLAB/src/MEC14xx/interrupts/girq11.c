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

/** @file girq11.c
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


#if GIRQ11_DISAGG == 0

void __attribute__((weak, interrupt, nomips16, section(".girqs")))
girq11_isr(void)
{
    JTVIC_GROUP_EN_CLR->w = (1ul<<3);
}

#else

void __attribute__((weak, interrupt, nomips16))
girq11_b0(void)
{
    return;
}

void __attribute__((weak, interrupt, nomips16))
girq11_b1(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ11_ID, 1, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq11_b2(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ11_ID, 2, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq11_b3(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ11_ID, 3, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq11_b4(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ11_ID, 4, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq11_b5(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ11_ID, 5, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq11_b6(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ11_ID, 6, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq11_b7(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ11_ID, 7, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq11_b8(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ11_ID, 8, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq11_b9(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ11_ID, 9, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq11_b10(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ11_ID, 10, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq11_b11(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ11_ID, 11, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq11_b12(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ11_ID, 12, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq11_b13(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ11_ID, 13, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq11_b14(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ11_ID, 14, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq11_b15(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ11_ID, 15, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq11_b16(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ11_ID, 16, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq11_b17(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ11_ID, 17, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq11_b18(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ11_ID, 18, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq11_b19(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ11_ID, 19, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq11_b20(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ11_ID, 20, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq11_b21(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ11_ID, 21, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq11_b22(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ11_ID, 22, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq11_b23(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ11_ID, 23, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq11_b24(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ11_ID, 24, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq11_b25(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ11_ID, 25, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq11_b26(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ11_ID, 26, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq11_b27(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ11_ID, 27, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq11_b28(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ11_ID, 28, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq11_b29(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ11_ID, 29, JTVIC_CLR_SRC);
}

void __attribute__((weak, interrupt, nomips16))
girq11_b30(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ11_ID, 30, JTVIC_CLR_SRC);
}

#endif

/* end girq11.c */
/**   @}
 */

