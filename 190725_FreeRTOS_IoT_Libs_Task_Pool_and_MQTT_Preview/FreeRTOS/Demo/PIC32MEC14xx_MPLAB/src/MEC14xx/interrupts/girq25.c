/*****************************************************************************
* (c) 2013 Microchip Technology Inc. and its subsidiaries.
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

/** @file girq25.c
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


#if GIRQ25_DISAGG == 0

void __attribute__((weak, interrupt, nomips16, section(".girqs")))
girq25_isr(void)
{
    JTVIC_GROUP_EN_CLR->w = (1ul<<15);
}

#else

void __attribute__((weak, interrupt, nomips16))
girq25_b0(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ25_ID, 0);
}

void __attribute__((weak, interrupt, nomips16))
girq25_b1(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ25_ID, 1);
}

void __attribute__((weak, interrupt, nomips16))
girq25_b2(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ25_ID, 2);
}

void __attribute__((weak, interrupt, nomips16))
girq25_b3(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ25_ID, 3);
}

void __attribute__((weak, interrupt, nomips16))
girq25_b4(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ25_ID, 4);
}

void __attribute__((weak, interrupt, nomips16))
girq25_b5(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ25_ID, 5);
}

void __attribute__((weak, interrupt, nomips16))
girq25_b6(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ25_ID, 6);
}

void __attribute__((weak, interrupt, nomips16))
girq25_b7(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ25_ID, 7);
}

void __attribute__((weak, interrupt, nomips16))
girq25_b8(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ25_ID, 8);
}

void __attribute__((weak, interrupt, nomips16))
girq25_b9(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ25_ID, 9);
}

void __attribute__((weak, interrupt, nomips16))
girq25_b10(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ25_ID, 10);
}

void __attribute__((weak, interrupt, nomips16))
girq25_b11(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ25_ID, 11);
}

void __attribute__((weak, interrupt, nomips16))
girq25_b12(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ25_ID, 12);
}

void __attribute__((weak, interrupt, nomips16))
girq25_b13(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ25_ID, 13);
}

void __attribute__((weak, interrupt, nomips16))
girq25_b14(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ25_ID, 14);
}

void __attribute__((weak, interrupt, nomips16))
girq25_b15(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ25_ID, 15);
}

void __attribute__((weak, interrupt, nomips16))
girq25_b16(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ25_ID, 16);
}

void __attribute__((weak, interrupt, nomips16))
girq25_b17(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ25_ID, 17);
}

void __attribute__((weak, interrupt, nomips16))
girq25_b18(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ25_ID, 18);
}

void __attribute__((weak, interrupt, nomips16))
girq25_b19(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ25_ID, 19);
}

void __attribute__((weak, interrupt, nomips16))
girq25_b20(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ25_ID, 20);
}

void __attribute__((weak, interrupt, nomips16))
girq25_b21(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ25_ID, 21);
}

void __attribute__((weak, interrupt, nomips16))
girq25_b22(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ25_ID, 22);
}

void __attribute__((weak, interrupt, nomips16))
girq25_b23(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ25_ID, 23);
}

void __attribute__((weak, interrupt, nomips16))
girq25_b24(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ25_ID, 24);
}

void __attribute__((weak, interrupt, nomips16))
girq25_b25(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ25_ID, 25);
}

void __attribute__((weak, interrupt, nomips16))
girq25_b26(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ25_ID, 26);
}

void __attribute__((weak, interrupt, nomips16))
girq25_b27(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ25_ID, 27);
}


#endif

/* end girq25.c */
/**   @}
 */

