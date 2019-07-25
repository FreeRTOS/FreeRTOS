/*****************************************************************************
* (c) 2014 Microchip Technology Inc. and its subsidiaries.
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

/** @file girq19.c
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


#if GIRQ19_DISAGG == 0

void __attribute__((weak, interrupt, nomips16, section(".girqs")))
girq19_isr(void)
{
    JTVIC_GROUP_EN_CLR->w = (1ul<<11);
}

#else

void __attribute__((weak, interrupt, nomips16))
girq19_b0(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ19_ID, 0);
}

void __attribute__((weak, interrupt, nomips16))
girq19_b1(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ19_ID, 1);
}

void __attribute__((weak, interrupt, nomips16))
girq19_b2(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ19_ID, 2);
}

void __attribute__((weak, interrupt, nomips16))
girq19_b3(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ19_ID, 3);
}

void __attribute__((weak, interrupt, nomips16))
girq19_b4(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ19_ID, 4);
}

void __attribute__((weak, interrupt, nomips16))
girq19_b5(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ19_ID, 5);
}

void __attribute__((weak, interrupt, nomips16))
girq19_b6(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ19_ID, 6);
}

void __attribute__((weak, interrupt, nomips16))
girq19_b7(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ19_ID, 7);
}

void __attribute__((weak, interrupt, nomips16))
girq19_b8(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ19_ID, 8);
}


#endif

/* end girq19.c */
/**   @}
 */

