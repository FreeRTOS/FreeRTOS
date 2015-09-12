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

/** @file girq17.c
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


#if GIRQ17_DISAGG == 0

void __attribute__((weak, interrupt, nomips16, section(".girqs")))
girq17_isr(void)
{
    JTVIC_GROUP_EN_CLR->w = (1ul<<9);
}

#else

void __attribute__((weak, interrupt, nomips16))
girq17_b0(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ17_ID].EN_CLR = (1ul << 0);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ17_ID].SOURCE = (1ul << 0);
}

void __attribute__((weak, interrupt, nomips16))
girq17_b1(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ17_ID].EN_CLR = (1ul << 1);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ17_ID].SOURCE = (1ul << 1);
}

void __attribute__((weak, interrupt, nomips16))
girq17_b2(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ17_ID].EN_CLR = (1ul << 2);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ17_ID].SOURCE = (1ul << 2);
}

void __attribute__((weak, interrupt, nomips16))
girq17_b3(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ17_ID].EN_CLR = (1ul << 3);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ17_ID].SOURCE = (1ul << 3);
}

void __attribute__((weak, interrupt, nomips16))
girq17_b4(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ17_ID].EN_CLR = (1ul << 4);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ17_ID].SOURCE = (1ul << 4);
}

void __attribute__((weak, interrupt, nomips16))
girq17_b5(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ17_ID].EN_CLR = (1ul << 5);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ17_ID].SOURCE = (1ul << 5);
}

void __attribute__((weak, interrupt, nomips16))
girq17_b6(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ17_ID].EN_CLR = (1ul << 6);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ17_ID].SOURCE = (1ul << 6);
}

void __attribute__((weak, interrupt, nomips16))
girq17_b7(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ17_ID].EN_CLR = (1ul << 7);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ17_ID].SOURCE = (1ul << 7);
}

void __attribute__((weak, interrupt, nomips16))
girq17_b8(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ17_ID].EN_CLR = (1ul << 8);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ17_ID].SOURCE = (1ul << 8);
}

void __attribute__((weak, interrupt, nomips16))
girq17_b9(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ17_ID].EN_CLR = (1ul << 9);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ17_ID].SOURCE = (1ul << 9);
}

void __attribute__((weak, interrupt, nomips16))
girq17_b10(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ17_ID].EN_CLR = (1ul << 10);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ17_ID].SOURCE = (1ul << 10);
}

#endif

/* end girq17.c */
/**   @}
 */

