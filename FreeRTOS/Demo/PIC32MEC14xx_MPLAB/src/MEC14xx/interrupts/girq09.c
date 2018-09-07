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

/** @file girq09.c
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


#if GIRQ09_DISAGG == 0

/*
 * Aggregated mode handler, must handle all enabled 
 * GIRQ08 sources. 
*/
void __attribute__((weak, interrupt, nomips16, section(".girqs")))
girq09_isr( void )
{
    JTVIC_GROUP_EN_CLR->w = (1ul<<1);
}

#else

void __attribute__((weak, interrupt, nomips16))
girq09_b0(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].EN_CLR = (1ul << 0);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].SOURCE = (1ul << 0);
}

void __attribute__((weak, interrupt, nomips16))
girq09_b1(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].EN_CLR = (1ul << 1);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].SOURCE = (1ul << 1);
}

void __attribute__((weak, interrupt, nomips16))
girq09_b2(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].EN_CLR = (1ul << 2);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].SOURCE = (1ul << 2);
}

void __attribute__((weak, interrupt, nomips16))
girq09_b3(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].EN_CLR = (1ul << 3);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].SOURCE = (1ul << 3);
}

void __attribute__((weak, interrupt, nomips16))
girq09_b4(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].EN_CLR = (1ul << 4);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].SOURCE = (1ul << 4);
}

void __attribute__((weak, interrupt, nomips16))
girq09_b5(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].EN_CLR = (1ul << 5);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].SOURCE = (1ul << 5);
}

void __attribute__((weak, interrupt, nomips16))
girq09_b6(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].EN_CLR = (1ul << 6);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].SOURCE = (1ul << 6);
}

void __attribute__((weak, interrupt, nomips16))
girq09_b7(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].EN_CLR = (1ul << 7);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].SOURCE = (1ul << 7);
}

void __attribute__((weak, interrupt, nomips16))
girq09_b8(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].EN_CLR = (1ul << 8);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].SOURCE = (1ul << 8);
}

void __attribute__((weak, interrupt, nomips16))
girq09_b9(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].EN_CLR = (1ul << 9);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].SOURCE = (1ul << 9);
}

void __attribute__((weak, interrupt, nomips16))
girq09_b10(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].EN_CLR = (1ul << 10);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].SOURCE = (1ul << 10);
}

void __attribute__((weak, interrupt, nomips16))
girq09_b11(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].EN_CLR = (1ul << 11);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].SOURCE = (1ul << 11);
}

void __attribute__((weak, interrupt, nomips16))
girq09_b12(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].EN_CLR = (1ul << 12);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].SOURCE = (1ul << 12);
}

void __attribute__((weak, interrupt, nomips16))
girq09_b13(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].EN_CLR = (1ul << 13);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].SOURCE = (1ul << 13);
}

void __attribute__((weak, interrupt, nomips16))
girq09_b14(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].EN_CLR = (1ul << 14);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].SOURCE = (1ul << 14);
}

void __attribute__((weak, interrupt, nomips16))
girq09_b15(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].EN_CLR = (1ul << 15);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].SOURCE = (1ul << 15);
}

void __attribute__((weak, interrupt, nomips16))
girq09_b16(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].EN_CLR = (1ul << 16);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].SOURCE = (1ul << 16);
}

void __attribute__((weak, interrupt, nomips16))
girq09_b17(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].EN_CLR = (1ul << 17);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].SOURCE = (1ul << 17);
}

void __attribute__((weak, interrupt, nomips16))
girq09_b18(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].EN_CLR = (1ul << 18);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].SOURCE = (1ul << 18);
}

void __attribute__((weak, interrupt, nomips16))
girq09_b19(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].EN_CLR = (1ul << 19);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].SOURCE = (1ul << 19);
}

void __attribute__((weak, interrupt, nomips16))
girq09_b20(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].EN_CLR = (1ul << 20);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].SOURCE = (1ul << 20);
}

void __attribute__((weak, interrupt, nomips16))
girq09_b21(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].EN_CLR = (1ul << 21);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].SOURCE = (1ul << 21);
}

void __attribute__((weak, interrupt, nomips16))
girq09_b22(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].EN_CLR = (1ul << 22);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].SOURCE = (1ul << 22);
}

void __attribute__((weak, interrupt, nomips16))
girq09_b23(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].EN_CLR = (1ul << 23);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].SOURCE = (1ul << 23);
}

void __attribute__((weak, interrupt, nomips16))
girq09_b24(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].EN_CLR = (1ul << 24);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].SOURCE = (1ul << 24);
}

void __attribute__((weak, interrupt, nomips16))
girq09_b25(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].EN_CLR = (1ul << 25);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].SOURCE = (1ul << 25);
}

void __attribute__((weak, interrupt, nomips16))
girq09_b26(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].EN_CLR = (1ul << 26);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].SOURCE = (1ul << 26);
}

void __attribute__((weak, interrupt, nomips16))
girq09_b27(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].EN_CLR = (1ul << 27);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].SOURCE = (1ul << 27);
}

void __attribute__((weak, interrupt, nomips16))
girq09_b28(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].EN_CLR = (1ul << 28);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].SOURCE = (1ul << 28);
}

void __attribute__((weak, interrupt, nomips16))
girq09_b29(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].EN_CLR = (1ul << 29);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].SOURCE = (1ul << 29);
}

void __attribute__((weak, interrupt, nomips16))
girq09_b30(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].EN_CLR = (1ul << 30);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ09_ID].SOURCE = (1ul << 30);
}


#endif

/* end girq09.c */
/**   @}
 */

