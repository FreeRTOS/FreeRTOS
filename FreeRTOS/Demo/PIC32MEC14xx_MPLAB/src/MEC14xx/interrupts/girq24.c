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

/** @file girq24.c
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
#include "MEC14xx/mec14xx_bbled.h"
#include "MEC14xx/mec14xx_trace_func.h"


typedef void (* GIRQ24_FPVU8)(uint8_t);


/* MIPS M14K internal counter is connected to GIRQ24 bit[0]
 * It is a simple counter which fires an interrupt when its 
 * count value is equal to a match value.
 * 
 */
 
#if GIRQ24_DISAGG == 0


void girq24_dflt_handler(uint8_t inum)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ24_ID].EN_CLR = (1ul << inum);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ24_ID].SOURCE = (1ul << inum);
}

void __attribute__((weak)) m14k_counter_handler(uint8_t inum)
{
    uint32_t r;

    (void) inum;

    r = _CP0_GET_COUNT();
    r += (M14K_TIMER_COMPARE);
    /* Write of CP0.Compare clears status in M14K */
    _CP0_SET_COUNT(r);

    JTVIC_GIRQ->REGS[MEC14xx_GIRQ24_ID].SOURCE = (1ul << 0);

}

/*
 * TODO - FreeRTOS M14K Software Interrupt 0 handler
 * is vPortYieldISR in port_asm.S
 * vPortYieldISR was designed to be entered directly by the
 * CPU not via a higher level ISR handler.
 * One work-around is to modify vPortYieldISR to do the work
 * of girq24_handler below. It must determine which GIRQ24 source
 * was active: M14K counter, SoftIRQ0, or SoftIRQ1.
 */
void __attribute__((weak)) m14k_soft_irq0(uint8_t inum)
{
    (void) inum;

    JTVIC_GIRQ->REGS[MEC14xx_GIRQ24_ID].SOURCE = (1ul << 1);

}

void __attribute__((weak)) m14k_soft_irq1(uint8_t inum)
{
    (void) inum;

    JTVIC_GIRQ->REGS[MEC14xx_GIRQ24_ID].SOURCE = (1ul << 2);
    
}

void girq24_b_0_2( void )
{
    uint32_t d;

    d = JTVIC_GIRQ->REGS[MEC14xx_GIRQ24_ID].RESULT & (GIRQ24_SRC_MASK);

    if ( d & (1ul << 0) )
    {
        m14k_counter_handler(0);
    }

    if ( d & (1ul << 2) )
    {
        m14k_soft_irq1(2);
    }
}


const GIRQ24_FPVU8 girq24_htable[GIRQ24_NUM_SOURCES] =
{
    m14k_counter_handler,   /* m14k_counter_handler, */
    m14k_soft_irq0,         /* m14k_soft_irq0, */
    m14k_soft_irq1,         /* m14k_soft_irq1 */
};

void __attribute__((weak, interrupt, nomips16, section(".girqs")))
girq24_isr(void)
{
    uint32_t d;
    uint8_t bitpos;

    d = JTVIC_GIRQ->REGS[MEC14xx_GIRQ24_ID].RESULT & (GIRQ24_SRC_MASK);
    while ( 0 != d )
    {
        bitpos = 31 - ((uint8_t)__builtin_clz(d) & 0x1F);
        (girq24_htable[bitpos])(bitpos);
        d &= ~(1ul << bitpos);
    }
}

#else

void __attribute__((weak, interrupt, nomips16))
girq24_b0(void)
{
    uint32_t r;
    
    r = _CP0_GET_COUNT();
    r += (M14K_TIMER_COMPARE);
    _CP0_SET_COUNT(r);

    JTVIC_GIRQ->REGS[MEC14xx_GIRQ24_ID].SOURCE = (1ul << 0);    
}

void __attribute__((weak, interrupt, nomips16))
girq24_b1(void)
{

    _CP0_BIC_CAUSE(0x100ul);
 
    jtvic_clr_source(MEC14xx_GIRQ24_ID, 1);
}

void __attribute__((weak, interrupt, nomips16))
girq24_b2(void)
{

    _CP0_BIC_CAUSE(0x200ul);

    jtvic_clr_source(MEC14xx_GIRQ24_ID, 2);
}

#endif

/* end girq24.c */
/**   @}
 */

