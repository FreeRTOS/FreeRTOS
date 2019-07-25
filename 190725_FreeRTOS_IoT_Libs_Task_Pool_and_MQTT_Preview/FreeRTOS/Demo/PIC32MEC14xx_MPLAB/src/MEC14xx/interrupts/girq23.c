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

/** @file girq23.c
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


typedef void (* GIRQ23_FPVU8)(uint8_t);

#if GIRQ23_DISAGG == 0

/*
 * FreeRTOS ISR for HW timer used as RTOS tick.
 * Implemented in MEC14xx FreeRTOS porting layer, port_asm.S
 * It save/restores CPU context and clears HW timer interrupt 
 * status in JTVIC. On each timer tick it checks if any task 
 * requires service. If yes then it triggers the PendSV low 
 * priority software interrupt.
 * Issue:
 * When aggregated girq23_isr save CPU context but this context 
 * is not the same as a FreeRTOS context save. If the RTOS timer 
 * is active then girq23_isr would call vPortTickInterruptHandler 
 * which uses FreeRTOS portSAVE_CONTEXT macro to save RTOS + CPU 
 * context. At this point you have two context saves on the stack.
 * There is a problem:
 * vPortTickInterruptHandler does not return but exits using 
 * portRESTORE_CONTEXT. This means the context save performed 
 * by aggregated girq23_isr is left on the stack. Eventually 
 * a stack overflow will occur.
 * 
 * Solutions:
 * 1. vPortTickInterruptHandler must be modified to handle scan 
 *    GIRQ23 Result bits and all the respective handler. All 
 *    other GIRQ23 source are called as hook functions.
 *  
 * 2. Do not use vPortTickInterruptHandler.
 *    Modify girq23_isr here to use FreeRTOS portSAVE_CONTEXT 
 *    and portRESTORE_CONTEXT macros. 
 *    If RTOS timer is active interrupt then call vPortIncrementTick 
 *    as vPortTickInterruptHandler does.
 *    For all other GIRQ23 sources call the respective handlers.
 *  
 *  NOTE: for both of the above solutions a we must either:
 *  A. Service one source only resulting in GIRQ23 firing multiple 
 *     times if more than one source is active.
 *  B. Service all active sources with RTOS Timer checked first.
 *  
 *  We will implement 1A with a single hook for all other sources.
 *  
 */

extern void vPortIncrementTick(void);

void girq23_dflt_handler(uint8_t inum)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ23_ID].EN_CLR = (1ul << inum);
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ23_ID].SOURCE = (1ul << inum);
}

void __attribute__((weak)) rtos_tmr_handler(uint8_t inum)
{
    (void) inum;

    JTVIC_GIRQ->REGS[MEC14xx_GIRQ23_ID].SOURCE = (1ul << 4);
}

const GIRQ23_FPVU8 girq23_htable[GIRQ23_NUM_SOURCES] =
{
    girq23_dflt_handler,    /* btmr0_handler, */
    girq23_dflt_handler,    /* btmr1_handler, */
    girq23_dflt_handler,    /* btmr2_handler, */
    girq23_dflt_handler,    /* btmr3_handler, */
    vPortIncrementTick,
    girq23_dflt_handler,    /* hib_tmr_handler, */
    girq23_dflt_handler,    /* week_tmr_handler, */
    girq23_dflt_handler,    /* week_tmr_handler, */
    girq23_dflt_handler,    /* week_tmr_handler, */
    girq23_dflt_handler,    /* week_tmr_handler, */
    girq23_dflt_handler,    /* week_tmr_handler, */
    girq23_dflt_handler,    /* vci_handler, */
    girq23_dflt_handler,    /* vci_handler, */
    girq23_dflt_handler,    /* vci_handler, */
};

/* Called by FreeRTOS vPortTickInterruptHandler(girq23_isr) 
 * after saving FreeRTOS context 
 */
void girq23_handler(void)
{
    uint32_t d;
    uint8_t bitpos;

    d = JTVIC_GIRQ->REGS[MEC14xx_GIRQ23_ID].RESULT & (GIRQ23_SRC_MASK);
    while ( 0 != d )
    {
        bitpos = 31 - ((uint8_t)__builtin_clz(d) & 0x1F);
        (girq23_htable[bitpos])(bitpos);
        d &= ~(1ul << bitpos);
    }
}

void __attribute__((weak, interrupt, nomips16, section(".girqs")))
girq23_isr(void)
{
    uint32_t d;
    uint8_t bitpos;

    d = JTVIC_GIRQ->REGS[MEC14xx_GIRQ23_ID].RESULT & (GIRQ23_SRC_MASK);
    while ( 0 != d )
    {
        bitpos = 31 - ((uint8_t)__builtin_clz(d) & 0x1F);
        (girq23_htable[bitpos])(bitpos);
        d &= ~(1ul << bitpos);
    }    
}

#else


/* 16-bit Basic Timer 0 */
void __attribute__((weak, interrupt, nomips16))
girq23_b0(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ23_ID].SOURCE = (1ul << 0);  
}

/* 16-bit Basic Timer 1 */
void __attribute__((weak, interrupt, nomips16))
girq23_b1(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ23_ID, 1, TRUE);
}

/* 16-bit Basic Timer 2 */
void __attribute__((weak, interrupt, nomips16))
girq23_b2(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ23_ID, 2, TRUE);
}

/* 16-bit Basic Timer 3 */
void __attribute__((weak, interrupt, nomips16))
girq23_b3(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ23_ID, 3, TRUE);
}

/* RTOS Timer  */
void __attribute__((weak, interrupt, nomips16))
girq23_b4(void)
{
    JTVIC_GIRQ->REGS[MEC14xx_GIRQ23_ID].SOURCE = (1ul << 4);
    
}

/* Hibernation Timer */
void __attribute__((weak, interrupt, nomips16))
girq23_b5(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ23_ID, 5, TRUE);
}

/* Week Alarm */
void __attribute__((weak, interrupt, nomips16))
girq23_b6(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ23_ID, 6, TRUE);
}

/* Sub-Week Alarm */
void __attribute__((weak, interrupt, nomips16))
girq23_b7(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ23_ID, 7, TRUE);
}

/* Week Alarm One Second */
void __attribute__((weak, interrupt, nomips16))
girq23_b8(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ23_ID, 8, TRUE);
}

/* Week Alarm Sub Second */
void __attribute__((weak, interrupt, nomips16))
girq23_b9(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ23_ID, 9, TRUE);
}

/* Week Alarm System Power Present Pin */
void __attribute__((weak, interrupt, nomips16))
girq23_b10(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ23_ID, 10, TRUE);
}

/* VCI OVRD Input  */
void __attribute__((weak, interrupt, nomips16))
girq23_b11(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ23_ID, 11, TRUE);
}

/* VCI IN0 */
void __attribute__((weak, interrupt, nomips16))
girq23_b12(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ23_ID, 12, TRUE);
}

/* VCI IN1 */
void __attribute__((weak, interrupt, nomips16))
girq23_b13(void)
{
    jtvic_dis_clr_source(MEC14xx_GIRQ23_ID, 13, TRUE);
}


#endif


/* end girq23.c */
/**   @}
 */

