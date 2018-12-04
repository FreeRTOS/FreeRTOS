#if 0
/*******************************************************************************
 * (c) Copyright 2016-2018 Microsemi SoC Products Group. All rights reserved.
 *
 * @file riscv_hal.c
 * @author Microsemi SoC Products Group
 * @brief Implementation of Hardware Abstraction Layer for Mi-V soft processors
 *
 * SVN $Revision: 9835 $
 * SVN $Date: 2018-03-19 19:11:35 +0530 (Mon, 19 Mar 2018) $
 */
#include <stdlib.h>
#include <stdint.h>
#include <unistd.h>

#include "riscv_hal.h"

#ifdef __cplusplus
extern "C" {
#endif

#define RTC_PRESCALER 100UL

#define SUCCESS 0U
#define ERROR   1U

/*------------------------------------------------------------------------------
 *
 */
uint8_t Invalid_IRQHandler(void);
uint8_t External_1_IRQHandler(void);
uint8_t External_2_IRQHandler(void);
uint8_t External_3_IRQHandler(void);
uint8_t External_4_IRQHandler(void);
uint8_t External_5_IRQHandler(void);
uint8_t External_6_IRQHandler(void);
uint8_t External_7_IRQHandler(void);
uint8_t External_8_IRQHandler(void);
uint8_t External_9_IRQHandler(void);
uint8_t External_10_IRQHandler(void);
uint8_t External_11_IRQHandler(void);
uint8_t External_12_IRQHandler(void);
uint8_t External_13_IRQHandler(void);
uint8_t External_14_IRQHandler(void);
uint8_t External_15_IRQHandler(void);
uint8_t External_16_IRQHandler(void);
uint8_t External_17_IRQHandler(void);
uint8_t External_18_IRQHandler(void);
uint8_t External_19_IRQHandler(void);
uint8_t External_20_IRQHandler(void);
uint8_t External_21_IRQHandler(void);
uint8_t External_22_IRQHandler(void);
uint8_t External_23_IRQHandler(void);
uint8_t External_24_IRQHandler(void);
uint8_t External_25_IRQHandler(void);
uint8_t External_26_IRQHandler(void);
uint8_t External_27_IRQHandler(void);
uint8_t External_28_IRQHandler(void);
uint8_t External_29_IRQHandler(void);
uint8_t External_30_IRQHandler(void);
uint8_t External_31_IRQHandler(void);

/*------------------------------------------------------------------------------
 *
 */
extern void Software_IRQHandler(void);
extern void Timer_IRQHandle( void );

/*------------------------------------------------------------------------------
 * Increment value for the mtimecmp register in order to achieve a system tick
 * interrupt as specified through the SysTick_Config() function.
 */
static uint64_t g_systick_increment = 0U;

/*------------------------------------------------------------------------------
 * Disable all interrupts.
 */
void __disable_irq(void)
{
    clear_csr(mstatus, MSTATUS_MPIE);
    clear_csr(mstatus, MSTATUS_MIE);
}

/*------------------------------------------------------------------------------
 * Enabler all interrupts.
 */
void __enable_irq(void)
{
    set_csr(mstatus, MSTATUS_MIE);
}

/*------------------------------------------------------------------------------
 * Configure the machine timer to generate an interrupt.
 */
uint32_t SysTick_Config(uint32_t ticks)
{
    uint32_t ret_val = ERROR;

    g_systick_increment = (uint64_t)(ticks) / RTC_PRESCALER;

    if (g_systick_increment > 0U)
    {
        uint32_t mhart_id = read_csr(mhartid);

        PRCI->MTIMECMP[mhart_id] = PRCI->MTIME + g_systick_increment;

        set_csr(mie, MIP_MTIP);

        __enable_irq();

        ret_val = SUCCESS;
    }

    return ret_val;
}

/*------------------------------------------------------------------------------
 * RISC-V interrupt handler for machine timer interrupts.
 */
volatile uint32_t ulTimerInterrupts = 0;
extern void Timer_IRQHandler( void );
static void handle_m_timer_interrupt(void)
{
//    clear_csr(mie, MIP_MTIP);

    Timer_IRQHandler();

//    PRCI->MTIMECMP[read_csr(mhartid)] = PRCI->MTIME + g_systick_increment;

//    set_csr(mie, MIP_MTIP);
}

/*------------------------------------------------------------------------------
 * RISC-V interrupt handler for external interrupts.
 */
uint8_t (*ext_irq_handler_table[32])(void) =
{
    Invalid_IRQHandler,
    External_1_IRQHandler,
    External_2_IRQHandler,
    External_3_IRQHandler,
    External_4_IRQHandler,
    External_5_IRQHandler,
    External_6_IRQHandler,
    External_7_IRQHandler,
    External_8_IRQHandler,
    External_9_IRQHandler,
    External_10_IRQHandler,
    External_11_IRQHandler,
    External_12_IRQHandler,
    External_13_IRQHandler,
    External_14_IRQHandler,
    External_15_IRQHandler,
    External_16_IRQHandler,
    External_17_IRQHandler,
    External_18_IRQHandler,
    External_19_IRQHandler,
    External_20_IRQHandler,
    External_21_IRQHandler,
    External_22_IRQHandler,
    External_23_IRQHandler,
    External_24_IRQHandler,
    External_25_IRQHandler,
    External_26_IRQHandler,
    External_27_IRQHandler,
    External_28_IRQHandler,
    External_29_IRQHandler,
    External_30_IRQHandler,
    External_31_IRQHandler
};

/*------------------------------------------------------------------------------
 *
 */
static void handle_m_ext_interrupt(void)
{
    uint32_t int_num  = PLIC_ClaimIRQ();
    uint8_t disable = EXT_IRQ_KEEP_ENABLED;

    disable = ext_irq_handler_table[int_num]();

    PLIC_CompleteIRQ(int_num);

    if(EXT_IRQ_DISABLE == disable)
    {
        PLIC_DisableIRQ((IRQn_Type)int_num);
    }
}

static void handle_m_soft_interrupt(void)
{
    Software_IRQHandler();

    /*Clear software interrupt*/
    PRCI->MSIP[0] = 0x00U;
}

/*------------------------------------------------------------------------------
 * Trap/Interrupt handler
 */
#define ENV_CALL_FROM_M_MODE 11
extern void vTaskSwitchContext( void );

uintptr_t handle_trap(uintptr_t mcause, uintptr_t mepc)
{
	/*_RB_*/
	if( mcause == ENV_CALL_FROM_M_MODE )
	{
		vTaskSwitchContext();

		/* Ensure not to return to the instruction that generated the exception. */
		mepc += 4;
	} else
	/*end _RB_*/
    if ((mcause & MCAUSE_INT) && ((mcause & MCAUSE_CAUSE)  == IRQ_M_EXT))
    {
        handle_m_ext_interrupt();
    }
    else if ((mcause & MCAUSE_INT) && ((mcause & MCAUSE_CAUSE)  == IRQ_M_TIMER))
    {
        handle_m_timer_interrupt();
    }
    else if ( (mcause & MCAUSE_INT) && ((mcause & MCAUSE_CAUSE)  == IRQ_M_SOFT))
    {
        handle_m_soft_interrupt();
    }
    else
    {
#ifndef NDEBUG
        /*
         Arguments supplied to this function are mcause, mepc (exception PC) and stack pointer
         based onprivileged-isa specification
         mcause values and meanings are:
         0 Instruction address misaligned (mtval/mbadaddr is the address)
         1 Instruction access fault       (mtval/mbadaddr is the address)
         2 Illegal instruction            (mtval/mbadaddr contains the offending instruction opcode)
         3 Breakpoint
         4 Load address misaligned        (mtval/mbadaddr is the address)
         5 Load address fault             (mtval/mbadaddr is the address)
         6 Store/AMO address fault        (mtval/mbadaddr is the address)
         7 Store/AMO access fault         (mtval/mbadaddr is the address)
         8 Environment call from U-mode
         9 Environment call from S-mode
         A Environment call from M-mode
         B Instruction page fault
         C Load page fault                (mtval/mbadaddr is the address)
         E Store page fault               (mtval/mbadaddr is the address)
        */

         uintptr_t mip      = read_csr(mip);      /* interrupt pending */
         uintptr_t mbadaddr = read_csr(mbadaddr); /* additional info and meaning depends on mcause */
         uintptr_t mtvec    = read_csr(mtvec);    /* trap vector */
         uintptr_t mscratch = read_csr(mscratch); /* temporary, sometimes might hold temporary value of a0 */
         uintptr_t mstatus  = read_csr(mstatus);  /* status contains many smaller fields: */

		/* breakpoint*/
        __asm("ebreak");
#else
        _exit(1 + mcause);
#endif
    }
    return mepc;
}

#ifdef __cplusplus
}
#endif
#endif
