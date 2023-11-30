/** @file sys_startup.c
*   @brief Startup Source File
*   @date 05.November.2010
*   @version 1.01.001
*
*   This file contains:
*   - Include Files
*   - Type Definitions
*   - External Functions
*   - VIM RAM Setup
*   - Startup Routine
*   .
*   which are relevant for the Starup.
*/

/* (c) Texas Instruments 2010, All rights reserved. */

/* Include Files */

#include "sys_types.h"
#include "sys_common.h"
#include "sys_system.h"
#include "sys_vim.h"
#include "sys_core.h"
#include "sys_memory.h"
#include "FreeRTOS.h"


/* External Functions */

extern void __TI_auto_init(void);
extern void main(void);
extern void exit(int);

/* Vim Ram Definition */
/** @struct vimRam
*   @brief Vim Ram Definition
*
*   This type is used to access the Vim Ram.
*/

static const t_isrFuncPTR s_vim_init[] =
{
    phantomInterrupt,
    esmHighLevelInterrupt,
    phantomInterrupt,
	#if configUSE_PREEMPTION == 0
		vPortNonPreemptiveTick, /* RTI */
	#else
		vPortPreemptiveTick,	/* RTI */
	#endif
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    vPortYeildWithinAPI,    /* software interrupt */
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
    phantomInterrupt,
};


/* Startup Routine */

#pragma INTERRUPT(_c_int00, RESET)

void _c_int00()
{
    /* Enable VFP Unit */
	_coreEnableVfp();

    /* Initialize Core Registers */
    _coreInitRegisters();

    /* Initialize Stack Pointers */
    _coreInitStackPointer();

    /* Enable IRQ offset via Vic controller */
	_coreEnableIrqVicOffset();

    /* Initialize System */
    systemInit();

    /* Initialize VIM table */
    {
        unsigned i;

        for (i = 0; i < 96U; i++)
        {
            vimRAM->ISR[i] = s_vim_init[i];
        }
    }

    /* set IRQ/FIQ priorities */
    vimREG->FIRQPR0 =  SYS_FIQ
                    | (SYS_FIQ <<  1U)
                    | (SYS_IRQ <<  2U)
                    | (SYS_IRQ <<  3U)
                    | (SYS_IRQ <<  4U)
                    | (SYS_IRQ <<  5U)
                    | (SYS_IRQ <<  6U)
                    | (SYS_IRQ <<  7U)
                    | (SYS_IRQ <<  8U)
                    | (SYS_IRQ <<  9U)
                    | (SYS_IRQ << 10U)
                    | (SYS_IRQ << 11U)
                    | (SYS_IRQ << 12U)
                    | (SYS_IRQ << 13U)
                    | (SYS_IRQ << 14U)
                    | (SYS_IRQ << 15U)
                    | (SYS_IRQ << 16U)
                    | (SYS_IRQ << 17U)
                    | (SYS_IRQ << 18U)
                    | (SYS_IRQ << 19U)
                    | (SYS_IRQ << 20U)
                    | (SYS_IRQ << 21U)
                    | (SYS_IRQ << 22U)
                    | (SYS_IRQ << 23U)
                    | (SYS_IRQ << 24U)
                    | (SYS_IRQ << 25U)
                    | (SYS_IRQ << 26U)
                    | (SYS_IRQ << 27U)
                    | (SYS_IRQ << 28U)
                    | (SYS_IRQ << 29U)
                    | (SYS_IRQ << 30U)
                    | (SYS_IRQ << 31U);

    vimREG->FIRQPR1 =  SYS_IRQ
                    | (SYS_IRQ <<  1U)
                    | (SYS_IRQ <<  2U)
                    | (SYS_IRQ <<  3U)
                    | (SYS_IRQ <<  4U)
                    | (SYS_IRQ <<  5U)
                    | (SYS_IRQ <<  6U)
                    | (SYS_IRQ <<  7U)
                    | (SYS_IRQ <<  8U)
                    | (SYS_IRQ <<  9U)
                    | (SYS_IRQ << 10U)
                    | (SYS_IRQ << 11U)
                    | (SYS_IRQ << 12U)
                    | (SYS_IRQ << 13U)
                    | (SYS_IRQ << 14U)
                    | (SYS_IRQ << 15U)
                    | (SYS_IRQ << 16U)
                    | (SYS_IRQ << 17U)
                    | (SYS_IRQ << 18U)
                    | (SYS_IRQ << 19U)
                    | (SYS_IRQ << 20U)
                    | (SYS_IRQ << 21U)
                    | (SYS_IRQ << 22U)
                    | (SYS_IRQ << 23U)
                    | (SYS_IRQ << 24U)
                    | (SYS_IRQ << 25U)
                    | (SYS_IRQ << 26U)
                    | (SYS_IRQ << 27U)
                    | (SYS_IRQ << 28U)
                    | (SYS_IRQ << 29U)
                    | (SYS_IRQ << 30U);

    /* enable interrupts */
    vimREG->REQMASKSET0 = 1U
                        | (0U << 1)
                        | (1U << 2)	  /* RTI */
                        | (0U << 3)
                        | (0U << 4)
                        | (0U << 5)
                        | (0U << 6)
                        | (0U << 7)
                        | (0U << 8)
                        | (0U << 9)
                        | (0U << 10)
                        | (0U << 11)
                        | (0U << 12)
                        | (0U << 13)
                        | (0U << 14)
                        | (0U << 15)
                        | (0U << 16)
                        | (0U << 17)
                        | (0U << 18)
                        | (0U << 19)
                        | (0U << 20)
                        | (1U << 21)  /* Software Interrupt */
                        | (0U << 22)
                        | (0U << 23)
                        | (0U << 24)
                        | (0U << 25)
                        | (0U << 26)
                        | (0U << 27)
                        | (0U << 28)
                        | (0U << 29)
                        | (0U << 30)
                        | (0U << 31);

    vimREG->REQMASKSET1 = 0U
                        | (0U << 1)
                        | (0U << 2)
                        | (0U << 3)
                        | (0U << 4)
                        | (0U << 5)
                        | (0U << 6)
                        | (0U << 7)
                        | (0U << 8)
                        | (0U << 9)
                        | (0U << 10)
                        | (0U << 11)
                        | (0U << 12)
                        | (0U << 13)
                        | (0U << 14)
                        | (0U << 15)
                        | (0U << 16)
                        | (0U << 17)
                        | (0U << 18)
                        | (0U << 19)
                        | (0U << 20)
                        | (0U << 21)
                        | (0U << 22)
                        | (0U << 23)
                        | (0U << 24)
                        | (0U << 25)
                        | (0U << 26)
                        | (0U << 27)
                        | (0U << 28)
                        | (0U << 29)
                        | (0U << 30);


    /* initalise global variable and constructors */
	__TI_auto_init();

    /* call the application */
    main();
    exit(0);
}


