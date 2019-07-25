/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2014, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/**
 * \file
 * This file contains the default exception handlers.
 *
 * \note
 * The exception handler has weak aliases.
 * As they are weak aliases, any function with the same name will override
 * this definition.
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Default NMI interrupt handler.
 */
void NMI_Handler( void )
{
	while ( 1 ) ;
}

/**
 * \brief This function back trace the stack to give exact address where fault 
 happened
**/
#if (TRACE_LEVEL > 4) 
__STATIC_INLINE uint32_t StackUnwind(void)
{
	uint32_t Fault_Add;

#if defined (__CC_ARM)
	uint32_t temp;
	__ASM("mrs temp, msp ");
	__ASM{ ldr Fault_Add, [temp,#28]}
#else
	__ASM("mrs r0, msp ");
	__ASM("ldr %0, [r0,#28]" : "=r" (Fault_Add));
#endif
	return Fault_Add;
}
#endif

/**
 * \brief If Other Faults are enabled then HardFault error will look for those 
 *  errors to give more detail about fault
**/
static void HardFault_reason(void)
{
	uint32_t CFSRValue; 
	TRACE_DEBUG("In Hard Fault Handler\n\r");
	TRACE_DEBUG("SCB->HFSR = 0x%08x\n\r", SCB->HFSR);

	if ((SCB->HFSR & SCB_HFSR_DEBUGEVT_Msk)) {
		TRACE_DEBUG("Debug Event Hard Fault\n\r");
		TRACE_DEBUG("SCB->DFSR = 0x%08x\n", SCB->DFSR );
	}

	if ((SCB->HFSR & SCB_HFSR_VECTTBL_Msk)) {
		TRACE_DEBUG("Fault was due to vector table read on \
			exception processing\n\r");
	}
	// Forced HardFault
	if ((SCB->HFSR & SCB_HFSR_FORCED_Msk)) {
		TRACE_DEBUG("Forced Hard Fault\n\r");
		TRACE_DEBUG("SCB->CFSR = 0x%08x\n\r", SCB->CFSR );
		// Usage Fault
		if((SCB->CFSR & SCB_CFSR_USGFAULTSR_Msk)) 
		{
			CFSRValue = SCB->CFSR;
			TRACE_DEBUG("Usage fault: ");
			CFSRValue >>= SCB_CFSR_USGFAULTSR_Pos;
			if((CFSRValue & (1 << 9))) {
				TRACE_DEBUG("Divide by zero\n\r");
			}
			if((CFSRValue & (1 << 8))) {
				TRACE_DEBUG("Unaligned access error\n\r");
			}
			if((CFSRValue & (1 << 3))) {
				TRACE_DEBUG("Coprocessor access error\n\r");
			}
			if((CFSRValue & (1 << 2))) {
				TRACE_DEBUG("Integrity check error on EXC_RETURN\n\r");
			}
		}
		// Bus Fault
		if((SCB->CFSR & SCB_CFSR_BUSFAULTSR_Msk)) {
			CFSRValue = SCB->CFSR;
			TRACE_DEBUG("Bus fault: ");
			CFSRValue >>= SCB_CFSR_BUSFAULTSR_Pos;

			if((CFSRValue & (1 << 7)) && (CFSRValue & (1 << 1))) {
				TRACE_DEBUG("Precise data access error. Bus Fault Address \
					Register is: %x \n\r", SCB->BFAR );
			}
			if((CFSRValue & (1 << 4))) {
				TRACE_DEBUG("Bus fault has occurred on exception entry\n\r");
			}
			if((CFSRValue & (1 << 3))) {
				TRACE_DEBUG("bus fault has occurred on exception return\n\r");
			}
			if((CFSRValue & (1 << 2))) {
				TRACE_DEBUG("Imprecise data access error\n\r");
			}

			if((CFSRValue & (1 << 0))) {
				TRACE_DEBUG("This bit indicates a bus fault on an instruction \
					pre-fetch. \n\r");
			}
		}
	}
	// MemoryFault
	if((SCB->CFSR & SCB_CFSR_MEMFAULTSR_Msk)) {
		CFSRValue = SCB->CFSR;
		TRACE_DEBUG("Memory fault: ");
		CFSRValue >>= SCB_CFSR_MEMFAULTSR_Pos;
		if((CFSRValue & (1 << 9)) != 0) {
			TRACE_DEBUG("Divide by zero\n\r");
		}
	}
	__ISB();
	__DMB();
	__ASM volatile("BKPT #01");
}
/**
 * \brief Default HardFault interrupt handler.
 */

void HardFault_Handler( void )
{
	TRACE_DEBUG("\n\rHardFault at address 0X%x\n\r", StackUnwind());
	__ISB();
	__DMB();
	HardFault_reason();
}

#ifndef MPU_EXAMPLE_FEATURE
/**
 * \brief Default MemManage interrupt handler.
 */
void MemManage_Handler( void )
{
	TRACE_DEBUG("\n\rMemoryMemFault (MPU fault) at address 0X%x\n\r",
		StackUnwind());
	__ISB();
	__DMB();
	__ASM volatile("BKPT #01");
}
#endif

/**
 * \brief Default BusFault interrupt handler.
 */
void BusFault_Handler( void )
{
	__ASM("nop");
	__ASM("nop");
	TRACE_DEBUG("\n\rBus Fault at address 0X%x\n\r", StackUnwind());

	__ISB();
	__DMB();
	__ASM volatile("BKPT #01");
}

/**
 * \brief Default UsageFault interrupt handler.
 */
void UsageFault_Handler( void )
{
	TRACE_DEBUG("\r\nUsage fault at address 0X%x", StackUnwind());

	__ISB();
	__DMB();
	__ASM volatile("BKPT #01");  
}
