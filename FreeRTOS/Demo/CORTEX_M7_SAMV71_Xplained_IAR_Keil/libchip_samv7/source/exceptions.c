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

/** Flag to indicate whether the svc is done */
volatile uint32_t dwRaisePriDone=0;

/**
 * \brief Default NMI interrupt handler.
 */
void NMI_Handler( void )
{
    while ( 1 ) ;
}

__INLINE static uint32_t StackUnwind(void)
{
    uint32_t Fault_Add;
    asm volatile (" mrs r0, msp " );
    asm volatile (" ldr %0, [r0,#28]" :"=r" (Fault_Add));  
    return Fault_Add;
}

static void HardFault_reason(void)
{
    uint32_t CFSRValue, BFAR;
    printf("In Hard Fault Handler\n\r");
    printf("SCB->HFSR = 0x%08x\n\r", SCB->HFSR);

    if ((SCB->HFSR & SCB_HFSR_DEBUGEVT_Msk)) {
        printf("Debug Event Hard Fault\n\r");
        printf("SCB->DFSR = 0x%08x\n", SCB->DFSR );
    }

    if ((SCB->HFSR & SCB_HFSR_VECTTBL_Msk)) {
        printf("Fault was due to vector table read on exception processing\n\r");     
    }

    if ((SCB->HFSR & SCB_HFSR_FORCED_Msk)) {
        printf("Forced Hard Fault\n\r");
        printf("SCB->CFSR = 0x%08x\n\r", SCB->CFSR );
        // Usage Fault
        if((SCB->CFSR & SCB_CFSR_USGFAULTSR_Msk)) 
        {
            CFSRValue = SCB->CFSR;
            printf("Usage fault: ");
            CFSRValue >>= SCB_CFSR_USGFAULTSR_Pos;                  
            if((CFSRValue & (1 << 9))) {
                printf("Divide by zero\n\r");
            }
            if((CFSRValue & (1 << 8))) {
                printf("Unaligned access error\n\r");
            }
            if((CFSRValue & (1 << 3))) {
                printf("Coprocessor access error\n\r");
            }
            if((CFSRValue & (1 << 2))) {
                printf("Integrity check error on EXC_RETURN\n\r");
            }
        }

        // Bus Fault
        if((SCB->CFSR & SCB_CFSR_BUSFAULTSR_Msk)) 
        {
            CFSRValue = SCB->CFSR;
            printf("Bus fault: ");
            CFSRValue >>= SCB_CFSR_BUSFAULTSR_Pos;                 

            if((CFSRValue & (1 << 7)) && (CFSRValue & (1 << 1))) {
                BFAR = SCB->BFAR;
                printf("Precise data access error. Bus Fault Address Register is: %x \n\r", BFAR );
            }
            if((CFSRValue & (1 << 4))) {
                printf("Bus fault has occurred on exception entry\n\r");
            }
            if((CFSRValue & (1 << 3))) {
                printf("bus fault has occurred on exception return\n\r");
            }
            if((CFSRValue & (1 << 2))) {
                printf("Imprecise data access error\n\r");
            }

            if((CFSRValue & (1 << 0))) {
                printf("This bit indicates a bus fault on an instruction prefetch. \n\r");
            }

        }
    }

    // MemoryFault      
    if((SCB->CFSR & SCB_CFSR_MEMFAULTSR_Msk)) 
    {
        CFSRValue = SCB->CFSR;
        printf("Memory fault: ");
        CFSRValue >>= SCB_CFSR_MEMFAULTSR_Pos;                 
        if((CFSRValue & (1 << 9)) != 0) {
            printf("Divide by zero\n\r");
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

    printf("HardFault at addr 0X%x\n\r", StackUnwind());

    __ISB();
    __DMB();
    HardFault_reason();

}

/**
 * \brief Default MemManage interrupt handler.
 */
void MemManage_Handler( void )
{
    printf("MemoryMemFault (MPU fault) at addr 0X%x\n\r", StackUnwind());

    __ISB();
    __DMB();
    __ASM volatile("BKPT #01");  
}

/**
 * \brief Default BusFault interrupt handler.
 */
void BusFault_Handler( void )
{
    asm("nop");
    asm("nop");
    printf("Bus Fault at addr 0X%x\n\r", StackUnwind());

    __ISB();
    __DMB();
    __ASM volatile("BKPT #01");  
}

/**
 * \brief Default UsageFault interrupt handler.
 */
void UsageFault_Handler( void )
{
    printf("Usage fault at addr 0X%x", StackUnwind());

    __ISB();
    __DMB();
    __ASM volatile("BKPT #01");  
}

/**
 * \brief Default SVC interrupt handler.
 */
WEAK void SVC_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default DebugMon interrupt handler.
 */
WEAK void DebugMon_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default PendSV interrupt handler.
 */
void PendSV_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default SysTick interrupt handler.
 */
WEAK void SysTick_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default interrupt handler for Supply Controller.
 */
WEAK void SUPC_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default interrupt handler for Reset Controller.
 */
WEAK void RSTC_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default interrupt handler for Real Time Clock.
 */
WEAK void RTC_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default interrupt handler for Real Time Timer.
 */
WEAK void RTT_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default interrupt handler for Watchdog Timer.
 */
WEAK void WDT0_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default interrupt handler for PMC.
 */
WEAK void PMC_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default interrupt handler for EEFC.
 */
WEAK void EFC_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default interrupt handler for UART0.
 */
WEAK void UART0_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default interrupt handler for UART1.
 */
WEAK void UART1_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default interrupt handler for SMC.
 */
WEAK void TC10_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default interrupt handler for PIOA Controller.
 */
WEAK void PIOA_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default interrupt handler for PIOB Controller.
 */
WEAK void PIOB_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default interrupt handler for PIOC Controller.
 */
WEAK void PIOC_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default interrupt handler for USART0.
 */
WEAK void USART0_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default interrupt handler for USART1.
 */
WEAK void USART1_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default interrupt handler for USART2.
 */
WEAK void USART2_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default interrupt handler for MCI.
 */
WEAK void HSMCI_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default interrupt handler for TWI0.
 */
WEAK void TWI0_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default interrupt handler for TWI1.
 */
WEAK void TWI1_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default interrupt handler for SPI.
 */
WEAK void SPI0_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default interrupt handler for SSC.
 */
WEAK void SSC_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default interrupt handler for TC0.
 */
WEAK void TC0_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default interrupt handler for TC1.
 */
WEAK void TC1_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default interrupt handler for TC2.
 */
WEAK void TC2_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default SUPC interrupt handler for TC3.
 */
WEAK void TC3_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default SUPC interrupt handler for TC4.
 */
WEAK void TC4_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default SUPC interrupt handler for TC5.
 */
WEAK void TC5_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default SUPC interrupt handler for ADC.
 */
WEAK void AFEC1_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default SUPC interrupt handler for DAC.
 */
WEAK void DACC_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default SUPC interrupt handler for PWM.
 */
WEAK void PWM0_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default SUPC interrupt handler for CRCCU.
 */
WEAK void TC9_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default SUPC interrupt handler for ACC.
 */
WEAK void ACC_Handler( void )
{
    while ( 1 ) ;
}

/**
 * \brief Default SUPC interrupt handler for USBD.
 */
WEAK void TC11_Handler( void )
{
    while ( 1 ) ;
}

WEAK void USBHS_Handler(void)
{
    //	udd_interrupt();
    while(1);
}
