/*
 * -------------------------------------------
 *    MSP432 DriverLib - v3_10_00_09
 * -------------------------------------------
 *
 * --COPYRIGHT--,BSD,BSD
 * Copyright (c) 2014, Texas Instruments Incorporated
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * *  Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 * *  Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * *  Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS;
 * OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR
 * OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * --/COPYRIGHT--*/
//*****************************************************************************
//
// Copyright (C) 2012 - 2015 Texas Instruments Incorporated - http://www.ti.com/
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
//
//  Redistributions of source code must retain the above copyright
//  notice, this list of conditions and the following disclaimer.
//
//  Redistributions in binary form must reproduce the above copyright
//  notice, this list of conditions and the following disclaimer in the
//  documentation and/or other materials provided with the
//  distribution.
//
//  Neither the name of Texas Instruments Incorporated nor the names of
//  its contributors may be used to endorse or promote products derived
//  from this software without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
// OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
// LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
// DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
// THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
//
// MSP432 Startup Code for IAR Embedded Workbench for ARM
//
//****************************************************************************

#include <stdint.h>

//*****************************************************************************
//
// Enable the IAR extensions for this source file.
//
//*****************************************************************************
#pragma language=extended

//*****************************************************************************
//
// Forward declaration of the default fault handlers.
//
//*****************************************************************************
void ResetISR(void);
static void NmiSR(void);
static void FaultISR(void);
static void IntDefaultHandler(void);

//*****************************************************************************
//
// External declaration for the interrupt handler used by the application.
//
//*****************************************************************************
extern void SysTick_Handler( void );
extern void PendSV_Handler( void );
extern void SVC_Handler( void );
extern void vUART_Handler( void );
extern void vT32_0_Handler( void );
extern void vT32_1_Handler( void );
extern void PORT1_IRQHandler( void );
//*****************************************************************************
//
// The entry point for the application startup code.
//
//*****************************************************************************
extern void __iar_program_start(void);

//*****************************************************************************
//
// Reserve space for the system stack.
//
//*****************************************************************************
static uint32_t systemStack[128] @ ".noinit";

//*****************************************************************************
//
// A union that describes the entries of the vector table.  The union is needed
// since the first entry is the stack pointer and the remainder are function
// pointers.
//
//*****************************************************************************
typedef union
{
    void (*handler)(void);
    uint32_t ptr;
}
uVectorEntry;

//*****************************************************************************
//
// The vector table.  Note that the proper constructs must be placed on this to
// ensure that it ends up at physical address 0x0000.0000.
//
//*****************************************************************************
__root const uVectorEntry __vector_table[] @ ".intvec" =
{
    { .ptr = (uint32_t)systemStack + sizeof(systemStack) },
                                            // The initial stack pointer
    ResetISR,                               // The reset handler
    NmiSR,                                  // The NMI handler
    FaultISR,                               // The hard fault handler
    IntDefaultHandler,                      // The MPU fault handler
    IntDefaultHandler,                      // The bus fault handler
    IntDefaultHandler,                      // The usage fault handler
    0,                                      // Reserved
    0,                                      // Reserved
    0,                                      // Reserved
    0,                                      // Reserved
    SVC_Handler,                             // SVCall handler
    IntDefaultHandler,                      // Debug monitor handler
    0,                                      // Reserved
    PendSV_Handler,                             // The PendSV handler
    SysTick_Handler,                            // The SysTick handler
    IntDefaultHandler,                      // PSS ISR
    IntDefaultHandler,                      // CS ISR
    IntDefaultHandler,                      // PCM ISR
    IntDefaultHandler,                      // WDT ISR
    IntDefaultHandler,                      // FPU ISR
    IntDefaultHandler,                      // FLCTL ISR
    IntDefaultHandler,                      // COMP_E0_MODULE ISR
    IntDefaultHandler,                      // COMP_E1_MODULE ISR
    IntDefaultHandler,                      // TA0_0 ISR
    IntDefaultHandler,                      // TA0_N ISR
    IntDefaultHandler,                      // TA1_0 ISR
    IntDefaultHandler,                      // TA1_N ISR
    IntDefaultHandler,                      // TA2_0 ISR
    IntDefaultHandler,                      // TA2_N ISR
    IntDefaultHandler,                      // TA3_0 ISR
    IntDefaultHandler,                      // TA3_N ISR
    vUART_Handler,                            // EUSCIA0 ISR
    IntDefaultHandler,                      // EUSCIA1 ISR
    IntDefaultHandler,                      // EUSCIA2 ISR
    IntDefaultHandler,                      // EUSCIA3 ISR
    IntDefaultHandler,                      // EUSCIB0 ISR
    IntDefaultHandler,                      // EUSCIB1 ISR
    IntDefaultHandler,                      // EUSCIB2 ISR
    IntDefaultHandler,                      // EUSCIB3 ISR
    IntDefaultHandler,                      // ADC12 ISR
    vT32_0_Handler,                                // T32_INT1 ISR
    vT32_1_Handler,                                // T32_INT2 ISR
    IntDefaultHandler,                      // T32_INTC ISR
    IntDefaultHandler,                      // AES ISR
    IntDefaultHandler,                      // RTC ISR
    IntDefaultHandler,                      // DMA_ERR ISR
    IntDefaultHandler,                      // DMA_INT3 ISR
    IntDefaultHandler,                      // DMA_INT2 ISR
    IntDefaultHandler,                       // DMA_INT1 ISR
    IntDefaultHandler,                      // DMA_INT0 ISR
    PORT1_IRQHandler,                      // PORT1 ISR
    IntDefaultHandler,                      // PORT2 ISR
    IntDefaultHandler,                      // PORT3 ISR
    IntDefaultHandler,                      // PORT4 ISR
    IntDefaultHandler,                      // PORT5 ISR
    IntDefaultHandler,                      // PORT6 ISR
    IntDefaultHandler,                      // Reserved 41
    IntDefaultHandler,                      // Reserved 42
    IntDefaultHandler,                      // Reserved 43
    IntDefaultHandler,                      // Reserved 44
    IntDefaultHandler,                      // Reserved 45
    IntDefaultHandler,                      // Reserved 46
    IntDefaultHandler,                      // Reserved 47
    IntDefaultHandler,                      // Reserved 48
    IntDefaultHandler,                      // Reserved 49
    IntDefaultHandler,                      // Reserved 50
    IntDefaultHandler,                      // Reserved 51
    IntDefaultHandler,                      // Reserved 52
    IntDefaultHandler,                      // Reserved 53
    IntDefaultHandler,                      // Reserved 54
    IntDefaultHandler,                      // Reserved 55
    IntDefaultHandler,                      // Reserved 56
    IntDefaultHandler,                      // Reserved 57
    IntDefaultHandler,                      // Reserved 58
    IntDefaultHandler,                      // Reserved 59
    IntDefaultHandler,                      // Reserved 60
    IntDefaultHandler,                      // Reserved 61
    IntDefaultHandler,                      // Reserved 62
    IntDefaultHandler,                      // Reserved 63
    IntDefaultHandler                       // Reserved 64
};

//*****************************************************************************
//
// This is the code that gets called when the processor first starts execution
// following a reset event.  Only the absolutely necessary set is performed,
// after which the application supplied entry() routine is called.  Any fancy
// actions (such as making decisions based on the reset cause register, and
// resetting the bits in that register) are left solely in the hands of the
// application.
//
//*****************************************************************************
void
ResetISR(void)
{
void SystemInit(void);

	// Initialize the device
	SystemInit();

    //
    // Call the application's entry point.
    //
    __iar_program_start();
}

//*****************************************************************************
//
// This is the code that gets called when the processor receives a NMI.  This
// simply enters an infinite loop, preserving the system state for examination
// by a debugger.
//
//*****************************************************************************
static void
NmiSR(void)
{
    //
    // Enter an infinite loop.
    //
    while(1)
    {
    }
}

//*****************************************************************************
//
// This is the code that gets called when the processor receives a fault
// interrupt.  This simply enters an infinite loop, preserving the system state
// for examination by a debugger.
//
//*****************************************************************************
static void
FaultISR(void)
{
    //
    // Enter an infinite loop.
    //
    while(1)
    {
    }
}

//*****************************************************************************
//
// This is the code that gets called when the processor receives an unexpected
// interrupt.  This simply enters an infinite loop, preserving the system state
// for examination by a debugger.
//
//*****************************************************************************
static void
IntDefaultHandler(void)
{
    //
    // Go into an infinite loop.
    //
    while(1)
    {
    }
}
