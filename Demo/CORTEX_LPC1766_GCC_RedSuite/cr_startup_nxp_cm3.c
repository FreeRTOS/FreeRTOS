//*****************************************************************************
//   +--+       
//   | ++----+   
//   +-++    |  
//     |     |  
//   +-+--+  |   
//   | +--+--+  
//   +----+    Copyright (c) 2009 Code Red Technologies Ltd. 
//
// cr_startup.c - Startup code for use with Code Red tools on NXP LPC17 family
//
// Software License Agreement
// 
// The software is owned by Code Red Technologies and/or its suppliers, and is 
// protected under applicable copyright laws.  All rights are reserved.  Any 
// use in violation of the foregoing restrictions may subject the user to criminal 
// sanctions under applicable laws, as well as to civil liability for the breach 
// of the terms and conditions of this license.
// 
// THIS SOFTWARE IS PROVIDED "AS IS".  NO WARRANTIES, WHETHER EXPRESS, IMPLIED
// OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE APPLY TO THIS SOFTWARE.
// LMI SHALL NOT, IN ANY CIRCUMSTANCES, BE LIABLE FOR SPECIAL, INCIDENTAL, OR
// CONSEQUENTIAL DAMAGES, FOR ANY REASON WHATSOEVER.
// 
//*****************************************************************************
#define WEAK __attribute__ ((weak))
#define ALIAS(f) __attribute__ ((weak, alias (#f)))

//*****************************************************************************
//
// Forward declaration of the default handlers.
//
//*****************************************************************************
void Reset_Handler(void);
void ResetISR(void) ALIAS(Reset_Handler);
static void NMI_Handler(void);
static void HardFault_Handler(void);
static void MemManage_Handler(void);
static void BusFault_Handler(void);
static void UsageFault_Handler(void);
static void DebugMon_Handler(void);

//*****************************************************************************
//
// Forward declaration of the specific IRQ handlers. These are aliased
// to the IntDefaultHandler, which is a 'forever' loop. When the application
// defines a handler (with the same name), this will automatically take 
// precedence over these weak definitions
//
//*****************************************************************************
void WDT_IRQHandler(void) ALIAS(IntDefaultHandler);
void TIMER0_IRQHandler(void) ALIAS(IntDefaultHandler);
void TIMER1_IRQHandler(void) ALIAS(IntDefaultHandler);
void TIMER2_IRQHandler(void) ALIAS(IntDefaultHandler);
void TIMER3_IRQHandler(void) ALIAS(IntDefaultHandler);
void UART0_IRQHandler(void) ALIAS(IntDefaultHandler);
void UART1_IRQHandler(void) ALIAS(IntDefaultHandler);
void UART2_IRQHandler(void) ALIAS(IntDefaultHandler);
void UART3_IRQHandler(void) ALIAS(IntDefaultHandler);
void PWM1_IRQHandler(void) ALIAS(IntDefaultHandler);
void I2C0_IRQHandler(void) ALIAS(IntDefaultHandler);
void I2C1_IRQHandler(void) ALIAS(IntDefaultHandler);
void I2C2_IRQHandler(void) ALIAS(IntDefaultHandler);
void SPI_IRQHandler(void) ALIAS(IntDefaultHandler);
void SSP0_IRQHandler(void) ALIAS(IntDefaultHandler);
void SSP1_IRQHandler(void) ALIAS(IntDefaultHandler);
void PLL0_IRQHandler(void) ALIAS(IntDefaultHandler);
void RTC_IRQHandler(void) ALIAS(IntDefaultHandler);
void EINT0_IRQHandler(void) ALIAS(IntDefaultHandler);
void EINT1_IRQHandler(void) ALIAS(IntDefaultHandler);
void EINT2_IRQHandler(void) ALIAS(IntDefaultHandler);
void EINT3_IRQHandler(void) ALIAS(IntDefaultHandler);
void ADC_IRQHandler(void) ALIAS(IntDefaultHandler);
void BOD_IRQHandler(void) ALIAS(IntDefaultHandler);
void USB_IRQHandler(void) ALIAS(IntDefaultHandler);
void CAN_IRQHandler(void) ALIAS(IntDefaultHandler);
void DMA_IRQHandler(void) ALIAS(IntDefaultHandler);
void I2S_IRQHandler(void) ALIAS(IntDefaultHandler);
void ENET_IRQHandler(void) ALIAS(IntDefaultHandler);
void RIT_IRQHandler(void) ALIAS(IntDefaultHandler);
void MCPWM_IRQHandler(void) ALIAS(IntDefaultHandler);
void QEI_IRQHandler(void) ALIAS(IntDefaultHandler);
void PLL1_IRQHandler(void) ALIAS(IntDefaultHandler);

extern void xPortSysTickHandler(void);
extern void xPortPendSVHandler(void);
extern void vPortSVCHandler( void );
extern void vEMAC_ISR( void );



//*****************************************************************************
//
// The entry point for the C++ library startup
//
//*****************************************************************************
extern WEAK void __libc_init_array(void);

//*****************************************************************************
//
// The entry point for the application.
// __main() is the entry point for redlib based applications
// main() is the entry point for newlib based applications
//
//*****************************************************************************
extern WEAK void __main(void);
extern WEAK void main(void);
//*****************************************************************************
//
// External declaration for the pointer to the stack top from the Linker Script
//
//*****************************************************************************
extern void _vStackTop;

//*****************************************************************************
//
// The vector table.
// This relies on the linker script to place at correct location in memory.
//
//*****************************************************************************
__attribute__ ((section(".isr_vector")))
void (* const g_pfnVectors[])(void) =
{
	// Core Level - CM3
	(void *)&_vStackTop,					// The initial stack pointer
	Reset_Handler,							// The reset handler
	NMI_Handler,							// The NMI handler
	HardFault_Handler,						// The hard fault handler
	MemManage_Handler,						// The MPU fault handler
	BusFault_Handler,						// The bus fault handler
	UsageFault_Handler,						// The usage fault handler
	0,										// Reserved
	0,										// Reserved
	0,										// Reserved
	0,										// Reserved
	    vPortSVCHandler,                        // SVCall handler
	DebugMon_Handler,						// Debug monitor handler
	0,										// Reserved
	    xPortPendSVHandler,                     // The PendSV handler
	    xPortSysTickHandler,                    // The SysTick handler

	// Chip Level - LPC17
	WDT_IRQHandler,							// 16, 0x40 - WDT
	TIMER0_IRQHandler,						// 17, 0x44 - TIMER0
	TIMER1_IRQHandler,						// 18, 0x48 - TIMER1
	TIMER2_IRQHandler,						// 19, 0x4c - TIMER2
	TIMER3_IRQHandler,						// 20, 0x50 - TIMER3
	UART0_IRQHandler,						// 21, 0x54 - UART0
	UART1_IRQHandler,						// 22, 0x58 - UART1
	UART2_IRQHandler,						// 23, 0x5c - UART2
	UART3_IRQHandler,						// 24, 0x60 - UART3
	PWM1_IRQHandler,						// 25, 0x64 - PWM1
	I2C0_IRQHandler,						// 26, 0x68 - I2C0
	I2C1_IRQHandler,						// 27, 0x6c - I2C1
	I2C2_IRQHandler,						// 28, 0x70 - I2C2
	SPI_IRQHandler,							// 29, 0x74 - SPI
	SSP0_IRQHandler,						// 30, 0x78 - SSP0
	SSP1_IRQHandler,						// 31, 0x7c - SSP1
	PLL0_IRQHandler,						// 32, 0x80 - PLL0 (Main PLL)
	RTC_IRQHandler,							// 33, 0x84 - RTC
	EINT0_IRQHandler,						// 34, 0x88 - EINT0
	EINT1_IRQHandler,						// 35, 0x8c - EINT1
	EINT2_IRQHandler,						// 36, 0x90 - EINT2
	EINT3_IRQHandler,						// 37, 0x94 - EINT3
	ADC_IRQHandler,							// 38, 0x98 - ADC
	BOD_IRQHandler,							// 39, 0x9c - BOD
	USB_IRQHandler,							// 40, 0xA0 - USB
	CAN_IRQHandler,							// 41, 0xa4 - CAN
	DMA_IRQHandler,							// 42, 0xa8 - GP DMA
	I2S_IRQHandler,							// 43, 0xac - I2S
	    vEMAC_ISR,                      		// Ethernet.
	RIT_IRQHandler,							// 45, 0xb4 - RITINT
	MCPWM_IRQHandler,						// 46, 0xb8 - Motor Control PWM
	QEI_IRQHandler,							// 47, 0xbc - Quadrature Encoder
	PLL1_IRQHandler,						// 48, 0xc0 - PLL1 (USB PLL)
};

//*****************************************************************************
//
// The following are constructs created by the linker, indicating where the
// the "data" and "bss" segments reside in memory.  The initializers for the
// for the "data" segment resides immediately following the "text" segment.
//
//*****************************************************************************
extern unsigned long _etext;
extern unsigned long _data;
extern unsigned long _edata;
extern unsigned long _bss;
extern unsigned long _ebss;

//*****************************************************************************
// Reset entry point for your code.
// Sets up a simple runtime environment and initializes the C/C++
// library.
//
//*****************************************************************************
void Reset_Handler(void)
{
    unsigned long *pulSrc, *pulDest;

    //
    // Copy the data segment initializers from flash to SRAM.
    //
    pulSrc = &_etext;
    for(pulDest = &_data; pulDest < &_edata; )
    {
        *pulDest++ = *pulSrc++;
    }

    //
    // Zero fill the bss segment.  This is done with inline assembly since this
    // will clear the value of pulDest if it is not kept in a register.
    //
    __asm("    ldr     r0, =_bss\n"
          "    ldr     r1, =_ebss\n"
          "    mov     r2, #0\n"
          "    .thumb_func\n"
          "zero_loop:\n"
          "        cmp     r0, r1\n"
          "        it      lt\n"
          "        strlt   r2, [r0], #4\n"
          "        blt     zero_loop");

    //
    // Call C++ library initilisation, if present
    //
	if (__libc_init_array)
		__libc_init_array() ;

	//
	// Call the application's entry point.
	// __main() is the entry point for redlib based applications (which calls main())
	// main() is the entry point for newlib based applications
	//
	if (__main)
		__main() ;
	else
		main() ;

	//
	// main() shouldn't return, but if it does, we'll just enter an infinite loop 
	//
	while (1) {
		;
	}
}

//*****************************************************************************
//
// This is the code that gets called when the processor receives a NMI.  This
// simply enters an infinite loop, preserving the system state for examination
// by a debugger.
//
//*****************************************************************************
static void NMI_Handler(void)
{
    while(1)
    {
    }
}

static void HardFault_Handler(void)
{
    while(1)
    {
    }
}

static void MemManage_Handler(void)
{
    while(1)
    {
    }
}

static void BusFault_Handler(void)
{
    while(1)
    {
    }
}

static void UsageFault_Handler(void)
{
    while(1)
    {
    }
}

static void DebugMon_Handler(void)
{
    while(1)
    {
    }
}


//*****************************************************************************
//
// Processor ends up here if an unexpected interrupt occurs or a handler
// is not present in the application code.
//
//*****************************************************************************
static void IntDefaultHandler(void)
{
    //
    // Go into an infinite loop.
    //
    while(1)
    {
    }
}
