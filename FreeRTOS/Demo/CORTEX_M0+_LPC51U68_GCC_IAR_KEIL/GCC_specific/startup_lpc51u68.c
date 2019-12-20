//*****************************************************************************
// LPC51U68 startup code for use with MCUXpresso IDE
//
// Version : 020818
//*****************************************************************************
//
// Copyright 2016-2018 NXP
//
// SPDX-License-Identifier: BSD-3-Clause
//*****************************************************************************

#if defined (DEBUG)
#pragma GCC push_options
#pragma GCC optimize ("Og")
#endif // (DEBUG)

#if defined (__cplusplus)
#ifdef __REDLIB__
#error Redlib does not support C++
#else
//*****************************************************************************
//
// The entry point for the C++ library startup
//
//*****************************************************************************
extern "C" {
    extern void __libc_init_array(void);
}
#endif
#endif

#define WEAK __attribute__ ((weak))
#define WEAK_AV __attribute__ ((weak, section(".after_vectors")))
#define ALIAS(f) __attribute__ ((weak, alias (#f)))

//*****************************************************************************
#if defined (__cplusplus)
extern "C" {
#endif

//*****************************************************************************
// Variable to store CRP value in. Will be placed automatically
// by the linker when "Enable Code Read Protect" selected.
// See crp.h header for more information
//*****************************************************************************
//*****************************************************************************
// Declaration of external SystemInit function
//*****************************************************************************
#if defined (__USE_CMSIS)
extern void SystemInit(void);
#endif // (__USE_CMSIS)

//*****************************************************************************
// Forward declaration of the core exception handlers.
// When the application defines a handler (with the same name), this will
// automatically take precedence over these weak definitions.
// If your application is a C++ one, then any interrupt handlers defined
// in C++ files within in your main application will need to have C linkage
// rather than C++ linkage. To do this, make sure that you are using extern "C"
// { .... } around the interrupt handler within your main application code.
//*****************************************************************************
     void ResetISR(void);
WEAK void NMI_Handler(void);
WEAK void HardFault_Handler(void);
WEAK void SVC_Handler(void);
WEAK void PendSV_Handler(void);
WEAK void SysTick_Handler(void);
WEAK void IntDefaultHandler(void);

//*****************************************************************************
// Forward declaration of the application IRQ handlers. When the application
// defines a handler (with the same name), this will automatically take
// precedence over weak definitions below
//*****************************************************************************
WEAK void WDT_BOD_IRQHandler(void);
WEAK void DMA0_IRQHandler(void);
WEAK void GINT0_IRQHandler(void);
WEAK void GINT1_IRQHandler(void);
WEAK void PIN_INT0_IRQHandler(void);
WEAK void PIN_INT1_IRQHandler(void);
WEAK void PIN_INT2_IRQHandler(void);
WEAK void PIN_INT3_IRQHandler(void);
WEAK void UTICK0_IRQHandler(void);
WEAK void MRT0_IRQHandler(void);
WEAK void CTIMER0_IRQHandler(void);
WEAK void CTIMER1_IRQHandler(void);
WEAK void SCT0_IRQHandler(void);
WEAK void CTIMER3_IRQHandler(void);
WEAK void FLEXCOMM0_IRQHandler(void);
WEAK void FLEXCOMM1_IRQHandler(void);
WEAK void FLEXCOMM2_IRQHandler(void);
WEAK void FLEXCOMM3_IRQHandler(void);
WEAK void FLEXCOMM4_IRQHandler(void);
WEAK void FLEXCOMM5_IRQHandler(void);
WEAK void FLEXCOMM6_IRQHandler(void);
WEAK void FLEXCOMM7_IRQHandler(void);
WEAK void ADC0_SEQA_IRQHandler(void);
WEAK void ADC0_SEQB_IRQHandler(void);
WEAK void ADC0_THCMP_IRQHandler(void);
WEAK void Reserved41_IRQHandler(void);
WEAK void Reserved42_IRQHandler(void);
WEAK void USB0_NEEDCLK_IRQHandler(void);
WEAK void USB0_IRQHandler(void);
WEAK void RTC_IRQHandler(void);

//*****************************************************************************
// Forward declaration of the driver IRQ handlers. These are aliased
// to the IntDefaultHandler, which is a 'forever' loop. When the driver
// defines a handler (with the same name), this will automatically take
// precedence over these weak definitions
//*****************************************************************************
void WDT_BOD_DriverIRQHandler(void) ALIAS(IntDefaultHandler);
void DMA0_DriverIRQHandler(void) ALIAS(IntDefaultHandler);
void GINT0_DriverIRQHandler(void) ALIAS(IntDefaultHandler);
void GINT1_DriverIRQHandler(void) ALIAS(IntDefaultHandler);
void PIN_INT0_DriverIRQHandler(void) ALIAS(IntDefaultHandler);
void PIN_INT1_DriverIRQHandler(void) ALIAS(IntDefaultHandler);
void PIN_INT2_DriverIRQHandler(void) ALIAS(IntDefaultHandler);
void PIN_INT3_DriverIRQHandler(void) ALIAS(IntDefaultHandler);
void UTICK0_DriverIRQHandler(void) ALIAS(IntDefaultHandler);
void MRT0_DriverIRQHandler(void) ALIAS(IntDefaultHandler);
void CTIMER0_DriverIRQHandler(void) ALIAS(IntDefaultHandler);
void CTIMER1_DriverIRQHandler(void) ALIAS(IntDefaultHandler);
void SCT0_DriverIRQHandler(void) ALIAS(IntDefaultHandler);
void CTIMER3_DriverIRQHandler(void) ALIAS(IntDefaultHandler);
void FLEXCOMM0_DriverIRQHandler(void) ALIAS(IntDefaultHandler);
void FLEXCOMM1_DriverIRQHandler(void) ALIAS(IntDefaultHandler);
void FLEXCOMM2_DriverIRQHandler(void) ALIAS(IntDefaultHandler);
void FLEXCOMM3_DriverIRQHandler(void) ALIAS(IntDefaultHandler);
void FLEXCOMM4_DriverIRQHandler(void) ALIAS(IntDefaultHandler);
void FLEXCOMM5_DriverIRQHandler(void) ALIAS(IntDefaultHandler);
void FLEXCOMM6_DriverIRQHandler(void) ALIAS(IntDefaultHandler);
void FLEXCOMM7_DriverIRQHandler(void) ALIAS(IntDefaultHandler);
void ADC0_SEQA_DriverIRQHandler(void) ALIAS(IntDefaultHandler);
void ADC0_SEQB_DriverIRQHandler(void) ALIAS(IntDefaultHandler);
void ADC0_THCMP_DriverIRQHandler(void) ALIAS(IntDefaultHandler);
void Reserved41_DriverIRQHandler(void) ALIAS(IntDefaultHandler);
void Reserved42_DriverIRQHandler(void) ALIAS(IntDefaultHandler);
void USB0_NEEDCLK_DriverIRQHandler(void) ALIAS(IntDefaultHandler);
void USB0_DriverIRQHandler(void) ALIAS(IntDefaultHandler);
void RTC_DriverIRQHandler(void) ALIAS(IntDefaultHandler);

//*****************************************************************************
// The entry point for the application.
// __main() is the entry point for Redlib based applications
// main() is the entry point for Newlib based applications
//*****************************************************************************
#if defined (__REDLIB__)
extern void __main(void);
#endif
extern int main(void);

//*****************************************************************************
// External declaration for the pointer to the stack top from the Linker Script
//*****************************************************************************
extern void _vStackTop(void);
//*****************************************************************************
// External declaration for LPC MCU vector table checksum from  Linker Script
//*****************************************************************************
WEAK extern void __valid_user_code_checksum();

//*****************************************************************************
//*****************************************************************************
#if defined (__cplusplus)
} // extern "C"
#endif
//*****************************************************************************
// The vector table.
// This relies on the linker script to place at correct location in memory.
//*****************************************************************************
extern void (* const g_pfnVectors[])(void);
extern void * __Vectors __attribute__ ((alias ("g_pfnVectors")));

__attribute__ ((used, section(".isr_vector")))
void (* const g_pfnVectors[])(void) = {
    // Core Level - CM0P
    &_vStackTop,                       // The initial stack pointer
    ResetISR,                          // The reset handler
    NMI_Handler,                       // The NMI handler
    HardFault_Handler,                 // The hard fault handler
    0,                                 // Reserved
    0,                                 // Reserved
    0,                                 // Reserved
    __valid_user_code_checksum,        // LPC MCU checksum
    0,                                 // ECRP
    0,                                 // Reserved
    0,                                 // Reserved
    SVC_Handler,                       // SVCall handler
    0,                                 // Reserved
    0,                                 // Reserved
    PendSV_Handler,                    // The PendSV handler
    SysTick_Handler,                   // The SysTick handler

    // Chip Level - LPC51U68
    WDT_BOD_IRQHandler,       // 16: Windowed watchdog timer, Brownout detect
    DMA0_IRQHandler,          // 17: DMA controller
    GINT0_IRQHandler,         // 18: GPIO group 0
    GINT1_IRQHandler,         // 19: GPIO group 1
    PIN_INT0_IRQHandler,      // 20: Pin interrupt 0 or pattern match engine slice 0
    PIN_INT1_IRQHandler,      // 21: Pin interrupt 1or pattern match engine slice 1
    PIN_INT2_IRQHandler,      // 22: Pin interrupt 2 or pattern match engine slice 2
    PIN_INT3_IRQHandler,      // 23: Pin interrupt 3 or pattern match engine slice 3
    UTICK0_IRQHandler,        // 24: Micro-tick Timer
    MRT0_IRQHandler,          // 25: Multi-rate timer
    CTIMER0_IRQHandler,       // 26: Standard counter/timer CTIMER0
    CTIMER1_IRQHandler,       // 27: Standard counter/timer CTIMER1
    SCT0_IRQHandler,          // 28: SCTimer/PWM
    CTIMER3_IRQHandler,       // 29: Standard counter/timer CTIMER3
    FLEXCOMM0_IRQHandler,     // 30: Flexcomm Interface 0 (USART, SPI, I2C)
    FLEXCOMM1_IRQHandler,     // 31: Flexcomm Interface 1 (USART, SPI, I2C)
    FLEXCOMM2_IRQHandler,     // 32: Flexcomm Interface 2 (USART, SPI, I2C)
    FLEXCOMM3_IRQHandler,     // 33: Flexcomm Interface 3 (USART, SPI, I2C)
    FLEXCOMM4_IRQHandler,     // 34: Flexcomm Interface 4 (USART, SPI, I2C)
    FLEXCOMM5_IRQHandler,     // 35: Flexcomm Interface 5 (USART, SPI, I2C)
    FLEXCOMM6_IRQHandler,     // 36: Flexcomm Interface 6 (USART, SPI, I2C, I2S)
    FLEXCOMM7_IRQHandler,     // 37: Flexcomm Interface 7 (USART, SPI, I2C, I2S)
    ADC0_SEQA_IRQHandler,     // 38: ADC0 sequence A completion.
    ADC0_SEQB_IRQHandler,     // 39: ADC0 sequence B completion.
    ADC0_THCMP_IRQHandler,    // 40: ADC0 threshold compare and error.
    Reserved41_IRQHandler,    // 41: Reserved interrupt
    Reserved42_IRQHandler,    // 42: Reserved interrupt
    USB0_NEEDCLK_IRQHandler,  // 43: USB Activity Wake-up Interrupt
    USB0_IRQHandler,          // 44: USB device
    RTC_IRQHandler,           // 45: RTC alarm and wake-up interrupts
}; /* End of g_pfnVectors */

//*****************************************************************************
// Functions to carry out the initialization of RW and BSS data sections. These
// are written as separate functions rather than being inlined within the
// ResetISR() function in order to cope with MCUs with multiple banks of
// memory.
//*****************************************************************************
__attribute__ ((section(".after_vectors.init_data")))
void data_init(unsigned int romstart, unsigned int start, unsigned int len) {
    unsigned int *pulDest = (unsigned int*) start;
    unsigned int *pulSrc = (unsigned int*) romstart;
    unsigned int loop;
    for (loop = 0; loop < len; loop = loop + 4)
        *pulDest++ = *pulSrc++;
}

__attribute__ ((section(".after_vectors.init_bss")))
void bss_init(unsigned int start, unsigned int len) {
    unsigned int *pulDest = (unsigned int*) start;
    unsigned int loop;
    for (loop = 0; loop < len; loop = loop + 4)
        *pulDest++ = 0;
}

//*****************************************************************************
// The following symbols are constructs generated by the linker, indicating
// the location of various points in the "Global Section Table". This table is
// created by the linker via the Code Red managed linker script mechanism. It
// contains the load address, execution address and length of each RW data
// section and the execution and length of each BSS (zero initialized) section.
//*****************************************************************************
extern unsigned int __data_section_table;
extern unsigned int __data_section_table_end;
extern unsigned int __bss_section_table;
extern unsigned int __bss_section_table_end;

//*****************************************************************************
// Reset entry point for your code.
// Sets up a simple runtime environment and initializes the C/C++
// library.
//*****************************************************************************
__attribute__ ((section(".after_vectors.reset")))
void ResetISR(void) {

    // Disable interrupts
    __asm volatile ("cpsid i");

    // Enable SRAM clock used by Stack
    __asm volatile ("LDR R0, =0x40000220\n\t"
                    "MOV R1, #56\n\t"
                    "STR R1, [R0]");

#if defined (__USE_CMSIS)
// If __USE_CMSIS defined, then call CMSIS SystemInit code
    SystemInit();

#endif // (__USE_CMSIS)

    //
    // Copy the data sections from flash to SRAM.
    //
    unsigned int LoadAddr, ExeAddr, SectionLen;
    unsigned int *SectionTableAddr;

    // Load base address of Global Section Table
    SectionTableAddr = &__data_section_table;

    // Copy the data sections from flash to SRAM.
    while (SectionTableAddr < &__data_section_table_end) {
        LoadAddr = *SectionTableAddr++;
        ExeAddr = *SectionTableAddr++;
        SectionLen = *SectionTableAddr++;
        data_init(LoadAddr, ExeAddr, SectionLen);
    }

    // At this point, SectionTableAddr = &__bss_section_table;
    // Zero fill the bss segment
    while (SectionTableAddr < &__bss_section_table_end) {
        ExeAddr = *SectionTableAddr++;
        SectionLen = *SectionTableAddr++;
        bss_init(ExeAddr, SectionLen);
    }

#if !defined (__USE_CMSIS)
// Assume that if __USE_CMSIS defined, then CMSIS SystemInit code
// will setup the VTOR register

    // Check to see if we are running the code from a non-zero
    // address (eg RAM, external flash), in which case we need
    // to modify the VTOR register to tell the CPU that the
    // vector table is located at a non-0x0 address.
    unsigned int * pSCB_VTOR = (unsigned int *) 0xE000ED08;
    if ((unsigned int *)g_pfnVectors!=(unsigned int *) 0x00000000) {
        *pSCB_VTOR = (unsigned int)g_pfnVectors;
    }
#endif // (__USE_CMSIS)

#if defined (__cplusplus)
    //
    // Call C++ library initialisation
    //
    __libc_init_array();
#endif

    // Reenable interrupts
    __asm volatile ("cpsie i");

#if defined (__REDLIB__)
    // Call the Redlib library, which in turn calls main()
    __main();
#else
    main();
#endif

    //
    // main() shouldn't return, but if it does, we'll just enter an infinite loop
    //
    while (1) {
        ;
    }
}

//*****************************************************************************
// Default core exception handlers. Override the ones here by defining your own
// handler routines in your application code.
//*****************************************************************************
WEAK_AV void NMI_Handler(void)
{ while(1) {}
}

WEAK_AV void HardFault_Handler(void)
{ while(1) {}
}

WEAK_AV void SVC_Handler(void)
{ while(1) {}
}

WEAK_AV void PendSV_Handler(void)
{ while(1) {}
}

WEAK_AV void SysTick_Handler(void)
{ while(1) {}
}

//*****************************************************************************
// Processor ends up here if an unexpected interrupt occurs or a specific
// handler is not present in the application code.
//*****************************************************************************
WEAK_AV void IntDefaultHandler(void)
{ while(1) {}
}

//*****************************************************************************
// Default application exception handlers. Override the ones here by defining
// your own handler routines in your application code. These routines call
// driver exception handlers or IntDefaultHandler() if no driver exception
// handler is included.
//*****************************************************************************
WEAK_AV void WDT_BOD_IRQHandler(void)
{   WDT_BOD_DriverIRQHandler();
}

WEAK_AV void DMA0_IRQHandler(void)
{   DMA0_DriverIRQHandler();
}

WEAK_AV void GINT0_IRQHandler(void)
{   GINT0_DriverIRQHandler();
}

WEAK_AV void GINT1_IRQHandler(void)
{   GINT1_DriverIRQHandler();
}

WEAK_AV void PIN_INT0_IRQHandler(void)
{   PIN_INT0_DriverIRQHandler();
}

WEAK_AV void PIN_INT1_IRQHandler(void)
{   PIN_INT1_DriverIRQHandler();
}

WEAK_AV void PIN_INT2_IRQHandler(void)
{   PIN_INT2_DriverIRQHandler();
}

WEAK_AV void PIN_INT3_IRQHandler(void)
{   PIN_INT3_DriverIRQHandler();
}

WEAK_AV void UTICK0_IRQHandler(void)
{   UTICK0_DriverIRQHandler();
}

WEAK_AV void MRT0_IRQHandler(void)
{   MRT0_DriverIRQHandler();
}

WEAK_AV void CTIMER0_IRQHandler(void)
{   CTIMER0_DriverIRQHandler();
}

WEAK_AV void CTIMER1_IRQHandler(void)
{   CTIMER1_DriverIRQHandler();
}

WEAK_AV void SCT0_IRQHandler(void)
{   SCT0_DriverIRQHandler();
}

WEAK_AV void CTIMER3_IRQHandler(void)
{   CTIMER3_DriverIRQHandler();
}

WEAK_AV void FLEXCOMM0_IRQHandler(void)
{   FLEXCOMM0_DriverIRQHandler();
}

WEAK_AV void FLEXCOMM1_IRQHandler(void)
{   FLEXCOMM1_DriverIRQHandler();
}

WEAK_AV void FLEXCOMM2_IRQHandler(void)
{   FLEXCOMM2_DriverIRQHandler();
}

WEAK_AV void FLEXCOMM3_IRQHandler(void)
{   FLEXCOMM3_DriverIRQHandler();
}

WEAK_AV void FLEXCOMM4_IRQHandler(void)
{   FLEXCOMM4_DriverIRQHandler();
}

WEAK_AV void FLEXCOMM5_IRQHandler(void)
{   FLEXCOMM5_DriverIRQHandler();
}

WEAK_AV void FLEXCOMM6_IRQHandler(void)
{   FLEXCOMM6_DriverIRQHandler();
}

WEAK_AV void FLEXCOMM7_IRQHandler(void)
{   FLEXCOMM7_DriverIRQHandler();
}

WEAK_AV void ADC0_SEQA_IRQHandler(void)
{   ADC0_SEQA_DriverIRQHandler();
}

WEAK_AV void ADC0_SEQB_IRQHandler(void)
{   ADC0_SEQB_DriverIRQHandler();
}

WEAK_AV void ADC0_THCMP_IRQHandler(void)
{   ADC0_THCMP_DriverIRQHandler();
}

WEAK_AV void Reserved41_IRQHandler(void)
{   Reserved41_DriverIRQHandler();
}

WEAK_AV void Reserved42_IRQHandler(void)
{   Reserved42_DriverIRQHandler();
}

WEAK_AV void USB0_NEEDCLK_IRQHandler(void)
{   USB0_NEEDCLK_DriverIRQHandler();
}

WEAK_AV void USB0_IRQHandler(void)
{   USB0_DriverIRQHandler();
}

WEAK_AV void RTC_IRQHandler(void)
{   RTC_DriverIRQHandler();
}

//*****************************************************************************

#if defined (DEBUG)
#pragma GCC pop_options
#endif // (DEBUG)
