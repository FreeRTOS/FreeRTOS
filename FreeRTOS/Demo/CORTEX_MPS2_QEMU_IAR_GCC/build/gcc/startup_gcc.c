/*
 * FreeRTOS V202212.01
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

#include <stdint.h>
#include <stdio.h>

/* UART peripheral register addresses and bits. */
#define UART0_ADDR             ( ( UART_t * ) ( 0x40004000 ) )
#define UART_DR( baseaddr )    ( *( uint32_t * ) ( baseaddr ) )
#define UART_STATE( baseaddr ) ( *( uint32_t * ) ( baseaddr + 4 ) )
#define UART_STATE_TXFULL      ( 1 << 0 )

typedef struct UART_t
{
    volatile uint32_t DATA;
    volatile uint32_t STATE;
    volatile uint32_t CTRL;
    volatile uint32_t INTSTATUS;
    volatile uint32_t BAUDDIV;
} UART_t;


/* FreeRTOS interrupt handlers. */
extern void vPortSVCHandler( void );
extern void xPortPendSVHandler( void );
extern void xPortSysTickHandler( void );
extern void TIMER0_Handler( void );
extern void TIMER1_Handler( void );

/* Exception handlers. */
static void HardFault_Handler( void ) __attribute__( ( naked ) );
static void Default_Handler( void ) __attribute__( ( naked ) );
void Reset_Handler( void );

extern int main( void );
extern uint32_t _estack;

/* Vector table. */
const uint32_t* isr_vector[] __attribute__((section(".isr_vector"))) =
{
    ( uint32_t * ) &_estack,
    ( uint32_t * ) &Reset_Handler,     // Reset                -15
    ( uint32_t * ) &Default_Handler,   // NMI_Handler          -14
    ( uint32_t * ) &HardFault_Handler, // HardFault_Handler    -13
    ( uint32_t * ) &Default_Handler,   // MemManage_Handler    -12
    ( uint32_t * ) &Default_Handler,   // BusFault_Handler     -11
    ( uint32_t * ) &Default_Handler,   // UsageFault_Handler   -10
    0, // reserved
    0, // reserved
    0, // reserved
    0, // reserved   -6
    ( uint32_t * ) &vPortSVCHandler,    // SVC_Handler              -5
    ( uint32_t * ) &Default_Handler,    // DebugMon_Handler         -4
    0, // reserved
    ( uint32_t * ) &xPortPendSVHandler, // PendSV handler    -2
    ( uint32_t * ) &xPortSysTickHandler,// SysTick_Handler   -1
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    ( uint32_t * ) TIMER0_Handler,     // Timer 0
	( uint32_t * ) TIMER1_Handler,     // Timer 1
    0,
    0,
    0,
    0, // Ethernet   13
};

void Reset_Handler( void )
{
    main();
}

/* Variables used to store the value of registers at the time a hardfault
 * occurs.  These are volatile to try and prevent the compiler/linker optimising
 * them away as the variables never actually get used. */
volatile uint32_t r0;
volatile uint32_t r1;
volatile uint32_t r2;
volatile uint32_t r3;
volatile uint32_t r12;
volatile uint32_t lr; /* Link register. */
volatile uint32_t pc; /* Program counter. */
volatile uint32_t psr;/* Program status register. */

/* Called from the hardfault handler to provide information on the processor
 * state at the time of the fault.
 */
void prvGetRegistersFromStack( uint32_t *pulFaultStackAddress )
{
    r0 = pulFaultStackAddress[ 0 ];
    r1 = pulFaultStackAddress[ 1 ];
    r2 = pulFaultStackAddress[ 2 ];
    r3 = pulFaultStackAddress[ 3 ];

    r12 = pulFaultStackAddress[ 4 ];
    lr = pulFaultStackAddress[ 5 ];
    pc = pulFaultStackAddress[ 6 ];
    psr = pulFaultStackAddress[ 7 ];

    printf( "Calling prvGetRegistersFromStack() from fault handler" );
    fflush( stdout );

    /* When the following line is hit, the variables contain the register values. */
    for( ;; );
}


void Default_Handler( void )
{
    __asm volatile
    (
        ".align 8                                \n"
        " ldr r3, NVIC_INT_CTRL_CONST            \n" /* Load the address of the interrupt control register into r3. */
        " ldr r2, [r3, #0]                       \n" /* Load the value of the interrupt control register into r2. */
        " uxtb r2, r2                            \n" /* The interrupt number is in the least significant byte - clear all other bits. */
        "Infinite_Loop:                          \n" /* Sit in an infinite loop - the number of the executing interrupt is held in r2. */
        " b  Infinite_Loop                       \n"
        ".align 4                                \n"
        "NVIC_INT_CTRL_CONST: .word 0xe000ed04   \n"
    );
}

void HardFault_Handler( void )
{
    __asm volatile
    (
        ".align 8                                                   \n"
        " tst lr, #4                                                \n"
        " ite eq                                                    \n"
        " mrseq r0, msp                                             \n"
        " mrsne r0, psp                                             \n"
        " ldr r1, [r0, #24]                                         \n"
        " ldr r2, handler2_address_const                            \n"
        " bx r2                                                     \n"
        " handler2_address_const: .word prvGetRegistersFromStack    \n"
    );
}


