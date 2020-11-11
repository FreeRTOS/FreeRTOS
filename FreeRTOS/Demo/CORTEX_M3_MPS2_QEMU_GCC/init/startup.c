/*
 * FreeRTOS V202011.00
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
 * https://www.gihub.com/FreeRTOS
 *
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern uint32_t _estack, _sidata, _sdata, _edata, _sbss, _ebss;

__attribute__((naked)) void Reset_Handler(void) {
    // set stack pointer
    __asm volatile ("ldr r0, =_estack");
    __asm volatile ("mov sp, r0");
    // copy .data section from flash to RAM
    for (uint32_t *src = &_sidata, *dest = &_sdata; dest < &_edata;) {
        *dest++ = *src++;
    }
    // zero out .bss section
    for (uint32_t *dest = &_sbss; dest < &_ebss;) {
        *dest++ = 0;
    }
    // jump to board initialisation
    void _start(void);
    _start();
}

void Default_Handler(void) {
    for (;;) {
    }
}
extern void vPortSVCHandler( void );
extern void xPortPendSVHandler( void );
extern void xPortSysTickHandler( void );

const uint32_t isr_vector[] __attribute__((section(".isr_vector"))) = {
    (uint32_t)&_estack,
    (uint32_t)&Reset_Handler,
    (uint32_t)&Default_Handler, // NMI_Handler
    (uint32_t)&Default_Handler, // HardFault_Handler
    (uint32_t)&Default_Handler, // MemManage_Handler
    (uint32_t)&Default_Handler, // BusFault_Handler
    (uint32_t)&Default_Handler, // UsageFault_Handler
    0,
    0,
    0,
    0,
    (uint32_t)&vPortSVCHandler, // SVC_Handler
    (uint32_t)&Default_Handler, // DebugMon_Handler
    0,
    (uint32_t)&xPortPendSVHandler, // PendSV handler
    (uint32_t)&xPortSysTickHandler, // SysTick_Handler
};

extern int main();
extern void uart_init();
void _start(void) {
    uart_init();
    main(0, 0);
    exit(0);
}

__attribute__((naked)) void exit(int status) {
    // Force qemu to exit using ARM Semihosting
    __asm volatile (
        "mov r1, r0\n"
        "cmp r1, #0\n"
        "bne .notclean\n"
        "ldr r1, =0x20026\n" // ADP_Stopped_ApplicationExit, a clean exit
        ".notclean:\n"
        "movs r0, #0x18\n" // SYS_EXIT
        "bkpt 0xab\n"
        "end: b end\n"
        );
}

