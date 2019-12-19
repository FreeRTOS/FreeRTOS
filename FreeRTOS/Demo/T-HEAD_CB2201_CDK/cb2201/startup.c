/*
 * Copyright (C) 2017 C-SKY Microsystems Co., Ltd. All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
extern void __start(void);

extern void trap(void);
extern void CKPendSVIsr(void);
extern void CKTimer1Isr(void);
extern void vectorirq_handler(void);

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
#define ALIAS(f) __attribute__ ((weak, alias (#f)))

//*****************************************************************************
#if defined (__cplusplus)
extern "C" {
#endif

//*****************************************************************************
//
// Forward declaration of the default handlers. These are aliased.
// When the application defines a handler (with the same name), this will
// automatically take precedence over these weak definitions
//
//*****************************************************************************
void ResetISR(void);
#if defined (__MULTICORE_MASTER)
void ResetISR2(void);
#endif

WEAK void PendSV_Handler(void);

//*****************************************************************************
//
// Forward declaration of the specific IRQ handlers. These are aliased
// to the IntDefaultHandler, which is a 'forever' loop. When the application
// defines a handler (with the same name), this will automatically take
// precedence over these weak definitions
//
//*****************************************************************************

//*****************************************************************************
//
// The entry point for the application.
// __main() is the entry point for Redlib based applications
// main() is the entry point for Newlib based applications
//
//*****************************************************************************



//*****************************************************************************
//
// The vector table.
// This relies on the linker script to place at correct location in memory.
//
//*****************************************************************************
extern void (* const g_pfnVectors[])(void);
__attribute__ ((used, section(".exp_table")))
void (* const g_pfnVectors[])(void) = {
    // Core Level
    __start,                // 0, Boot entry
    trap,                   // 1, exception default entry
    trap,                   // 2, exception default entry
    trap,                   // 3, exception default entry
    trap,                   // 4, exception default entry
    trap,                   // 5, exception default entry
    trap,                   // 6, exception default entry
    trap,                   // 7, exception default entry
    trap,                   // 8, exception default entry
    trap,                   // 9, exception default entry
    trap,                   // 10, exception default entry
    trap,                   // 11, exception default entry
    trap,                   // 12, exception default entry
    trap,                   // 13, exception default entry
    trap,                   // 14, exception default entry
    trap,                   // 15, exception default entry
    CKPendSVIsr,            // 16, exception default entry
    trap,                   // 17, exception default entry
    trap,                   // 18, exception default entry
    trap,                   // 19, exception default entry
    trap,                   // 20, exception default entry
    trap,                   // 21, exception default entry
    trap,                   // 22, exception default entry
    trap,                   // 23, exception default entry
    trap,                   // 24, exception default entry
    trap,                   // 25, exception default entry
    trap,                   // 26, exception default entry
    trap,                   // 27, exception default entry
    trap,                   // 28, exception default entry
    trap,                   // 29, exception default entry
    trap,                   // 30, exception default entry
    trap,                   // 31, exception default entry

    // External Interrupts
    vectorirq_handler,      //
    CKTimer1Isr,            //
    vectorirq_handler,      //
    vectorirq_handler,      //
    vectorirq_handler,      //
    vectorirq_handler,      //
    vectorirq_handler,      //
    vectorirq_handler,      //
    vectorirq_handler,      //
    vectorirq_handler,      //
    vectorirq_handler,      //
    vectorirq_handler,      //
    vectorirq_handler,      //
    vectorirq_handler,      //
    vectorirq_handler,      //
    vectorirq_handler,      //
    vectorirq_handler,      //
    vectorirq_handler,      //
    vectorirq_handler,      //
    vectorirq_handler,      //
    vectorirq_handler,      //
    vectorirq_handler,      //
    vectorirq_handler,      //
    vectorirq_handler,      //
    vectorirq_handler,      //
    vectorirq_handler,      //
    vectorirq_handler,      //
    vectorirq_handler,      //
    vectorirq_handler,      //
    vectorirq_handler,      //
}; /* End of g_pfnVectors */

