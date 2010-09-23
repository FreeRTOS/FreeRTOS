/*****************************************************************************
 * Copyright (c) 2001, 2002 Rowley Associates Limited.                       *
 *                                                                           *
 * This file may be distributed under the terms of the License Agreement     *
 * provided with this software.                                              *
 *                                                                           *
 * THIS FILE IS PROVIDED AS IS WITH NO WARRANTY OF ANY KIND, INCLUDING THE   *
 * WARRANTY OF DESIGN, MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE. *
 *****************************************************************************/

/*****************************************************************************
 *                           Preprocessor Definitions
 *                           ------------------------
 *
 * VECTORED_IRQ_INTERRUPTS
 *
 *   Enable vectored IRQ interrupts. If defined, the PC register will be loaded
 *   with the contents of the VICVectAddr register on an IRQ exception.
 *
 * USE_PLL
 *
 *   If defined, connect PLL as processor clock source. If undefined, the 
 *   oscillator clock will be used.
 *
 * PLLCFG_VAL
 *
 *   Override the default PLL configuration (multiplier = 5, divider = 2)
 *   by defining PLLCFG_VAL.
 *
 * USE_MAM
 *
 *   If defined then the memory accelerator module (MAM) will be enabled.
 *
 * MAMCR_VAL & MAMTIM_VAL
 * 
 *   Override the default MAM configuration (fully enabled, 3 fetch cycles)
 *   by defining MAMCR_VAL and MAMTIM_VAL.
 *
 * VPBDIV_VAL
 *
 *   If defined then this value will be used to configure the VPB divider.
 *
 * SRAM_EXCEPTIONS
 *
 *   If defined, enable copying and re-mapping of interrupt vectors from User 
 *   FLASH to SRAM. If undefined, interrupt vectors will be mapped in User 
 *   FLASH.
 *
 *****************************************************************************/

#ifndef PLLCFG_VAL
#define PLLCFG_VAL 0x24 
#endif

#ifndef MAMCR_VAL
#define MAMCR_VAL 2
#endif

#ifndef MAMTIM_VAL
#define MAMTIM_VAL 3
#endif

#define MAMCR_OFFS   0x000
#define MAMTIM_OFFS  0x004

#define PLLCON_OFFS  0x080
#define PLLCFG_OFFS  0x084
#define PLLSTAT_OFFS 0x088
#define PLLFEED_OFFS 0x08C

#define VPBDIV_OFFS  0x100

  .section .vectors, "ax"
  .code 32
  .align 0

/*****************************************************************************
 * Exception Vectors                                                         *
 *****************************************************************************/
_vectors:
  ldr pc, [pc, #reset_handler_address - . - 8]  /* reset */
  ldr pc, [pc, #undef_handler_address - . - 8]  /* undefined instruction */
  ldr pc, [pc, #swi_handler_address - . - 8]    /* swi handler */
  ldr pc, [pc, #pabort_handler_address - . - 8] /* abort prefetch */
  ldr pc, [pc, #dabort_handler_address - . - 8] /* abort data */
#ifdef VECTORED_IRQ_INTERRUPTS
  .word 0xB9205F84                              /* boot loader checksum */
  ldr pc, [pc, #-0xFF0]                         /* irq handler */
#else
  .word 0xB8A06F60                              /* boot loader checksum */
  ldr pc, [pc, #irq_handler_address - . - 8]    /* irq handler */
#endif
  ldr pc, [pc, #fiq_handler_address - . - 8]    /* fiq handler */

reset_handler_address:
  .word reset_handler
undef_handler_address:
  .word undef_handler
swi_handler_address:
  .word swi_handler
pabort_handler_address:
  .word pabort_handler
dabort_handler_address:
  .word dabort_handler
irq_handler_address:
  .word irq_handler
fiq_handler_address:
  .word fiq_handler

  .section .init, "ax"
  .code 32
  .align 0

/******************************************************************************
 *                                                                            *
 * Default exception handlers                                                 *
 *                                                                            *
 ******************************************************************************/

reset_handler:
#if defined(USE_PLL) || defined(USE_MAM) || defined(VPBDIV_VAL)
  ldr r0, =0xE01FC000
#endif
#if defined(USE_PLL)
  /* Configure PLL Multiplier/Divider */
  ldr r1, =PLLCFG_VAL
  str r1, [r0, #PLLCFG_OFFS]
  /* Enable PLL */
  mov r1, #0x1
  str r1, [r0, #PLLCON_OFFS]
  mov r1, #0xAA
  str r1, [r0, #PLLFEED_OFFS]
  mov r1, #0x55
  str r1, [r0, #PLLFEED_OFFS]
  /* Wait for PLL to lock */
pll_lock_loop:
  ldr r1, [r0, #PLLSTAT_OFFS]
  tst r1, #0x400
  beq pll_lock_loop
  /* PLL Locked, connect PLL as clock source */
  mov r1, #0x3
  str r1, [r0, #PLLCON_OFFS]
  mov r1, #0xAA
  str r1, [r0, #PLLFEED_OFFS]
  mov r1, #0x55
  str r1, [r0, #PLLFEED_OFFS]
#endif

#if defined(USE_MAM)
  mov r1, #0
  str r1, [r0, #MAMCR_OFFS]
  ldr r1, =MAMTIM_VAL
  str r1, [r0, #MAMTIM_OFFS]
  ldr r1, =MAMCR_VAL
  str r1, [r0, #MAMCR_OFFS]
#endif

#if defined(VPBDIV_VAL)
  ldr r1, =VPBDIV_VAL
  str r1, [r0, #VPBDIV_OFFS]
#endif

#if defined(SRAM_EXCEPTIONS)
  /* Copy exception vectors into SRAM */
  mov r8, #0x40000000
  ldr r9, =_vectors
  ldmia r9!, {r0-r7}
  stmia r8!, {r0-r7}
  ldmia r9!, {r0-r6}
  stmia r8!, {r0-r6}

  /* Re-map interrupt vectors from SRAM */
  ldr r0, MEMMAP
  mov r1, #2 /* User RAM Mode. Interrupt vectors are re-mapped from SRAM */
  str r1, [r0]
#endif /* SRAM_EXCEPTIONS */
  
  b _start

#ifdef SRAM_EXCEPTIONS
MEMMAP:
  .word 0xE01FC040
#endif

/******************************************************************************
 *                                                                            *
 * Default exception handlers                                                 *
 * These are declared weak symbols so they can be redefined in user code.     * 
 *                                                                            *
 ******************************************************************************/

undef_handler:
  b undef_handler
  
swi_handler:
  b swi_handler
  
pabort_handler:
  b pabort_handler
  
dabort_handler:
  b dabort_handler
  
irq_handler:
  b irq_handler
  
fiq_handler:
  b fiq_handler

  .weak undef_handler, swi_handler, pabort_handler, dabort_handler, irq_handler, fiq_handler
                                                    

                  
