/*****************************************************************************
  Exception handlers and startup code for ATMEL AT91SAM7.

  Copyright (c) 2004 Rowley Associates Limited.

  This file may be distributed under the terms of the License Agreement
  provided with this software. 
 
  THIS FILE IS PROVIDED AS IS WITH NO WARRANTY OF ANY KIND, INCLUDING THE
  WARRANTY OF DESIGN, MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE.
 *****************************************************************************/

#define REG_BASE 0xFFFFF000
#define CKGR_MOR_OFFSET 0xC20
#define CKGR_PLLR_OFFSET 0xC2C
#define PMC_MCKR_OFFSET 0xC30
#define PMC_SR_OFFSET 0xC68
#define WDT_MR_OFFSET 0xD44
#define MC_RCR_OFFSET 0xF00
#define MC_FMR_OFFSET 0xF60

#define CKGR_MOR_MOSCEN (1 << 0)
#define CKGR_MOR_OSCBYPASS (1 << 1)
#define CKGR_MOR_OSCOUNT_BIT_OFFSET (8)

#define CKGR_PLLR_DIV_BIT_OFFSET (0)
#define CKGR_PLLR_PLLCOUNT_BIT_OFFSET (8)
#define CKGR_PLLR_OUT_BIT_OFFSET (14)
#define CKGR_PLLR_MUL_BIT_OFFSET (16)
#define CKGR_PLLR_USBDIV_BIT_OFFSET (28)

#define PMC_MCKR_CSS_MAIN_CLOCK (0x1)
#define PMC_MCKR_CSS_PLL_CLOCK (0x3)
#define PMC_MCKR_PRES_CLK (0)
#define PMC_MCKR_PRES_CLK_2 (1 << 2)
#define PMC_MCKR_PRES_CLK_4 (2 << 2)
#define PMC_MCKR_PRES_CLK_8 (3 << 2)
#define PMC_MCKR_PRES_CLK_16 (4 << 2)
#define PMC_MCKR_PRES_CLK_32 (5 << 2)
#define PMC_MCKR_PRES_CLK_64 (6 << 2)

#define PMC_SR_MOSCS (1 << 0)
#define PMC_SR_LOCK (1 << 2)
#define PMC_SR_MCKRDY (1 << 3)
#define PMC_SR_PCKRDY0 (1 << 8)
#define PMC_SR_PCKRDY1 (1 << 9)
#define PMC_SR_PCKRDY2 (1 << 10)

#define MC_RCR_RCB (1 << 0)

#define MC_FMR_FWS_0FWS (0)
#define MC_FMR_FWS_1FWS (1 << 8)
#define MC_FMR_FWS_2FWS (2 << 8)
#define MC_FMR_FWS_3FWS (3 << 8)
#define MC_FMR_FMCN_BIT_OFFSET 16

#define WDT_MR_WDDIS (1 << 15)

  .section .vectors, "ax"
  .code 32
  .align 0
  
/*****************************************************************************
  Exception Vectors
 *****************************************************************************/
_vectors:
  ldr pc, [pc, #reset_handler_address - . - 8]  /* reset */
  ldr pc, [pc, #undef_handler_address - . - 8]  /* undefined instruction */
  ldr pc, [pc, #swi_handler_address - . - 8]    /* swi handler */
  ldr pc, [pc, #pabort_handler_address - . - 8] /* abort prefetch */
  ldr pc, [pc, #dabort_handler_address - . - 8] /* abort data */
  nop
  ldr pc, [PC, #-0xF20]    /* irq */
  ldr pc, [pc, #fiq_handler_address - . - 8]    /* fiq */

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
  Reset handler
 ******************************************************************************/
reset_handler:


  ldr r10, =REG_BASE

  /* Set up FLASH wait state */
  ldr r0, =(50 << MC_FMR_FMCN_BIT_OFFSET) | MC_FMR_FWS_1FWS
  str r0, [r10, #MC_FMR_OFFSET]

  /* Disable Watchdog */
  ldr r0, =WDT_MR_WDDIS
  str r0, [r10, #WDT_MR_OFFSET]

  /* Enable the main oscillator */
  ldr r0, =(6 << CKGR_MOR_OSCOUNT_BIT_OFFSET) | CKGR_MOR_MOSCEN
  str r0, [r10, #CKGR_MOR_OFFSET]
  
1:/* Wait for main oscillator to stabilize */
  ldr r0, [r10, #PMC_SR_OFFSET]
  tst r0, #PMC_SR_MOSCS
  beq 1b

  /* Set up the PLL */
  ldr r0, =(5 << CKGR_PLLR_DIV_BIT_OFFSET) | (28 << CKGR_PLLR_PLLCOUNT_BIT_OFFSET) | (25 << CKGR_PLLR_MUL_BIT_OFFSET)
  str r0, [r10, #CKGR_PLLR_OFFSET]
  
1:/* Wait for PLL to lock */
  ldr r0, [r10, #PMC_SR_OFFSET]
  tst r0, #PMC_SR_LOCK
  beq 1b

  /* Select PLL as clock source */
  ldr r0, =(PMC_MCKR_CSS_PLL_CLOCK | PMC_MCKR_PRES_CLK_2)
  str r0, [r10, #PMC_MCKR_OFFSET]
  
#ifdef __FLASH_BUILD
  /* Copy exception vectors into Internal SRAM */
  mov r8, #0x00200000
  ldr r9, =_vectors
  ldmia r9!, {r0-r7}
  stmia r8!, {r0-r7}
  ldmia r9!, {r0-r6}
  stmia r8!, {r0-r6}

  /* Remap Internal SRAM to 0x00000000 */
  ldr r0, =MC_RCR_RCB
  strb r0, [r10, #MC_RCR_OFFSET]
#endif


  /* Jump to the default C runtime startup code. */
  b _start

/******************************************************************************
  Default exception handlers
  (These are declared weak symbols so they can be redefined in user code)
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
