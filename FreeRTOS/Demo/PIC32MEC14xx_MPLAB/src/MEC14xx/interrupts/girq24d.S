/*
    Copyright (C) 2014 Microchip Inc.
    All rights reserved

    1 tab == 4 spaces!
*/

#ifdef __XC32
#include <xc.h>
#include <sys/asm.h>
#else
#include "Regs.S"
#endif

#include "MEC14xx/mec14xx_girqm.h"

/******************************************************************/

/***************************************************************
 *  MEC14xx GIRQ24 Disaggregated Vector Jump table
 *
 ***************************************************************/

    .extern girq24_b0
    .extern girq24_b1
    .extern girq24_b2

#if GIRQ24_DISAGG != 0

/* 
 * FreeRTOS Handler for MIPS M14K Software Interrupt 0 
 * implemented in the porting layer.
 */
    .extern vPortYieldISR

/*
 * Disaggregated girq24_isr
 * Program address of this version of girq24_isr into JTVIC GIRQ24
 * Aggregator Control register with bit[0] = 1.
 */

/*
 * NOTE: All the additional labels surrounding every instruction are
 * there to force GCC OBJDUMP to disassemble microMIPS correctly.
 */

    .insn
#ifdef __XC32
    .section .girqs.girq24_isr, code
#else
    .section .girqs.girq24_isr,"x"
#endif
    .set  nomips16
    .set  micromips
    .set  noreorder
    .set  noat
    .ent girq24_isr
    .global girq24_isr
    .align 2

girq24_isr:
    J       girq24_b0
g24b0b:
    NOP

    .align 2
g24b1a:
    J       vPortYieldISR   /* girq24_b1 */
g24b1b:
    NOP

    .align 2
g24b2a:
    J       girq24_b2
g24b2b:
    NOP
g24end:
    .end girq24_isr

#endif

/******************************************************************/


