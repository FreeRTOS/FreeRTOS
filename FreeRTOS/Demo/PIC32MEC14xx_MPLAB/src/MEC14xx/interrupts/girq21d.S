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
 *  MEC14xx GIRQ21 Disaggregated Vector Jump table
 *
 ***************************************************************/

    .extern girq21_b0

#if GIRQ21_DISAGG != 0

/*
 * Disaggregated girq21_isr
 * Program address of this version of girq21_isr into JTVIC GIRQ21
 * Aggregator Control register with bit[0] = 1.
 * NOTE: GIRQ21 has no sources, it is a wake only and actually 
 * does not send an interrupt message to the M14K.
 * 
 */

/*
 * NOTE: All the additional labels surrounding every instruction are
 * there to force GCC OBJDUMP to disassemble microMIPS correctly.
 */

    .insn
#ifdef __XC32
    .section .girqs.girq21_isr, code
#else
    .section .girqs.girq21_isr,"x"
#endif
    .set  nomips16
    .set  micromips
    .set  noreorder
    .set  noat
    .ent girq21_isr
    .global girq21_isr
    .align 2
girq21_isr:

    J       girq21_b0
g21b0b:
    NOP
g21end:
    .end girq21_isr


#endif

/******************************************************************/


