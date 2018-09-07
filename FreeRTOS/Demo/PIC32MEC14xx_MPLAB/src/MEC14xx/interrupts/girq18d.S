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
 *  MEC14xx GIRQ18 Disaggregated Vector Jump table
 *
 ***************************************************************/

.extern girq18_b0

#if GIRQ18_DISAGG != 0

/*
 * Disaggregated girq18_isr
 * Program address of this version of girq18_isr into JTVIC GIRQ18
 * Aggregator Control register with bit[0] = 1.
 */

/*
 * NOTE: All the additional labels surrounding every instruction are
 * there to force GCC OBJDUMP to disassemble microMIPS correctly.
 */
    
/*
 * NOTE: GIRQ18 has only one source, no need for indirect jumps.
 */
    .insn
#ifdef __XC32
    .section .girqs.girq18_isr, code
#else
    .section .girqs.girq18_isr,"x"
#endif
    .set  nomips16
    .set  micromips
    .set  noreorder
    .set  noat
    .ent girq18_isr
    .global girq18_isr
    .align 2

girq18_isr:
    J        girq18_b0
g18b0b:
    NOP
g18end:
    .end girq18_isr

#endif

/******************************************************************/


