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
 *  MEC14xx GIRQ20 Disaggregated Vector Jump table
 *
 ***************************************************************/

    .extern girq20_b0
    .extern girq20_b1
    .extern girq20_b2
    .extern girq20_b3
    .extern girq20_b4
    .extern girq20_b5

#if GIRQ20_DISAGG != 0

/*
 * Disaggregated girq20_isr
 * Program address of this version of girq20_isr into JTVIC GIRQ20
 * Aggregator Control register with bit[0] = 1.
 */

/*
 * NOTE: All the additional labels surrounding every instruction are
 * there to force GCC OBJDUMP to disassemble microMIPS correctly.
 */

    .insn
#ifdef __XC32
    .section .girqs.girq20_isr, code
#else
    .section .girqs.girq20_isr,"x"
#endif
    .set  nomips16
    .set  micromips
    .set  noreorder
    .set  noat
    .ent girq20_isr
    .global girq20_isr
    .align 2

girq20_isr:
    J       girq20_b0
g20b0b:
    NOP

    .align 2
g20b1a:
    J       girq20_b1
g20b1b:
    NOP

    .align 2
g20b2a:
    J       girq20_b2
g20b2b:
    NOP

    .align 2
g20b3a:
    J       girq20_b3
g20b3b:
    NOP

    .align 2
g20b4a:
    J       girq20_b4
g20b4b:
    NOP

    .align 2
g20b5a:
    J       girq20_b5
g20b5b:
    NOP
g20end:
    .end girq20_isr

#endif

/******************************************************************/


