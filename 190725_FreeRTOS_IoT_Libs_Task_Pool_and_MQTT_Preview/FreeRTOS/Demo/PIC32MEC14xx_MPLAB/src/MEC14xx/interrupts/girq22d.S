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
 *  MEC14xx GIRQ22 Disaggregated Vector Jump table
 *
 ***************************************************************/

    .extern girq22_b0
    .extern girq22_b1
    .extern girq22_b2
    .extern girq22_b3
    .extern girq22_b4
    .extern girq22_b5
    .extern girq22_b6
    .extern girq22_b7
    .extern girq22_b8
    .extern girq22_b9

#if GIRQ22_DISAGG != 0

/*
 * Disaggregated girq22_isr
 * Program address of this version of girq22_isr into JTVIC GIRQ22
 * Aggregator Control register with bit[0] = 1.
 */

/*
 * NOTE: All the additional labels surrounding every instruction are
 * there to force GCC OBJDUMP to disassemble microMIPS correctly.
 */

    .insn
#ifdef __XC32
    .section .girqs.girq22_isr, code
#else
    .section .girqs.girq22_isr,"x"
#endif
    .set  nomips16
    .set  micromips
    .set  noreorder
    .set  noat
    .ent girq22_isr
    .global girq22_isr
    .align 2

girq22_isr:
    J       girq22_b0
g22b0b:
    NOP

    .align 2
g22b1a:
    J       girq22_b1
g22b1b:
    NOP

    .align 2
g22b2a:
    J       girq22_b2
g22b2b:
    NOP

    .align 2
g22b3a:
    J       girq22_b3
g22b3b:
    NOP

    .align 2
g22b4a:
    J       girq22_b4
g22b4b:
    NOP

    .align 2
g22b5a:
    J       girq22_b5
g22b5b:
    NOP

    .align 2
g22b6a:
    J       girq22_b6
g22b6b:
    NOP

    .align 2
g22b7a:
    J       girq22_b7
g22b7b:
    NOP

    .align 2
g22b8a:
    J       girq22_b8
g22b8b:
    NOP

    .align 2
g22b9a:
    J       girq22_b9
g22b9b:
    NOP
g22end:
    .end girq22_isr

#endif

/******************************************************************/


