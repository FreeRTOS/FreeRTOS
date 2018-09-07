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
 *  MEC14xx GIRQ26 Disaggregated Vector Jump table
 *
 ***************************************************************/

    .extern girq26_b0
    .extern girq26_b1
    .extern girq26_b2
    .extern girq26_b3
    .extern girq26_b4
    .extern girq26_b5
    .extern girq26_b6
    .extern girq26_b7
    .extern girq26_b8
    .extern girq26_b9
    .extern girq26_b10
    .extern girq26_b11

#if GIRQ26_DISAGG != 0

/*
 * Disaggregated girq26_isr
 * Program address of this version of girq26_isr into JTVIC GIRQ26
 * Aggregator Control register with bit[0] = 1.
 */

/*
 * NOTE: All the additional labels surrounding every instruction are
 * there to force GCC OBJDUMP to disassemble microMIPS correctly.
 */

    .insn
#ifdef __XC32
    .section .girqs.girq26_isr, code
#else
    .section .girqs.girq26_isr,"x"
#endif
    .set  nomips16
    .set  micromips
    .set  noreorder
    .set  noat
    .ent girq26_isr
    .global girq26_isr
    .align 2

girq26_isr:
    J       girq26_b0
g26b0b:
    NOP

    .align 2
g26b1a:
    J       girq26_b1
g26b1b:
    NOP

    .align 2
g26b2a:
    J       girq26_b2
g26b2b:
    NOP

    .align 2
g26b3a:
    J       girq26_b3
g26b3b:
    NOP

    .align 2
g26b4a:
    J       girq26_b4
g26b4b:
    NOP

    .align 2
g26b5a:
    J       girq26_b5
g26b5b:
    NOP

    .align 2
g26b6a:
    J       girq26_b6
g26b6b:
    NOP

    .align 2
g26b7a:
    J       girq26_b7
g26b7b:
    NOP

    .align 2
g26b8a:
    J       girq26_b8
g26b8b:
    NOP

    .align 2
g26b9a:
    J       girq26_b9
g26b9b:
    NOP

    .align 2
g26b10a:
    J       girq26_b10
g26b10b:
    NOP

    .align 2
g26b11a:
    J       girq26_b11
g26b11b:
    NOP
g26end:
    .end girq26_isr

#endif

/******************************************************************/


