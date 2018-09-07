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
 *  MEC14xx GIRQ19 Disaggregated Vector Jump table
 *
 ***************************************************************/

    .extern girq19_b0
    .extern girq19_b1
    .extern girq19_b2
    .extern girq19_b3
    .extern girq19_b4
    .extern girq19_b5
    .extern girq19_b6
    .extern girq19_b7
    .extern girq19_b8

#if GIRQ19_DISAGG != 0

/*
 * Disaggregated girq19_isr
 * Program address of this version of girq19_isr into JTVIC GIRQ19
 * Aggregator Control register with bit[0] = 1.
 */

/*
 * NOTE: All the additional labels surrounding every instruction are
 * there to force GCC OBJDUMP to disassemble microMIPS correctly.
 */

    .insn
#ifdef __XC32
    .section .girqs.girq19_isr, code
#else
    .section .girqs.girq19_isr,"x"
#endif
    .set  nomips16
    .set  micromips
    .set  noreorder
    .set  noat
    .ent girq19_isr
    .global girq19_isr
    .align 2

girq19_isr:
    J       girq19_b0
g19b0b:
    NOP

    .align 2
g19b1a:
    J       girq19_b1
g19b1b:
    NOP

    .align 2
g19b2a:
    J       girq19_b2
g19b2b:
    NOP

    .align 2
g19b3a:
    J       girq19_b3
g19b3b:
    NOP

    .align 2
g19b4a:
    J       girq19_b4
g19b4b:
    NOP

    .align 2
g19b5a:
    J       girq19_b5
g19b5b:
    NOP

    .align 2
g19b6a:
    J       girq19_b6
g19b6b:
    NOP

    .align 2
g19b7a:
    J       girq19_b7
g19b7b:
    NOP

    .align 2
g19b8a:
    J       girq19_b8
g19b8b:
    NOP
g19end:
    .end girq19_isr

#endif

/******************************************************************/


