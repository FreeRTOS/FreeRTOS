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
 *  MEC14xx GIRQ13 Disaggregated Vector Jump table
 *
 ***************************************************************/

    .extern girq13_b0
    .extern girq13_b1
    .extern girq13_b2
    .extern girq13_b3
    .extern girq13_b4
    .extern girq13_b5
    .extern girq13_b6

#if GIRQ13_DISAGG != 0

/*
 * Disaggregated girq13_isr
 * Program address of this version of girq23v into JTVIC GIRQ13
 * Aggregator Control register with bit[0] = 1.
 */
    .insn
#ifdef __XC32
    .section .girqs.girq13_isr, code
#else
    .section .girqs.girq13_isr,"x"
#endif
    .set  nomips16
    .set  micromips
    .set  noreorder
    .set  noat
    .ent girq13_isr
    .global girq13_isr
    .align 2

girq13_isr:
    J       girq13_b0
    NOP

    .align 2
    J       girq13_b1
    NOP

    .align 2
    J       girq13_b2
    NOP

    .align 2
    J       girq13_b3
    NOP

    .align 2
    J       girq13_b4
    NOP

    .align 2
    J       girq13_b5
    NOP

    .align 2
    J       girq13_b6
    NOP

    .end girq13_isr

#endif

/******************************************************************/


