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
 *  MEC14xx GIRQ10 Disaggregated Vector Jump table
 *
 ***************************************************************/

    .extern girq10_b0
    .extern girq10_b1
    .extern girq10_b2
    .extern girq10_b3
    .extern girq10_b4
    .extern girq10_b5
    .extern girq10_b6
    .extern girq10_b7
    .extern girq10_b8
    .extern girq10_b9
    .extern girq10_b10
    .extern girq10_b11
    .extern girq10_b12
    .extern girq10_b13
    .extern girq10_b14
    .extern girq10_b15
    .extern girq10_b16
    .extern girq10_b17
    .extern girq10_b18
    .extern girq10_b19
    .extern girq10_b20
    .extern girq10_b21
    .extern girq10_b22
    .extern girq10_b23

#if GIRQ10_DISAGG != 0

/*
 * Disaggregated girq10_isr
 * Program address of this version of girq23_isr into JTVIC GIRQ09
 * Aggregator Control register with bit[0] = 1.
 */
    .insn
#ifdef __XC32
    .section .girqs.girq10_isr, code
#else
    .section .girqs.girq10_isr,"x"
#endif
    .set  nomips16
    .set  micromips
    .set  noreorder
    .set  noat
    .ent girq10_isr
    .global girq10_isr
    .align 2

girq10_isr:
    J       girq10_b0
    NOP

    .align 2
    J       girq10_b1
    NOP

    .align 2
    J       girq10_b2
    NOP

    .align 2
    J       girq10_b3
    NOP

    .align 2
    J       girq10_b4
    NOP

    .align 2
    J       girq10_b5
    NOP

    .align 2
    J       girq10_b6
    NOP

    .align 2
    J       girq10_b7
    NOP

    .align 2
    J       girq10_b8
    NOP

    .align 2
    J       girq10_b9
    NOP

    .align 2
    J       girq10_b10
    NOP

    .align 2
    J       girq10_b11
    NOP

    .align 2
    J       girq10_b12
    NOP

    .align 2
    J       girq10_b13
    NOP

    .align 2
    J       girq10_b14
    NOP

    .align 2
    J       girq10_b15
    NOP

    .align 2
    J       girq10_b16
    NOP

    .align 2
    J       girq10_b17
    NOP

    .align 2
    J       girq10_b18
    NOP

    .align 2
    J       girq10_b19
    NOP

    .align 2
    J       girq10_b20
    NOP

    .align 2
    J       girq10_b21
    NOP

    .align 2
    J       girq10_b22
    NOP

    .align 2
    J       girq10_b23
    NOP

    .end girq10_isr

#endif

/******************************************************************/


