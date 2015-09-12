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
 *  MEC14xx GIRQ15 Disaggregated Vector Jump table
 *
 ***************************************************************/
    .extern girq15_b0
    .extern girq15_b1
    .extern girq15_b2
    .extern girq15_b3
    .extern girq15_b4
    .extern girq15_b5
    .extern girq15_b6
    .extern girq15_b7
    .extern girq15_b8
    .extern girq15_b9
    .extern girq15_b10
    .extern girq15_b11
    .extern girq15_b12
    .extern girq15_b13
    .extern girq15_b14
    .extern girq15_b15
    .extern girq15_b16
    .extern girq15_b17
    .extern girq15_b18

#if GIRQ15_DISAGG != 0

/*
 * Disaggregated girq15_isr
 * Program address of this version of girq15_isr into JTVIC GIRQ15
 * Aggregator Control register with bit[0] = 1.
 */
    .insn
#ifdef __XC32
    .section .girqs.girq15_isr, code
#else
    .section .girqs.girq15_isr,"x"
#endif
    .set  nomips16
    .set  micromips
    .set  noreorder
    .set  noat
    .ent girq15_isr
    .global girq15_isr
    .align 2

girq15_isr:
    J       girq15_b0
    NOP

    .align 2
    J       girq15_b1
    NOP

    .align 2
    J       girq15_b2
    NOP

    .align 2
    J       girq15_b3
    NOP

    .align 2
    J       girq15_b4
    NOP

    .align 2
    J       girq15_b5
    NOP

    .align 2
    J       girq15_b6
    NOP

    .align 2
    J       girq15_b7
    NOP

    .align 2
    J       girq15_b8
    NOP

    .align 2
    J       girq15_b9
    NOP

    .align 2
    J       girq15_b10
    NOP

    .align 2
    J       girq15_b11
    NOP

    .align 2
    J       girq15_b12
    NOP

    .align 2
    J       girq15_b13
    NOP

    .align 2
    J       girq15_b14
    NOP

    .align 2
    J       girq15_b15
    NOP

    .align 2
    J       girq15_b16
    NOP

    .align 2
    J       girq15_b17
    NOP

    .align 2
    J       girq15_b18
    NOP

    .end girq15_isr

#endif

/******************************************************************/


