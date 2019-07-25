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
 *  MEC14xx GIRQ17 Disaggregated Vector Jump table
 *
 ***************************************************************/

    .extern girq17_b0
    .extern girq17_b1
    .extern girq17_b2
    .extern girq17_b3
    .extern girq17_b4
    .extern girq17_b5
    .extern girq17_b6
    .extern girq17_b7
    .extern girq17_b8
    .extern girq17_b9
    .extern girq17_b10

#if GIRQ17_DISAGG != 0

/*
 * Disaggregated girq17_isr
 * Program address of this version of girq17_isr into JTVIC GIRQ17
 * Aggregator Control register with bit[0] = 1.
 */
    .insn
#ifdef __XC32
    .section .girqs.girq17_isr, code
#else
    .section .girqs.girq17_isr,"x"
#endif
    .set  nomips16
    .set  micromips
    .set  noreorder
    .set  noat
    .ent girq17_isr
    .global girq17_isr
    .align 2

girq17_isr:
    J       girq17_b0
    NOP

    .align 2
    J       girq17_b1
    NOP

    .align 2
    J       girq17_b2
    NOP

    .align 2
    J       girq17_b3
    NOP

    .align 2
    J       girq17_b4
    NOP

    .align 2
    J       girq17_b5
    NOP

    .align 2
    J       girq17_b6
    NOP

    .align 2
    J       girq17_b7
    NOP

    .align 2
    J       girq17_b8
    NOP

    .align 2
    J       girq17_b9
    NOP

    .align 2
    J       girq17_b10
    NOP

    .end girq17_isr

#endif

/******************************************************************/


