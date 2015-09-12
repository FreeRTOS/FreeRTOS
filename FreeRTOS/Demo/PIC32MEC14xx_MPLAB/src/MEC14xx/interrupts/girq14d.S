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
 *  MEC14xx GIRQ14 Disaggregated Vector Jump table
 *
 ***************************************************************/

    .extern girq14_b0
    .extern girq14_b1
    .extern girq14_b2
    .extern girq14_b3
    .extern girq14_b4
    .extern girq14_b5

#if GIRQ14_DISAGG != 0

/*
 * Disaggregated girq14_isr
 * Program address of this version of girq14_isr into JTVIC GIRQ14
 * Aggregator Control register with bit[0] = 1.
 */
    .insn
#ifdef __XC32
    .section .girqs.girq14_isr, code
#else
    .section .girqs.girq14_isr,"x"
#endif
    .set  nomips16
    .set  micromips
    .set  noreorder
    .set  noat
    .ent girq14_isr
    .global girq14_isr
    .align 2

girq14_isr:
    J       girq14_b0
    NOP

    .align 2
    J       girq14_b1
    NOP

    .align 2
    J       girq14_b2
    NOP

    .align 2
    J       girq14_b3
    NOP

    .align 2
    J       girq14_b4
    NOP

    .align 2
    J       girq14_b5
    NOP

    .end girq14_isr

#endif

/******************************************************************/


