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
 *  MEC14xx GIRQ16 Disaggregated Vector Jump table
 *
 ***************************************************************/

    .extern girq16_b0
    .extern girq16_b1
    .extern girq16_b2
    .extern girq16_b3
    .extern girq16_b4
    .extern girq16_b5
    .extern girq16_b6
    .extern girq16_b7
    .extern girq16_b8
    .extern girq16_b9

#if GIRQ16_DISAGG != 0
/*
 * Disaggregated girq16_isr
 * Program address of this version of girq16_isr into JTVIC GIRQ16
 * Aggregator Control register with bit[0] = 1.
 */
    .insn
#ifdef __XC32
    .section .girqs.girq16_isr, code
#else
    .section .girqs.girq16_isr,"x"
#endif
    .set  nomips16
    .set  micromips
    .set  noreorder
    .set  noat
    .ent girq16_isr
    .global girq16_isr
    .align 2

girq16_isr:
    J       girq16_b0
    NOP

    .align 2
    J       girq16_b1
    NOP

    .align 2
    J       girq16_b2
    NOP

    .align 2
    J       girq16_b3
    NOP

    .align 2
    J       girq16_b4
    NOP

    .align 2
    J       girq16_b5
    NOP

    .align 2
    J       girq16_b6
    NOP

    .align 2
    J       girq16_b7
    NOP

    .align 2
    J       girq16_b8
    NOP

    .align 2
    J       girq16_b9
    NOP

    .end girq16_isr

#endif

/******************************************************************/


