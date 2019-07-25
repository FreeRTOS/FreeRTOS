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
 *  MEC14xx GIRQ08 Disaggregated Vector Jump table
 *
 ***************************************************************/

    .extern girq08_b0
    .extern girq08_b1
    .extern girq08_b2
    .extern girq08_b3
    .extern girq08_b4
    .extern girq08_b5
    .extern girq08_b6
    .extern girq08_b7
    .extern girq08_b8
    .extern girq08_b9
    .extern girq08_b10
    .extern girq08_b11
    .extern girq08_b12
    .extern girq08_b13
    .extern girq08_b14
    .extern girq08_b15
    .extern girq08_b16
    .extern girq08_b17
    .extern girq08_b18
    .extern girq08_b19
    .extern girq08_b20
    .extern girq08_b21
    .extern girq08_b22

#if GIRQ08_DISAGG != 0

/*
 * Disaggregated girq08v
 * Program address of this version of girq23v into JTVIC GIRQ08 
 * Aggregator Control register with bit[0] = 1.
 */
    .insn
#ifdef __XC32
    .section .girqs.girq08_isr,code
#else
    .section .girqs.girq08_isr,"x"
#endif
    .set  nomips16
    .set  micromips
    .set  noreorder
    .set  noat
    .global girq08_isr
    .ent girq08_isr
    .align 2

girq08_isr:
    J       girq08_b0
    NOP

    .align 2
    J       girq08_b1
    NOP

    .align 2
    J       girq08_b2
    NOP

    .align 2
    J       girq08_b3
    NOP

    .align 2
    J       girq08_b4
    NOP

    .align 2
    J       girq08_b5
    NOP

    .align 2
    J       girq08_b6
    NOP

    .align 2
    J       girq08_b7
    NOP

    .align 2
    J       girq08_b8
    NOP

    .align 2
    J       girq08_b9
    NOP

    .align 2
    J       girq08_b10
    NOP

    .align 2
    J       girq08_b11
    NOP

    .align 2
    J       girq08_b12
    NOP

    .align 2
    J       girq08_b13
    NOP

    .align 2
    J       girq08_b14
    NOP

    .align 2
    J       girq08_b15
    NOP

    .align 2
    J       girq08_b16
    NOP

    .align 2
    J       girq08_b17
    NOP

    .align 2
    J       girq08_b18
    NOP

    .align 2
    J       girq08_b19
    NOP

    .align 2
    J       girq08_b20
    NOP

    .align 2
    J       girq08_b21
    NOP

    .align 2
    J       girq08_b22
    NOP

    .end girq08_isr

/******************************************************************/

#endif

