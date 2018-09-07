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
 *  MEC14xx GIRQ12 Disaggregated Vector Jump table
 *
 ***************************************************************/

    .extern girq12_b0
    .extern girq12_b1
    .extern girq12_b2

#if GIRQ12_DISAGG != 0

/*
 * Disaggregated girq12_isr
 * Program address of this version of girq23v into JTVIC GIRQ12
 * Aggregator Control register with bit[0] = 1.
 */
    .insn
#ifdef __XC32
    .section .girqs.girq12_isr, code
#else
    .section .girqs.girq12_isr,"x"
#endif
    .set  nomips16
    .set  micromips
    .set  noreorder
    .set  noat
    .ent girq12_isr
    .global girq12_isr
    .align 2

girq12_isr:
    J       girq12_b0
    NOP

    .align 2
    J       girq12_b1
    NOP

    .align 2
    J       girq12_b2
    NOP

    .end girq12_isr

#endif

/******************************************************************/


