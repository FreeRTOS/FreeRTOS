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
 *  MEC14xx GIRQ09 Disaggregated Vector Jump table
 *
 ***************************************************************/

    .extern girq09_b0
    .extern girq09_b1
    .extern girq09_b2
    .extern girq09_b3
    .extern girq09_b4
    .extern girq09_b5
    .extern girq09_b6
    .extern girq09_b7
    .extern girq09_b8
    .extern girq09_b9
    .extern girq09_b10
    .extern girq09_b11
    .extern girq09_b12
    .extern girq09_b13
    .extern girq09_b14
    .extern girq09_b15
    .extern girq09_b16
    .extern girq09_b17
    .extern girq09_b18
    .extern girq09_b19
    .extern girq09_b20
    .extern girq09_b21
    .extern girq09_b22
    .extern girq09_b23
    .extern girq09_b24
    .extern girq09_b25
    .extern girq09_b26
    .extern girq09_b27
    .extern girq09_b28
    .extern girq09_b29
    .extern girq09_b30

#if GIRQ09_DISAGG != 0

/*
 * Disaggregated girq09v
 * Program address of this version of girq23v into JTVIC GIRQ09
 * Aggregator Control register with bit[0] = 1.
 */
    .insn
#ifdef __XC32
    .section .girqs.girq09_isr, code
#else
    .section .girqs.girq09_isr,"x"
#endif
    .set  nomips16
    .set  micromips
    .set  noreorder
    .set  noat
    .global girq09_isr
    .ent girq09_isr
    .align 2

girq09_isr:
    J       girq09_b0
    NOP

    .align 2
    J       girq09_b1
    NOP

    .align 2
    J       girq09_b2
    NOP

    .align 2
    J       girq09_b3
    NOP

    .align 2
    J       girq09_b4
    NOP

    .align 2
    J       girq09_b5
    NOP

    .align 2
    J       girq09_b6
    NOP

    .align 2
    J       girq09_b7
    NOP

    .align 2
    J       girq09_b8
    NOP

    .align 2
    J       girq09_b9
    NOP

    .align 2
    J       girq09_b10
    NOP

    .align 2
    J       girq09_b11
    NOP

    .align 2
    J       girq09_b12
    NOP

    .align 2
    J       girq09_b13
    NOP

    .align 2
    J       girq09_b14
    NOP

    .align 2
    J       girq09_b15
    NOP

    .align 2
    J       girq09_b16
    NOP

    .align 2
    J       girq09_b17
    NOP

    .align 2
    J       girq09_b18
    NOP

    .align 2
    J       girq09_b19
    NOP

    .align 2
    J       girq09_b20
    NOP

    .align 2
    J       girq09_b21
    NOP

    .align 2
    J       girq09_b22
    NOP

    .align 2
    J       girq09_b23
    NOP

    .align 2
    J       girq09_b24
    NOP

    .align 2
    J       girq09_b25
    NOP

    .align 2
    J       girq09_b26
    NOP

    .align 2
    J       girq09_b27
    NOP

    .align 2
    J       girq09_b28
    NOP

    .align 2
    J       girq09_b29
    NOP

    .align 2
    J       girq09_b30
    NOP

    .end girq09_isr


#endif

/******************************************************************/


