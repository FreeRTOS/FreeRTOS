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
 *  MEC14xx GIRQ11 Disaggregated Vector Jump table
 *
 ***************************************************************/

    .extern girq11_b0
    .extern girq11_b1
    .extern girq11_b2
    .extern girq11_b3
    .extern girq11_b4
    .extern girq11_b5
    .extern girq11_b6
    .extern girq11_b7
    .extern girq11_b8
    .extern girq11_b9
    .extern girq11_b10
    .extern girq11_b11
    .extern girq11_b12
    .extern girq11_b13
    .extern girq11_b14
    .extern girq11_b15
    .extern girq11_b16
    .extern girq11_b17
    .extern girq11_b18
    .extern girq11_b19
    .extern girq11_b20
    .extern girq11_b21
    .extern girq11_b22
    .extern girq11_b23
    .extern girq11_b24
    .extern girq11_b25
    .extern girq11_b26
    .extern girq11_b27
    .extern girq11_b28
    .extern girq11_b30

#if GIRQ11_DISAGG != 0

/*
 * Disaggregated girq11_isr
 * Program address of this version of girq23v into JTVIC GIRQ11
 * Aggregator Control register with bit[0] = 1.
 */
    .insn
#ifdef __XC32
    .section .girqs.girq11_isr, code
#else
    .section .girqs.girq11_isr,"x"
#endif
    .set  nomips16
    .set  micromips
    .set  noreorder
    .set  noat
    .ent girq11_isr
    .global girq11_isr
    .align 2

girq11_isr:
#if 1
    J       girq11_b0
    NOP

    .align 2
    J       girq11_b1
    NOP

    .align 2
    J       girq11_b2
    NOP

    .align 2
    J       girq11_b3
    NOP

    .align 2
    J       girq11_b4
    NOP

    .align 2
    J       girq11_b5
    NOP

    .align 2
    J       girq11_b6
    NOP

    .align 2
    J       girq11_b7
    NOP

    .align 2
    J       girq11_b8
    NOP

    .align 2
    J       girq11_b9
    NOP

    .align 2
    J       girq11_b10
    NOP

    .align 2
    J       girq11_b11
    NOP

    .align 2
    J       girq11_b12
    NOP

    .align 2
    J       girq11_b13
    NOP

    .align 2
    J       girq11_b14
    NOP

    .align 2
    J       girq11_b15
    NOP

    .align 2
    J       girq11_b16
    NOP

    .align 2
    J       girq11_b17
    NOP

    .align 2
    J       girq11_b18
    NOP

    .align 2
    J       girq11_b19
    NOP

    .align 2
    J       girq11_b20
    NOP

    .align 2
    J       girq11_b21
    NOP

    .align 2
    J       girq11_b22
    NOP

    .align 2
    J       girq11_b23
    NOP

    .align 2
    J       girq11_b24
    NOP

    .align 2
    J       girq11_b25
    NOP

    .align 2
    J       girq11_b26
    NOP

    .align 2
    J       girq11_b27
    NOP

    .align 2
    J       girq11_b28
    NOP

    .align 2
    J       girq11_b29
    NOP

    .align 2
    J       girq11_b30
    NOP

    .end girq11_isr
#else
    gen_jump_table 11,0,30
#endif

#endif

/******************************************************************/


