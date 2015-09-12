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


/***************************************************************
 *  MEC14xx GIRQ23 Disaggregated Vector Jump table
 *
 ***************************************************************/

    .extern girq23_b0
    .extern girq23_b1
    .extern girq23_b2
    .extern girq23_b3
    .extern girq23_b4
    .extern girq23_b5
    .extern girq23_b6
    .extern girq23_b7
    .extern girq23_b8
    .extern girq23_b9
    .extern girq23_b10
    .extern girq23_b11
    .extern girq23_b12
    .extern girq23_b13

#if GIRQ23_DISAGG != 0

/*
 * FreeRTOS Handler for MEC14xx RTOS Timer
 * implemented in the porting layer.
 */
    .extern vPortTickInterruptHandler

/*
 * Disaggregated girq23_isr
 * Program address of this version of girq23_isr into JTVIC GIRQ23
 * Aggregator Control register with bit[0] = 1.
 */

/*
 * NOTE: All the additional labels surrounding every instruction are
 * there to force GCC OBJDUMP to disassemble microMIPS correctly.
 */

    .insn
#ifdef __XC32
    .section .girqs.girq23_isr, code
#else
    .section .girqs.girq23_isr,"x"
#endif
    .set  nomips16
    .set  micromips
    .set  noreorder
    .set  noat
    .ent girq23_isr
    .global girq23_isr
    .align 2

girq23_isr:

    J       girq23_b0
g23b0b:
    NOP

    .align 2
g23b1a:
    J       girq23_b1
g23b1b:
    NOP

    .align 2
g23b2a:
    J       girq23_b2
g23b2b:
    NOP

    .align 2
g23b3a:
    J       girq23_b3
g23b3b:
    NOP

    .align 2
g23b4a:
    J       girq23_b4 
g23b4b:
    NOP

    .align 2
g23b5a:
    J       girq23_b5
g23b5b:
    NOP

    .align 2
g23b6a:
    J       girq23_b6
g23b6b:
    NOP

    .align 2
g23b7a:
    J       girq23_b7
g23b7b:
    NOP

    .align 2
g23b8a:
    J       girq23_b8
g23b8b:
    NOP

    .align 2
g23b9a:
    J       girq23_b9
g23b9b:
    NOP

    .align 2
g23b10a:
    J       girq23_b10
g23b10b:
    NOP

    .align 2
g23b11a:
    J       girq23_b11
g23b11b:
    NOP

    .align 2
g23b12a:
    J       girq23_b12
g23b12b:
    NOP

    .align 2
g23b13a:
    J       girq23_b13
g23b13b:
    NOP
g23end:
    .end girq23_isr

#endif

/******************************************************************/




