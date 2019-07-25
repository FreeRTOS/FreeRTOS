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
 *  MEC14xx GIRQ25 Disaggregated Vector Jump table
 *
 ***************************************************************/

    .extern girq25_b0
    .extern girq25_b1
    .extern girq25_b2
    .extern girq25_b3
    .extern girq25_b4
    .extern girq25_b5
    .extern girq25_b6
    .extern girq25_b7
    .extern girq25_b8
    .extern girq25_b9
    .extern girq25_b10
    .extern girq25_b11
    .extern girq25_b12
    .extern girq25_b13
    .extern girq25_b14
    .extern girq25_b15
    .extern girq25_b16
    .extern girq25_b17
    .extern girq25_b18
    .extern girq25_b19
    .extern girq25_b20
    .extern girq25_b21
    .extern girq25_b22
    .extern girq25_b23
    .extern girq25_b24
    .extern girq25_b25
    .extern girq25_b26
    .extern girq25_b27

#if GIRQ25_DISAGG != 0

/*
 * Disaggregated girq25_isr
 * Program address of this version of girq25_isr into JTVIC GIRQ25
 * Aggregator Control register with bit[0] = 1.
 */

/*
 * NOTE: All the additional labels surrounding every instruction are
 * there to force GCC OBJDUMP to disassemble microMIPS correctly.
 */

    .insn
#ifdef __XC32
    .section .girqs.girq25_isr, code
#else
    .section .girqs.girq25_isr,"x"
#endif
    .set  nomips16
    .set  micromips
    .set  noreorder
    .set  noat
    .ent girq25_isr
    .global girq25_isr
    .align 2

girq25_isr:
    J       girq25_b0
g25b0b:
    NOP

    .align 2
g25b1a:
    J       girq25_b1
g25b1b:
    NOP

    .align 2
g25b2a:
    J       girq25_b2
g25b2b:
    NOP

    .align 2
g25b3a:
    J       girq25_b3
g25b3b:
    NOP

    .align 2
g25b4a:
    J       girq25_b4
g25b4b:
    NOP

    .align 2
g25b5a:
    J       girq25_b5
g25b5b:
    NOP

    .align 2
g25b6a:
    J       girq25_b6
g25b6b:
    NOP

    .align 2
g25b7a:
    J       girq25_b7
g25b7b:
    NOP

    .align 2
g25b8a:
    J       girq25_b8
g25b8b:
    NOP

    .align 2
g25b9a:
    J       girq25_b9
g25b9b:
    NOP

    .align 2
g25b10a:
    J       girq25_b10
g25b10b:
    NOP

    .align 2
g25b11a:
    J       girq25_b11
g25b11b:
    NOP

    .align 2
g25b12a:
    J       girq25_b12
g25b12b:
    NOP

    .align 2
g25b13a:
    J       girq25_b13
g25b13b:
    NOP

    .align 2
g25b14a:
    J       girq25_b14
g25b14b:
    NOP

    .align 2
g25b15a:
    J       girq25_b15
g25b15b:
    NOP

    .align 2
g25b16a:
    J       girq25_b16
g25b16b:
    NOP

    .align 2
g25b17a:
    J       girq25_b17
g25b17b:
    NOP

    .align 2
g25b18a:
    J       girq25_b18
g25b18b:
    NOP

    .align 2
g25b19a:
    J       girq25_b19
g25b19b:
    NOP

    .align 2
g25b20a:
    J       girq25_b20
g25b20b:
    NOP

    .align 2
g25b21a:
    J       girq25_b21
g25b21b:
    NOP

    .align 2
g25b22a:
    J       girq25_b22
g25b22b:
    NOP

    .align 2
g25b23a:
    J       girq25_b23
g25b23b:
    NOP

    .align 2
g25b24a:
    J       girq25_b24
g25b24b:
    NOP

    .align 2
g25b25a:
    J       girq25_b25
g25b25b:
    NOP

    .align 2
g25b26a:
    J       girq25_b26
g25b26b:
    NOP

    .align 2
g25b27a:
    J       girq25_b27
g25b27b:
    NOP
g25end:
    .end girq25_isr

#endif

/******************************************************************/


