/*--------------------------------------------------------------------------
 dabort.s

 Copyright (C) 2009-2018 Texas Instruments Incorporated - www.ti.com


  Redistribution and use in source and binary forms, with or without
  modification, are permitted provided that the following conditions
  are met:

    Redistributions of source code must retain the above copyright
    notice, this list of conditions and the following disclaimer.

    Redistributions in binary form must reproduce the above copyright
    notice, this list of conditions and the following disclaimer in the
    documentation and/or other materials provided with the
    distribution.

    Neither the name of Texas Instruments Incorporated nor the names of
    its contributors may be used to endorse or promote products derived
    from this software without specific prior written permission.

  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
  A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
  OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

--------------------------------------------------------------------------*/


    .section .text
    .syntax unified
    .cpu cortex-r4
    .arm


/*-------------------------------------------------------------------------------*/
@ Run Memory Test

    .extern custom_dabort
    .extern vHandleMemoryFault
    .weak _dabort
    .type _dabort, %function

_dabort:
        stmfd   r13!, {r0 - r12, lr}@ push registers and link register on to stack
        ldr     r12, esmsr3         @ ESM Group3 status register
        ldr     r0,  [r12]
        tst     r0,  #0x8           @ check if bit 3 is set, this indicates uncorrectable ECC error on B0TCM
        bne     ramErrorFound
        tst     r0, #0x20           @ check if bit 5 is set, this indicates uncorrectable ECC error on B1TCM
        bne     ramErrorFound2

noRAMerror:
        tst     r0, #0x80           @ check if bit 7 is set, this indicates uncorrectable ECC error on ATCM
        bne     flashErrorFound

/* Create a Exception Fault Stack similiar to the way it is created by the ARMvM
 * architecture. The auto-pushed exception stack will contain:
 * +-------+-----+----------+----------+------+
 * | R0-R3 | R12 | LR (R14) | PC (R15) | CPSR |
 * +-------+-----+----------+----------+------+
 *
 * <-------><----><---------><---------><----->
 *     4      1        1         1         1
*/
MemManage_Handler:
        /* Pop the pushed values so we can re-do the stack the way we need it to be */
        LDMFD   R13!, {R0 - R12, LR}
        /* Abort exceptions increment the LR 0x8 after the fault-inducing instruction */
        SUB     LR, #0x8

        SRSDB   SP!, #0x17              /* Save the pre-exception PC and CPSR */
        STMDB   SP, { R0-R3, R12, LR }^ /* Save the user R0-R3, R12, and LR */
        SUB     SP, SP, #0x18           /* Can't auto-increment SP with ^ operator */
        /* Need the SP in R0 */
        MOV     R0, SP

        /* Call vHandleMemoryFault - This will modify the return state if necessary */
        BLX     vHandleMemoryFault

        POP     { R0-R3, R12, LR }         /* Pop the original values off the stack */
        /* Return to the next instruction after the fault was generated */
        RFEIA   SP!

ramErrorFound:
        ldr     r1, ramctrl         @ RAM control register for B0TCM TCRAMW
        ldr     r2, [r1]
        tst     r2, #0x100          @ check if bit 8 is set in RAMCTRL, this indicates ECC memory write is enabled
        beq     ramErrorReal
        mov     r2, #0x20
        str     r2, [r1, #0x10]     @ clear RAM error status register

        mov     r2, #0x08
        str     r2, [r12]           @ clear ESM group3 channel3 flag for uncorrectable RAM ECC errors
        mov     r2, #5
        str     r2, [r12, #0x18]    @ The nERROR pin will become inactive once the LTC counter expires

        ldmfd   r13!, {r0 - r12, lr}
        subs    pc, lr, #4          @ branch to instruction after the one that caused the abort
                                    @ this is the case because the data abort was caused intentionally
                                    @ and we do not want to cause the same data abort again.

ramErrorFound2:
        ldr     r1, ram2ctrl        @ RAM control register for B1TCM TCRAMW
        ldr     r2, [r1]
        tst     r2, #0x100          @ check if bit 8 is set in RAMCTRL, this indicates ECC memory write is enabled
        beq     ramErrorReal
        mov     r2, #0x20
        str     r2, [r1, #0x10]     @ clear RAM error status register

        mov     r2, #0x20
        str     r2, [r12]           @ clear ESM group3 flags channel5 flag for uncorrectable RAM ECC errors
        mov     r2, #5
        str     r2, [r12, #0x18]    @ The nERROR pin will become inactive once the LTC counter expires

        ldmfd   r13!, {r0 - r12, lr}
        subs    pc, lr, #4          @ branch to instruction after the one that caused the abort
                                    @ this is the case because the data abort was caused intentionally
                                    @ and we do not want to cause the same data abort again.


ramErrorReal:
        b       ramErrorReal        @ branch here forever as continuing operation is not recommended

flashErrorFound:
        ldr     r1, flashbase
        ldr     r2, [r1, #0x6C]     @ read FDIAGCTRL register

        mov     r2, r2, lsr #16
        tst     r2, #5              @ check if bits 19:16 are 5, this indicates diagnostic mode is enabled
        beq     flashErrorReal
        mov     r2, #1
        mov     r2, r2, lsl #8

        str     r2, [r1, #0x1C]     @ clear FEDACSTATUS error flag

        mov     r2, #0x80
        str     r2, [r12]           @ clear ESM group3 flag for uncorrectable flash ECC error
        mov     r2, #5
        str     r2, [r12, #0x18]    @ The nERROR pin will become inactive once the LTC counter expires

        ldmfd   r13!, {r0 - r12, lr}
        subs    pc, lr, #4          @ branch to instruction after the one that caused the abort
                                    @ this is the case because the data abort was caused intentionally
                                    @ and we do not want to cause the same data abort again.


flashErrorReal:
        b       flashErrorReal      @ branch here forever as continuing operation is not recommended

esmsr3:      .word 0xFFFFF520
ramctrl:     .word 0xFFFFF800
ram2ctrl:    .word 0xFFFFF900
ram1errstat: .word 0xFFFFF810
ram2errstat: .word 0xFFFFF910
flashbase:   .word 0xFFF87000



