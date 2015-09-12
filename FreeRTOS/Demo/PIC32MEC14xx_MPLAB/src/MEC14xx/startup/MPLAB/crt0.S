/*********************************************************************
 *
 *                  C Runtime Startup
 *
 *********************************************************************
 * Filename:        crt0.S
 *
 * Processor:       PIC32
 *
 * Compiler:        MPLAB XC32
 *                  MPLAB X IDE
 * Company:         Microchip Technology Inc.
 *
 * Software License Agreement
 *
 * This software is developed by Microchip Technology Inc. and its
 * subsidiaries ("Microchip").
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1.      Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2.      Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * 3.      Microchip's name may not be used to endorse or promote products
 * derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY MICROCHIP "AS IS" AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL
 * MICROCHIP BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING BUT NOT LIMITED TO
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA OR PROFITS;
 * OR BUSINESS INTERRUPTION) HOWSOEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR
 * OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
 * ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 ********************************************************************/

#include <xc.h>
#include <cp0defs.h>

/* MEC14xx */
#define PIC32_SRS_SET_COUNT 1
#define INIT_SSX
#undef INIT_MMU_MZ_FIXED
#undef INIT_L1_CACHE

/* MEC14xx fill stack with sentinel value */
#define EN_STACK_FILL */

#if (__XC32_VERSION > 1000) && !defined(CPP_INIT)
#define CPP_INIT
#endif

#if !defined(PIC32_SRS_SET_COUNT)
# warning PIC32_SRS_SET_COUNT not defined on build line
# define PIC32_SRS_SET_COUNT 2
#endif

#if !defined(STACK_FILL_VALUE)
# define STACK_FILL_VALUE 0xDEADBEEFul
#endif

/* This file contains 32-bit assembly code */
       .set nomips16

        ##################################################################
        # Entry point of the entire application
        ##################################################################
        .section .reset,code,keep
        .align 2
        .set noreorder
        .ent _reset

############################
# Begin ISA switching code #
############################

#if defined(__PIC32_HAS_MICROMIPS) || defined(__mips_micromips)
#if defined (__mips_micromips)
        .set micromips
#endif
_reset:
        .word 0x10000003     /* MIPS32:    branch to 0xBFC00010 from here     */
                             /* MicroMIPS: ADDI32 $0, $0, 0x0007 (nop)        */
                             /* DO NOT change the relative branch             */

        .word 0x00000000     /* NOP */
__reset_micromips_isa:
        .set    micromips
        jal     _startup
        nop

        .align 2
        /* Device not in proper ISA mode */
        .set nomicromips
__reset_switch_isa:
        jal _startup
        nop

#else

_reset:
        jal _startup
        nop

#endif  /* __PIC32_HAS_MICROMIPS */

        .align 2
        .end _reset
        .globl _reset
        .size _reset, .-_reset

        .section .reset.startup,code,keep
        .align 2
        .set noreorder

#if defined (__mips_micromips)
        .set micromips
#else
        .set nomicromips
#endif

############################
# End ISA switching code   #
############################


        ##################################################################
        # Startup code
        ##################################################################
        .align 2
        .set noreorder
        .ent _startup
_startup:

        ##################################################################
        # New - Set BEV=1 for the cases where M14K instruction pointer 
        # is changed to force ROM to run again. CP0.BEV must be 1 to 
        # safely write CP0.EBASE
        ##################################################################
        mfc0    k0, _CP0_STATUS
        lui     k1, 0x0040
        or      k0, k0, k1        # CP0.STATUS.BEV(bit[22]) = 1
        mtc0    k0, _CP0_STATUS
        ehb

        ##################################################################
        # Initialize Stack Pointer
        #   _stack is initialized by the linker script to point to the
        #    starting location of the stack in DRM
        ##################################################################
        la      sp,_stack

        ##################################################################
        # Initialize Global Pointer
        #   _gp is initialized by the linker script to point to "middle"
        #   of the small variables region
        ##################################################################
        la      gp,_gp

#if (PIC32_SRS_SET_COUNT == 2)
        ##################################################################
        # Initialize Global Pointer in Shadow Set
        #   The SRSCtl's PSS field must be set to the shadow set in which
        #   to initialize the global pointer.  Since we have only a
        #   single shadow set (besides the normal), we will initialize
        #   SRSCtl<PSS> to SRSCtl<HSS>.  We then write the global pointer
        #   to the previous shadow set to ensure that on interrupt, the
        #   global pointer has been initialized.
        ##################################################################
        mfc0    t1,_CP0_SRSCTL          # Read SRSCtl register
        add     t3,t1,zero              # Save off current SRSCtl
        ext     t2,t1,26,4              # to obtain HSS field
        ins     t1,t2,6,4               # Put HSS field
        mtc0    t1,_CP0_SRSCTL          # into SRSCtl<PSS>
        ehb                             # Clear hazard before using new SRSCTL
        wrpgpr  gp,gp                   # Set global pointer in PSS
        mtc0    t3,_CP0_SRSCTL          # Restore SRSCtl
        ehb

#elif (PIC32_SRS_SET_COUNT > 2)
        ##################################################################
        # Initialize Global Pointer in Shadow Set(s)
        #   The SRSCtl PSS field must be set to the shadow set in which
        #   to initialize the global pointer.  We will initialize
        #   SRSCtl<PSS> to the number of reg sets and work down to set zero.
        #   We write the global pointer to the previous shadow set to
        #   ensure that on interrupt, the global pointer has been
        #   initialized.
        ##################################################################
        mfc0    t1,_CP0_SRSCTL          # Read SRSCtl register
        add     t3,t1,zero              # Save off current SRSCtl

        li      t2,(PIC32_SRS_SET_COUNT-1)

1:      ins     t1,t2,6,4               # Put next shadow set field
        mtc0    t1,_CP0_SRSCTL          # into SRSCtl<PSS>
        ehb                             # Clear hazard before using new SRSCTL
        wrpgpr  gp,gp                   # Set global pointer in PSS

        addiu   t2,t2,-1                # Next lower shadow set
                                        # Loop for all sets
        bne     t2,$0,1b                # Down to zero (normal GPR set)
        nop

        mtc0    t3,_CP0_SRSCTL          # Restore SRSCtl
        ehb

#endif /* (PIC32_SRS_SET_COUNT > 2) */

        ##################################################################
        # Call the "on reset" procedure
        ##################################################################
        la      t0,_on_reset
        jalr    t0
        nop

#if defined(INIT_MMU_MZ_FIXED)
        ##################################################################
        # Initialize TLB for fixed mapping to EBI and SQI
        ##################################################################
        .extern __pic32_tlb_init_ebi_sqi
        la      t0,__pic32_tlb_init_ebi_sqi
        jalr    t0
        nop
#endif

#if defined(INIT_L1_CACHE)
        ##################################################################
        # Initialize L1 cache register
        ##################################################################
        .extern __pic32_init_cache
        la      t0,__pic32_init_cache
        jalr    t0
        nop
#endif

#if defined(EN_STACK_FILL)
        ##################################################################
        # Fill stack
        # TODO - handle different stack lengths:
        # mulitple of 4, 8, 16, or 32
        ##################################################################
        la      t0,_stack_start
        la      t1,_stack
        b       _stack_check

_stack_init:
        sw      zero,0x0(t0)
        sw      zero,0x4(t0)
        sw      zero,0x8(t0)
        sw      zero,0xc(t0)
        addu    t0,16

_stack_check:
        bltu    t0,t1,_stack_init
        nop
#endif

        ##################################################################
        # Clear uninitialized data sections
        ##################################################################
        la      t0,_bss_begin
        la      t1,_bss_end
        b       _bss_check
        nop

_bss_init:
        sw      zero,0x0(t0)
        sw      zero,0x4(t0)
        sw      zero,0x8(t0)
        sw      zero,0xc(t0)
        addu    t0,16
_bss_check:
        bltu    t0,t1,_bss_init
        nop

        ##################################################################
        # Initialize data using the linker-generated .dinit table
        ##################################################################
        .equiv FMT_CLEAR,0
        .equiv FMT_COPY,1
_dinit_init:
        la      t0,_dinit_addr

#define SRC t0
#define DST t1
#define LEN t2
#define FMT t3

0:      lw      DST,0(SRC)
        beqz    DST,9f
        addu    SRC,4
        lw      LEN,0(SRC)
        addu    SRC,4
        lw      FMT,0(SRC)
        beq     FMT,$0,_dinit_clear
        addu    SRC,4

_dinit_copy:
        lbu     t4,0(SRC)
        subu    LEN,1
        addu    SRC,1
        sb      t4,0(DST)
        bne     LEN,$0,_dinit_copy
        addu    DST,1

        b       _dinit_end
        nop

_dinit_clear:
        sb      $0,(DST)
        subu    LEN,1
        bne     LEN,$0,_dinit_clear
        addu    DST,1

_dinit_end:
        addu    SRC,3
        addiu   LEN,$0,0xFFFFFFFC
        and     SRC,LEN,SRC
        lw      DST,0(SRC)
        bne     DST,$0,0b
        nop
9:

        ##################################################################
        # If there are no RAM functions, skip the next section --
        # initializing bus matrix registers.
        ##################################################################
        la      t1,_ramfunc_begin
        beqz    t1,_ramfunc_done
        nop

#if defined(INIT_SSX)
  /* No initialization required */
#else /* Use BMX */
        ##################################################################
        # Initialize bus matrix registers if RAM functions exist in the
        # application
        ##################################################################
        la      t1,_bmxdkpba_address
        la      t2,BMXDKPBA
        sw      t1,0(t2)
        la      t1,_bmxdudba_address
        la      t2,BMXDUDBA
        sw      t1,0(t2)
        la      t1,_bmxdupba_address
        la      t2,BMXDUPBA
        sw      t1,0(t2)
#endif /* INIT_SSX */

_ramfunc_done:

        ##################################################################
        # Initialize CP0 registers
        ##################################################################
        # Initialize Count register
        ##################################################################
        mtc0    zero,_CP0_COUNT

        ##################################################################
        # Initialize Compare register
        ##################################################################
        li      t2,-1
        mtc0    t2,_CP0_COMPARE

        ##################################################################
        # Initialize EBase register
        ##################################################################
        la      t1,_ebase_address
        mtc0    t1,_CP0_EBASE

        ##################################################################
        # Initialize IntCtl register
        ##################################################################
        la      t1,_vector_spacing
        li      t2,0                    # Clear t2 and
        ins     t2,t1,5,5               # shift value to VS field
        mtc0    t2,_CP0_INTCTL

        ##################################################################
        # Initialize CAUSE registers
        # - Enable counting of Count register <DC = 0>
        # - Use special exception vector <IV = 1>
        # - Clear pending software interrupts <IP1:IP0 = 0>
        ##################################################################
        li      t1,0x00800000
        mtc0    t1,_CP0_CAUSE

        ##################################################################
        # Initialize STATUS register
        # - Access to Coprocessor 0 not allowed in user mode <CU0 = 0>
        # - User mode uses configured endianness <RE = 0>
        # - Preserve Bootstrap Exception vectors <BEV>
        # - Preserve soft reset <SR> and non-maskable interrupt <NMI>
        # - CorExtend enabled based on whether CorExtend User Defined
        #   Instructions have been implemented <CEE = Config<UDI>>
        # - Disable any pending interrups <IM7..IM2 = 0, IM1..IM0 = 0>
        # - Disable hardware interrupts <IPL7:IPL2 = 0>
        # - Base mode is Kernel mode <UM = 0>
        # - Error level is normal <ERL = 0>
        # - Exception level is normal <EXL = 0>
        # - Interrupts are disabled <IE = 0>
        # - DSPr2 ASE is enabled for devices that support it <MX = 1>
        ##################################################################
        mfc0    t0,_CP0_CONFIG
        ext     t1,t0,22,1              # Extract UDI from Config register
        sll     t1,t1,17                # Move UDI to Status.CEE location
        mfc0    t0,_CP0_STATUS
        and     t0,t0,0x00580000        # Preserve SR, NMI, and BEV
#if defined(INIT_DSPR2)
        li      t2, 0x01000000          # Set the Status.MX bit to enable DSP
        or      t0,t2,t0
#endif
        or      t0,t1,t0                # Include Status.CEE (from UDI)
        mtc0    t0,_CP0_STATUS

        ##################################################################
        # Call the "on bootstrap" procedure
        ##################################################################
        la      t0,_on_bootstrap
        jalr    t0
        nop

        ##################################################################
        # Initialize Status<BEV> for normal exception vectors
        ##################################################################
        mfc0    t0,_CP0_STATUS
        and     t0,t0,0xffbfffff        # Clear BEV
        mtc0    t0,_CP0_STATUS

        ##################################################################
        # Call main. We do this via a thunk in the text section so that
        # a normal jump and link can be used, enabling the startup code
        # to work properly whether main is written in MIPS16 or MIPS32
        # code. I.e., the linker will correctly adjust the JAL to JALX if
        # necessary
        ##################################################################
        and     a0,a0,0
        and     a1,a1,0
        la      t0,_main_entry
        jr      t0
        nop

        .end _startup


        ##################################################################
        # General Exception Vector Handler
        # Jumps to _general_exception_context
        ##################################################################
        .section .gen_handler,code
        .set noreorder
        .ent _gen_exception
_gen_exception:
0:      la      k0,_general_exception_context
        jr      k0
        nop

        .end _gen_exception

#if defined(INIT_MMU_MZ_FIXED)
        ##################################################################
        # Simple TLB-Refill Exception Vector
        # Jumps to _simple_tlb_refill_exception_context
        ##################################################################
        .section .simple_tlb_refill_vector,code,keep
        .set noreorder
        .ent simple_tlb_refill_vector
simple_tlb_refill_vector:
        la      k0,_simple_tlb_refill_exception_context
        jr      k0
        nop

        .end simple_tlb_refill_vector
#endif

#if defined(INIT_L1_CACHE)
        ##################################################################
        # Cache-Error Exception Vector Handler
        # Jumps to _cache_err_exception_context
        ##################################################################
        .section .cache_err_vector,code,keep
        .set noreorder
        .ent _cache_err_vector
_cache_err_vector:
        la      k0,_cache_err_exception_context
        jr      k0
        nop

        .end _cache_err_vector
#endif

        .section .text.main_entry,code,keep
        .ent _main_entry
_main_entry:

#if defined(CPP_INIT)
        .weak _init
        # call .init section to run constructors etc
        lui	a0,%hi(_init)
        addiu	sp,sp,-24
        addiu	a0,a0,%lo(_init)
        beq	a0,$0,2f
        sw	$31,20(sp)	 #,
        jalr	a0
        nop
2:
#endif
        and     a0,a0,0
        and     a1,a1,0

        ##################################################################

        # Call main
        ##################################################################
        jal main
        nop

#if defined(CALL_EXIT)
        ##################################################################
        # Call exit()
        ##################################################################
        jal exit
        nop
#endif

        ##################################################################
        # Just in case, go into infinite loop
        # Call a software breakpoint only with -mdebugger compiler option
        ##################################################################
        .weak __exception_handler_break
__crt0_exit:
1:
        la      v0,__exception_handler_break
        beq     v0,0,0f
        nop
        jalr    v0
        nop

0:      b       1b
        nop

        .globl __crt0_exit
        .end _main_entry

    ###############################################################
    # launch_fw
    ###############################################################
    .globl  rom_launch_fw
    .set    nomips16
    .set    micromips
    .ent   rom_launch_fw
    .type  rom_launch_fw, @function

rom_launch_fw:

    .set    noreorder
    .set    nomacro

lfw1:
    di
lfw2:
    ehb
lfw3:
    nop
    
    # turn off core timer
lfw4:
    mfc0    t0, _CP0_CAUSE
lfw5:
    lui     t1, 0xf7ff
lfw6:
    ori     t1, t1, 0xffff
lfw7:
    and     t0, t0, t1
lfw8:
    mtc0    t0, _CP0_CAUSE
lfw9:
    ehb
lfw10:
    nop
lfw11:
    mfc0    t0, _CP0_STATUS
lfw12:
    lui     t1, 0x0040
lfw13:
    or      t0, t0, t1        # BEV(bit[22]) = 1
lfw14:
    mtc0    t0, _CP0_STATUS
lfw15:
    ehb
lfw16:
    nop
lfw17:    
    JR.HB   a0
lfw18:
    nop
0:
    j       0b                  # should not get here
lfw19:
    nop

    .set    macro
    .set    reorder

    .end    rom_launch_fw
    .size   rom_launch_fw, .-rom_launch_fw
    