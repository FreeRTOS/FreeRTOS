/***********************************************************************/
/*  This file is part of the uVision/ARM development tools             */
/*  Copyright KEIL ELEKTRONIK GmbH 2002-2004                           */
/***********************************************************************/
/*                                                                     */
/*  STARTUP.S:  Startup file for Philips LPC2000 device series         */
/*                                                                     */
/***********************************************************************/


/* 
//*** <<< Use Configuration Wizard in Context Menu >>> *** 
*/


// *** Startup Code (executed after Reset) ***


// Standard definitions of Mode bits and Interrupt (I & F) flags in PSRs

        Mode_USR  EQU      0x10
        Mode_FIQ  EQU      0x11
        Mode_IRQ  EQU      0x12
        Mode_SVC  EQU      0x13
        Mode_ABT  EQU      0x17
        Mode_UND  EQU      0x1B
        Mode_SYS  EQU      0x1F

        I_Bit     EQU      0x80    /* when I bit is set, IRQ is disabled */
        F_Bit     EQU      0x40    /* when F bit is set, FIQ is disabled */


/*
// <h> Stack Configuration (Stack Sizes in Bytes)
//   <o0> Undefined Mode      <0x0-0xFFFFFFFF>
//   <o1> Supervisor Mode     <0x0-0xFFFFFFFF>
//   <o2> Abort Mode          <0x0-0xFFFFFFFF>
//   <o3> Fast Interrupt Mode <0x0-0xFFFFFFFF>
//   <o4> Interrupt Mode      <0x0-0xFFFFFFFF>
//   <o5> User/System Mode    <0x0-0xFFFFFFFF>
// </h>
*/
        UND_Stack_Size  EQU     0x00000004
        SVC_Stack_Size  EQU     0x00000100
        ABT_Stack_Size  EQU     0x00000004
        FIQ_Stack_Size  EQU     0x00000004
        IRQ_Stack_Size  EQU     0x00000300
        USR_Stack_Size  EQU     0x00000200

AREA   STACK, DATA, READWRITE, ALIGN=2
        DS   (USR_Stack_Size+3)&~3  ; Stack for User/System Mode 
        DS   (IRQ_Stack_Size+3)&~3  ; Stack for Interrupt Mode
        DS   (FIQ_Stack_Size+3)&~3  ; Stack for Fast Interrupt Mode 
        DS   (ABT_Stack_Size+3)&~3  ; Stack for Abort Mode
        DS   (SVC_Stack_Size+3)&~3  ; Stack for Supervisor Mode
        DS   (UND_Stack_Size+3)&~3  ; Stack for Undefined Mode
Top_Stack:


// Phase Locked Loop (PLL) definitions
        PLL_BASE        EQU     0xE01FC080  /* PLL Base Address */
        PLLCON_OFS      EQU     0x00        /* PLL Control Offset*/
        PLLCFG_OFS      EQU     0x04        /* PLL Configuration Offset */
        PLLSTAT_OFS     EQU     0x08        /* PLL Status Offset */
        PLLFEED_OFS     EQU     0x0C        /* PLL Feed Offset */
        PLLCON_PLLE     EQU     (1<<0)      /* PLL Enable */
        PLLCON_PLLC     EQU     (1<<1)      /* PLL Connect */
        PLLCFG_MSEL     EQU     (0x1F<<0)   /* PLL Multiplier */
        PLLCFG_PSEL     EQU     (0x03<<5)   /* PLL Divider */
        PLLSTAT_PLOCK   EQU     (1<<10)     /* PLL Lock Status */

/*
// <e> PLL Setup
// <i> Phase Locked Loop
//   <o1.0..4>   MSEL: PLL Multiplier Selection
//               <1-32><#-1>
//               <i> M Value
//   <o1.5..6>   PSEL: PLL Divider Selection
//               <0=> 1   <1=> 2   <2=> 4   <3=> 8
//               <i> P Value
// </e>
*/
        PLL_SETUP       EQU     1
        PLLCFG_Val      EQU     0x00000024


// Memory Accelerator Module (MAM) definitions
        MAM_BASE        EQU     0xE01FC000  /* MAM Base Address */
        MAMCR_OFS       EQU     0x00        /* MAM Control Offset*/
        MAMTIM_OFS      EQU     0x04        /* MAM Timing Offset */

/*
// <e> MAM Setup
// <i> Memory Accelerator Module
//   <o1.0..1>   MAM Control
//               <0=> Disabled
//               <1=> Partially Enabled
//               <2=> Fully Enabled
//               <i> Mode
//   <o2.0..2>   MAM Timing
//               <0=> Reserved  <1=> 1   <2=> 2   <3=> 3
//               <4=> 4         <5=> 5   <6=> 6   <7=> 7
//               <i> Fetch Cycles
// </e>
*/
        MAM_SETUP       EQU     1
        MAMCR_Val       EQU     0x00000002
        MAMTIM_Val      EQU     0x00000003


// External Memory Controller (EMC) definitions
        EMC_BASE        EQU     0xFFE00000  /* EMC Base Address */
        BCFG0_OFS       EQU     0x00        /* BCFG0 Offset */
        BCFG1_OFS       EQU     0x04        /* BCFG1 Offset */
        BCFG2_OFS       EQU     0x08        /* BCFG2 Offset */
        BCFG3_OFS       EQU     0x0C        /* BCFG3 Offset */

/*
// <e> External Memory Controller (EMC)
*/
        EMC_SETUP       EQU     0

/*
//   <e> Bank Configuration 0 (BCFG0)
//     <o1.0..3>   IDCY: Idle Cycles <0-15>
//     <o1.5..9>   WST1: Wait States 1 <0-31>
//     <o1.11..15> WST2: Wait States 2 <0-31>
//     <o1.10>     RBLE: Read Byte Lane Enable
//     <o1.26>     WP: Write Protect
//     <o1.27>     BM: Burst ROM
//     <o1.28..29> MW: Memory Width  <0=>  8-bit  <1=> 16-bit
//                                   <2=> 32-bit  <3=> Reserved
//   </e>
*/
        BCFG0_SETUP EQU         0
        BCFG0_Val   EQU         0x0000FBEF

/*
//   <e> Bank Configuration 1 (BCFG1)
//     <o1.0..3>   IDCY: Idle Cycles <0-15>
//     <o1.5..9>   WST1: Wait States 1 <0-31>
//     <o1.11..15> WST2: Wait States 2 <0-31>
//     <o1.10>     RBLE: Read Byte Lane Enable
//     <o1.26>     WP: Write Protect
//     <o1.27>     BM: Burst ROM
//     <o1.28..29> MW: Memory Width  <0=>  8-bit  <1=> 16-bit
//                                   <2=> 32-bit  <3=> Reserved
//   </e>
*/
        BCFG1_SETUP EQU         0
        BCFG1_Val   EQU         0x0000FBEF

/*
//   <e> Bank Configuration 0 (BCFG2)
//     <o1.0..3>   IDCY: Idle Cycles <0-15>
//     <o1.5..9>   WST1: Wait States 1 <0-31>
//     <o1.11..15> WST2: Wait States 2 <0-31>
//     <o1.10>     RBLE: Read Byte Lane Enable
//     <o1.26>     WP: Write Protect
//     <o1.27>     BM: Burst ROM
//     <o1.28..29> MW: Memory Width  <0=>  8-bit  <1=> 16-bit
//                                   <2=> 32-bit  <3=> Reserved
//   </e>
*/
        BCFG2_SETUP EQU         0
        BCFG2_Val   EQU         0x0000FBEF

/*
//   <e> Bank Configuration 3 (BCFG3)
//     <o1.0..3>   IDCY: Idle Cycles <0-15>
//     <o1.5..9>   WST1: Wait States 1 <0-31>
//     <o1.11..15> WST2: Wait States 2 <0-31>
//     <o1.10>     RBLE: Read Byte Lane Enable
//     <o1.26>     WP: Write Protect
//     <o1.27>     BM: Burst ROM
//     <o1.28..29> MW: Memory Width  <0=>  8-bit  <1=> 16-bit
//                                   <2=> 32-bit  <3=> Reserved
//   </e>
*/
        BCFG3_SETUP EQU         0
        BCFG3_Val   EQU         0x0000FBEF

/*
// </e> End of EMC
*/


// External Memory Pins definitions
        PINSEL2         EQU     0xE002C014  /* PINSEL2 Address */
        PINSEL2_Val     EQU     0x0E6149E4  /* CS0..3, OE, WE, BLS0..3, 
                                               D0..31, A2..23, JTAG Pins */


// Starupt Code must be linked first at Address at which it expects to run.

$IF (EXTERNAL_MODE)
        CODE_BASE       EQU     0x80000000
$ELSE
        CODE_BASE       EQU     0x00000000
$ENDIF

AREA   STARTUPCODE, CODE, AT CODE_BASE   // READONLY, ALIGN=4
       PUBLIC  __startup

       EXTERN  CODE32 (?C?INIT)

__startup       PROC    CODE32

// Pre-defined interrupt handlers that may be directly 
// overwritten by C interrupt functions
EXTERN CODE32 (Undef_Handler?A)
EXTERN CODE32 (vPortYieldProcessor?A)
EXTERN CODE32 (PAbt_Handler?A)
EXTERN CODE32 (DAbt_Handler?A)
EXTERN CODE32 (IRQ_Handler?A)
EXTERN CODE32 (FIQ_Handler?A)

// Exception Vectors
// Mapped to Address 0.
// Absolute addressing mode must be used.

Vectors:        LDR     PC,Reset_Addr         
                LDR     PC,Undef_Addr
                LDR     PC,SWI_Addr
                LDR     PC,PAbt_Addr
                LDR     PC,DAbt_Addr
                NOP                            /* Reserved Vector */
;               LDR     PC,IRQ_Addr
                LDR     PC,[PC, #-0x0FF0]      /* Vector from VicVectAddr */
                LDR     PC,FIQ_Addr

Reset_Addr:     DD      Reset_Handler
Undef_Addr:     DD      Undef_Handler?A
SWI_Addr:       DD      vPortYieldProcessor?A
PAbt_Addr:      DD      PAbt_Handler?A
DAbt_Addr:      DD      DAbt_Handler?A
                DD      0                      /* Reserved Address */
IRQ_Addr:       DD      IRQ_Handler?A
FIQ_Addr:       DD      FIQ_Handler?A


// Reset Handler

Reset_Handler:  


$IF (EXTERNAL_MODE)
                LDR     R0, =PINSEL2
                LDR     R1, =PINSEL2_Val
                STR     R1, [R0]
$ENDIF


IF (EMC_SETUP != 0)
                LDR     R0, =EMC_BASE

IF (BCFG0_SETUP != 0)
                LDR     R1, =BCFG0_Val
                STR     R1, [R0, #BCFG0_OFS]
ENDIF

IF (BCFG1_SETUP != 0)
                LDR     R1, =BCFG1_Val
                STR     R1, [R0, #BCFG1_OFS]
ENDIF

IF (BCFG2_SETUP != 0)
                LDR     R1, =BCFG2_Val
                STR     R1, [R0, #BCFG2_OFS]
ENDIF

IF (BCFG3_SETUP != 0)
                LDR     R1, =BCFG3_Val
                STR     R1, [R0, #BCFG3_OFS]
ENDIF

ENDIF


IF (PLL_SETUP != 0)
                LDR     R0, =PLL_BASE
                MOV     R1, #0xAA
                MOV     R2, #0x55

// Configure and Enable PLL
                MOV     R3, #PLLCFG_Val
                STR     R3, [R0, #PLLCFG_OFS] 
                MOV     R3, #PLLCON_PLLE
                STR     R3, [R0, #PLLCON_OFS]
                STR     R1, [R0, #PLLFEED_OFS]
                STR     R2, [R0, #PLLFEED_OFS]

// Wait until PLL Locked
PLL_Loop:       LDR     R3, [R0, #PLLSTAT_OFS]
                ANDS    R3, R3, #PLLSTAT_PLOCK
                BEQ     PLL_Loop

// Switch to PLL Clock
                MOV     R3, #(PLLCON_PLLE | PLLCON_PLLC)
                STR     R3, [R0, #PLLCON_OFS]
                STR     R1, [R0, #PLLFEED_OFS]
                STR     R2, [R0, #PLLFEED_OFS]
ENDIF


IF (MAM_SETUP != 0)
                LDR     R0, =MAM_BASE
                MOV     R1, #MAMTIM_Val
                STR     R1, [R0, #MAMTIM_OFS] 
                MOV     R1, #MAMCR_Val
                STR     R1, [R0, #MAMCR_OFS] 
ENDIF


// Memory Mapping (when Interrupt Vectors are in RAM)
                MEMMAP  EQU  0xE01FC040  /* Memory Mapping Control */

$IF (RAM_INTVEC)
                LDR     R0, =MEMMAP
                MOV     R1, #2
                STR     R1, [R0]
$ENDIF


// Setup Stack for each mode
                LDR     R0, =Top_Stack

// Enter Undefined Instruction Mode and set its Stack Pointer
                MSR     CPSR_c, #Mode_UND|I_Bit|F_Bit
                MOV     SP, R0
                SUB     R0, R0, #UND_Stack_Size

// Enter Abort Mode and set its Stack Pointer
                MSR     CPSR_c, #Mode_ABT|I_Bit|F_Bit
                MOV     SP, R0
                SUB     R0, R0, #ABT_Stack_Size

// Enter FIQ Mode and set its Stack Pointer
                MSR     CPSR_c, #Mode_FIQ|I_Bit|F_Bit
                MOV     SP, R0
                SUB     R0, R0, #FIQ_Stack_Size

// Enter IRQ Mode and set its Stack Pointer
                MSR     CPSR_c, #Mode_IRQ|I_Bit|F_Bit
                MOV     SP, R0
                SUB     R0, R0, #IRQ_Stack_Size

// Enter Supervisor Mode and set its Stack Pointer
                MSR     CPSR_c, #Mode_SVC|I_Bit|F_Bit
                MOV     SP, R0
                SUB     R0, R0, #SVC_Stack_Size

// Enter S Mode and set its Stack Pointer
                MSR     CPSR_c, #Mode_SYS
                MOV     SP, R0

// Start in supervisor mode
                MSR     CPSR_c, #Mode_SVC|I_Bit|F_Bit

// Enter the C code
                LDR     R0,=?C?INIT
                TST     R0,#1       ; Bit-0 set: INIT is Thumb
                LDREQ   LR,=exit?A  ; ARM Mode
                LDRNE   LR,=exit?T  ; Thumb Mode
                BX      R0
                ENDP

PUBLIC exit?A
exit?A          PROC    CODE32
                B       exit?A
                ENDP

PUBLIC exit?T
exit?T          PROC    CODE16
exit:           B       exit?T
                ENDP


                END
