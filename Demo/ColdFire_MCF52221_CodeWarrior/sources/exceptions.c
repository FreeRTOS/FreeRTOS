/*
 * File:    exceptions.c
 * Purpose: Generic exception handling for ColdFire processors
 *
 */
#include "exceptions.h"
#include "startcf.h"
#include "support_common.h"
#include <ansi_parms.h>

#define REGISTER_ABI __REGABI__


extern void vPIT0InterruptHandler( void );
extern void vUART0InterruptHandler( void );
extern void vPortYieldISR( void );
extern void vFECISRHandler( void );

/***********************************************************************/
/*
 *  Set NO_PRINTF to 0 in order the exceptions.c interrupt handler
 *  to output messages to the standard io. 
 * 
 */
#define NO_PRINTF    1

#if NO_PRINTF
#define VECTORDISPLAY(MESSAGE)                    asm { nop; };
#define VECTORDISPLAY2(MESSAGE,MESSAGE2)          asm { nop; };
#define VECTORDISPLAY3(MESSAGE,MESSAGE2,MESSAGE3) asm { nop; };
#else
#include <stdio.h>
#define VECTORDISPLAY(MESSAGE1)                    printf(MESSAGE1);
#define VECTORDISPLAY2(MESSAGE1,MESSAGE2)          printf(MESSAGE1,MESSAGE2);
#define VECTORDISPLAY3(MESSAGE1,MESSAGE2,MESSAGE3) printf(MESSAGE1,MESSAGE2,MESSAGE3);
#endif

#ifdef __cplusplus
extern "C" {
#endif

extern unsigned long far _SP_INIT[];

/***********************************************************************/
/*
 * Handling of the TRK ColdFire libs (printf support in Debugger Terminal) 
 * 
 * To enable this support (setup by default in CONSOLE_RAM build target
 * if available):  
 * - Set CONSOLE_IO_SUPPORT to 1 in this file; this will enable 
 *   TrapHandler_printf for the trap #14 exception.
 *   (this is set by default to 1 in the ColdFire Pre-Processor panel for
 *   the CONSOLE_RAM build target)
 *
 * - Make sure the file:
 *   {Compiler}ColdFire_Support\msl\MSL_C\MSL_ColdFire\Src\console_io_cf.c
 *   is referenced from your project. 
 *
 * - Make sure that in the CF Exceptions panel the check box
 *   "46 TRAP #14 for Console I/O", in the "User Application Exceptions"
 *   area is set.
 *
 */
#ifndef CONSOLE_IO_SUPPORT
#define CONSOLE_IO_SUPPORT  0 
#endif

#if CONSOLE_IO_SUPPORT
asm void TrapHandler_printf(void) {
   HALT
   RTE
}
#endif                                                   

/***********************************************************************/
/*
 * This is the handler for all exceptions which are not common to all 
 * ColdFire Chips.  
 *
 * Called by mcf_exception_handler
 * 
 */
void derivative_interrupt(unsigned long vector)
{
   if (vector < 64 || vector > 192) {
      VECTORDISPLAY2("User Defined Vector #%d\n",vector);
   }
}

/***********************************************************************
 *
 * This is the exception handler for all  exceptions common to all 
 * chips ColdFire.  Most exceptions do nothing, but some of the more 
 * important ones are handled to some extent.
 *
 * Called by asm_exception_handler 
 *
 * The ColdFire family of processors has a simplified exception stack
 * frame that looks like the following:
 *
 *              3322222222221111 111111
 *              1098765432109876 5432109876543210
 *           8 +----------------+----------------+
 *             |         Program Counter         |
 *           4 +----------------+----------------+
 *             |FS/Fmt/Vector/FS|      SR        |
 *   SP -->  0 +----------------+----------------+
 *
 * The stack self-aligns to a 4-byte boundary at an exception, with
 * the FS/Fmt/Vector/FS field indicating the size of the adjustment
 * (SP += 0,1,2,3 bytes).
 *             31     28 27      26 25    18 17      16 15                                  0
 *           4 +---------------------------------------+------------------------------------+
 *             | Format | FS[3..2] | Vector | FS[1..0] |                 SR                 |
 *   SP -->  0 +---------------------------------------+------------------------------------+
 */ 
#define MCF5XXX_RD_SF_FORMAT(PTR)   \
   ((*((unsigned short *)(PTR)) >> 12) & 0x00FF)

#define MCF5XXX_RD_SF_VECTOR(PTR)   \
   ((*((unsigned short *)(PTR)) >>  2) & 0x00FF)

#define MCF5XXX_RD_SF_FS(PTR)    \
   ( ((*((unsigned short *)(PTR)) & 0x0C00) >> 8) | (*((unsigned short *)(PTR)) & 0x0003) )

#define MCF5XXX_SF_SR(PTR)    *(((unsigned short *)(PTR))+1)

#define MCF5XXX_SF_PC(PTR)    *((unsigned long *)(PTR)+1)

#define MCF5XXX_EXCEPTFMT     "%s -- PC = %#08X\n"


void mcf_exception_handler(void *framepointer) 
{
   volatile unsigned long exceptionStackFrame = (*(unsigned long *)(framepointer)); 
   volatile unsigned short stackFrameSR       = MCF5XXX_SF_SR(framepointer);  
   volatile unsigned short stackFrameWord     = (*(unsigned short *)(framepointer));  
   volatile unsigned long  stackFrameFormat   = (unsigned long)MCF5XXX_RD_SF_FORMAT(&stackFrameWord);
   volatile unsigned long  stackFrameFS       = (unsigned long)MCF5XXX_RD_SF_FS(&stackFrameWord);
   volatile unsigned long  stackFrameVector   = (unsigned long)MCF5XXX_RD_SF_VECTOR(&stackFrameWord);
   volatile unsigned long  stackFramePC       = MCF5XXX_SF_PC(framepointer);

   switch (stackFrameFormat)
   {
      case 4:
      case 5:
      case 6:
      case 7:
         break;
      default:
         VECTORDISPLAY3(MCF5XXX_EXCEPTFMT,"Illegal stack type", stackFramePC);
         break;
   }

   switch (stackFrameVector)
   {
   case 2:
      VECTORDISPLAY3(MCF5XXX_EXCEPTFMT, "Access Error", stackFramePC);
      switch (stackFrameFS)
      {
         case 4:
            VECTORDISPLAY("Error on instruction fetch\n");
            break;
         case 8:
            VECTORDISPLAY("Error on operand write\n");
            break;
         case 9:
            VECTORDISPLAY("Attempted write to write-protected space\n");
            break;
         case 12:
            VECTORDISPLAY("Error on operand read\n");
            break;
         default:
            VECTORDISPLAY("Reserved Fault Status Encoding\n");
            break;
      }
      break;
   case 3:
      VECTORDISPLAY3(MCF5XXX_EXCEPTFMT, "Address Error", stackFramePC);
      switch (stackFrameFS)
      {
         case 4:
            VECTORDISPLAY("Error on instruction fetch\n");
            break;
         case 8:
            VECTORDISPLAY("Error on operand write\n");
            break;
         case 9:
            VECTORDISPLAY("Attempted write to write-protected space\n");
            break;
         case 12:
            VECTORDISPLAY("Error on operand read\n");
            break;
         default:
            VECTORDISPLAY("Reserved Fault Status Encoding\n");
            break;
      }
      break;
   case 4:
      VECTORDISPLAY3(MCF5XXX_EXCEPTFMT, "Illegal instruction", stackFramePC);
      break;
   case 8:
      VECTORDISPLAY3(MCF5XXX_EXCEPTFMT, "Privilege violation", stackFramePC);
      break;
   case 9:
      VECTORDISPLAY3(MCF5XXX_EXCEPTFMT, "Trace Exception", stackFramePC);
      break;
   case 10:
      VECTORDISPLAY3(MCF5XXX_EXCEPTFMT, "Unimplemented A-Line Instruction", 	stackFramePC);
      break;
   case 11:
      VECTORDISPLAY3(MCF5XXX_EXCEPTFMT, "Unimplemented F-Line Instruction", 	stackFramePC);
      break;
   case 12:
      VECTORDISPLAY3(MCF5XXX_EXCEPTFMT, "Debug Interrupt", stackFramePC);
      break;
   case 14:
      VECTORDISPLAY3(MCF5XXX_EXCEPTFMT, "Format Error", stackFramePC);
      break;
   case 15:
      VECTORDISPLAY3(MCF5XXX_EXCEPTFMT, "Unitialized Interrupt", stackFramePC);
      break;
   case 24:
      VECTORDISPLAY3(MCF5XXX_EXCEPTFMT, "Spurious Interrupt", stackFramePC);
      break;
   case 25:
   case 26:
   case 27:
   case 28:
   case 29:
   case 30:
   case 31:
      VECTORDISPLAY2("Autovector interrupt level %d\n", stackFrameVector - 24);
      break;
   case 32:
   case 33:
   case 34:
   case 35:
   case 36:
   case 37:
   case 38:
   case 39:
   case 40:
   case 41:
   case 42:
   case 43:
   case 44:
   case 45:
   case 46:
   case 47:
      VECTORDISPLAY2("TRAP #%d\n", stackFrameVector - 32);
      break;
   case 5:
   case 6:
   case 7:
   case 13:
   case 16:
   case 17:
   case 18:
   case 19:
   case 20:
   case 21:
   case 22:
   case 23:
   case 48:
   case 49:
   case 50:
   case 51:
   case 52:
   case 53:
   case 54:
   case 55:
   case 56:
   case 57:
   case 58:
   case 59:
   case 60:
   case 61:
   case 62:
   case 63:
      VECTORDISPLAY2("Reserved: #%d\n", stackFrameVector);
      break;
   default:
      derivative_interrupt(stackFrameVector);
   break;
   }
}

#if REGISTER_ABI
asm void asm_exception_handler(void)
{
   link     a6,#0 
   lea     -20(sp), sp
   movem.l d0-d2/a0-a1, (sp)
   lea     24(sp),a0   /* A0 point to exception stack frame on the stack */
   jsr     mcf_exception_handler
   movem.l (sp), d0-d2/a0-a1
   lea     20(sp), sp
   unlk a6
   rte
}
#else
asm void asm_exception_handler(void)
{
   link     a6,#0 
   lea     -20(sp), sp
   movem.l d0-d2/a0-a1, (sp)
   pea     24(sp)   /* push exception frame address */
   jsr     mcf_exception_handler
   movem.l 4(sp), d0-d2/a0-a1
   lea     24(sp), sp
   unlk a6
   rte
}
#endif

typedef void (* vectorTableEntryType)(void);

#pragma define_section vectortable ".vectortable" far_absolute R

/* CF have 255 vector + SP_INIT in the vector table (256 entries)
*/  
__declspec(vectortable) vectorTableEntryType _vect[256] = {   /* Interrupt vector table */
   (vectorTableEntryType)__SP_AFTER_RESET,  /*   0 (0x000) Initial supervisor SP      */
   _startup,                        /*   1 (0x004) Initial PC                 */
   asm_exception_handler,           /*   2 (0x008) Access Error               */
   asm_exception_handler,           /*   3 (0x00C) Address Error              */
   asm_exception_handler,           /*   4 (0x010) Illegal Instruction        */
   asm_exception_handler,           /*   5 (0x014) Reserved                   */
   asm_exception_handler,           /*   6 (0x018) Reserved                   */
   asm_exception_handler,           /*   7 (0x01C) Reserved                   */
   asm_exception_handler,           /*   8 (0x020) Privilege Violation        */
   asm_exception_handler,           /*   9 (0x024) Trace                      */
   asm_exception_handler,           /*  10 (0x028) Unimplemented A-Line       */
   asm_exception_handler,           /*  11 (0x02C) Unimplemented F-Line       */
   asm_exception_handler,           /*  12 (0x030) Debug Interrupt            */
   asm_exception_handler,           /*  13 (0x034) Reserved                   */
   asm_exception_handler,           /*  14 (0x038) Format Error               */
   asm_exception_handler,           /*  15 (0x03C) Unitialized Int            */
   asm_exception_handler,           /*  16 (0x040) Reserved                   */
   asm_exception_handler,           /*  17 (0x044) Reserved                   */
   asm_exception_handler,           /*  18 (0x048) Reserved                   */
   asm_exception_handler,           /*  19 (0x04C) Reserved                   */
   asm_exception_handler,           /*  20 (0x050) Reserved                   */
   asm_exception_handler,           /*  21 (0x054) Reserved                   */
   asm_exception_handler,           /*  22 (0x058) Reserved                   */
   asm_exception_handler,           /*  23 (0x05C) Reserved                   */
   asm_exception_handler,           /*  24 (0x060) Spurious Interrupt         */
   asm_exception_handler,           /*  25 (0x064) Autovector Level 1         */
   asm_exception_handler,           /*  26 (0x068) Autovector Level 2         */
   asm_exception_handler,           /*  27 (0x06C) Autovector Level 3         */
   asm_exception_handler,           /*  28 (0x070) Autovector Level 4         */
   asm_exception_handler,           /*  29 (0x074) Autovector Level 5         */
   asm_exception_handler,           /*  30 (0x078) Autovector Level 6         */
   asm_exception_handler,           /*  31 (0x07C) Autovector Level 7         */
   asm_exception_handler,           /*  32 (0x080) TRAP #0                    */
   asm_exception_handler,           /*  33 (0x084) TRAP #1                    */
   asm_exception_handler,           /*  34 (0x088) TRAP #2                    */
   asm_exception_handler,           /*  35 (0x08C) TRAP #3                    */
   asm_exception_handler,           /*  36 (0x090) TRAP #4                    */
   asm_exception_handler,           /*  37 (0x094) TRAP #5                    */
   asm_exception_handler,           /*  38 (0x098) TRAP #6                    */
   asm_exception_handler,           /*  39 (0x09C) TRAP #7                    */
   asm_exception_handler,           /*  40 (0x0A0) TRAP #8                    */
   asm_exception_handler,           /*  41 (0x0A4) TRAP #9                    */
   asm_exception_handler,           /*  42 (0x0A8) TRAP #10                   */
   asm_exception_handler,           /*  43 (0x0AC) TRAP #11                   */
   asm_exception_handler,           /*  44 (0x0B0) TRAP #12                   */
   asm_exception_handler,           /*  45 (0x0B4) TRAP #13                   */
#if CONSOLE_IO_SUPPORT   
   TrapHandler_printf,              /*  46 (0x0B8) TRAP #14                   */
#else
   asm_exception_handler,           /*  46 (0x0B8) TRAP #14                   */
#endif   
   asm_exception_handler,           /*  47 (0x0BC) TRAP #15                   */
   asm_exception_handler,           /*  48 (0x0C0) Reserved                   */
   asm_exception_handler,           /*  49 (0x0C4) Reserved                   */
   asm_exception_handler,           /*  50 (0x0C8) Reserved                   */
   asm_exception_handler,           /*  51 (0x0CC) Reserved                   */
   asm_exception_handler,           /*  52 (0x0D0) Reserved                   */
   asm_exception_handler,           /*  53 (0x0D4) Reserved                   */
   asm_exception_handler,           /*  54 (0x0D8) Reserved                   */
   asm_exception_handler,           /*  55 (0x0DC) Reserved                   */
   asm_exception_handler,           /*  56 (0x0E0) Reserved                   */
   asm_exception_handler,           /*  57 (0x0E4) Reserved                   */
   asm_exception_handler,           /*  58 (0x0E8) Reserved                   */
   asm_exception_handler,           /*  59 (0x0EC) Reserved                   */
   asm_exception_handler,           /*  60 (0x0F0) Reserved                   */
   asm_exception_handler,           /*  61 (0x0F4) Reserved                   */
   asm_exception_handler,           /*  62 (0x0F8) Reserved                   */
   asm_exception_handler,           /*  63 (0x0FC) Reserved                   */
   asm_exception_handler,           /*  64 (0x100) Device-specific interrupts */
   asm_exception_handler,           /*  65 (0x104) Device-specific interrupts */
   asm_exception_handler,           /*  66 (0x108) Device-specific interrupts */
   asm_exception_handler,           /*  67 (0x10C) Device-specific interrupts */
   asm_exception_handler,           /*  68 (0x110) Device-specific interrupts */
   asm_exception_handler,           /*  69 (0x114) Device-specific interrupts */
   asm_exception_handler,           /*  70 (0x118) Device-specific interrupts */
   asm_exception_handler,           /*  71 (0x11C) Device-specific interrupts */
   asm_exception_handler,           /*  72 (0x120) Device-specific interrupts */
   asm_exception_handler,           /*  73 (0x124) Device-specific interrupts */
   asm_exception_handler,           /*  74 (0x128) Device-specific interrupts */
   asm_exception_handler,           /*  75 (0x12C) Device-specific interrupts */
   asm_exception_handler,           /*  76 (0x130) Device-specific interrupts */
   vUART0InterruptHandler,          /*  77 (0x134) Device-specific interrupts */
   asm_exception_handler,           /*  78 (0x138) Device-specific interrupts */
   asm_exception_handler,           /*  79 (0x13C) Device-specific interrupts */
   vPortYieldISR,           		/*  80 (0x140) Device-specific interrupts */
   asm_exception_handler,           /*  81 (0x144) Device-specific interrupts */
   asm_exception_handler,           /*  82 (0x148) Device-specific interrupts */
   asm_exception_handler,           /*  83 (0x14C) Device-specific interrupts */
   asm_exception_handler,           /*  84 (0x150) Device-specific interrupts */
   asm_exception_handler,           /*  85 (0x154) Device-specific interrupts */
   asm_exception_handler,           /*  86 (0x158) Device-specific interrupts */
   asm_exception_handler,           /*  87 (0x15C) Device-specific interrupts */
   asm_exception_handler,           /*  88 (0x160) Device-specific interrupts */
   asm_exception_handler,           /*  89 (0x164) Device-specific interrupts */
   asm_exception_handler,           /*  90 (0x168) Device-specific interrupts */
   asm_exception_handler,           /*  91 (0x16C) Device-specific interrupts */
   asm_exception_handler,           /*  92 (0x170) Device-specific interrupts */
   asm_exception_handler,           /*  93 (0x174) Device-specific interrupts */
   asm_exception_handler,           /*  94 (0x178) Device-specific interrupts */
   asm_exception_handler,           /*  95 (0x17C) Device-specific interrupts */
   asm_exception_handler,           /*  96 (0x180) Level 1 software interrupt */
   asm_exception_handler,           /*  97 (0x184) Level 2 software interrupt */
   asm_exception_handler,           /*  98 (0x188) Level 3 software interrupt */
   asm_exception_handler,           /*  99 (0x18C) Level 4 software interrupt */
   asm_exception_handler,           /* 100 (0x190) Level 5 software interrupt */
   asm_exception_handler,           /* 101 (0x194) Level 6 software interrupt */
   asm_exception_handler,           /* 102 (0x198) Level 7 software interrupt */
   asm_exception_handler,           /* 103 (0x19C) Reserved                   */
   asm_exception_handler,           /* 104 (0x1A0) Reserved                   */
   asm_exception_handler,           /* 105 (0x1A4) Reserved                   */
   asm_exception_handler,           /* 106 (0x1A8) Reserved                   */
   asm_exception_handler,           /* 107 (0x___) Reserved                   */
   asm_exception_handler,           /* 108 (0x___) Reserved                   */
   asm_exception_handler,           /* 109 (0x___) Reserved                   */
   asm_exception_handler,           /* 110 (0x___) Reserved                   */
   asm_exception_handler,           /* 111 (0x___) Reserved                   */
   asm_exception_handler,           /* 112 (0x___) Reserved                   */
   asm_exception_handler,           /* 113 (0x___) Reserved                   */
   asm_exception_handler,           /* 114 (0x___) Reserved                   */
   asm_exception_handler,           /* 115 (0x___) Reserved                   */
   asm_exception_handler,           /* 116 (0x___) Reserved                   */
   asm_exception_handler,           /* 117 (0x___) Reserved                   */
   asm_exception_handler,           /* 118 (0x___) Reserved                   */
   vPIT0InterruptHandler,           /* 119 (0x___) Reserved                   */
   asm_exception_handler,           /* 120 (0x___) Reserved                   */
   asm_exception_handler,           /* 121 (0x___) Reserved                   */
   asm_exception_handler,           /* 122 (0x___) Reserved                   */
   asm_exception_handler,           /* 123 (0x___) Reserved                   */
   asm_exception_handler,           /* 124 (0x___) Reserved                   */
   asm_exception_handler,           /* 125 (0x___) Reserved                   */
   asm_exception_handler,           /* 126 (0x___) Reserved                   */
   asm_exception_handler,           /* 127 (0x___) Reserved                   */
   asm_exception_handler,           /* 128 (0x___) Reserved                   */
   asm_exception_handler,           /* 129 (0x___) Reserved                   */
   asm_exception_handler,           /* 130 (0x___) Reserved                   */
   asm_exception_handler,           /* 131 (0x___) Reserved                   */
   asm_exception_handler,           /* 132 (0x___) Reserved                   */
   asm_exception_handler,           /* 133 (0x___) Reserved                   */
   asm_exception_handler,           /* 134 (0x___) Reserved                   */
   asm_exception_handler,           /* 135 (0x___) Reserved                   */
   asm_exception_handler,           /* 136 (0x___) Reserved                   */
   asm_exception_handler,           /* 137 (0x___) Reserved                   */
   asm_exception_handler,           /* 138 (0x___) Reserved                   */
   asm_exception_handler,           /* 139 (0x___) Reserved                   */
   asm_exception_handler,           /* 140 (0x___) Reserved                   */
   asm_exception_handler,           /* 141 (0x___) Reserved                   */
   asm_exception_handler,           /* 142 (0x___) Reserved                   */
   asm_exception_handler,           /* 143 (0x___) Reserved                   */
   asm_exception_handler,           /* 144 (0x___) Reserved                   */
   asm_exception_handler,           /* 145 (0x___) Reserved                   */
   asm_exception_handler,           /* 146 (0x___) Reserved                   */
   asm_exception_handler,           /* 147 (0x___) Reserved                   */
   asm_exception_handler,           /* 148 (0x___) Reserved                   */
   asm_exception_handler,           /* 149 (0x___) Reserved                   */
   asm_exception_handler,           /* 150 (0x___) Reserved                   */
   asm_exception_handler,           /* 151 (0x___) Reserved                   */
   asm_exception_handler,           /* 152 (0x___) Reserved                   */
   asm_exception_handler,           /* 153 (0x___) Reserved                   */
   asm_exception_handler,           /* 154 (0x___) Reserved                   */
   asm_exception_handler,           /* 155 (0x___) Reserved                   */
   asm_exception_handler,           /* 156 (0x___) Reserved                   */
   asm_exception_handler,           /* 157 (0x___) Reserved                   */
   asm_exception_handler,           /* 158 (0x___) Reserved                   */
   asm_exception_handler,           /* 159 (0x___) Reserved                   */
   asm_exception_handler,           /* 160 (0x___) Reserved                   */
   asm_exception_handler,           /* 161 (0x___) Reserved                   */
   asm_exception_handler,           /* 162 (0x___) Reserved                   */
   asm_exception_handler,           /* 163 (0x___) Reserved                   */
   asm_exception_handler,           /* 164 (0x___) Reserved                   */
   asm_exception_handler,           /* 165 (0x___) Reserved                   */
   asm_exception_handler,           /* 166 (0x___) Reserved                   */
   asm_exception_handler,           /* 167 (0x___) Reserved                   */
   asm_exception_handler,           /* 168 (0x___) Reserved                   */
   asm_exception_handler,           /* 169 (0x___) Reserved                   */
   asm_exception_handler,           /* 170 (0x___) Reserved                   */
   asm_exception_handler,           /* 171 (0x___) Reserved                   */
   asm_exception_handler,           /* 172 (0x___) Reserved                   */
   asm_exception_handler,           /* 173 (0x___) Reserved                   */
   asm_exception_handler,           /* 174 (0x___) Reserved                   */
   asm_exception_handler,           /* 175 (0x___) Reserved                   */
   asm_exception_handler,           /* 176 (0x___) Reserved                   */
   asm_exception_handler,           /* 177 (0x___) Reserved                   */
   asm_exception_handler,           /* 178 (0x___) Reserved                   */
   asm_exception_handler,           /* 179 (0x___) Reserved                   */
   asm_exception_handler,           /* 180 (0x___) Reserved                   */
   asm_exception_handler,           /* 181 (0x___) Reserved                   */
   asm_exception_handler,           /* 182 (0x___) Reserved                   */
   asm_exception_handler,           /* 183 (0x___) Reserved                   */
   asm_exception_handler,           /* 184 (0x___) Reserved                   */
   asm_exception_handler,           /* 185 (0x___) Reserved                   */
   asm_exception_handler,           /* 186 (0x___) Reserved                   */
   asm_exception_handler,           /* 187 (0x___) Reserved                   */
   asm_exception_handler,           /* 188 (0x___) Reserved                   */
   asm_exception_handler,           /* 189 (0x___) Reserved                   */
   asm_exception_handler,           /* 190 (0x___) Reserved                   */
   asm_exception_handler,           /* 191 (0x___) Reserved                   */
   asm_exception_handler,           /* 192 (0x___) Reserved                   */
   asm_exception_handler,           /* 193 (0x___) Reserved                   */
   asm_exception_handler,           /* 194 (0x___) Reserved                   */
   asm_exception_handler,           /* 195 (0x___) Reserved                   */
   asm_exception_handler,           /* 196 (0x___) Reserved                   */
   asm_exception_handler,           /* 197 (0x___) Reserved                   */
   asm_exception_handler,           /* 198 (0x___) Reserved                   */
   asm_exception_handler,           /* 199 (0x___) Reserved                   */
   asm_exception_handler,           /* 200 (0x___) Reserved                   */
   asm_exception_handler,           /* 201 (0x___) Reserved                   */
   asm_exception_handler,           /* 202 (0x___) Reserved                   */
   asm_exception_handler,           /* 203 (0x___) Reserved                   */
   asm_exception_handler,           /* 204 (0x___) Reserved                   */
   asm_exception_handler,           /* 205 (0x___) Reserved                   */
   asm_exception_handler,           /* 206 (0x___) Reserved                   */
   asm_exception_handler,           /* 207 (0x___) Reserved                   */
   asm_exception_handler,           /* 208 (0x___) Reserved                   */
   asm_exception_handler,           /* 209 (0x___) Reserved                   */
   asm_exception_handler,           /* 210 (0x___) Reserved                   */
   asm_exception_handler,           /* 211 (0x___) Reserved                   */
   asm_exception_handler,           /* 212 (0x___) Reserved                   */
   asm_exception_handler,           /* 213 (0x___) Reserved                   */
   asm_exception_handler,           /* 214 (0x___) Reserved                   */
   asm_exception_handler,           /* 215 (0x___) Reserved                   */
   asm_exception_handler,           /* 216 (0x___) Reserved                   */
   asm_exception_handler,           /* 217 (0x___) Reserved                   */
   asm_exception_handler,           /* 218 (0x___) Reserved                   */
   asm_exception_handler,           /* 219 (0x___) Reserved                   */
   asm_exception_handler,           /* 220 (0x___) Reserved                   */
   asm_exception_handler,           /* 221 (0x___) Reserved                   */
   asm_exception_handler,           /* 222 (0x___) Reserved                   */
   asm_exception_handler,           /* 223 (0x___) Reserved                   */
   asm_exception_handler,           /* 224 (0x___) Reserved                   */
   asm_exception_handler,           /* 225 (0x___) Reserved                   */
   asm_exception_handler,           /* 226 (0x___) Reserved                   */
   asm_exception_handler,           /* 227 (0x___) Reserved                   */
   asm_exception_handler,           /* 228 (0x___) Reserved                   */
   asm_exception_handler,           /* 229 (0x___) Reserved                   */
   asm_exception_handler,           /* 230 (0x___) Reserved                   */
   asm_exception_handler,           /* 231 (0x___) Reserved                   */
   asm_exception_handler,           /* 232 (0x___) Reserved                   */
   asm_exception_handler,           /* 233 (0x___) Reserved                   */
   asm_exception_handler,           /* 234 (0x___) Reserved                   */
   asm_exception_handler,           /* 235 (0x___) Reserved                   */
   asm_exception_handler,           /* 236 (0x___) Reserved                   */
   asm_exception_handler,           /* 237 (0x___) Reserved                   */
   asm_exception_handler,           /* 238 (0x___) Reserved                   */
   asm_exception_handler,           /* 239 (0x___) Reserved                   */
   asm_exception_handler,           /* 240 (0x___) Reserved                   */
   asm_exception_handler,           /* 241 (0x___) Reserved                   */
   asm_exception_handler,           /* 242 (0x___) Reserved                   */
   asm_exception_handler,           /* 243 (0x___) Reserved                   */
   asm_exception_handler,           /* 244 (0x___) Reserved                   */
   asm_exception_handler,           /* 245 (0x___) Reserved                   */
   asm_exception_handler,           /* 246 (0x___) Reserved                   */
   asm_exception_handler,           /* 247 (0x___) Reserved                   */
   asm_exception_handler,           /* 248 (0x___) Reserved                   */
   asm_exception_handler,           /* 249 (0x___) Reserved                   */
   asm_exception_handler,           /* 250 (0x___) Reserved                   */
   asm_exception_handler,           /* 251 (0x___) Reserved                   */
   asm_exception_handler,           /* 252 (0x___) Reserved                   */
   asm_exception_handler,           /* 253 (0x___) Reserved                   */
   asm_exception_handler,           /* 254 (0x___) Reserved                   */
   asm_exception_handler,           /* 255 (0x___) Reserved                   */ 
};

/********************************************************************
 * MCF5xxx ASM utility functions
 */
asm void mcf5xxx_wr_vbr(unsigned long) { /* Set VBR */
	move.l	4(SP),D0
    movec d0,VBR 
	nop
	rts	
}	

/********************************************************************
 * MCF5xxx startup copy functions:
 *
 * Set VBR and performs RAM vector table initializatiom.
 * The following symbol should be defined in the lcf:
 * __VECTOR_RAM
 *
 * _vect is the start of the exception table in the code
 * In case _vect address is different from __VECTOR_RAM,
 * the vector table is copied from _vect to __VECTOR_RAM.
 * In any case VBR is set to __VECTOR_RAM.
 */ 
void initialize_exceptions(void)
{
#if 0
	/*
	 * Memory map definitions from linker command files used by mcf5xxx_startup
	 */

	register uint32 n;
    
	/* 
     * Copy the vector table to RAM 
     */
	if (__VECTOR_RAM != (unsigned long*)_vect)
	{
		for (n = 0; n < 256; n++)
			__VECTOR_RAM[n] = (unsigned long)_vect[n];
	}
	mcf5xxx_wr_vbr((unsigned long)__VECTOR_RAM);
#endif

	mcf5xxx_wr_vbr((unsigned long)_vect);
}

#ifdef __cplusplus
}
#endif
