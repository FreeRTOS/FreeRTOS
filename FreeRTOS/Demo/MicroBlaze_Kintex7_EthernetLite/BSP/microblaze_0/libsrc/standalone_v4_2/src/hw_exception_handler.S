/******************************************************************************
*
* Copyright (C) 2004 - 2014 Xilinx, Inc.  All rights reserved.
*
* Permission is hereby granted, free of charge, to any person obtaining a copy
* of this software and associated documentation files (the "Software"), to deal
* in the Software without restriction, including without limitation the rights
* to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
* copies of the Software, and to permit persons to whom the Software is
* furnished to do so, subject to the following conditions:
*
* The above copyright notice and this permission notice shall be included in
* all copies or substantial portions of the Software.
*
* Use of the Software is limited solely to applications:
* (a) running on a Xilinx device, or
* (b) that interact with a Xilinx device through a bus or interconnect.
*
* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
* XILINX  BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
* WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
* OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
* SOFTWARE.
*
* Except as contained in this notice, the name of the Xilinx shall not be used
* in advertising or otherwise to promote the sale, use or other dealings in
* this Software without prior written authorization from Xilinx.
*
******************************************************************************/
/*
 * Microblaze HW Exception Handler
 * - Non self-modifying exception handler for the following exception conditions
 *   - Unalignment
 *   - Instruction bus error
 *   - Data bus error
 *   - Illegal instruction opcode
 *   - Divide-by-zero
 *   - Stack protection violation
 */

#include "microblaze_exceptions_g.h"
#include "xparameters.h"

/* Helpful Macros */
#define EX_HANDLER_STACK_SIZ            (4*21)
#define RMSR_OFFSET                     (20 * 4)
#define R17_OFFSET                      (0)    
#define REG_OFFSET(regnum)              (4 * (regnum + 1))
#define NUM_TO_REG(num)                 r ## num

#define R3_TO_STACK(regnum)             swi     r3, r1, REG_OFFSET(regnum)
#define R3_FROM_STACK(regnum)           lwi     r3, r1, REG_OFFSET(regnum)      

#define PUSH_REG(regnum)                swi     NUM_TO_REG(regnum), r1, REG_OFFSET(regnum)
#define POP_REG(regnum)                 lwi     NUM_TO_REG(regnum), r1, REG_OFFSET(regnum)
        
/* Uses r5 */
#define PUSH_MSR                                                                \
        mfs     r5, rmsr;                                                       \
        swi     r5, r1, RMSR_OFFSET;
   
#define PUSH_MSR_AND_ENABLE_EXC                                                 \
        mfs     r5, rmsr;                                                       \
        swi     r5, r1, RMSR_OFFSET;                                            \
        ori     r5, r5, 0x100;                          /* Turn ON the EE bit*/ \
        mts     rmsr, r5;
    
/* Uses r5 */
#define POP_MSR                                                                 \
        lwi     r5, r1, RMSR_OFFSET;                                            \
        mts     rmsr, r5;       

/* Push r17 */    
#define PUSH_R17                swi     r17, r1, R17_OFFSET
/* Pop r17 */        
#define POP_R17                 lwi     r17, r1, R17_OFFSET
       
#define LWREG_NOP                                                               \
        bri     ex_handler_unhandled;                                           \
        nop;

#define SWREG_NOP                                                               \
        bri     ex_handler_unhandled;                                           \
        nop;        
        
/* r3 is the source */
#define R3_TO_LWREG_V(regnum)                                                   \
        R3_TO_STACK (regnum);                                                   \
        bri     ex_handler_done; 

/* r3 is the source */
#define R3_TO_LWREG(regnum)                                                     \
        or      NUM_TO_REG (regnum), r0, r3;                                    \
        bri     ex_handler_done;                        

/* r3 is the target */          
#define SWREG_TO_R3_V(regnum)                                                   \
        R3_FROM_STACK (regnum);                                                 \
        bri     ex_sw_tail;                                                     
                
/* r3 is the target */  
#define SWREG_TO_R3(regnum)                                                     \
        or      r3, r0, NUM_TO_REG (regnum);                                    \
        bri     ex_sw_tail; 

/* regnum is the source */  
#define FP_EX_OPB_SAVE(regnum)                                                  \
        swi     NUM_TO_REG (regnum), r0, mb_fpex_op_b;                          \
        nop;                                                                    \
        bri     handle_fp_ex_opa; 

/* regnum is the source */  
#define FP_EX_OPB_SAVE_V(regnum)                                                \
        R3_FROM_STACK (regnum);                                                 \
        swi     r3, r0, mb_fpex_op_b;                                           \
        bri     handle_fp_ex_opa; 
        
/* regnum is the source */  
#define FP_EX_OPA_SAVE(regnum)                                                  \
        swi     NUM_TO_REG (regnum), r0, mb_fpex_op_a;                          \
        nop;                                                                    \
        bri     handle_fp_ex_done; 
    
/* regnum is the source */  
#define FP_EX_OPA_SAVE_V(regnum)                                                \
        R3_FROM_STACK (regnum);                                                 \
        swi     r3, r0, mb_fpex_op_a;                                           \
        bri     handle_fp_ex_done; 

#define FP_EX_UNHANDLED                                                         \
        bri     fp_ex_unhandled;                                                \
        nop;                                                                    \
        nop;

/* ESR masks */    
#define ESR_EXC_MASK            0x0000001F
#define ESR_REG_MASK            0x000003E0
#define ESR_LW_SW_MASK          0x00000400
#define ESR_WORD_MASK           0x00000800
#define ESR_DS_MASK             0x00001000
        
/* Extern declarations */
.extern XNullHandler


#ifdef MICROBLAZE_EXCEPTIONS_ENABLED                    /* If exceptions are enabled in the processor */
                
/* 
 * hw_exception_handler - Handler for unaligned exceptions
 * Exception handler notes:     
 * - Does not handle exceptions other than unaligned exceptions
 * - Does not handle exceptions during load into r17, r1, r0.
 * - Does not handle exceptions during store from r17 (cannot be done) and r1 (slows down common case)
 *
 *  Relevant register structures
 *        
 *  EAR - |----|----|----|----|----|----|----|----|      
 *      - <  ##   32 bit faulting address     ##  >      
 *       
 *  ESR - |----|----|----|----|----| - | - |-----|-----| 
 *      -                            W   S   REG   EXC
 *
 *        
 * STACK FRAME STRUCTURE
 * ---------------------
 *
 *      +-------------+         + 0
 *      |     r17     |
 *      +-------------+         + 4                    
 *      |  Args for   |
 *      |  next func  |
 *      +-------------+         + 8
 *      |     r1      |
 *      |      .      |
 *      |      .      |
 *      |      .      |
 *      |      .      |
 *      |     r18     |
 *      +-------------+         + 80
 *      |     MSR     |         
 *      +-------------+         + 84    
 *      |      .      | 
 *      |      .      |           
 */        

         
.global _hw_exception_handler                               
.section .text                                          
.align 2
.ent _hw_exception_handler
.type _hw_exception_handler, @function    
_hw_exception_handler:                      

#if defined(XPAR_MICROBLAZE_USE_STACK_PROTECTION) && (XPAR_MICROBLAZE_USE_STACK_PROTECTION == 1)
	/* Immediately halt for stack protection violation exception without using any stack       */
	swi	r3, r0, mb_sp_save_r3;			/* Save temporary register                 */
	mfs	r3, resr;				/* Extract ESR[DS]                         */
	andi	r3, r3, ESR_EXC_MASK;
	xori	r3, r3, 0x7;				/* Check for stack protection violation    */
	bnei	r3, ex_handler_not_sp_violation;
ex_handler_sp_violation:
	bri	0;					/* Halt here if stack protection violation */
ex_handler_not_sp_violation:
	lwi	r3, r0, mb_sp_save_r3;			/* Restore temporary register              */
#endif /* defined(XPAR_MICROBLAZE_USE_STACK_PROTECTION) && (XPAR_MICROBLAZE_USE_STACK_PROTECTION == 1) */

        addik   r1, r1, -(EX_HANDLER_STACK_SIZ);        /* Create stack frame */
        PUSH_REG(3);              
        PUSH_REG(4);              
        PUSH_REG(5);              
        PUSH_REG(6);
#ifdef MICROBLAZE_CAN_HANDLE_EXCEPTIONS_IN_DELAY_SLOTS
        mfs     r6, resr;
        andi    r6, r6, ESR_DS_MASK;
        beqi    r6, ex_handler_no_ds;
        mfs     r17, rbtr;
ex_handler_no_ds:       
#endif
        PUSH_R17;    
        PUSH_MSR_AND_ENABLE_EXC;                        /* Exceptions enabled here. This will allow nested exceptions */
                
        mfs     r3, resr;    
        andi    r5, r3, ESR_EXC_MASK;                   /* Extract ESR[EXC]                     */
#ifndef NO_UNALIGNED_EXCEPTIONS
        xori    r6, r5, 1;                              /* 00001 = Unaligned Exception          */  
        bnei    r6, handle_ex_regular;               

        la      r4, r0, MB_ExceptionVectorTable;        /* Check if user has registered an unaligned exception handler */
        lwi     r4, r4, 8; 
        la      r6, r0, XNullHandler;                   /* If exceptionvectortable entry is still XNullHandler, use */
        xor     r6, r4, r6;                             /* the default exception handler */
        beqi    r6, handle_unaligned_ex ;           
    
handle_ex_regular:      
#endif  /* ! NO_UNALIGNED_EXCEPTIONS */

#if defined (MICROBLAZE_FP_EXCEPTION_ENABLED) && defined (MICROBLAZE_FP_EXCEPTION_DECODE)
        xori   r6, r5, 6;                               /* 00110 = FPU exception */
        beqi   r6, handle_fp_ex;                        /* Go and decode the FP exception */
#endif  /* defined (MICROBLAZE_FP_EXCEPTION_ENABLED) && defined (MICROBLAZE_FP_EXCEPTION_DECODE) */

handle_other_ex:                                        /* Handle Other exceptions here         */        
        ori     r6, r0, 20; 
        cmp     r6, r5, r6;                             /* >= 20 are exceptions we do not handle. */
        blei    r6, ex_handler_unhandled;

        ori     r6, r0, 7;
        cmp     r6, r5, r6;                             /* Convert MMU exception indices into an ordinal of 7 */
        bgti    r6, handle_other_ex_tail;
        ori     r5, r0, 0x7; 
                
handle_other_ex_tail:       
        PUSH_REG(7);                                    /* Save other volatiles before we make procedure calls below   */
        PUSH_REG(8);             
        PUSH_REG(9);              
        PUSH_REG(10);             
        PUSH_REG(11);             
        PUSH_REG(12);
        PUSH_REG(15);
        PUSH_REG(18);        

        la      r4, r0, MB_ExceptionVectorTable;        /* Load the Exception vector table base address         */
        addk    r7, r5, r5;                             /* Calculate exception vector offset = r5 * 8           */
        addk    r7, r7, r7;         
        addk    r7, r7, r7;
        addk    r7, r7, r4;                             /* Get pointer to exception vector               */
        lwi     r5, r7, 4;                              /* Load argument to exception handler from table */
        lw      r7, r7, r0;                             /* Load vector itself here                       */

        brald   r15, r7;                                /* Branch to handler                             */
        nop;
        
        POP_REG(7);                                     /* Restore other volatiles */
        POP_REG(8);              
        POP_REG(9);               
        POP_REG(10);              
        POP_REG(11);              
        POP_REG(12);
        POP_REG(15);
        POP_REG(18);        

        bri     ex_handler_done;                        /* Complete exception handling       */        

#ifndef NO_UNALIGNED_EXCEPTIONS
handle_unaligned_ex:    
        andi    r6, r3, ESR_REG_MASK;                   /* Mask and extract the register operand */
        srl     r6, r6;                                 /* r6 >> 5 */
        srl     r6, r6;
        srl     r6, r6;
        srl     r6, r6;
        srl     r6, r6;
        sbi     r6, r0, ex_reg_op;                      /* Store the register operand in a temporary location */
        mfs     r4, rear;                              
        andi    r6, r3, ESR_LW_SW_MASK;                 /* Extract ESR[S]               */
        bnei    r6, ex_sw;
ex_lw:  
        andi    r6, r3, ESR_WORD_MASK;                  /* Extract ESR[W]               */
        beqi    r6, ex_lhw;
        lbui    r5, r4, 0;                              /* Exception address in r4      */
        sbi     r5, r0, ex_tmp_data_loc_0;              /* Load a word, byte-by-byte from destination address and save it in tmp space  */              
        lbui    r5, r4, 1;
        sbi     r5, r0, ex_tmp_data_loc_1;
        lbui    r5, r4, 2;
        sbi     r5, r0, ex_tmp_data_loc_2;
        lbui    r5, r4, 3;
        sbi     r5, r0, ex_tmp_data_loc_3;
        lwi     r3, r0, ex_tmp_data_loc_0;              /* Get the destination register value into r3   */
        bri     ex_lw_tail;      
ex_lhw: 
        lbui    r5, r4, 0;                              /* Exception address in r4                      */
        sbi     r5, r0, ex_tmp_data_loc_0;              /* Load a half-word, byte-by-byte from destination address and save it in tmp space */  
        lbui    r5, r4, 1;                               
        sbi     r5, r0, ex_tmp_data_loc_1;
        lhui    r3, r0, ex_tmp_data_loc_0;              /* Get the destination register value into r3   */
ex_lw_tail:
        lbui    r5, r0, ex_reg_op;                      /* Get the destination register number into r5  */
        la      r6, r0, lw_table;                       /* Form load_word jump table offset (lw_table + (8 * regnum)) */
        addk    r5, r5, r5;                              
        addk    r5, r5, r5;
        addk    r5, r5, r5;
        addk    r5, r5, r6;
        bra     r5;
ex_lw_end:                                              /* Exception handling of load word, ends */
ex_sw:          
        lbui    r5, r0, ex_reg_op;                      /* Get the destination register number into r5 */
        la      r6, r0, sw_table;                       /* Form store_word jump table offset (sw_table + (8 * regnum)) */
        add     r5, r5, r5;                             
        add     r5, r5, r5;
        add     r5, r5, r5;
        add     r5, r5, r6;
        bra     r5;
ex_sw_tail:             
        mfs     r6, resr;                               
        andi    r6, r6, ESR_WORD_MASK;                  /* Extract ESR[W]       */
        beqi    r6, ex_shw;
        swi     r3, r0, ex_tmp_data_loc_0;
        lbui    r3, r0, ex_tmp_data_loc_0;              /* Store the word, byte-by-byte into destination address                */
        sbi     r3, r4, 0;
        lbui    r3, r0, ex_tmp_data_loc_1;
        sbi     r3, r4, 1;
        lbui    r3, r0, ex_tmp_data_loc_2;
        sbi     r3, r4, 2;       
        lbui    r3, r0, ex_tmp_data_loc_3;
        sbi     r3, r4, 3;                      
        bri     ex_handler_done;
ex_shw:         
        swi     r3, r0, ex_tmp_data_loc_0;              /* Store the lower half-word, byte-by-byte into destination address      */
	
#ifdef __LITTLE_ENDIAN__
        lbui    r3, r0, ex_tmp_data_loc_0;
#else
        lbui    r3, r0, ex_tmp_data_loc_2;
#endif
        sbi     r3, r4, 0;
#ifdef __LITTLE_ENDIAN__
        lbui    r3, r0, ex_tmp_data_loc_1;
#else
        lbui    r3, r0, ex_tmp_data_loc_3;
#endif
        sbi     r3, r4, 1;
ex_sw_end:                                              /* Exception handling of store word, ends. */
        bri     ex_handler_done; 
#endif  /* !NO_UNALIGNED_EXCEPTIONS */

#if defined (MICROBLAZE_FP_EXCEPTION_ENABLED) && defined (MICROBLAZE_FP_EXCEPTION_DECODE)
handle_fp_ex:
        addik   r3, r17, -4;                            /* r17 contains (addr of exception causing FP instruction + 4) */
        lw      r4, r0, r3;                             /* We might find ourselves in a spot here. Unguaranteed load   */

handle_fp_ex_opb:
        la      r6, r0, fp_table_opb;                   /* Decode opB and store its value in mb_fpex_op_b */
        srl     r4, r4; 
        srl     r4, r4; 
        srl     r4, r4; 
        srl     r4, r4; 
        srl     r4, r4; 
        srl     r4, r4; 
        srl     r4, r4; 
        srl     r4, r4; 
        srl     r4, r4; 
        srl     r4, r4; 
        srl     r4, r4; 
        andi    r3, r4, 0x1F;
        add     r3, r3, r3;                             /* Calculate (fp_table_opb + (regno * 12)) in r5 */
        add     r3, r3, r3;
        add     r5, r3, r3;
        add     r5, r5, r3;
        add     r5, r5, r6;
        bra     r5; 

handle_fp_ex_opa:
        la      r6, r0, fp_table_opa;                   /* Decode opA and store its value in mb_fpex_op_a */
        srl     r4, r4; 
        srl     r4, r4; 
        srl     r4, r4; 
        srl     r4, r4; 
        srl     r4, r4; 
        andi    r3, r4, 0x1F;
        add     r3, r3, r3;                             /* Calculate (fp_table_opb + (regno * 12)) in r5 */
        add     r3, r3, r3;
        add     r5, r3, r3;
        add     r5, r5, r3;
        add     r5, r5, r6;
        bra     r5; 

handle_fp_ex_done:
        ori     r5, r0, 6;                              /* Set exception number back to 6 */
        bri     handle_other_ex_tail; 
    
fp_ex_unhandled:    
        bri     0; 
#endif  /* defined (MICROBLAZE_FP_EXCEPTION_ENABLED) && defined (MICROBLAZE_FP_EXCEPTION_DECODE) */
                     
ex_handler_done:
        POP_R17;
        POP_MSR;
        POP_REG(3);               
        POP_REG(4);               
        POP_REG(5);               
        POP_REG(6); 

        rted    r17, 0
        addik   r1, r1, (EX_HANDLER_STACK_SIZ);         /* Restore stack frame  */        
ex_handler_unhandled:   
        bri 0                                           /* UNHANDLED. TRAP HERE */                                                 
.end _hw_exception_handler  

#ifndef NO_UNALIGNED_EXCEPTIONS        

/* 
 * hw_exception_handler Jump Table
 * - Contains code snippets for each register that caused the unaligned exception.
 * - Hence exception handler is NOT self-modifying
 * - Separate table for load exceptions and store exceptions.
 * - Each table is of size:   (8 * 32) = 256 bytes
 */
                
.section .text
.align  4
lw_table:
lw_r0:  R3_TO_LWREG   (0); 
lw_r1:  LWREG_NOP;
lw_r2:  R3_TO_LWREG   (2);
lw_r3:  R3_TO_LWREG_V (3);
lw_r4:  R3_TO_LWREG_V (4);
lw_r5:  R3_TO_LWREG_V (5);
lw_r6:  R3_TO_LWREG_V (6);
lw_r7:  R3_TO_LWREG   (7);
lw_r8:  R3_TO_LWREG   (8);
lw_r9:  R3_TO_LWREG   (9);
lw_r10: R3_TO_LWREG   (10);
lw_r11: R3_TO_LWREG   (11);                             
lw_r12: R3_TO_LWREG   (12);
lw_r13: R3_TO_LWREG   (13);
lw_r14: R3_TO_LWREG   (14);                                                     
lw_r15: R3_TO_LWREG   (15);                                                     
lw_r16: R3_TO_LWREG   (16);                                                     
lw_r17: LWREG_NOP;
lw_r18: R3_TO_LWREG   (18);                                                     
lw_r19: R3_TO_LWREG   (19);                                                     
lw_r20: R3_TO_LWREG   (20);                                                     
lw_r21: R3_TO_LWREG   (21);
lw_r22: R3_TO_LWREG   (22);
lw_r23: R3_TO_LWREG   (23);                                                     
lw_r24: R3_TO_LWREG   (24);                                                     
lw_r25: R3_TO_LWREG   (25);                                                     
lw_r26: R3_TO_LWREG   (26);                                                     
lw_r27: R3_TO_LWREG   (27);                                                     
lw_r28: R3_TO_LWREG   (28);                                                     
lw_r29: R3_TO_LWREG   (29);                                                     
lw_r30: R3_TO_LWREG   (30);
lw_r31: R3_TO_LWREG   (31);

sw_table:
sw_r0:  SWREG_TO_R3   (0); 
sw_r1:  SWREG_NOP;
sw_r2:  SWREG_TO_R3   (2);
sw_r3:  SWREG_TO_R3_V (3);
sw_r4:  SWREG_TO_R3_V (4);
sw_r5:  SWREG_TO_R3_V (5);
sw_r6:  SWREG_TO_R3_V (6);
sw_r7:  SWREG_TO_R3   (7);
sw_r8:  SWREG_TO_R3   (8);
sw_r9:  SWREG_TO_R3   (9);
sw_r10: SWREG_TO_R3   (10);
sw_r11: SWREG_TO_R3   (11);                             
sw_r12: SWREG_TO_R3   (12);
sw_r13: SWREG_TO_R3   (13);
sw_r14: SWREG_TO_R3   (14);                                                     
sw_r15: SWREG_TO_R3   (15);                                                     
sw_r16: SWREG_TO_R3   (16);                                                     
sw_r17: SWREG_NOP; 
sw_r18: SWREG_TO_R3   (18);                                                     
sw_r19: SWREG_TO_R3   (19);                                                     
sw_r20: SWREG_TO_R3   (20);                                                     
sw_r21: SWREG_TO_R3   (21);
sw_r22: SWREG_TO_R3   (22);
sw_r23: SWREG_TO_R3   (23);                                                     
sw_r24: SWREG_TO_R3   (24);                                                     
sw_r25: SWREG_TO_R3   (25);                                                     
sw_r26: SWREG_TO_R3   (26);                                                     
sw_r27: SWREG_TO_R3   (27);                                                     
sw_r28: SWREG_TO_R3   (28);                                                     
sw_r29: SWREG_TO_R3   (29);                                                     
sw_r30: SWREG_TO_R3   (30);
sw_r31: SWREG_TO_R3   (31);

/* Temporary data structures used in the handler */
.section .data
.align 2
ex_tmp_data_loc_0:      
        .byte 0
ex_tmp_data_loc_1:      
        .byte 0
ex_tmp_data_loc_2:      
        .byte 0
ex_tmp_data_loc_3:      
        .byte 0                 
ex_reg_op:
        .byte 0
    
#endif /* ! NO_UNALIGNED_EXCEPTIONS */
    
#if defined (MICROBLAZE_FP_EXCEPTION_ENABLED) && defined (MICROBLAZE_FP_EXCEPTION_DECODE)
/* 
 * FP exception decode jump table.
 * - Contains code snippets for each register that could have been a source operand for an excepting FP instruction
 * - Hence exception handler is NOT self-modifying
 * - Separate table for opA and opB
 * - Each table is of size:   (12 * 32) = 384 bytes
 */
    
.section .text
.align  4
fp_table_opa:
opa_r0: FP_EX_OPA_SAVE (0); 
opa_r1: FP_EX_UNHANDLED; 
opa_r2: FP_EX_OPA_SAVE (2);     
opa_r3: FP_EX_OPA_SAVE_V (3);     
opa_r4: FP_EX_OPA_SAVE_V (4);     
opa_r5: FP_EX_OPA_SAVE_V (5);     
opa_r6: FP_EX_OPA_SAVE_V (6);     
opa_r7: FP_EX_OPA_SAVE (7);     
opa_r8: FP_EX_OPA_SAVE (8);     
opa_r9: FP_EX_OPA_SAVE (9);     
opa_r10: FP_EX_OPA_SAVE (10);     
opa_r11: FP_EX_OPA_SAVE (11);     
opa_r12: FP_EX_OPA_SAVE (12);     
opa_r13: FP_EX_OPA_SAVE (13);     
opa_r14: FP_EX_UNHANDLED; 
opa_r15: FP_EX_UNHANDLED; 
opa_r16: FP_EX_UNHANDLED; 
opa_r17: FP_EX_UNHANDLED; 
opa_r18: FP_EX_OPA_SAVE (18);     
opa_r19: FP_EX_OPA_SAVE (19);     
opa_r20: FP_EX_OPA_SAVE (20);     
opa_r21: FP_EX_OPA_SAVE (21);     
opa_r22: FP_EX_OPA_SAVE (22);     
opa_r23: FP_EX_OPA_SAVE (23);     
opa_r24: FP_EX_OPA_SAVE (24);     
opa_r25: FP_EX_OPA_SAVE (25);     
opa_r26: FP_EX_OPA_SAVE (26);     
opa_r27: FP_EX_OPA_SAVE (27);     
opa_r28: FP_EX_OPA_SAVE (28);     
opa_r29: FP_EX_OPA_SAVE (29);     
opa_r30: FP_EX_OPA_SAVE (30);     
opa_r31: FP_EX_OPA_SAVE (31);     

fp_table_opb:   
opb_r0: FP_EX_OPB_SAVE (0); 
opb_r1: FP_EX_UNHANDLED; 
opb_r2: FP_EX_OPB_SAVE (2);     
opb_r3: FP_EX_OPB_SAVE_V (3);     
opb_r4: FP_EX_OPB_SAVE_V (4);     
opb_r5: FP_EX_OPB_SAVE_V (5);     
opb_r6: FP_EX_OPB_SAVE_V (6);     
opb_r7: FP_EX_OPB_SAVE (7);     
opb_r8: FP_EX_OPB_SAVE (8);     
opb_r9: FP_EX_OPB_SAVE (9);     
opb_r10: FP_EX_OPB_SAVE (10);     
opb_r11: FP_EX_OPB_SAVE (11);     
opb_r12: FP_EX_OPB_SAVE (12);     
opb_r13: FP_EX_OPB_SAVE (13);     
opb_r14: FP_EX_UNHANDLED; 
opb_r15: FP_EX_UNHANDLED; 
opb_r16: FP_EX_UNHANDLED; 
opb_r17: FP_EX_UNHANDLED; 
opb_r18: FP_EX_OPB_SAVE (18);     
opb_r19: FP_EX_OPB_SAVE (19);     
opb_r20: FP_EX_OPB_SAVE (20);     
opb_r21: FP_EX_OPB_SAVE (21);     
opb_r22: FP_EX_OPB_SAVE (22);     
opb_r23: FP_EX_OPB_SAVE (23);     
opb_r24: FP_EX_OPB_SAVE (24);     
opb_r25: FP_EX_OPB_SAVE (25);     
opb_r26: FP_EX_OPB_SAVE (26);     
opb_r27: FP_EX_OPB_SAVE (27);     
opb_r28: FP_EX_OPB_SAVE (28);     
opb_r29: FP_EX_OPB_SAVE (29);     
opb_r30: FP_EX_OPB_SAVE (30);     
opb_r31: FP_EX_OPB_SAVE (31);     
    
#endif  /* defined (MICROBLAZE_FP_EXCEPTION_ENABLED) && defined (MICROBLAZE_FP_EXCEPTION_DECODE) */
    
#if defined(MICROBLAZE_FP_EXCEPTION_ENABLED) && defined(MICROBLAZE_FP_EXCEPTION_DECODE)
/* This is where we store the opA and opB of the last excepting FP instruction */
.section .data    
.align 2
.global mb_fpex_op_a
.global mb_fpex_op_b
mb_fpex_op_a:
        .long 0
mb_fpex_op_b:
        .long 0
#endif /* defined (MICROBLAZE_FP_EXCEPTION_ENABLED) && defined (MICROBLAZE_FP_EXCEPTION_DECODE) */

#if defined(XPAR_MICROBLAZE_USE_STACK_PROTECTION) && (XPAR_MICROBLAZE_USE_STACK_PROTECTION == 1)
/* This is where we store the register used to check which exception occurred */
	.section .data
	.align 2
mb_sp_save_r3:
        .long 0
#endif /* defined(XPAR_MICROBLAZE_USE_STACK_PROTECTION) && (XPAR_MICROBLAZE_USE_STACK_PROTECTION == 1) */

/* The exception vector table */
.section .data
.align 2
.global MB_ExceptionVectorTable
MB_ExceptionVectorTable:
    .long XNullHandler
    .long 0                                 /* --          FSL Exception         -- */
    .long XNullHandler
    .long 1                                 /* -- Unaligned Access Exception     -- */
    .long XNullHandler
    .long 2                                 /* --   Illegal Opcode Exception     -- */
    .long XNullHandler
    .long 3                                 /* --      Instruction Bus Exception -- */
    .long XNullHandler
    .long 4                                 /* --     Data Bus Exception         -- */
    .long XNullHandler
    .long 5                                 /* --       Div-by-0 Exception       -- */
    .long XNullHandler
    .long 6                                 /* --         FPU  Exception         -- */
    .long XNullHandler
    .long 7                                 /* --         MMU  Exceptions        -- */    

#else                                       /* Dummy exception handler, in case exceptions are not present in the processor */

.global _hw_exception_handler                               
.section .text                                          
.align 2
.ent _hw_exception_handler
_hw_exception_handler:
        bri     0; 
.end _hw_exception_handler        
                                
#endif  /* MICROBLAZE_EXCEPTIONS_ENABLED */



