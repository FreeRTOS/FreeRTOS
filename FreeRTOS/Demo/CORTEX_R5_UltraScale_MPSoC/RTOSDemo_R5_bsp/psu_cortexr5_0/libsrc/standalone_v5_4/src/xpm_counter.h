/******************************************************************************
*
* Copyright (C) 2014 - 2015 Xilinx, Inc. All rights reserved.
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
/*****************************************************************************/
/**
*
* @file xpm_counter.h
*
* This header file contains APIs for configuring and controlling the Cortex-R5
* Performance Monitor Events.
* Cortex-R5 Performance Monitor has 6 event counters which can be used to
* count a variety of events described in Coretx-R5 TRM. This file defines
* configurations, where value configures the event counters to count a
* set of events.
*
* Xpm_SetEvents can be used to set the event counters to count a set of events
* and Xpm_GetEventCounters can be used to read the counter values.
*
* @note
*
* This file doesn't handle the Cortex-R5 cycle counter, as the cycle counter is
* being used for time keeping.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 5.00  pkp  02/10/14 Initial version
* </pre>
*
******************************************************************************/

#ifndef XPMCOUNTER_H /* prevent circular inclusions */
#define XPMCOUNTER_H /* by using protection macros */

/***************************** Include Files ********************************/

#include <stdint.h>
#include "xpseudo_asm.h"
#include "xil_types.h"

#ifdef __cplusplus
extern "C" {
#endif /* __cplusplus */

/************************** Constant Definitions ****************************/

/* Number of performance counters */
#define XPM_CTRCOUNT 6U

/* The following constants define the Cortex-R5 Performance Monitor Events */

/*
 * Software increment. The register is incremented only on writes to the
 * Software Increment Register
 */
#define XPM_EVENT_SOFTINCR 0x00U

/*
 * Instruction fetch that causes a refill at (at least) the lowest level(s) of
 * instruction or unified cache. Includes the speculative linefills in the
 * count
 */
#define XPM_EVENT_INSRFETCH_CACHEREFILL 0x01U

/*
 * Instruction fetch that causes a TLB refill at (at least) the lowest level of
 * TLB. Includes the speculative requests in the count
 */
#define XPM_EVENT_INSTRFECT_TLBREFILL 0x02U

/*
 * Data read or write operation that causes a refill at (at least) the lowest
 * level(s)of data or unified cache. Counts the number of allocations performed
 * in the Data Cache due to a read or a write
 */
#define XPM_EVENT_DATA_CACHEREFILL 0x03U

/*
 * Data read or write operation that causes a cache access at (at least) the
 * lowest level(s) of data or unified cache. This includes speculative reads
 */
#define XPM_EVENT_DATA_CACHEACCESS 0x04U

/*
 * Data read or write operation that causes a TLB refill at (at least) the
 * lowest level of TLB. This does not include micro TLB misses due to PLD, PLI,
 * CP15 Cache operation by MVA and CP15 VA to PA operations
 */
#define XPM_EVENT_DATA_TLBREFILL 0x05U

/*
 * Data read architecturally executed. Counts the number of data read
 * instructions accepted by the Load Store Unit. This includes counting the
 * speculative and aborted LDR/LDM, as well as the reads due to the SWP
 * instructions
 */
#define XPM_EVENT_DATA_READS 0x06U

/*
 * Data write architecturally executed. Counts the number of data write
 * instructions accepted by the Load Store Unit. This includes counting the
 * speculative and aborted STR/STM, as well as the writes due to the SWP
 * instructions
 */
#define XPM_EVENT_DATA_WRITE 0x07U

/* Exception taken. Counts the number of exceptions architecturally taken.*/
#define XPM_EVENT_EXCEPTION 0x09U

/* Exception return architecturally executed.*/
#define XPM_EVENT_EXCEPRETURN 0x0AU

/*
 * Change to ContextID retired. Counts the number of instructions
 * architecturally executed writing into the ContextID Register
 */
#define XPM_EVENT_CHANGECONTEXT 0x0BU

/*
 * Software change of PC, except by an exception, architecturally executed.
 * Count the number of PC changes architecturally executed, excluding the PC
 * changes due to taken exceptions
 */
#define XPM_EVENT_SW_CHANGEPC 0x0CU

/*
 * Immediate branch architecturally executed (taken or not taken). This includes
 * the branches which are flushed due to a previous load/store which aborts
 * late
 */
#define XPM_EVENT_IMMEDBRANCH 0x0DU

/*
 * Unaligned access architecturally executed. Counts the number of aborted
 * unaligned accessed architecturally executed, and the number of not-aborted
 * unaligned accesses, including the speculative ones
 */
#define XPM_EVENT_UNALIGNEDACCESS 0x0FU

/*
 * Branch mispredicted/not predicted. Counts the number of mispredicted or
 * not-predicted branches executed. This includes the branches which are flushed
 * due to a previous load/store which aborts late
 */
#define XPM_EVENT_BRANCHMISS 0x10U

/*
 * Counts clock cycles when the Cortex-R5 processor is not in WFE/WFI. This
 * event is not exported on the PMUEVENT bus
 */
#define XPM_EVENT_CLOCKCYCLES 0x11U

/*
 * Branches or other change in program flow that could have been predicted by
 * the branch prediction resources of the processor. This includes the branches
 * which are flushed due to a previous load/store which aborts late
 */
#define XPM_EVENT_BRANCHPREDICT 0x12U

/*
 * Java bytecode execute. Counts the number of Java bytecodes being decoded,
 * including speculative ones
 */
#define XPM_EVENT_JAVABYTECODE 0x40U

/*
 * Software Java bytecode executed. Counts the number of software java bytecodes
 * being decoded, including speculative ones
 */
#define XPM_EVENT_SWJAVABYTECODE 0x41U

/*
 * Jazelle backward branches executed. Counts the number of Jazelle taken
 * branches being executed. This includes the branches which are flushed due
 * to a previous load/store which aborts late
 */
#define XPM_EVENT_JAVABACKBRANCH 0x42U

/*
 * Coherent linefill miss Counts the number of coherent linefill requests
 * performed by the Cortex-R5 processor which also miss in all the other
 * Cortex-R5 processors, meaning that the request is sent to the external
 * memory
 */
#define XPM_EVENT_COHERLINEMISS 0x50U

/*
 * Coherent linefill hit. Counts the number of coherent linefill requests
 * performed by the Cortex-R5 processor which hit in another Cortex-R5
 * processor, meaning that the linefill data is fetched directly from the
 * relevant Cortex-R5 cache
 */
#define XPM_EVENT_COHERLINEHIT 0x51U

/*
 * Instruction cache dependent stall cycles. Counts the number of cycles where
 * the processor is ready to accept new instructions, but does not receive any
 * due to the instruction side not being able to provide any and the
 * instruction cache is currently performing at least one linefill
 */
#define XPM_EVENT_INSTRSTALL 0x60U

/*
 * Data cache dependent stall cycles. Counts the number of cycles where the core
 * has some instructions that it cannot issue to any pipeline, and the Load
 * Store unit has at least one pending linefill request, and no pending
 */
#define XPM_EVENT_DATASTALL 0x61U

/*
 * Main TLB miss stall cycles. Counts the number of cycles where the processor
 * is stalled waiting for the completion of translation table walks from the
 * main TLB. The processor stalls can be due to the instruction side not being
 * able to provide the instructions, or to the data side not being able to
 * provide the necessary data, due to them waiting for the main TLB translation
 * table walk to complete
 */
#define XPM_EVENT_MAINTLBSTALL 0x62U

/*
 * Counts the number of STREX instructions architecturally executed and
 * passed
 */
#define XPM_EVENT_STREXPASS 0x63U

/*
 * Counts the number of STREX instructions architecturally executed and
 * failed
 */
#define XPM_EVENT_STREXFAIL 0x64U

/*
 * Data eviction. Counts the number of eviction requests due to a linefill in
 * the data cache
 */
#define XPM_EVENT_DATAEVICT 0x65U

/*
 * Counts the number of cycles where the issue stage does not dispatch any
 * instruction because it is empty or cannot dispatch any instructions
 */
#define XPM_EVENT_NODISPATCH 0x66U

/*
 * Counts the number of cycles where the issue stage is empty
 */
#define XPM_EVENT_ISSUEEMPTY 0x67U

/*
 * Counts the number of instructions going through the Register Renaming stage.
 * This number is an approximate number of the total number of instructions
 * speculatively executed, and even more approximate of the total number of
 * instructions architecturally executed. The approximation depends mainly on
 * the branch misprediction rate.
 * The renaming stage can handle two instructions in the same cycle so the event
 * is two bits long:
 *    - b00 no instructions renamed
 *    - b01 one instruction renamed
 *    - b10 two instructions renamed
 */
#define XPM_EVENT_INSTRRENAME 0x68U

/*
 * Counts the number of procedure returns whose condition codes do not fail,
 * excluding all returns from exception. This count includes procedure returns
 * which are flushed due to a previous load/store which aborts late.
 * Only the following instructions are reported:
 * - BX R14
 * - MOV PC LR
 * - POP {..,pc}
 * - LDR pc,[sp],#offset
 * The following instructions are not reported:
 * - LDMIA R9!,{..,PC} (ThumbEE state only)
 * - LDR PC,[R9],#offset (ThumbEE state only)
 * - BX R0 (Rm != R14)
 * - MOV PC,R0 (Rm != R14)
 * - LDM SP,{...,PC} (writeback not specified)
 * - LDR PC,[SP,#offset] (wrong addressing mode)
 */
#define XPM_EVENT_PREDICTFUNCRET 0x6EU

/*
 * Counts the number of instructions being executed in the main execution
 * pipeline of the processor, the multiply pipeline and arithmetic logic unit
 * pipeline. The counted instructions are still speculative
 */
#define XPM_EVENT_MAINEXEC 0x70U

/*
 * Counts the number of instructions being executed in the processor second
 * execution pipeline (ALU). The counted instructions are still speculative
 */
#define XPM_EVENT_SECEXEC 0x71U

/*
 * Counts the number of instructions being executed in the Load/Store unit. The
 * counted instructions are still speculative
 */
#define XPM_EVENT_LDRSTR 0x72U

/*
 * Counts the number of Floating-point instructions going through the Register
 * Rename stage. Instructions are still speculative in this stage.
 *Two floating-point instructions can be renamed in the same cycle so the event
 * is two bitslong:
 *0b00 no floating-point instruction renamed
 *0b01 one floating-point instruction renamed
 *0b10 two floating-point instructions renamed
 */
#define XPM_EVENT_FLOATRENAME 0x73U

/*
 * Counts the number of Neon instructions going through the Register Rename
 * stage.Instructions are still speculative in this stage.
 * Two NEON instructions can be renamed in the same cycle so the event is two
 * bits long:
 *0b00 no NEON instruction renamed
 *0b01 one NEON instruction renamed
 *0b10 two NEON instructions renamed
 */
#define XPM_EVENT_NEONRENAME 0x74U

/*
 * Counts the number of cycles where the processor is stalled because PLD slots
 * are all full
 */
#define XPM_EVENT_PLDSTALL 0x80U

/*
 * Counts the number of cycles when the processor is stalled and the data side
 * is stalled too because it is full and executing writes to the external
 * memory
 */
#define XPM_EVENT_WRITESTALL 0x81U

/*
 * Counts the number of stall cycles due to main TLB misses on requests issued
 * by the instruction side
 */
#define XPM_EVENT_INSTRTLBSTALL 0x82U

/*
 * Counts the number of stall cycles due to main TLB misses on requests issued
 * by the data side
 */
#define XPM_EVENT_DATATLBSTALL 0x83U

/*
 * Counts the number of stall cycles due to micro TLB misses on the instruction
 * side. This event does not include main TLB miss stall cycles that are already
 * counted in the corresponding main TLB event
 */
#define XPM_EVENT_INSTR_uTLBSTALL 0x84U

/*
 * Counts the number of stall cycles due to micro TLB misses on the data side.
 * This event does not include main TLB miss stall cycles that are already
 * counted in the corresponding main TLB event
 */
#define XPM_EVENT_DATA_uTLBSTALL 0x85U

/*
 * Counts the number of stall cycles because of the execution of a DMB memory
 * barrier. This includes all DMB instructions being executed, even
 * speculatively
 */
#define XPM_EVENT_DMB_STALL 0x86U

/*
 * Counts the number of cycles during which the integer core clock is enabled
 */
#define XPM_EVENT_INT_CLKEN 0x8AU

/*
 * Counts the number of cycles during which the Data Engine clock is enabled
 */
#define XPM_EVENT_DE_CLKEN 0x8BU

/*
 * Counts the number of ISB instructions architecturally executed
 */
#define XPM_EVENT_INSTRISB 0x90U

/*
 * Counts the number of DSB instructions architecturally executed
 */
#define XPM_EVENT_INSTRDSB 0x91U

/*
 * Counts the number of DMB instructions speculatively executed
 */
#define XPM_EVENT_INSTRDMB 0x92U

/*
 * Counts the number of external interrupts executed by the processor
 */
#define XPM_EVENT_EXTINT 0x93U

/*
 * PLE cache line request completed
 */
#define XPM_EVENT_PLE_LRC 0xA0U

/*
 * PLE cache line request skipped
 */
#define XPM_EVENT_PLE_LRS 0xA1U

/*
 * PLE FIFO flush
 */
#define XPM_EVENT_PLE_FLUSH 0xA2U

/*
 * PLE request complete
 */
#define XPM_EVENT_PLE_CMPL 0xA3U

/*
 * PLE FIFO overflow
 */
#define XPM_EVENT_PLE_OVFL 0xA4U

/*
 * PLE request programmed
 */
#define XPM_EVENT_PLE_PROG 0xA5U

/*
 * The following constants define the configurations for Cortex-R5 Performance
 * Monitor Events. Each configuration configures the event counters for a set
 * of events.
 * -----------------------------------------------
 * Config		PmCtr0... PmCtr5
 * -----------------------------------------------
 * XPM_CNTRCFG1		{ XPM_EVENT_SOFTINCR,
 *			  XPM_EVENT_INSRFETCH_CACHEREFILL,
 *			  XPM_EVENT_INSTRFECT_TLBREFILL,
 *			  XPM_EVENT_DATA_CACHEREFILL,
 *			  XPM_EVENT_DATA_CACHEACCESS,
 *			  XPM_EVENT_DATA_TLBREFILL }
 *
 * XPM_CNTRCFG2		{ XPM_EVENT_DATA_READS,
 *			  XPM_EVENT_DATA_WRITE,
 *			  XPM_EVENT_EXCEPTION,
 *			  XPM_EVENT_EXCEPRETURN,
 *			  XPM_EVENT_CHANGECONTEXT,
 *			  XPM_EVENT_SW_CHANGEPC }
 *
 * XPM_CNTRCFG3		{ XPM_EVENT_IMMEDBRANCH,
 *			  XPM_EVENT_UNALIGNEDACCESS,
 *			  XPM_EVENT_BRANCHMISS,
 *			  XPM_EVENT_CLOCKCYCLES,
 *			  XPM_EVENT_BRANCHPREDICT,
 *			  XPM_EVENT_JAVABYTECODE }
 *
 * XPM_CNTRCFG4		{ XPM_EVENT_SWJAVABYTECODE,
 *			  XPM_EVENT_JAVABACKBRANCH,
 *			  XPM_EVENT_COHERLINEMISS,
 *			  XPM_EVENT_COHERLINEHIT,
 *			  XPM_EVENT_INSTRSTALL,
 *			  XPM_EVENT_DATASTALL }
 *
 * XPM_CNTRCFG5		{ XPM_EVENT_MAINTLBSTALL,
 *			  XPM_EVENT_STREXPASS,
 *			  XPM_EVENT_STREXFAIL,
 *			  XPM_EVENT_DATAEVICT,
 *			  XPM_EVENT_NODISPATCH,
 *			  XPM_EVENT_ISSUEEMPTY }
 *
 * XPM_CNTRCFG6		{ XPM_EVENT_INSTRRENAME,
 *			  XPM_EVENT_PREDICTFUNCRET,
 *			  XPM_EVENT_MAINEXEC,
 *			  XPM_EVENT_SECEXEC,
 *			  XPM_EVENT_LDRSTR,
 *			  XPM_EVENT_FLOATRENAME }
 *
 * XPM_CNTRCFG7		{ XPM_EVENT_NEONRENAME,
 *			  XPM_EVENT_PLDSTALL,
 *			  XPM_EVENT_WRITESTALL,
 *			  XPM_EVENT_INSTRTLBSTALL,
 *			  XPM_EVENT_DATATLBSTALL,
 *			  XPM_EVENT_INSTR_uTLBSTALL }
 *
 * XPM_CNTRCFG8		{ XPM_EVENT_DATA_uTLBSTALL,
 *			  XPM_EVENT_DMB_STALL,
 *			  XPM_EVENT_INT_CLKEN,
 *			  XPM_EVENT_DE_CLKEN,
 *			  XPM_EVENT_INSTRISB,
 *			  XPM_EVENT_INSTRDSB }
 *
 * XPM_CNTRCFG9		{ XPM_EVENT_INSTRDMB,
 *			  XPM_EVENT_EXTINT,
 *			  XPM_EVENT_PLE_LRC,
 *			  XPM_EVENT_PLE_LRS,
 *			  XPM_EVENT_PLE_FLUSH,
 *			  XPM_EVENT_PLE_CMPL }
 *
 * XPM_CNTRCFG10	{ XPM_EVENT_PLE_OVFL,
 *			  XPM_EVENT_PLE_PROG,
 *			  XPM_EVENT_PLE_LRC,
 *			  XPM_EVENT_PLE_LRS,
 *			  XPM_EVENT_PLE_FLUSH,
 *			  XPM_EVENT_PLE_CMPL }
 *
 * XPM_CNTRCFG11	{ XPM_EVENT_DATASTALL,
 *			  XPM_EVENT_INSRFETCH_CACHEREFILL,
 *			  XPM_EVENT_INSTRFECT_TLBREFILL,
 *			  XPM_EVENT_DATA_CACHEREFILL,
 *			  XPM_EVENT_DATA_CACHEACCESS,
 *			  XPM_EVENT_DATA_TLBREFILL }
 */
#define XPM_CNTRCFG1	0
#define XPM_CNTRCFG2	1
#define XPM_CNTRCFG3	2
#define XPM_CNTRCFG4	3
#define XPM_CNTRCFG5	4
#define XPM_CNTRCFG6	5
#define XPM_CNTRCFG7	6
#define XPM_CNTRCFG8	7
#define XPM_CNTRCFG9	8
#define XPM_CNTRCFG10	9
#define XPM_CNTRCFG11	10

/**************************** Type Definitions ******************************/

/***************** Macros (Inline Functions) Definitions ********************/

/************************** Variable Definitions ****************************/

/************************** Function Prototypes *****************************/

/* Interface fuctions to access perfromance counters from abstraction layer */
void Xpm_SetEvents(s32 PmcrCfg);
void Xpm_GetEventCounters(u32 *PmCtrValue);

#ifdef __cplusplus
}
#endif

#endif
