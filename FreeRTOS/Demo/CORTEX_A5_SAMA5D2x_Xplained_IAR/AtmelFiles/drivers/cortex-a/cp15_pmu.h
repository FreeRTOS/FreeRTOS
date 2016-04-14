/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2015, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

#ifndef _CP15_PMU_H
#define _CP15_PMU_H

/*----------------------------------------------------------------------------
 *        Definition
 *----------------------------------------------------------------------------*/

#define CP15_PMCNTENSET         31
#define CP15_PMCNTENCLEAR       31
#define CP15_PMCR_DIVIDER       3
#define CP15_PMCR_RESET         2
#define CP15_PMCR_ENABLE        0

#define CP15_NoReset            0
#define CP15_ResetPerCounter    1
#define CP15_ResetCycCounter    2
#define CP15_ResetPerCycCounter 3

#define CP15_CountDividerSingle 0
#define CP15_CountDivider64     1

#define CP15_CounterNone        0
#define CP15_Counter0           1
#define CP15_Counter1           2
#define CP15_BothCounter        3

typedef enum {
	L1_IC_FILL,		// Level 1 instruction cache refill
	L1_ITLB_FILL,		// Level 1 instruction TLB refill
	L1_DC_FILL,		// Level 1 data cache refill
	L1_DC_ACC,		// Level 1 data cache access
	L1_DTLB_FILL,		// Level 1 data TLB refill
	LOAD,			// Load
	STORE,			// Store
	InstArchExec,		// Instruction architecturally executed
	ExcepetionTaken,	// Exception taken
	ExcepetionRet,		// Exception return
	WrCONTEXTIDR,		// Write to CONTEXTIDR
	SoftPCChange,		// Software change of the PC
	ImmBr,			// Immediate branch
	ProcRet,		// Procedure return
	UnalingedLdStr,		// Unaligned load or store
	MispredictedBranchExec,	// Mispredicted or not predicted branch speculatively executed
	PredictedBranchExec,	// Predictable branch speculatively executed
	DataMemAcc,		// Data memory access.
	ICAcc,			// Instruction Cache access.
	DCEviction,		// Data cache eviction.
	IRQException,		// IRQ exception taken.
	FIQException,		// FIQ exception taken.
	ExtMemReq,		// External memory request.
	NCExtMemReq,		// Non-cacheable external memory request
	PrefetchLineFill,	// Linefill because of prefetch.
	PrefetchLineDrop,	// Prefetch linefill dropped.
	EnteringRAmode,		// Entering read allocate mode.
	RAmode,			// Read allocate mode.
	reserved,		// Reserved, do not use
	DWstallSBFfull		// Data Write operation that stalls the pipeline because the store buffer is full.
} PerfEventType;

/*----------------------------------------------------------------------------
 *        Functions
 *----------------------------------------------------------------------------*/

extern uint32_t cp15_init_cycle_counter(void);
extern uint32_t cp15_get_cycle_counter(void);

extern uint32_t cp15_read_overflow_status(uint8_t EventCounter);
extern void cp15_overflow_status(uint8_t Enable, uint8_t ClearCounterFlag);
extern void cp15_soft_incr(uint8_t IncrCounter);

extern uint32_t cp15_count_evt(uint8_t Counter);
extern void cp15_enable_user_mode(void);
extern void cp15_enable_interrupt(uint8_t Enable, uint8_t Counter);
extern void cp15_disable_interrupt(uint8_t Disable, uint8_t Counter);
extern void cp15_init_perf_counter(PerfEventType Event, uint8_t Counter);

#endif
