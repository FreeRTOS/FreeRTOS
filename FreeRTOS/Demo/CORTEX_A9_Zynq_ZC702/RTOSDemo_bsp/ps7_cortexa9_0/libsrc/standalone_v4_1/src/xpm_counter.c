/******************************************************************************
*
* (c) Copyright 2011-13  Xilinx, Inc. All rights reserved.
*
* This file contains confidential and proprietary information of Xilinx, Inc.
* and is protected under U.S. and international copyright and other
* intellectual property laws.
*
* DISCLAIMER
* This disclaimer is not a license and does not grant any rights to the
* materials distributed herewith. Except as otherwise provided in a valid
* license issued to you by Xilinx, and to the maximum extent permitted by
* applicable law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND WITH ALL
* FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES AND CONDITIONS, EXPRESS,
* IMPLIED, OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF
* MERCHANTABILITY, NON-INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE;
* and (2) Xilinx shall not be liable (whether in contract or tort, including
* negligence, or under any other theory of liability) for any loss or damage
* of any kind or nature related to, arising under or in connection with these
* materials, including for any direct, or any indirect, special, incidental,
* or consequential loss or damage (including loss of data, profits, goodwill,
* or any type of loss or damage suffered as a result of any action brought by
* a third party) even if such damage or loss was reasonably foreseeable or
* Xilinx had been advised of the possibility of the same.
*
* CRITICAL APPLICATIONS
* Xilinx products are not designed or intended to be fail-safe, or for use in
* any application requiring fail-safe performance, such as life-support or
* safety devices or systems, Class III medical devices, nuclear facilities,
* applications related to the deployment of airbags, or any other applications
* that could lead to death, personal injury, or severe property or
* environmental damage (individually and collectively, "Critical
* Applications"). Customer assumes the sole risk and liability of any use of
* Xilinx products in Critical Applications, subject only to applicable laws
* and regulations governing limitations on product liability.
*
* THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS PART OF THIS FILE
* AT ALL TIMES.
*
******************************************************************************/
/*****************************************************************************/
/**
*
* @file xpm_counter.c
*
* This file contains APIs for configuring and controlling the Cortex-A9
* Performance Monitor Events. For more information about the event counters,
* see xpm_counter.h.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.00a sdm  07/11/11 First release
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xpm_counter.h"

/************************** Constant Definitions ****************************/

/**************************** Type Definitions ******************************/

typedef const u32 PmcrEventCfg[XPM_CTRCOUNT];

/***************** Macros (Inline Functions) Definitions ********************/

/************************** Variable Definitions *****************************/

static PmcrEventCfg PmcrEvents[] = {
	{
		XPM_EVENT_SOFTINCR,
		XPM_EVENT_INSRFETCH_CACHEREFILL,
		XPM_EVENT_INSTRFECT_TLBREFILL,
		XPM_EVENT_DATA_CACHEREFILL,
		XPM_EVENT_DATA_CACHEACCESS,
		XPM_EVENT_DATA_TLBREFILL
	},
	{
		XPM_EVENT_DATA_READS,
		XPM_EVENT_DATA_WRITE,
		XPM_EVENT_EXCEPTION,
		XPM_EVENT_EXCEPRETURN,
		XPM_EVENT_CHANGECONTEXT,
		XPM_EVENT_SW_CHANGEPC
	},
	{
		XPM_EVENT_IMMEDBRANCH,
		XPM_EVENT_UNALIGNEDACCESS,
		XPM_EVENT_BRANCHMISS,
		XPM_EVENT_CLOCKCYCLES,
		XPM_EVENT_BRANCHPREDICT,
		XPM_EVENT_JAVABYTECODE
	},
	{
		XPM_EVENT_SWJAVABYTECODE,
		XPM_EVENT_JAVABACKBRANCH,
		XPM_EVENT_COHERLINEMISS,
		XPM_EVENT_COHERLINEHIT,
		XPM_EVENT_INSTRSTALL,
		XPM_EVENT_DATASTALL
	},
	{
		XPM_EVENT_MAINTLBSTALL,
		XPM_EVENT_STREXPASS,
		XPM_EVENT_STREXFAIL,
		XPM_EVENT_DATAEVICT,
		XPM_EVENT_NODISPATCH,
		XPM_EVENT_ISSUEEMPTY
	},
	{
		XPM_EVENT_INSTRRENAME,
		XPM_EVENT_PREDICTFUNCRET,
		XPM_EVENT_MAINEXEC,
		XPM_EVENT_SECEXEC,
		XPM_EVENT_LDRSTR,
		XPM_EVENT_FLOATRENAME
	},
	{
		XPM_EVENT_NEONRENAME,
		XPM_EVENT_PLDSTALL,
		XPM_EVENT_WRITESTALL,
		XPM_EVENT_INSTRTLBSTALL,
		XPM_EVENT_DATATLBSTALL,
		XPM_EVENT_INSTR_uTLBSTALL
	},
	{
		XPM_EVENT_DATA_uTLBSTALL,
		XPM_EVENT_DMB_STALL,
		XPM_EVENT_INT_CLKEN,
		XPM_EVENT_DE_CLKEN,
		XPM_EVENT_INSTRISB,
		XPM_EVENT_INSTRDSB
	},
	{
		XPM_EVENT_INSTRDMB,
		XPM_EVENT_EXTINT,
		XPM_EVENT_PLE_LRC,
		XPM_EVENT_PLE_LRS,
		XPM_EVENT_PLE_FLUSH,
		XPM_EVENT_PLE_CMPL
	},
	{
		XPM_EVENT_PLE_OVFL,
		XPM_EVENT_PLE_PROG,
		XPM_EVENT_PLE_LRC,
		XPM_EVENT_PLE_LRS,
		XPM_EVENT_PLE_FLUSH,
		XPM_EVENT_PLE_CMPL
	},
	{
		XPM_EVENT_DATASTALL,
		XPM_EVENT_INSRFETCH_CACHEREFILL,
		XPM_EVENT_INSTRFECT_TLBREFILL,
		XPM_EVENT_DATA_CACHEREFILL,
		XPM_EVENT_DATA_CACHEACCESS,
		XPM_EVENT_DATA_TLBREFILL
	},
};

/************************** Function Prototypes ******************************/

void Xpm_DisableEventCounters(void);
void Xpm_EnableEventCounters (void);
void Xpm_ResetEventCounters (void);

/******************************************************************************/

/****************************************************************************/
/**
*
* This function disables the Cortex A9 event counters.
*
* @param	None.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void Xpm_DisableEventCounters(void)
{
	/* Disable the event counters */
	mtcp(XREG_CP15_COUNT_ENABLE_CLR, 0x3f);
}

/****************************************************************************/
/**
*
* This function enables the Cortex A9 event counters.
*
* @param	None.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void Xpm_EnableEventCounters(void)
{
	/* Enable the event counters */
	mtcp(XREG_CP15_COUNT_ENABLE_SET, 0x3f);
}

/****************************************************************************/
/**
*
* This function resets the Cortex A9 event counters.
*
* @param	None.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void Xpm_ResetEventCounters(void)
{
	u32 Reg;

#ifdef __GNUC__
	Reg = mfcp(XREG_CP15_PERF_MONITOR_CTRL);
#else
	{ register unsigned int C15Reg __asm(XREG_CP15_PERF_MONITOR_CTRL);
	  Reg = C15Reg; }
#endif
	Reg |= (1 << 2); /* reset event counters */
	mtcp(XREG_CP15_PERF_MONITOR_CTRL, Reg);
}

/****************************************************************************/
/**
*
* This function configures the Cortex A9 event counters controller, with the
* event codes, in a configuration selected by the user and enables the counters.
*
* @param	PmcrCfg is configuration value based on which the event counters
*		are configured.
*		Use XPM_CNTRCFG* values defined in xpm_counter.h.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void Xpm_SetEvents(int PmcrCfg)
{
	u32 Counter;
	const u32 *Ptr = PmcrEvents[PmcrCfg];

	Xpm_DisableEventCounters();

	for(Counter = 0; Counter < XPM_CTRCOUNT; Counter++) {

		/* Selecet event counter */
		mtcp(XREG_CP15_EVENT_CNTR_SEL, Counter);

		/* Set the event */
		mtcp(XREG_CP15_EVENT_TYPE_SEL, Ptr[Counter]);
	}

	Xpm_ResetEventCounters();
	Xpm_EnableEventCounters();
}

/****************************************************************************/
/**
*
* This function disables the event counters and returns the counter values.
*
* @param	PmCtrValue is a pointer to an array of type u32 PmCtrValue[6].
*		It is an output parameter which is used to return the PM
*		counter values.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void Xpm_GetEventCounters(u32 *PmCtrValue)
{
	u32 Counter;

	Xpm_DisableEventCounters();

	for(Counter = 0; Counter < XPM_CTRCOUNT; Counter++) {

		mtcp(XREG_CP15_EVENT_CNTR_SEL, Counter);
#ifdef __GNUC__
		PmCtrValue[Counter] = mfcp(XREG_CP15_PERF_MONITOR_COUNT);
#else
		{ register unsigned int Cp15Reg __asm(XREG_CP15_PERF_MONITOR_COUNT);
		  PmCtrValue[Counter] = Cp15Reg; }
#endif
	}
}
