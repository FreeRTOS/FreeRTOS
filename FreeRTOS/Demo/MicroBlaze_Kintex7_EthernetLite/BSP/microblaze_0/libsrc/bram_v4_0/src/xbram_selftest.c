/******************************************************************************
*
* Copyright (C) 2011 - 2014 Xilinx, Inc.  All rights reserved.
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
* @file xbram_selftest.c
*
* The implementation of the XBram driver's self test function. This SelfTest
* is only applicable if ECC is enabled.
* If ECC is not enabled then this function will return XST_SUCCESS.
* See xbram.h for more information about the driver.
* Temp change
*
* @note
*
* None
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.00a sa   11/24/10 First release
* 3.01a sa   01/13/12  Changed Selftest API from
*		       XBram_SelfTest(XBram *InstancePtr) to
*		       XBram_SelfTest(XBram *InstancePtr, u8 IntMask) and
*		       fixed a problem with interrupt generation for CR 639274
*		       Modified Selftest example to return XST_SUCCESS when
*		       ECC is not enabled and return XST_FAILURE when ECC is
*		       enabled and Control Base Address is zero (CR 636581)
*		       Modified Selftest to use correct CorrectableCounterBits
*		       for CR 635655
*		       Updated to check CorrectableFailingDataRegs in the case
*		       of LMB BRAM.
* 3.02a sa  04/16/12   Added test of byte and halfword read-modify-write
* 3.03a bss 05/22/13   Added Xil_DCacheFlushRange in InjectErrors API to
*		       flush the Cache after writing to BRAM (CR #719011)
* </pre>
*****************************************************************************/

/***************************** Include Files ********************************/
#include "xbram.h"
#include "xil_cache.h"
/************************** Constant Definitions ****************************/
#define TOTAL_BITS	39

/**************************** Type Definitions ******************************/

/***************** Macros (Inline Functions) Definitions ********************/
#define RD(reg)		XBram_ReadReg(InstancePtr->Config.CtrlBaseAddress, \
					XBRAM_ ## reg)
#define WR(reg, data)	XBram_WriteReg(InstancePtr->Config.CtrlBaseAddress, \
						XBRAM_ ## reg, data)

#define CHECK(reg, data, result) if (result!=XST_SUCCESS || RD(reg)!=data) \
						result = XST_FAILURE;

/************************** Variable Definitions ****************************/
static u32 PrngResult;

/************************** Function Prototypes *****************************/
static inline u32 PrngData(u32 *PrngResult);

static inline u32 CalculateEcc(u32 Data);

static void InjectErrors(XBram * InstancePtr, u32 Addr,
			 int Index1, int Index2, int Width,
			 u32 *ActualData, u32 *ActualEcc);


/*****************************************************************************/
/**
* Generate a pseudo random number.
*
* @param	The PrngResult is the previous random number in the pseudo
*		random sequence, also knwon as the seed. It is modified to
*		the calculated pseudo random number by the function.
*
* @return 	The generated pseudo random number
*
* @note		None.
*
******************************************************************************/
static inline u32 PrngData(u32 *PrngResult)
{
	*PrngResult = *PrngResult * 0x77D15E25 + 0x3617C161;
	return *PrngResult;
}


/*****************************************************************************/
/**
* Calculate ECC from Data.
*
* @param	The Data Value
*
* @return 	The calculated ECC
*
* @note		None.
*
******************************************************************************/
static inline u32 CalculateEcc(u32 Data)
{
	unsigned char c[7], d[32];
	u32 Result = 0;
	int Index;

	for (Index = 0; Index < 32; Index++) {
		d[31 - Index] = Data & 1;
		Data = Data >> 1;
	}

	c[0] =  d[0]  ^ d[1]  ^ d[3]  ^ d[4]  ^ d[6]  ^ d[8]  ^ d[10] ^ d[11] ^
		d[13] ^ d[15] ^ d[17] ^ d[19] ^ d[21] ^ d[23] ^ d[25] ^ d[26] ^
		d[28] ^ d[30];

	c[1] =  d[0]  ^ d[2]  ^ d[3]  ^ d[5]  ^ d[6]  ^ d[9]  ^ d[10] ^ d[12] ^
		d[13] ^ d[16] ^ d[17] ^ d[20] ^ d[21] ^ d[24] ^ d[25] ^ d[27] ^
		d[28] ^ d[31];

	c[2] =  d[1]  ^ d[2]  ^ d[3]  ^ d[7]  ^ d[8]  ^ d[9]  ^ d[10] ^ d[14] ^
		d[15] ^ d[16] ^ d[17] ^ d[22] ^ d[23] ^ d[24] ^ d[25] ^ d[29] ^
		d[30] ^ d[31];

	c[3] =  d[4]  ^ d[5]  ^ d[6]  ^ d[7]  ^ d[8]  ^ d[9]  ^ d[10] ^ d[18] ^
		d[19] ^ d[20] ^ d[21] ^ d[22] ^ d[23] ^ d[24] ^ d[25];

	c[4] =  d[11] ^ d[12] ^ d[13] ^ d[14] ^ d[15] ^ d[16] ^ d[17] ^ d[18] ^
		d[19] ^ d[20] ^ d[21] ^ d[22] ^ d[23] ^ d[24] ^ d[25];

	c[5] = d[26] ^ d[27] ^ d[28] ^ d[29] ^ d[30] ^ d[31];

	c[6] =  d[0]  ^ d[1]  ^ d[2]  ^ d[3]  ^ d[4]  ^  d[5] ^  d[6] ^ d[7]  ^
		d[8]  ^ d[9]  ^ d[10] ^ d[11] ^ d[12] ^ d[13] ^ d[14] ^ d[15] ^
		d[16] ^ d[17] ^ d[18] ^ d[19] ^ d[20] ^ d[21] ^ d[22] ^ d[23] ^
		d[24] ^ d[25] ^ d[26] ^ d[27] ^ d[28] ^ d[29] ^ d[30] ^ d[31] ^
		c[5]  ^ c[4]  ^ c[3] ^  c[2]  ^ c[1]  ^ c[0];

	for (Index = 0; Index < 7; Index++) {
		Result = Result << 1;
		Result |= c[Index] & 1;
	}

	return Result;
}

/*****************************************************************************/
/**
* Get the expected actual data read in case of uncorrectable errors.
*
* @param	The injected data value including errors (if any)
* @param	The syndrome (calculated ecc ^ actual ecc read)
*
* @return 	The actual data value read
*
* @note		None.
*
******************************************************************************/
static inline u32 UncorrectableData(u32 Data, u8 Syndrome)
{
	switch (Syndrome) {
		case 0x03: return Data ^ 0x00000034;
		case 0x05: return Data ^ 0x001a2000;
		case 0x09: return Data ^ 0x0d000000;
		case 0x0d: return Data ^ 0x00001a00;

		case 0x11: return Data ^ 0x60000000;
		case 0x13: return Data ^ 0x00000003;
		case 0x15: return Data ^ 0x00018000;
		case 0x19: return Data ^ 0x00c00000;
		case 0x1d: return Data ^ 0x00000180;

		case 0x21: return Data ^ 0x80000000;
		case 0x23: return Data ^ 0x00000008;
		case 0x25: return Data ^ 0x00040000;
		case 0x29: return Data ^ 0x02000000;
		case 0x2d: return Data ^ 0x00000400;

		case 0x31: return Data ^ 0x10000000;
		case 0x35: return Data ^ 0x00004000;
		case 0x39: return Data ^ 0x00200000;
		case 0x3d: return Data ^ 0x00000040;
	}
	return Data;
}

/*****************************************************************************/
/**
* Inject errors using the hardware fault injection functionality, and write
* random data and read it back using the indicated location.
*
* @param	InstancePtr is a pointer to the XBram instance to
*		be worked on.
* @param	The Addr is the indicated memory location to use
* @param	The Index1 is the bit location of the first injected error
* @param	The Index2 is the bit location of the second injected error
* @param	The Width is the data byte width
* @param	The ActualData is filled in with expected data for checking
* @param	The ActualEcc is filled in with expected ECC for checking
*
* @return 	None
*
* @note		None.
*
******************************************************************************/
static void InjectErrors(XBram * InstancePtr, u32 Addr,
			 int Index1, int Index2, int Width,
			 u32 *ActualData, u32 *ActualEcc)
{
	u32 InjectedData = 0;
	u32 InjectedEcc = 0;
	u32 RandomData = PrngData(&PrngResult);

	if (Index1 < 32) {
		InjectedData = 1 << Index1;
	} else {
		InjectedEcc = 1 << (Index1 - 32);
	}

	if (Index2 < 32) {
		InjectedData |= (1 << Index2);
	} else {
		InjectedEcc |= 1 << (Index2 - 32);
	}

	WR(FI_D_0_OFFSET, InjectedData);
	WR(FI_ECC_0_OFFSET, InjectedEcc);

	XBram_Out32(Addr, RandomData);
	Xil_DCacheFlushRange(Addr, 4);
	switch (Width) {
		case 1: /* Byte - Write to do Read-Modify-Write */
			XBram_Out8(Addr, PrngData(&PrngResult) & 0xFF);
			break;
		case 2: /* Halfword - Write to do Read-Modify-Write */
			XBram_Out16(Addr, PrngData(&PrngResult) & 0xFFFF);
			break;
		case 4:	/* Word - Read */
			(void) XBram_In32(Addr);
			break;
	}
	*ActualData = InjectedData ^ RandomData;
	*ActualEcc  = InjectedEcc ^ CalculateEcc(RandomData);
}


/*****************************************************************************/
/**
* Run a self-test on the driver/device. Unless fault injection is implemented
* in hardware, this function only does a minimal test in which available
* registers (if any) are written and read.
*
* With fault injection, all possible single-bit and double-bit errors are
* injected, and checked to the extent possible, given the implemented hardware.
*
* @param	InstancePtr is a pointer to the XBram instance.
* @param	IntMask is the interrupt mask to use. When testing
*		with interrupts, this should be set to allow interrupt
*		generation, otherwise it should be 0.
*
* @return
*		- XST_SUCCESS if fault injection/detection is working properly OR
*		  if ECC is Not Enabled in the HW.
*		- XST_FAILURE if the injected fault is not correctly detected or
*		  the Control Base Address is Zero when ECC is enabled.
*		.
*
*		If the BRAM device is not present in the
*		hardware a bus error could be generated. Other indicators of a
*		bus error, such as registers in bridges or buses, may be
*		necessary to determine if this function caused a bus error.
*
* @note		None.
*
******************************************************************************/
int XBram_SelfTest(XBram *InstancePtr, u8 IntMask)
{
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);



	if (InstancePtr->Config.EccPresent == 0) {
		return (XST_SUCCESS);
	}

	if (InstancePtr->Config.CtrlBaseAddress == 0) {
		return (XST_SUCCESS);
	}

	/*
	 * Only 32-bit data width is supported as of yet. 64-bit and 128-bit
	 * widths will be supported in future.
	 */
	if (InstancePtr->Config.DataWidth != 32)
		return (XST_SUCCESS);

	/*
	 * Read from the implemented readable registers in the hardware device.
	 */
	if (InstancePtr->Config.CorrectableFailingRegisters) {
		(void) RD(CE_FFA_0_OFFSET);
	}
	if (InstancePtr->Config.CorrectableFailingDataRegs) {
		(void) RD(CE_FFD_0_OFFSET);
		(void) RD(CE_FFE_0_OFFSET);
	}
	if (InstancePtr->Config.UncorrectableFailingRegisters) {
		(void) RD(UE_FFA_0_OFFSET);
	}
	if (InstancePtr->Config.UncorrectableFailingDataRegs) {
		(void) RD(UE_FFD_0_OFFSET);
		(void) RD(UE_FFE_0_OFFSET);
	}

	/*
	 * Write and read the implemented read/write registers in the hardware
	 * device.
	 */
	if (InstancePtr->Config.EccStatusInterruptPresent) {
		WR(ECC_EN_IRQ_OFFSET, 0);
		if (RD(ECC_EN_IRQ_OFFSET) != 0) {
			return (XST_FAILURE);
		}
	}

	if (InstancePtr->Config.CorrectableCounterBits > 0) {
		u32 Value;

		/* Calculate counter max value */
		if (InstancePtr->Config.CorrectableCounterBits == 32) {
		 	Value = 0xFFFFFFFF;
		} else {
		 	Value = (1 <<
		 		InstancePtr->Config.CorrectableCounterBits) - 1;
		 }

		WR(CE_CNT_OFFSET, Value);
		if (RD(CE_CNT_OFFSET) != Value) {
			return (XST_FAILURE);
		}

		WR(CE_CNT_OFFSET, 0);
		if (RD(CE_CNT_OFFSET) != 0) {
			return (XST_FAILURE);
		}
	}

	/*
	 * If fault injection is implemented, inject all possible single-bit
	 * and double-bit errors, and check all observable effects.
	 */
	if (InstancePtr->Config.FaultInjectionPresent &&
	    InstancePtr->Config.WriteAccess != 0) {

	    const u32 Addr[2] = {InstancePtr->Config.MemBaseAddress &
					0xfffffffc,
				 InstancePtr->Config.MemHighAddress &
					0xfffffffc};
	    u32 SavedWords[2];
	    u32 ActualData;
	    u32 ActualEcc;
	    u32 CounterValue = 0;
	    u32 CounterMax;
	    int WordIndex = 0;
	    int Result = XST_SUCCESS;
	    int Index1;
	    int Index2;
	    int Width;

	    PrngResult = 42; /* Random seed */

	    /* Save two words in BRAM used for test */
	    SavedWords[0] = XBram_In32(Addr[0]);
	    SavedWords[1] = XBram_In32(Addr[1]);

	    for (Width = 1; Width <= 4; Width <<= 1) {
		/* Calculate counter max value */
		if (InstancePtr->Config.CorrectableCounterBits == 32) {
			CounterMax = 0xFFFFFFFF;
		} else {
			CounterMax =(1 <<
				InstancePtr->Config.CorrectableCounterBits) - 1;
		}

		/* Inject and check all single bit errors */
		for (Index1 = 0; Index1 < TOTAL_BITS; Index1++) {
			/* Save counter value */
			if (InstancePtr->Config.CorrectableCounterBits > 0) {
				CounterValue = RD(CE_CNT_OFFSET);
			}

			/* Inject single bit error */
			InjectErrors(InstancePtr, Addr[WordIndex], Index1,
				     Index1, Width, &ActualData, &ActualEcc);

			/* Check that CE is set */
			if (InstancePtr->Config.EccStatusInterruptPresent) {
				CHECK(ECC_STATUS_OFFSET,
					XBRAM_IR_CE_MASK, Result);
			}

			/* Check that address, data, ECC are correct */
			if (InstancePtr->Config.CorrectableFailingRegisters) {
				CHECK(CE_FFA_0_OFFSET, Addr[WordIndex], Result);
 			}
 			/* Checks are only for LMB BRAM */
 			if (InstancePtr->Config.CorrectableFailingDataRegs) {
  				CHECK(CE_FFD_0_OFFSET, ActualData, Result);
  				CHECK(CE_FFE_0_OFFSET, ActualEcc, Result);
  			}

			/* Check that counter has incremented */
			if (InstancePtr->Config.CorrectableCounterBits > 0 &&
				CounterValue < CounterMax) {
					CHECK(CE_CNT_OFFSET,
					CounterValue + 1, Result);
			}

			/* Restore correct data in the used word */
			XBram_Out32(Addr[WordIndex], SavedWords[WordIndex]);

			/* Allow interrupts to occur */
			/* Clear status register */
			if (InstancePtr->Config.EccStatusInterruptPresent) {
				WR(ECC_EN_IRQ_OFFSET, IntMask);
				WR(ECC_STATUS_OFFSET, XBRAM_IR_ALL_MASK);
				WR(ECC_EN_IRQ_OFFSET, 0);
			}

			/* Switch to the other word */
			WordIndex = WordIndex ^ 1;

			if (Result != XST_SUCCESS) break;

		}

		if (Result != XST_SUCCESS) {
			return XST_FAILURE;
		}

		for (Index1 = 0; Index1 < TOTAL_BITS; Index1++) {
			for (Index2 = 0; Index2 < TOTAL_BITS; Index2++) {
			    if (Index1 != Index2) {
				/* Inject double bit error */
				InjectErrors(InstancePtr,
					Addr[WordIndex],
						Index1, Index2, Width,
						&ActualData,
						&ActualEcc);

				/* Check that UE is set */
				if (InstancePtr->Config.
				    EccStatusInterruptPresent) {
					CHECK(ECC_STATUS_OFFSET,
					XBRAM_IR_UE_MASK,
					Result);
				}

				/* Check that address, data, ECC are correct */
				if (InstancePtr->Config.
				    UncorrectableFailingRegisters) {
					CHECK(UE_FFA_0_OFFSET, Addr[WordIndex],
							Result);
					CHECK(UE_FFD_0_OFFSET,
						ActualData, Result);
					CHECK(UE_FFE_0_OFFSET, ActualEcc,
						Result);
					}

				/* Restore correct data in the used word */
				XBram_Out32(Addr[WordIndex],
						SavedWords[WordIndex]);

				/* Allow interrupts to occur */
				/* Clear status register */
				if (InstancePtr->Config.
				    EccStatusInterruptPresent) {
					WR(ECC_EN_IRQ_OFFSET, IntMask);
					WR(ECC_STATUS_OFFSET,
						XBRAM_IR_ALL_MASK);
					WR(ECC_EN_IRQ_OFFSET, 0);
				}

				/* Switch to the other word */
				WordIndex = WordIndex ^ 1;
			    }
				if (Result != XST_SUCCESS) break;
			}
			if (Result != XST_SUCCESS) break;
		}

		/* Check saturation of correctable error counter */
		if (InstancePtr->Config.CorrectableCounterBits > 0 &&
			Result == XST_SUCCESS) {

				WR(CE_CNT_OFFSET, CounterMax);

				InjectErrors(InstancePtr, Addr[WordIndex], 0, 0,
					4, &ActualData, &ActualEcc);

				CHECK(CE_CNT_OFFSET, CounterMax, Result);
		}

		/* Restore the two words used for test */
		XBram_Out32(Addr[0], SavedWords[0]);
		XBram_Out32(Addr[1], SavedWords[1]);

		/* Clear the Status Register. */
		if (InstancePtr->Config.EccStatusInterruptPresent) {
			WR(ECC_STATUS_OFFSET, XBRAM_IR_ALL_MASK);
		}

		/* Set Correctable Counter to zero */
		if (InstancePtr->Config.CorrectableCounterBits > 0) {
			WR(CE_CNT_OFFSET, 0);
		}

		if (Result != XST_SUCCESS) break;

	    } /* Width loop */

	    return (Result);
	}

	return (XST_SUCCESS);
}

