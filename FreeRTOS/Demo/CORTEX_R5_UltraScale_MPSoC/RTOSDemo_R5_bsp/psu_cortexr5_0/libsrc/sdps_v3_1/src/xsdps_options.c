/******************************************************************************
*
* Copyright (C) 2013 - 2016 Xilinx, Inc.  All rights reserved.
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
* @file xsdps_options.c
* @addtogroup sdps_v2_5
* @{
*
* Contains API's for changing the various options in host and card.
* See xsdps.h for a detailed description of the device and driver.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date     Changes
* ----- ---    -------- -----------------------------------------------
* 1.00a hk/sg  10/17/13 Initial release
* 2.1   hk     04/18/14 Increase sleep for eMMC switch command.
*                       Add sleep for microblaze designs. CR# 781117.
* 2.3   sk     09/23/14 Use XSdPs_Change_ClkFreq API whenever changing
*						clock.CR# 816586.
* 2.5 	sg	   07/09/15 Added SD 3.0 features
*       kvn    07/15/15 Modified the code according to MISRAC-2012.
* 2.7   sk     01/08/16 Added workaround for issue in auto tuning mode
*                       of SDR50, SDR104 and HS200.
*       sk     02/16/16 Corrected the Tuning logic.
*       sk     03/02/16 Configured the Tap Delay values for eMMC HS200 mode.
* 2.8   sk     04/20/16 Added new workaround for auto tuning.
* 3.0   sk     07/07/16 Used usleep API for both arm and microblaze.
*       sk     07/16/16 Added support for UHS modes.
*       sk     07/16/16 Added Tap delays accordingly to different SD/eMMC
*                       operating modes.
* 3.1   mi     09/07/16 Removed compilation warnings with extra compiler flags.
*       sk     11/07/16 Enable Rst_n bit in ext_csd reg if not enabled.
*       sk     11/16/16 Issue DLL reset at 31 iteration to load new zero value.
*
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/
#include "xsdps.h"
#include "sleep.h"

/************************** Constant Definitions *****************************/
#define UHS_SDR12_SUPPORT	0x1U
#define UHS_SDR25_SUPPORT	0x2U
#define UHS_SDR50_SUPPORT	0x4U
#define UHS_SDR104_SUPPORT	0x8U
#define UHS_DDR50_SUPPORT	0x10U
/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/
s32 XSdPs_CmdTransfer(XSdPs *InstancePtr, u32 Cmd, u32 Arg, u32 BlkCnt);
void XSdPs_SetupADMA2DescTbl(XSdPs *InstancePtr, u32 BlkCnt, const u8 *Buff);
static s32 XSdPs_Execute_Tuning(XSdPs *InstancePtr);
#if defined (ARMR5) || defined (__aarch64__)
s32 XSdPs_Uhs_ModeInit(XSdPs *InstancePtr, u8 Mode);
static void XSdPs_sdr50_tapdelay(u32 Bank, u32 DeviceId, u32 CardType);
static void XSdPs_ddr50_tapdelay(u32 Bank, u32 DeviceId, u32 CardType);
void XSdPs_SetTapDelay(XSdPs *InstancePtr);
static void XSdPs_DllReset(XSdPs *InstancePtr);
#endif

/*****************************************************************************/
/**
* Update Block size for read/write operations.
*
* @param	InstancePtr is a pointer to the instance to be worked on.
* @param	BlkSize - Block size passed by the user.
*
* @return	None
*
******************************************************************************/
s32 XSdPs_SetBlkSize(XSdPs *InstancePtr, u16 BlkSize)
{
	s32 Status;
	u32 PresentStateReg;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	PresentStateReg = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
			XSDPS_PRES_STATE_OFFSET);

	if ((PresentStateReg & ((u32)XSDPS_PSR_INHIBIT_CMD_MASK |
			(u32)XSDPS_PSR_INHIBIT_DAT_MASK |
			(u32)XSDPS_PSR_WR_ACTIVE_MASK | (u32)XSDPS_PSR_RD_ACTIVE_MASK)) != 0U) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}


	/* Send block write command */
	Status = XSdPs_CmdTransfer(InstancePtr, CMD16, BlkSize, 0U);
	if (Status != XST_SUCCESS) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	Status = (s32)XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
			XSDPS_RESP0_OFFSET);

	/* Set block size to the value passed */
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress, XSDPS_BLK_SIZE_OFFSET,
			 BlkSize & XSDPS_BLK_SIZE_MASK);

	Status = XST_SUCCESS;

	RETURN_PATH:
		return Status;

}

/*****************************************************************************/
/**
*
* API to get bus width support by card.
*
*
* @param	InstancePtr is a pointer to the XSdPs instance.
* @param	SCR - buffer to store SCR register returned by card.
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_FAILURE if fail.
*
* @note		None.
*
******************************************************************************/
s32 XSdPs_Get_BusWidth(XSdPs *InstancePtr, u8 *SCR)
{
	s32 Status;
	u32 StatusReg;
	u16 BlkCnt;
	u16 BlkSize;
	s32 LoopCnt;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	for (LoopCnt = 0; LoopCnt < 8; LoopCnt++) {
		SCR[LoopCnt] = 0U;
	}

	/* Send block write command */
	Status = XSdPs_CmdTransfer(InstancePtr, CMD55,
			InstancePtr->RelCardAddr, 0U);
	if (Status != XST_SUCCESS) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	BlkCnt = XSDPS_SCR_BLKCNT;
	BlkSize = XSDPS_SCR_BLKSIZE;

	/* Set block size to the value passed */
	BlkSize &= XSDPS_BLK_SIZE_MASK;
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_BLK_SIZE_OFFSET, BlkSize);

	XSdPs_SetupADMA2DescTbl(InstancePtr, BlkCnt, SCR);

	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_XFER_MODE_OFFSET,
			XSDPS_TM_DAT_DIR_SEL_MASK | XSDPS_TM_DMA_EN_MASK);

	Xil_DCacheInvalidateRange((INTPTR)SCR, 8);

	Status = XSdPs_CmdTransfer(InstancePtr, ACMD51, 0U, BlkCnt);
	if (Status != XST_SUCCESS) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	/*
	 * Check for transfer complete
	 * Polling for response for now
	 */
	do {
		StatusReg = XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
					XSDPS_NORM_INTR_STS_OFFSET);
		if ((StatusReg & XSDPS_INTR_ERR_MASK) != 0U) {
			/* Write to clear error bits */
			XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
					XSDPS_ERR_INTR_STS_OFFSET,
					XSDPS_ERROR_INTR_ALL_MASK);
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}
	} while ((StatusReg & XSDPS_INTR_TC_MASK) == 0U);

	/* Write to clear bit */
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_NORM_INTR_STS_OFFSET, XSDPS_INTR_TC_MASK);

	Status = (s32)XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
			XSDPS_RESP0_OFFSET);

	Status = XST_SUCCESS;

	RETURN_PATH:
		return Status;

}

/*****************************************************************************/
/**
*
* API to set bus width to 4-bit in card and host
*
*
* @param	InstancePtr is a pointer to the XSdPs instance.
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_FAILURE if fail.
*
* @note		None.
*
******************************************************************************/
s32 XSdPs_Change_BusWidth(XSdPs *InstancePtr)
{
	s32 Status;
	u32 StatusReg;
	u32 Arg;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);


	if (InstancePtr->CardType == XSDPS_CARD_SD) {

		Status = XSdPs_CmdTransfer(InstancePtr, CMD55, InstancePtr->RelCardAddr,
				0U);
		if (Status != XST_SUCCESS) {
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}

		InstancePtr->BusWidth = XSDPS_4_BIT_WIDTH;

		Arg = ((u32)InstancePtr->BusWidth);

		Status = XSdPs_CmdTransfer(InstancePtr, ACMD6, Arg, 0U);
		if (Status != XST_SUCCESS) {
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}
	} else {

		if ((InstancePtr->HC_Version == XSDPS_HC_SPEC_V3)
				&& (InstancePtr->CardType == XSDPS_CHIP_EMMC)) {
			/* in case of eMMC data width 8-bit */
			InstancePtr->BusWidth = XSDPS_8_BIT_WIDTH;
		} else {
			InstancePtr->BusWidth = XSDPS_4_BIT_WIDTH;
		}

		if (InstancePtr->BusWidth == XSDPS_8_BIT_WIDTH) {
			Arg = XSDPS_MMC_8_BIT_BUS_ARG;
		} else {
			Arg = XSDPS_MMC_4_BIT_BUS_ARG;
		}

		Status = XSdPs_CmdTransfer(InstancePtr, CMD6, Arg, 0U);
		if (Status != XST_SUCCESS) {
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}

		/* Check for transfer complete */
		do {
			StatusReg = XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
						XSDPS_NORM_INTR_STS_OFFSET);
			if ((StatusReg & XSDPS_INTR_ERR_MASK) != 0U) {
				/* Write to clear error bits */
				XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
						XSDPS_ERR_INTR_STS_OFFSET,
						XSDPS_ERROR_INTR_ALL_MASK);
				Status = XST_FAILURE;
				goto RETURN_PATH;
			}
		} while((StatusReg & XSDPS_INTR_TC_MASK) == 0U);

		/* Write to clear bit */
		XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
				XSDPS_NORM_INTR_STS_OFFSET, XSDPS_INTR_TC_MASK);
	}

	usleep(XSDPS_MMC_DELAY_FOR_SWITCH);

	StatusReg = XSdPs_ReadReg8(InstancePtr->Config.BaseAddress,
					XSDPS_HOST_CTRL1_OFFSET);

	/* Width setting in controller */
	if (InstancePtr->BusWidth == XSDPS_8_BIT_WIDTH) {
		StatusReg |= XSDPS_HC_EXT_BUS_WIDTH;
	} else {
		StatusReg |= XSDPS_HC_WIDTH_MASK;
	}

	XSdPs_WriteReg8(InstancePtr->Config.BaseAddress,
			XSDPS_HOST_CTRL1_OFFSET,
			(u8)StatusReg);

	Status = (s32)XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
			XSDPS_RESP0_OFFSET);

	Status = XST_SUCCESS;

	RETURN_PATH:
		return Status;

}

/*****************************************************************************/
/**
*
* API to get bus speed supported by card.
*
*
* @param	InstancePtr is a pointer to the XSdPs instance.
* @param	ReadBuff - buffer to store function group support data
*		returned by card.
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_FAILURE if fail.
*
* @note		None.
*
******************************************************************************/
s32 XSdPs_Get_BusSpeed(XSdPs *InstancePtr, u8 *ReadBuff)
{
	s32 Status;
	u32 StatusReg;
	u32 Arg;
	u16 BlkCnt;
	u16 BlkSize;
	s32 LoopCnt;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	for (LoopCnt = 0; LoopCnt < 64; LoopCnt++) {
		ReadBuff[LoopCnt] = 0U;
	}

	BlkCnt = XSDPS_SWITCH_CMD_BLKCNT;
	BlkSize = XSDPS_SWITCH_CMD_BLKSIZE;
	BlkSize &= XSDPS_BLK_SIZE_MASK;
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_BLK_SIZE_OFFSET, BlkSize);

	XSdPs_SetupADMA2DescTbl(InstancePtr, BlkCnt, ReadBuff);

	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_XFER_MODE_OFFSET,
			XSDPS_TM_DAT_DIR_SEL_MASK | XSDPS_TM_DMA_EN_MASK);

	Arg = XSDPS_SWITCH_CMD_HS_GET;

	Xil_DCacheInvalidateRange((INTPTR)ReadBuff, 64);

	Status = XSdPs_CmdTransfer(InstancePtr, CMD6, Arg, 1U);
	if (Status != XST_SUCCESS) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	/*
	 * Check for transfer complete
	 * Polling for response for now
	 */
	do {
		StatusReg = XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
					XSDPS_NORM_INTR_STS_OFFSET);
		if ((StatusReg & XSDPS_INTR_ERR_MASK) != 0U) {
			/* Write to clear error bits */
			XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
					XSDPS_ERR_INTR_STS_OFFSET,
					XSDPS_ERROR_INTR_ALL_MASK);
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}
	} while ((StatusReg & XSDPS_INTR_TC_MASK) == 0U);

	/* Write to clear bit */
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_NORM_INTR_STS_OFFSET, XSDPS_INTR_TC_MASK);

	Status = (s32)XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
			XSDPS_RESP0_OFFSET);

	Status = XST_SUCCESS;

	RETURN_PATH:
		return Status;

}

/*****************************************************************************/
/**
*
* API to set high speed in card and host. Changes clock in host accordingly.
*
*
* @param	InstancePtr is a pointer to the XSdPs instance.
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_FAILURE if fail.
*
* @note		None.
*
******************************************************************************/
s32 XSdPs_Change_BusSpeed(XSdPs *InstancePtr)
{
	s32 Status;
	u32 StatusReg;
	u32 Arg;
	u16 BlkCnt;
	u16 BlkSize;
	u8 ReadBuff[64];

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	if (InstancePtr->CardType == XSDPS_CARD_SD) {

		BlkCnt = XSDPS_SWITCH_CMD_BLKCNT;
		BlkSize = XSDPS_SWITCH_CMD_BLKSIZE;
		BlkSize &= XSDPS_BLK_SIZE_MASK;
		XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
				XSDPS_BLK_SIZE_OFFSET, BlkSize);

		XSdPs_SetupADMA2DescTbl(InstancePtr, BlkCnt, ReadBuff);

		Xil_DCacheFlushRange((INTPTR)ReadBuff, 64);

		XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
				XSDPS_XFER_MODE_OFFSET,
				XSDPS_TM_DAT_DIR_SEL_MASK | XSDPS_TM_DMA_EN_MASK);

		Arg = XSDPS_SWITCH_CMD_HS_SET;

		Status = XSdPs_CmdTransfer(InstancePtr, CMD6, Arg, 1U);
		if (Status != XST_SUCCESS) {
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}

		/*
		 * Check for transfer complete
		 * Polling for response for now
		 */
		do {
			StatusReg = XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
						XSDPS_NORM_INTR_STS_OFFSET);
			if ((StatusReg & XSDPS_INTR_ERR_MASK) != 0U) {
				/* Write to clear error bits */
				XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
						XSDPS_ERR_INTR_STS_OFFSET,
						XSDPS_ERROR_INTR_ALL_MASK);
				Status = XST_FAILURE;
				goto RETURN_PATH;
			}
		} while ((StatusReg & XSDPS_INTR_TC_MASK) == 0U);

		/* Write to clear bit */
		XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
				XSDPS_NORM_INTR_STS_OFFSET, XSDPS_INTR_TC_MASK);

		/* Change the clock frequency to 50 MHz */
		InstancePtr->BusSpeed = XSDPS_CLK_50_MHZ;
		Status = XSdPs_Change_ClkFreq(InstancePtr, InstancePtr->BusSpeed);
		if (Status != XST_SUCCESS) {
				Status = XST_FAILURE;
				goto RETURN_PATH;
		}

	} else if (InstancePtr->CardType == XSDPS_CARD_MMC) {
		Arg = XSDPS_MMC_HIGH_SPEED_ARG;

		Status = XSdPs_CmdTransfer(InstancePtr, CMD6, Arg, 0U);
		if (Status != XST_SUCCESS) {
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}

		/*
		 * Check for transfer complete
		 */
		do {
			StatusReg = XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
						XSDPS_NORM_INTR_STS_OFFSET);
			if ((StatusReg & XSDPS_INTR_ERR_MASK) != 0U) {
				/*
				 * Write to clear error bits
				 */
				XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
						XSDPS_ERR_INTR_STS_OFFSET,
						XSDPS_ERROR_INTR_ALL_MASK);
				Status = XST_FAILURE;
				goto RETURN_PATH;
			}
		} while ((StatusReg & XSDPS_INTR_TC_MASK) == 0U);

		/*
		 * Write to clear bit
		 */
		XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
				XSDPS_NORM_INTR_STS_OFFSET, XSDPS_INTR_TC_MASK);

		/* Change the clock frequency to 52 MHz */
		InstancePtr->BusSpeed = XSDPS_CLK_52_MHZ;
		Status = XSdPs_Change_ClkFreq(InstancePtr, XSDPS_CLK_52_MHZ);
		if (Status != XST_SUCCESS) {
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}
	} else {
		Arg = XSDPS_MMC_HS200_ARG;

		Status = XSdPs_CmdTransfer(InstancePtr, CMD6, Arg, 0U);
		if (Status != XST_SUCCESS) {
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}

		/*
		 * Check for transfer complete
		 */
		do {
			StatusReg = XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
						XSDPS_NORM_INTR_STS_OFFSET);
			if ((StatusReg & XSDPS_INTR_ERR_MASK) != 0U) {
				/*
				 * Write to clear error bits
				 */
				XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
						XSDPS_ERR_INTR_STS_OFFSET,
						XSDPS_ERROR_INTR_ALL_MASK);
				Status = XST_FAILURE;
				goto RETURN_PATH;
			}
		} while ((StatusReg & XSDPS_INTR_TC_MASK) == 0U);

		/*
		 * Write to clear bit
		 */
		XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
				XSDPS_NORM_INTR_STS_OFFSET, XSDPS_INTR_TC_MASK);

		/* Change the clock frequency to 200 MHz */
		InstancePtr->BusSpeed = XSDPS_MMC_HS200_MAX_CLK;

		Status = XSdPs_Change_ClkFreq(InstancePtr, InstancePtr->BusSpeed);
		if (Status != XST_SUCCESS) {
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}
		Status = XSdPs_Execute_Tuning(InstancePtr);
		if (Status != XST_SUCCESS) {
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}
	}

	usleep(XSDPS_MMC_DELAY_FOR_SWITCH);

	StatusReg = (s32)XSdPs_ReadReg8(InstancePtr->Config.BaseAddress,
					XSDPS_HOST_CTRL1_OFFSET);
	StatusReg |= XSDPS_HC_SPEED_MASK;
	XSdPs_WriteReg8(InstancePtr->Config.BaseAddress,
			XSDPS_HOST_CTRL1_OFFSET, (u8)StatusReg);

	Status = (s32)XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
			XSDPS_RESP0_OFFSET);


	Status = XST_SUCCESS;

	RETURN_PATH:
		return Status;

}

/*****************************************************************************/
/**
*
* API to change clock freq to given value.
*
*
* @param	InstancePtr is a pointer to the XSdPs instance.
* @param	SelFreq - Clock frequency in Hz.
*
* @return	None
*
* @note		This API will change clock frequency to the value less than
*		or equal to the given value using the permissible dividors.
*
******************************************************************************/
s32 XSdPs_Change_ClkFreq(XSdPs *InstancePtr, u32 SelFreq)
{
	u16 ClockReg;
	u16 DivCnt;
	u16 Divisor = 0U;
	u16 ExtDivisor;
	s32 Status;
	u16 ReadReg;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/* Disable clock */
	ClockReg = XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
			XSDPS_CLK_CTRL_OFFSET);
	ClockReg &= ~(XSDPS_CC_SD_CLK_EN_MASK | XSDPS_CC_INT_CLK_EN_MASK);
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_CLK_CTRL_OFFSET, ClockReg);

	if (InstancePtr->HC_Version == XSDPS_HC_SPEC_V3) {
#if defined (ARMR5) || defined (__aarch64__)
	if ((InstancePtr->Mode != XSDPS_DEFAULT_SPEED_MODE) &&
			(InstancePtr->Mode != XSDPS_UHS_SPEED_MODE_SDR12))
		/* Program the Tap delays */
		XSdPs_SetTapDelay(InstancePtr);
#endif
		/* Calculate divisor */
		for (DivCnt = 0x1U; DivCnt <= XSDPS_CC_EXT_MAX_DIV_CNT;DivCnt++) {
			if (((InstancePtr->Config.InputClockHz) / DivCnt) <= SelFreq) {
				Divisor = DivCnt >> 1;
				break;
			}
		}

		if (DivCnt > XSDPS_CC_EXT_MAX_DIV_CNT) {
			/* No valid divisor found for given frequency */
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}
	} else {
		/* Calculate divisor */
		DivCnt = 0x1U;
		while (DivCnt <= XSDPS_CC_MAX_DIV_CNT) {
			if (((InstancePtr->Config.InputClockHz) / DivCnt) <= SelFreq) {
				Divisor = DivCnt / 2U;
				break;
			}
			DivCnt = DivCnt << 1U;
		}

		if (DivCnt > XSDPS_CC_MAX_DIV_CNT) {
			/* No valid divisor found for given frequency */
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}
	}

	/* Set clock divisor */
	if (InstancePtr->HC_Version == XSDPS_HC_SPEC_V3) {
		ClockReg = XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
				XSDPS_CLK_CTRL_OFFSET);
		ClockReg &= ~(XSDPS_CC_SDCLK_FREQ_SEL_MASK |
		XSDPS_CC_SDCLK_FREQ_SEL_EXT_MASK);

		ExtDivisor = Divisor >> 8;
		ExtDivisor <<= XSDPS_CC_EXT_DIV_SHIFT;
		ExtDivisor &= XSDPS_CC_SDCLK_FREQ_SEL_EXT_MASK;

		Divisor <<= XSDPS_CC_DIV_SHIFT;
		Divisor &= XSDPS_CC_SDCLK_FREQ_SEL_MASK;
		ClockReg |= Divisor | ExtDivisor | (u16)XSDPS_CC_INT_CLK_EN_MASK;
		XSdPs_WriteReg16(InstancePtr->Config.BaseAddress, XSDPS_CLK_CTRL_OFFSET,
				ClockReg);
	} else {
		ClockReg = XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
				XSDPS_CLK_CTRL_OFFSET);
		ClockReg &= (~XSDPS_CC_SDCLK_FREQ_SEL_MASK);

		Divisor <<= XSDPS_CC_DIV_SHIFT;
		Divisor &= XSDPS_CC_SDCLK_FREQ_SEL_MASK;
		ClockReg |= Divisor | (u16)XSDPS_CC_INT_CLK_EN_MASK;
		XSdPs_WriteReg16(InstancePtr->Config.BaseAddress, XSDPS_CLK_CTRL_OFFSET,
				ClockReg);
	}

	/* Wait for internal clock to stabilize */
	ReadReg = XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
				XSDPS_CLK_CTRL_OFFSET);
	while((ReadReg & XSDPS_CC_INT_CLK_STABLE_MASK) == 0U) {
		ReadReg = XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
					XSDPS_CLK_CTRL_OFFSET);;
	}

	/* Enable SD clock */
	ClockReg = XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
			XSDPS_CLK_CTRL_OFFSET);
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_CLK_CTRL_OFFSET,
			ClockReg | XSDPS_CC_SD_CLK_EN_MASK);

	Status = XST_SUCCESS;

RETURN_PATH:
		return Status;

}

/*****************************************************************************/
/**
*
* API to send pullup command to card before using DAT line 3(using 4-bit bus)
*
*
* @param	InstancePtr is a pointer to the XSdPs instance.
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_FAILURE if fail.
*
* @note		None.
*
******************************************************************************/
s32 XSdPs_Pullup(XSdPs *InstancePtr)
{
	s32 Status;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	Status = XSdPs_CmdTransfer(InstancePtr, CMD55,
			InstancePtr->RelCardAddr, 0U);
	if (Status != XST_SUCCESS) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	Status = XSdPs_CmdTransfer(InstancePtr, ACMD42, 0U, 0U);
	if (Status != XST_SUCCESS) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	Status = XST_SUCCESS;

	RETURN_PATH:
		return Status;

}

/*****************************************************************************/
/**
*
* API to get EXT_CSD register of eMMC.
*
*
* @param	InstancePtr is a pointer to the XSdPs instance.
* @param	ReadBuff - buffer to store EXT_CSD
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_FAILURE if fail.
*
* @note		None.
*
******************************************************************************/
s32 XSdPs_Get_Mmc_ExtCsd(XSdPs *InstancePtr, u8 *ReadBuff)
{
	s32 Status;
	u32 StatusReg;
	u32 Arg = 0U;
	u16 BlkCnt;
	u16 BlkSize;
	s32 LoopCnt;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	for (LoopCnt = 0; LoopCnt < 512; LoopCnt++) {
		ReadBuff[LoopCnt] = 0U;
	}

	BlkCnt = XSDPS_EXT_CSD_CMD_BLKCNT;
	BlkSize = XSDPS_EXT_CSD_CMD_BLKSIZE;
	BlkSize &= XSDPS_BLK_SIZE_MASK;
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_BLK_SIZE_OFFSET, BlkSize);

	XSdPs_SetupADMA2DescTbl(InstancePtr, BlkCnt, ReadBuff);

	Xil_DCacheInvalidateRange((INTPTR)ReadBuff, 512U);

	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_XFER_MODE_OFFSET,
			XSDPS_TM_DAT_DIR_SEL_MASK | XSDPS_TM_DMA_EN_MASK);


	/* Send SEND_EXT_CSD command */
	Status = XSdPs_CmdTransfer(InstancePtr, CMD8, Arg, 1U);
	if (Status != XST_SUCCESS) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	/*
	 * Check for transfer complete
	 * Polling for response for now
	 */
	do {
		StatusReg = XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
					XSDPS_NORM_INTR_STS_OFFSET);
		if ((StatusReg & XSDPS_INTR_ERR_MASK) != 0U) {
			/* Write to clear error bits */
			XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
					XSDPS_ERR_INTR_STS_OFFSET,
					XSDPS_ERROR_INTR_ALL_MASK);
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}
	} while ((StatusReg & XSDPS_INTR_TC_MASK) == 0U);

	/* Write to clear bit */
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_NORM_INTR_STS_OFFSET, XSDPS_INTR_TC_MASK);

	Status = (s32)XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
			XSDPS_RESP0_OFFSET);

	Status = XST_SUCCESS;

	RETURN_PATH:
		return Status;

}

/*****************************************************************************/
/**
*
* API to write EXT_CSD register of eMMC.
*
*
* @param	InstancePtr is a pointer to the XSdPs instance.
* @param	Arg is the argument to be sent along with the command
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_FAILURE if fail.
*
* @note		None.
*
******************************************************************************/
s32 XSdPs_Set_Mmc_ExtCsd(XSdPs *InstancePtr, u32 Arg)
{
	s32 Status;
	u32 StatusReg;

	Status = XSdPs_CmdTransfer(InstancePtr, CMD6, Arg, 0U);
	if (Status != XST_SUCCESS) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	/*
	 * Check for transfer complete
	 */
	do {
		StatusReg = XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
					XSDPS_NORM_INTR_STS_OFFSET);
		if ((StatusReg & XSDPS_INTR_ERR_MASK) != 0U) {
			/*
			 * Write to clear error bits
			 */
			XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
					XSDPS_ERR_INTR_STS_OFFSET,
					XSDPS_ERROR_INTR_ALL_MASK);
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}
	} while ((StatusReg & XSDPS_INTR_TC_MASK) == 0U);

	/* Write to clear bit */
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_NORM_INTR_STS_OFFSET, XSDPS_INTR_TC_MASK);

	Status = (s32)XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
			XSDPS_RESP0_OFFSET);

	Status = XST_SUCCESS;

	RETURN_PATH:
		return Status;

}

#if defined (ARMR5) || defined (__aarch64__)
/*****************************************************************************/
/**
*
* API to Identify the supported UHS mode. This API will assign the
* corresponding tap delay API to the Config_TapDelay pointer based on the
* supported bus speed.
*
*
* @param	InstancePtr is a pointer to the XSdPs instance.
* @param	ReadBuff contains the response for CMD6
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XSdPs_Identify_UhsMode(XSdPs *InstancePtr, u8 *ReadBuff)
{

	Xil_AssertVoid(InstancePtr != NULL);

	if (((ReadBuff[13] & UHS_SDR104_SUPPORT) != 0U) &&
		(InstancePtr->Config.InputClockHz >= XSDPS_MMC_HS200_MAX_CLK)) {
		InstancePtr->Mode = XSDPS_UHS_SPEED_MODE_SDR104;
		InstancePtr->Config_TapDelay = XSdPs_sdr104_hs200_tapdelay;
	}
	else if (((ReadBuff[13] & UHS_SDR50_SUPPORT) != 0U) &&
		(InstancePtr->Config.InputClockHz >= XSDPS_SD_SDR50_MAX_CLK)) {
		InstancePtr->Mode = XSDPS_UHS_SPEED_MODE_SDR50;
		InstancePtr->Config_TapDelay = XSdPs_sdr50_tapdelay;
	}
	else if (((ReadBuff[13] & UHS_DDR50_SUPPORT) != 0U) &&
		(InstancePtr->Config.InputClockHz >= XSDPS_SD_DDR50_MAX_CLK)) {
		InstancePtr->Mode = XSDPS_UHS_SPEED_MODE_DDR50;
		InstancePtr->Config_TapDelay = XSdPs_ddr50_tapdelay;
	}
	else if (((ReadBuff[13] & UHS_SDR25_SUPPORT) != 0U) &&
		(InstancePtr->Config.InputClockHz >= XSDPS_SD_SDR25_MAX_CLK)) {
		InstancePtr->Mode = XSDPS_UHS_SPEED_MODE_SDR25;
		InstancePtr->Config_TapDelay = XSdPs_hsd_sdr25_tapdelay;
	}
	else
		InstancePtr->Mode = XSDPS_UHS_SPEED_MODE_SDR12;
}

/*****************************************************************************/
/**
*
* API to UHS-I mode initialization
*
*
* @param	InstancePtr is a pointer to the XSdPs instance.
* @param	Mode UHS-I mode
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_FAILURE if fail.
*
* @note		None.
*
******************************************************************************/
s32 XSdPs_Uhs_ModeInit(XSdPs *InstancePtr, u8 Mode)
{
	s32 Status;
	u16 StatusReg;
	u16 CtrlReg;
	u32 Arg;
	u16 BlkCnt;
	u16 BlkSize;
	u8 ReadBuff[64];

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/* Drive strength */

	/* Bus speed mode selection */
	BlkCnt = XSDPS_SWITCH_CMD_BLKCNT;
	BlkSize = XSDPS_SWITCH_CMD_BLKSIZE;
	BlkSize &= XSDPS_BLK_SIZE_MASK;
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress, XSDPS_BLK_SIZE_OFFSET,
			BlkSize);

	XSdPs_SetupADMA2DescTbl(InstancePtr, BlkCnt, ReadBuff);

	Xil_DCacheFlushRange((INTPTR)ReadBuff, 64);

	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress, XSDPS_XFER_MODE_OFFSET,
			XSDPS_TM_DAT_DIR_SEL_MASK | XSDPS_TM_DMA_EN_MASK);

	switch (Mode) {
	case 0U:
		Arg = XSDPS_SWITCH_CMD_SDR12_SET;
		InstancePtr->BusSpeed = XSDPS_SD_SDR12_MAX_CLK;
		break;
	case 1U:
		Arg = XSDPS_SWITCH_CMD_SDR25_SET;
		InstancePtr->BusSpeed = XSDPS_SD_SDR25_MAX_CLK;
		break;
	case 2U:
		Arg = XSDPS_SWITCH_CMD_SDR50_SET;
		InstancePtr->BusSpeed = XSDPS_SD_SDR50_MAX_CLK;
		break;
	case 3U:
		Arg = XSDPS_SWITCH_CMD_SDR104_SET;
		InstancePtr->BusSpeed = XSDPS_SD_SDR104_MAX_CLK;
		break;
	case 4U:
		Arg = XSDPS_SWITCH_CMD_DDR50_SET;
		InstancePtr->BusSpeed = XSDPS_SD_DDR50_MAX_CLK;
		break;
	default:
		Status = XST_FAILURE;
		goto RETURN_PATH;
		break;
	}

	Status = XSdPs_CmdTransfer(InstancePtr, CMD6, Arg, 1U);
	if (Status != XST_SUCCESS) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	/*
	 * Check for transfer complete
	 * Polling for response for now
	 */
	do {
		StatusReg = XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
				XSDPS_NORM_INTR_STS_OFFSET);
		if ((StatusReg & XSDPS_INTR_ERR_MASK) != 0U) {
			/* Write to clear error bits */
			XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
					XSDPS_ERR_INTR_STS_OFFSET, XSDPS_ERROR_INTR_ALL_MASK);
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}
	} while ((StatusReg & XSDPS_INTR_TC_MASK) == 0U);

	/* Write to clear bit */
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_NORM_INTR_STS_OFFSET, XSDPS_INTR_TC_MASK);


	/* Current limit */

	/* Set UHS mode in controller */
	CtrlReg = XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
			XSDPS_HOST_CTRL2_OFFSET);
	CtrlReg &= (u16)(~XSDPS_HC2_UHS_MODE_MASK);
	CtrlReg |= Mode;
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_HOST_CTRL2_OFFSET, CtrlReg);

	/* Change the clock frequency */
	Status = XSdPs_Change_ClkFreq(InstancePtr, InstancePtr->BusSpeed);
	if (Status != XST_SUCCESS) {
			Status = XST_FAILURE;
			goto RETURN_PATH;
	}

	if((Mode == XSDPS_UHS_SPEED_MODE_SDR104) ||
			(Mode == XSDPS_UHS_SPEED_MODE_SDR50)) {
		/* Send tuning pattern */
		Status = XSdPs_Execute_Tuning(InstancePtr);
		if (Status != XST_SUCCESS) {
				Status = XST_FAILURE;
				goto RETURN_PATH;
		}
	}

	Status = XST_SUCCESS;

	RETURN_PATH:
		return Status;
}
#endif

static s32 XSdPs_Execute_Tuning(XSdPs *InstancePtr)
{
	s32 Status;
	u16 BlkSize;
	u16 CtrlReg;
	u8 TuningCount;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	BlkSize = XSDPS_TUNING_CMD_BLKSIZE;
	if(InstancePtr->BusWidth == XSDPS_8_BIT_WIDTH)
	{
		BlkSize = BlkSize*2U;
	}
	BlkSize &= XSDPS_BLK_SIZE_MASK;
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress, XSDPS_BLK_SIZE_OFFSET,
			BlkSize);

	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress, XSDPS_XFER_MODE_OFFSET,
			XSDPS_TM_DAT_DIR_SEL_MASK);

	CtrlReg = XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
				XSDPS_HOST_CTRL2_OFFSET);
	CtrlReg |= XSDPS_HC2_EXEC_TNG_MASK;
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
				XSDPS_HOST_CTRL2_OFFSET, CtrlReg);

	/*
	 * workaround which can work for 1.0/2.0 silicon for auto tuning.
	 * This can be revisited for 3.0 silicon if necessary.
	 */
	/* Wait for ~60 clock cycles to reset the tap values */
	(void)usleep(1U);

#if defined (ARMR5) || defined (__aarch64__)
	/* Issue DLL Reset to load new SDHC tuned tap values */
	XSdPs_DllReset(InstancePtr);
#endif

	for (TuningCount = 0U; TuningCount < MAX_TUNING_COUNT; TuningCount++) {

		if (InstancePtr->CardType == XSDPS_CARD_SD) {
			Status = XSdPs_CmdTransfer(InstancePtr, CMD19, 0U, 1U);
		} else {
			Status = XSdPs_CmdTransfer(InstancePtr, CMD21, 0U, 1U);
		}

		if (Status != XST_SUCCESS) {
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}

		if ((XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
				XSDPS_HOST_CTRL2_OFFSET) & XSDPS_HC2_EXEC_TNG_MASK) == 0U) {
			break;
		}

		if (TuningCount == 31) {
#if defined (ARMR5) || defined (__aarch64__)
			/* Issue DLL Reset to load new SDHC tuned tap values */
			XSdPs_DllReset(InstancePtr);
#endif
		}
	}

	if ((XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
			XSDPS_HOST_CTRL2_OFFSET) & XSDPS_HC2_SAMP_CLK_SEL_MASK) == 0U) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	/* Wait for ~12 clock cycles to synchronize the new tap values */
	(void)usleep(1U);

#if defined (ARMR5) || defined (__aarch64__)
	/* Issue DLL Reset to load new SDHC tuned tap values */
	XSdPs_DllReset(InstancePtr);
#endif

	Status = XST_SUCCESS;

	RETURN_PATH: return Status;

}

#if defined (ARMR5) || defined (__aarch64__)
/*****************************************************************************/
/**
*
* API to set Tap Delay for SDR104 and HS200 modes
*
*
* @param	InstancePtr is a pointer to the XSdPs instance.
*
* @return	None
*
* @note		None.
*
******************************************************************************/
void XSdPs_sdr104_hs200_tapdelay(u32 Bank, u32 DeviceId, u32 CardType)
{
	u32 TapDelay;
	(void) CardType;

#ifdef XPAR_PSU_SD_0_DEVICE_ID
	if (DeviceId == 0U) {
		/* Program the OTAPDLY */
		TapDelay = XSdPs_ReadReg(XPS_SYS_CTRL_BASEADDR, SD_OTAPDLY);
		TapDelay |= SD0_OTAPDLYENA;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_OTAPDLY, TapDelay);
		if (Bank == 2)
			TapDelay |= SD0_OTAPDLYSEL_HS200_B2;
		else
			TapDelay |= SD0_OTAPDLYSEL_HS200_B0;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_OTAPDLY, TapDelay);
	} else {
#endif
		TapDelay = XSdPs_ReadReg(XPS_SYS_CTRL_BASEADDR, SD_OTAPDLY);
		TapDelay |= SD1_OTAPDLYENA;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_OTAPDLY, TapDelay);
		if (Bank == 2)
			TapDelay |= SD1_OTAPDLYSEL_HS200_B2;
		else
			TapDelay |= SD1_OTAPDLYSEL_HS200_B0;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_OTAPDLY, TapDelay);
#ifdef XPAR_PSU_SD_0_DEVICE_ID
	}
#endif
}

/*****************************************************************************/
/**
*
* API to set Tap Delay for SDR50 mode
*
*
* @param	InstancePtr is a pointer to the XSdPs instance.
*
* @return	None
*
* @note		None.
*
******************************************************************************/
void XSdPs_sdr50_tapdelay(u32 Bank, u32 DeviceId, u32 CardType)
{
	u32 TapDelay;
	(void) Bank;
	(void) CardType;

#ifdef XPAR_PSU_SD_0_DEVICE_ID
	if (DeviceId == 0U) {
		/* Program the OTAPDLY */
		TapDelay = XSdPs_ReadReg(XPS_SYS_CTRL_BASEADDR, SD_OTAPDLY);
		TapDelay |= SD0_OTAPDLYENA;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_OTAPDLY, TapDelay);
		TapDelay |= SD0_OTAPDLYSEL_SD50;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_OTAPDLY, TapDelay);
	} else {
#endif
		TapDelay = XSdPs_ReadReg(XPS_SYS_CTRL_BASEADDR, SD_OTAPDLY);
		TapDelay |= SD1_OTAPDLYENA;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_OTAPDLY, TapDelay);
		TapDelay |= SD1_OTAPDLYSEL_SD50;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_OTAPDLY, TapDelay);
#ifdef XPAR_PSU_SD_0_DEVICE_ID
	}
#endif
}

/*****************************************************************************/
/**
*
* API to set Tap Delay for DDR50 mode
*
*
* @param	InstancePtr is a pointer to the XSdPs instance.
*
* @return	None
*
* @note		None.
*
******************************************************************************/
void XSdPs_ddr50_tapdelay(u32 Bank, u32 DeviceId, u32 CardType)
{
	u32 TapDelay;
	(void) Bank;

#ifdef XPAR_PSU_SD_0_DEVICE_ID
	if (DeviceId == 0U) {
		TapDelay = XSdPs_ReadReg(XPS_SYS_CTRL_BASEADDR, SD_ITAPDLY);
		TapDelay |= SD0_ITAPCHGWIN;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_ITAPDLY, TapDelay);
		/* Program the ITAPDLY */
		TapDelay |= SD0_ITAPDLYENA;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_ITAPDLY, TapDelay);
		if (CardType== XSDPS_CARD_SD)
			TapDelay |= SD0_ITAPDLYSEL_SD_DDR50;
		else
			TapDelay |= SD0_ITAPDLYSEL_EMMC_DDR50;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_ITAPDLY, TapDelay);
		TapDelay &= ~SD0_ITAPCHGWIN;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_ITAPDLY, TapDelay);
		/* Program the OTAPDLY */
		TapDelay = XSdPs_ReadReg(XPS_SYS_CTRL_BASEADDR, SD_OTAPDLY);
		TapDelay |= SD0_OTAPDLYENA;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_OTAPDLY, TapDelay);
		if (CardType == XSDPS_CARD_SD)
			TapDelay |= SD0_OTAPDLYSEL_SD_DDR50;
		else
			TapDelay |= SD0_OTAPDLYSEL_EMMC_DDR50;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_OTAPDLY, TapDelay);
	} else {
#endif
		TapDelay = XSdPs_ReadReg(XPS_SYS_CTRL_BASEADDR, SD_ITAPDLY);
		TapDelay |= SD1_ITAPCHGWIN;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_ITAPDLY, TapDelay);
		/* Program the ITAPDLY */
		TapDelay |= SD1_ITAPDLYENA;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_ITAPDLY, TapDelay);
		if (CardType == XSDPS_CARD_SD)
			TapDelay |= SD1_ITAPDLYSEL_SD_DDR50;
		else
			TapDelay |= SD1_ITAPDLYSEL_EMMC_DDR50;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_ITAPDLY, TapDelay);
		TapDelay &= ~SD1_ITAPCHGWIN;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_ITAPDLY, TapDelay);
		/* Program the OTAPDLY */
		TapDelay = XSdPs_ReadReg(XPS_SYS_CTRL_BASEADDR, SD_OTAPDLY);
		TapDelay |= SD1_OTAPDLYENA;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_OTAPDLY, TapDelay);
		if (CardType == XSDPS_CARD_SD)
			TapDelay |= SD1_OTAPDLYSEL_SD_DDR50;
		else
			TapDelay |= SD1_OTAPDLYSEL_EMMC_DDR50;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_OTAPDLY, TapDelay);
#ifdef XPAR_PSU_SD_0_DEVICE_ID
	}
#endif
}

/*****************************************************************************/
/**
*
* API to set Tap Delay for HSD and SDR25 mode
*
*
* @param	InstancePtr is a pointer to the XSdPs instance.
*
* @return	None
*
* @note		None.
*
******************************************************************************/
void XSdPs_hsd_sdr25_tapdelay(u32 Bank, u32 DeviceId, u32 CardType)
{
	u32 TapDelay;
	(void) Bank;

#ifdef XPAR_PSU_SD_0_DEVICE_ID
	if (DeviceId == 0U) {
		TapDelay = XSdPs_ReadReg(XPS_SYS_CTRL_BASEADDR, SD_ITAPDLY);
		TapDelay |= SD0_ITAPCHGWIN;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_ITAPDLY, TapDelay);
		/* Program the ITAPDLY */
		TapDelay |= SD0_ITAPDLYENA;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_ITAPDLY, TapDelay);
		TapDelay |= SD0_ITAPDLYSEL_HSD;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_ITAPDLY, TapDelay);
		TapDelay &= ~SD0_ITAPCHGWIN;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_ITAPDLY, TapDelay);
		/* Program the OTAPDLY */
		TapDelay = XSdPs_ReadReg(XPS_SYS_CTRL_BASEADDR, SD_OTAPDLY);
		TapDelay |= SD0_OTAPDLYENA;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_OTAPDLY, TapDelay);
		if (CardType == XSDPS_CARD_SD)
			TapDelay |= SD0_OTAPDLYSEL_SD_HSD;
		else
			TapDelay |= SD0_OTAPDLYSEL_EMMC_HSD;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_OTAPDLY, TapDelay);
	} else {
#endif
		TapDelay = XSdPs_ReadReg(XPS_SYS_CTRL_BASEADDR, SD_ITAPDLY);
		TapDelay |= SD1_ITAPCHGWIN;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_ITAPDLY, TapDelay);
		/* Program the ITAPDLY */
		TapDelay |= SD1_ITAPDLYENA;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_ITAPDLY, TapDelay);
		TapDelay |= SD1_ITAPDLYSEL_HSD;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_ITAPDLY, TapDelay);
		TapDelay &= ~SD1_ITAPCHGWIN;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_ITAPDLY, TapDelay);
		/* Program the OTAPDLY */
		TapDelay = XSdPs_ReadReg(XPS_SYS_CTRL_BASEADDR, SD_OTAPDLY);
		TapDelay |= SD1_OTAPDLYENA;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_OTAPDLY, TapDelay);
		if (CardType == XSDPS_CARD_SD)
			TapDelay |= SD1_OTAPDLYSEL_SD_HSD;
		else
			TapDelay |= SD1_OTAPDLYSEL_EMMC_HSD;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_OTAPDLY, TapDelay);
#ifdef XPAR_PSU_SD_0_DEVICE_ID
	}
#endif
}

/*****************************************************************************/
/**
*
* API to set Tap Delay w.r.t speed modes
*
*
* @param	InstancePtr is a pointer to the XSdPs instance.
*
* @return	None
*
* @note		None.
*
******************************************************************************/
void XSdPs_SetTapDelay(XSdPs *InstancePtr)
{
	u32 DllCtrl, BankNum, DeviceId, CardType;

	BankNum = InstancePtr->Config.BankNumber;
	DeviceId = InstancePtr->Config.DeviceId ;
	CardType = InstancePtr->CardType ;
#ifdef XPAR_PSU_SD_0_DEVICE_ID
	if (DeviceId == 0U) {
		DllCtrl = XSdPs_ReadReg(XPS_SYS_CTRL_BASEADDR, SD_DLL_CTRL);
		DllCtrl |= SD0_DLL_RST;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_DLL_CTRL, DllCtrl);
		InstancePtr->Config_TapDelay(BankNum, DeviceId, CardType);
		DllCtrl &= ~SD0_DLL_RST;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_DLL_CTRL, DllCtrl);
	} else {
#endif
		DllCtrl = XSdPs_ReadReg(XPS_SYS_CTRL_BASEADDR, SD_DLL_CTRL);
		DllCtrl |= SD1_DLL_RST;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_DLL_CTRL, DllCtrl);
		InstancePtr->Config_TapDelay(BankNum, DeviceId, CardType);
		DllCtrl &= ~SD1_DLL_RST;
		XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_DLL_CTRL, DllCtrl);
#ifdef XPAR_PSU_SD_0_DEVICE_ID
	}
#endif
}

/*****************************************************************************/
/**
*
* API to reset the DLL
*
*
* @param	InstancePtr is a pointer to the XSdPs instance.
*
* @return	None
*
* @note		None.
*
******************************************************************************/
static void XSdPs_DllReset(XSdPs *InstancePtr)
{
	u32 ClockReg, DllCtrl;

	/* Disable clock */
	ClockReg = XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
			XSDPS_CLK_CTRL_OFFSET);
	ClockReg &= ~XSDPS_CC_SD_CLK_EN_MASK;
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_CLK_CTRL_OFFSET, ClockReg);

	/* Issue DLL Reset to load zero tap values */
	DllCtrl = XSdPs_ReadReg(XPS_SYS_CTRL_BASEADDR, SD_DLL_CTRL);
	if (InstancePtr->Config.DeviceId == 0U) {
		DllCtrl |= SD0_DLL_RST;
	} else {
		DllCtrl |= SD1_DLL_RST;
	}
	XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_DLL_CTRL, DllCtrl);

	/* Wait for 2 micro seconds */
	(void)usleep(2U);

	/* Release the DLL out of reset */
	DllCtrl = XSdPs_ReadReg(XPS_SYS_CTRL_BASEADDR, SD_DLL_CTRL);
	if (InstancePtr->Config.DeviceId == 0U) {
		DllCtrl &= ~SD0_DLL_RST;
	} else {
		DllCtrl &= ~SD1_DLL_RST;
	}
	XSdPs_WriteReg(XPS_SYS_CTRL_BASEADDR, SD_DLL_CTRL, DllCtrl);

	/* Wait for internal clock to stabilize */
	ClockReg = XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
				XSDPS_CLK_CTRL_OFFSET);
	while((ClockReg & XSDPS_CC_INT_CLK_STABLE_MASK) == 0U) {
		ClockReg = XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
					XSDPS_CLK_CTRL_OFFSET);
	}

	/* Enable SD clock */
	ClockReg = XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
			XSDPS_CLK_CTRL_OFFSET);
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_CLK_CTRL_OFFSET,
			ClockReg | XSDPS_CC_SD_CLK_EN_MASK);
}
#endif
/** @} */
