/******************************************************************************
*
* Copyright (C) 2013 - 2014 Xilinx, Inc.  All rights reserved.
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
* @addtogroup sdps_v2_1
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
*
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/
#include "xsdps.h"
/*
 * The header sleep.h and API usleep() can only be used with an arm design.
 * MB_Sleep() is used for microblaze design.
 */
#ifdef __arm__

#include "sleep.h"

#endif

#ifdef __MICROBLAZE__

#include "microblaze_sleep.h"

#endif

/************************** Constant Definitions *****************************/
#define XSDPS_SCR_BLKCNT	1
#define XSDPS_SCR_BLKSIZE	8
#define XSDPS_4_BIT_WIDTH	0x2
#define XSDPS_SWITCH_CMD_BLKCNT		1
#define XSDPS_SWITCH_CMD_BLKSIZE	64
#define XSDPS_SWITCH_CMD_HS_GET	0x00FFFFF0
#define XSDPS_SWITCH_CMD_HS_SET	0x80FFFFF1
#define XSDPS_EXT_CSD_CMD_BLKCNT	1
#define XSDPS_EXT_CSD_CMD_BLKSIZE	512
#define XSDPS_CLK_52_MHZ		52000000
#define XSDPS_MMC_HIGH_SPEED_ARG	0x03B90100
#define XSDPS_MMC_4_BIT_BUS_ARG		0x03B70100
#define XSDPS_MMC_DELAY_FOR_SWITCH	2000

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/
int XSdPs_CmdTransfer(XSdPs *InstancePtr, u32 Cmd, u32 Arg, u32 BlkCnt);
void XSdPs_SetupADMA2DescTbl(XSdPs *InstancePtr, u32 BlkCnt, const u8 *Buff);

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
int XSdPs_SetBlkSize(XSdPs *InstancePtr, u16 BlkSize)
{
	u32 Status = 0;
	u32 PresentStateReg = 0;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	PresentStateReg = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
			XSDPS_PRES_STATE_OFFSET);

	if (PresentStateReg & (XSDPS_PSR_INHIBIT_CMD_MASK |
			XSDPS_PSR_INHIBIT_DAT_MASK |
			XSDPS_PSR_WR_ACTIVE_MASK | XSDPS_PSR_RD_ACTIVE_MASK)) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}


	/*
	 * Send block write command
	 */
	Status = XSdPs_CmdTransfer(InstancePtr, CMD16, BlkSize, 0);
	if (Status != XST_SUCCESS) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	Status = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
			XSDPS_RESP0_OFFSET);

	/*
	 * Set block size to the value passed
	 */
	BlkSize &= XSDPS_BLK_SIZE_MASK;
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress, XSDPS_BLK_SIZE_OFFSET,
			 BlkSize);

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
int XSdPs_Get_BusWidth(XSdPs *InstancePtr, u8 *SCR)
{
	u32 Status = 0;
	u32 StatusReg = 0x0;
	u16 BlkCnt;
	u16 BlkSize;
	int LoopCnt;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	for (LoopCnt = 0; LoopCnt < 8; LoopCnt++) {
		SCR[LoopCnt] = 0;
	}

	/*
	 * Send block write command
	 */
	Status = XSdPs_CmdTransfer(InstancePtr, CMD55,
			InstancePtr->RelCardAddr, 0);
	if (Status != XST_SUCCESS) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	BlkCnt = XSDPS_SCR_BLKCNT;
	BlkSize = XSDPS_SCR_BLKSIZE;

	/*
	 * Set block size to the value passed
	 */
	BlkSize &= XSDPS_BLK_SIZE_MASK;
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_BLK_SIZE_OFFSET, BlkSize);

	XSdPs_SetupADMA2DescTbl(InstancePtr, BlkCnt, SCR);

	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_XFER_MODE_OFFSET,
			XSDPS_TM_DAT_DIR_SEL_MASK | XSDPS_TM_DMA_EN_MASK);

	Status = XSdPs_CmdTransfer(InstancePtr, ACMD51, 0, BlkCnt);
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
		if (StatusReg & XSDPS_INTR_ERR_MASK) {
			/*
			 * Write to clear error bits
			 */
			XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
					XSDPS_ERR_INTR_STS_OFFSET,
					XSDPS_ERROR_INTR_ALL_MASK);
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}
	} while ((StatusReg & XSDPS_INTR_TC_MASK) == 0);

	/*
	 * Write to clear bit
	 */
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_NORM_INTR_STS_OFFSET, XSDPS_INTR_TC_MASK);

	Status = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
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
int XSdPs_Change_BusWidth(XSdPs *InstancePtr)
{
	u32 Status = 0;
	u32 StatusReg = 0x0;
	u32 Arg = 0;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

#ifndef MMC_CARD

	Status = XSdPs_CmdTransfer(InstancePtr, CMD55,
			InstancePtr->RelCardAddr, 0);
	if (Status != XST_SUCCESS) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	Arg = XSDPS_4_BIT_WIDTH;
	Status = XSdPs_CmdTransfer(InstancePtr, ACMD6, Arg, 0);
	if (Status != XST_SUCCESS) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	StatusReg = XSdPs_ReadReg8(InstancePtr->Config.BaseAddress,
					XSDPS_HOST_CTRL1_OFFSET);
	StatusReg |= XSDPS_HC_WIDTH_MASK;
	XSdPs_WriteReg8(InstancePtr->Config.BaseAddress,
			XSDPS_HOST_CTRL1_OFFSET,StatusReg);

	Status = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
			XSDPS_RESP0_OFFSET);

#else

	Arg = XSDPS_MMC_4_BIT_BUS_ARG;
	Status = XSdPs_CmdTransfer(InstancePtr, ACMD6, Arg, 0);
	if (Status != XST_SUCCESS) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

#ifdef __arm__

	usleep(XSDPS_MMC_DELAY_FOR_SWITCH);

#endif

#ifdef __MICROBLAZE__

	/* 2 msec delay */
	MB_Sleep(2);

#endif

	StatusReg = XSdPs_ReadReg8(InstancePtr->Config.BaseAddress,
					XSDPS_HOST_CTRL1_OFFSET);
	StatusReg |= XSDPS_HC_WIDTH_MASK;
	XSdPs_WriteReg8(InstancePtr->Config.BaseAddress,
			XSDPS_HOST_CTRL1_OFFSET,StatusReg);

	Status = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
			XSDPS_RESP0_OFFSET);

#endif

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
int XSdPs_Get_BusSpeed(XSdPs *InstancePtr, u8 *ReadBuff)
{
	u32 Status = 0;
	u32 StatusReg = 0x0;
	u32 Arg = 0;
	u16 BlkCnt;
	u16 BlkSize;
	int LoopCnt;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	for (LoopCnt = 0; LoopCnt < 64; LoopCnt++) {
		ReadBuff[LoopCnt] = 0;
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

	Status = XSdPs_CmdTransfer(InstancePtr, CMD6, Arg, 1);
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
		if (StatusReg & XSDPS_INTR_ERR_MASK) {
			/*
			 * Write to clear error bits
			 */
			XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
					XSDPS_ERR_INTR_STS_OFFSET,
					XSDPS_ERROR_INTR_ALL_MASK);
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}
	} while ((StatusReg & XSDPS_INTR_TC_MASK) == 0);

	/*
	 * Write to clear bit
	 */
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_NORM_INTR_STS_OFFSET, XSDPS_INTR_TC_MASK);

	Status = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
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
int XSdPs_Change_BusSpeed(XSdPs *InstancePtr)
{
	u32 Status = 0;
	u32 StatusReg = 0x0;
	u32 Arg = 0;

#ifndef MMC_CARD
	u32 ClockReg;
	u8 ReadBuff[64];
	u16 BlkCnt;
	u16 BlkSize;
#endif

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

#ifndef MMC_CARD

	BlkCnt = XSDPS_SWITCH_CMD_BLKCNT;
	BlkSize = XSDPS_SWITCH_CMD_BLKSIZE;
	BlkSize &= XSDPS_BLK_SIZE_MASK;
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_BLK_SIZE_OFFSET, BlkSize);

	XSdPs_SetupADMA2DescTbl(InstancePtr, BlkCnt, ReadBuff);

	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_XFER_MODE_OFFSET,
			XSDPS_TM_DAT_DIR_SEL_MASK | XSDPS_TM_DMA_EN_MASK);

	Arg = XSDPS_SWITCH_CMD_HS_SET;
	Status = XSdPs_CmdTransfer(InstancePtr, CMD6, Arg, 1);
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
		if (StatusReg & XSDPS_INTR_ERR_MASK) {
			/*
			 * Write to clear error bits
			 */
			XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
					XSDPS_ERR_INTR_STS_OFFSET,
					XSDPS_ERROR_INTR_ALL_MASK);
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}
	} while ((StatusReg & XSDPS_INTR_TC_MASK) == 0);

	/*
	 * Write to clear bit
	 */
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_NORM_INTR_STS_OFFSET, XSDPS_INTR_TC_MASK);

	ClockReg = XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
			XSDPS_CLK_CTRL_OFFSET);
	ClockReg &= ~(XSDPS_CC_INT_CLK_EN_MASK | XSDPS_CC_SD_CLK_EN_MASK);

	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_CLK_CTRL_OFFSET, ClockReg);

	ClockReg = XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
			XSDPS_CLK_CTRL_OFFSET);
	ClockReg &= (~XSDPS_CC_SDCLK_FREQ_SEL_MASK);
	ClockReg |= XSDPS_CC_SDCLK_FREQ_BASE_MASK | XSDPS_CC_INT_CLK_EN_MASK;
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_CLK_CTRL_OFFSET, ClockReg);

	/*
	 * Wait for internal clock to stabilize
	 */
	while((XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
		XSDPS_CLK_CTRL_OFFSET) & XSDPS_CC_INT_CLK_STABLE_MASK) == 0);

	/*
	 * Enable SD clock
	 */
	ClockReg = XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
			XSDPS_CLK_CTRL_OFFSET);
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_CLK_CTRL_OFFSET,
			ClockReg | XSDPS_CC_SD_CLK_EN_MASK);


	StatusReg = XSdPs_ReadReg8(InstancePtr->Config.BaseAddress,
					XSDPS_HOST_CTRL1_OFFSET);
	StatusReg |= XSDPS_HC_SPEED_MASK;
	XSdPs_WriteReg8(InstancePtr->Config.BaseAddress,
			XSDPS_HOST_CTRL1_OFFSET,StatusReg);

	Status = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
			XSDPS_RESP0_OFFSET);

#else

	Arg = XSDPS_MMC_HIGH_SPEED_ARG;
	Status = XSdPs_CmdTransfer(InstancePtr, CMD6, Arg, 0);
	if (Status != XST_SUCCESS) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

#ifdef __arm__

	usleep(XSDPS_MMC_DELAY_FOR_SWITCH);

#endif

#ifdef __MICROBLAZE__

	/* 2 msec delay */
	MB_Sleep(2);

#endif

	XSdPs_Change_ClkFreq(InstancePtr, XSDPS_CLK_52_MHZ);

	StatusReg = XSdPs_ReadReg8(InstancePtr->Config.BaseAddress,
					XSDPS_HOST_CTRL1_OFFSET);
	StatusReg |= XSDPS_HC_SPEED_MASK;
	XSdPs_WriteReg8(InstancePtr->Config.BaseAddress,
			XSDPS_HOST_CTRL1_OFFSET,StatusReg);

	Status = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
			XSDPS_RESP0_OFFSET);
#endif

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
int XSdPs_Change_ClkFreq(XSdPs *InstancePtr, u32 SelFreq)
{
	u16 ClockReg;
	int DivCnt;
	u16 Divisor;
	u16 ClkLoopCnt;
	int Status;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Disable clock
	 */
	ClockReg = XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
			XSDPS_CLK_CTRL_OFFSET);
	ClockReg &= ~(XSDPS_CC_INT_CLK_EN_MASK | XSDPS_CC_SD_CLK_EN_MASK);

	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_CLK_CTRL_OFFSET, ClockReg);

	/*
	 * Calculate divisor
	 */
	DivCnt = 0x1;
	for(ClkLoopCnt = 0; ClkLoopCnt < XSDPS_CC_MAX_NUM_OF_DIV;
		ClkLoopCnt++) {
		if( ((InstancePtr->Config.InputClockHz)/DivCnt) <= SelFreq) {
			Divisor = DivCnt/2;
			Divisor = Divisor << XSDPS_CC_DIV_SHIFT;
			break;
		}
		DivCnt = DivCnt << 1;
	}

	if(ClkLoopCnt == 9) {

		/*
		 * No valid divisor found for given frequency
		 */
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	/*
	 * Set clock divisor
	 */
	ClockReg = XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
			XSDPS_CLK_CTRL_OFFSET);
	ClockReg &= (~XSDPS_CC_SDCLK_FREQ_SEL_MASK);

	ClockReg |= Divisor | XSDPS_CC_INT_CLK_EN_MASK;
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_CLK_CTRL_OFFSET, ClockReg);

	/*
	 * Wait for internal clock to stabilize
	 */
	while((XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
		XSDPS_CLK_CTRL_OFFSET) & XSDPS_CC_INT_CLK_STABLE_MASK) == 0);

	/*
	 * Enable SD clock
	 */
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
int XSdPs_Pullup(XSdPs *InstancePtr)
{
	u32 Status = 0;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	Status = XSdPs_CmdTransfer(InstancePtr, CMD55,
			InstancePtr->RelCardAddr, 0);
	if (Status != XST_SUCCESS) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	Status = XSdPs_CmdTransfer(InstancePtr, ACMD42, 0, 0);
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
int XSdPs_Get_Mmc_ExtCsd(XSdPs *InstancePtr, u8 *ReadBuff)
{
	u32 Status = 0;
	u32 StatusReg = 0x0;
	u32 Arg = 0;
	u16 BlkCnt;
	u16 BlkSize;
	int LoopCnt;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	for (LoopCnt = 0; LoopCnt < 512; LoopCnt++) {
		ReadBuff[LoopCnt] = 0;
	}

	BlkCnt = XSDPS_EXT_CSD_CMD_BLKCNT;
	BlkSize = XSDPS_EXT_CSD_CMD_BLKSIZE;
	BlkSize &= XSDPS_BLK_SIZE_MASK;
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_BLK_SIZE_OFFSET, BlkSize);

	XSdPs_SetupADMA2DescTbl(InstancePtr, BlkCnt, ReadBuff);

	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_XFER_MODE_OFFSET,
			XSDPS_TM_DAT_DIR_SEL_MASK | XSDPS_TM_DMA_EN_MASK);

	Arg = 0;

	/*
	 * Send SEND_EXT_CSD command
	 */
	Status = XSdPs_CmdTransfer(InstancePtr, CMD8, Arg, 1);
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
		if (StatusReg & XSDPS_INTR_ERR_MASK) {
			/*
			 * Write to clear error bits
			 */
			XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
					XSDPS_ERR_INTR_STS_OFFSET,
					XSDPS_ERROR_INTR_ALL_MASK);
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}
	} while ((StatusReg & XSDPS_INTR_TC_MASK) == 0);

	/*
	 * Write to clear bit
	 */
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_NORM_INTR_STS_OFFSET, XSDPS_INTR_TC_MASK);

	Status = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
			XSDPS_RESP0_OFFSET);

	Status = XST_SUCCESS;

	RETURN_PATH:
		return Status;

}

/** @} */
