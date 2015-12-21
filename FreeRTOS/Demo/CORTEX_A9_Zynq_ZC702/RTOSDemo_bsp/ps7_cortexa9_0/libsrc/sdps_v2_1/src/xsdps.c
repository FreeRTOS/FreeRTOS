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
* @file xsdps.c
* @addtogroup sdps_v2_1
* @{
*
* Contains the interface functions of the XSdPs driver.
* See xsdps.h for a detailed description of the device and driver.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date     Changes
* ----- ---    -------- -----------------------------------------------
* 1.00a hk/sg  10/17/13 Initial release
* 2.0   hk     12/13/13 Added check for arm to use sleep.h and its API's
* 2.1   hk     04/18/14 Add sleep for microblaze designs. CR# 781117.
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
#define XSDPS_CMD8_VOL_PATTERN	0x1AA
#define XSDPS_RESPOCR_READY	0x80000000
#define XSDPS_ACMD41_HCS	0x40000000
#define XSDPS_ACMD41_3V3	0x00300000
#define XSDPS_CMD1_HIGH_VOL	0x00FF8000
#define XSDPS_CMD1_DUAL_VOL	0x00FF8010

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

#define XSDPS_INIT_DELAY	2000

/************************** Function Prototypes ******************************/
u32 XSdPs_FrameCmd(u32 Cmd);
int XSdPs_CmdTransfer(XSdPs *InstancePtr, u32 Cmd, u32 Arg, u32 BlkCnt);
void XSdPs_SetupADMA2DescTbl(XSdPs *InstancePtr, u32 BlkCnt, const u8 *Buff);

/*****************************************************************************/
/**
*
* Initializes a specific XSdPs instance such that the driver is ready to use.
*
*
* @param	InstancePtr is a pointer to the XSdPs instance.
* @param	ConfigPtr is a reference to a structure containing information
*		about a specific SD device. This function initializes an
*		InstancePtr object for a specific device specified by the
*		contents of Config.
* @param	EffectiveAddr is the device base address in the virtual memory
*		address space. The caller is responsible for keeping the address
*		mapping from EffectiveAddr to the device physical base address
*		unchanged once this function is invoked. Unexpected errors may
*		occur if the address mapping changes after this function is
*		called. If address translation is not used, use
*		ConfigPtr->Config.BaseAddress for this device.
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_DEVICE_IS_STARTED if the device is already started.
*		It must be stopped to re-initialize.
*
* @note		This function initializes the host controller.
*		Initial clock of 400KHz is set.
*		Voltage of 3.3V is selected as that is supported by host.
*		Interrupts status is enabled and signal disabled by default.
*		Default data direction is card to host and
*		32 bit ADMA2 is selected. Defualt Block size is 512 bytes.
*
******************************************************************************/
int XSdPs_CfgInitialize(XSdPs *InstancePtr, XSdPs_Config *ConfigPtr,
				u32 EffectiveAddr)
{
	u32 ClockReg;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(ConfigPtr != NULL);

	/*
	 * Set some default values.
	 */
	InstancePtr->Config.BaseAddress = EffectiveAddr;
	InstancePtr->Config.InputClockHz = ConfigPtr->InputClockHz;
	InstancePtr->IsReady = XIL_COMPONENT_IS_READY;

	/*
	 * "Software reset for all" is initiated
	 */
	XSdPs_WriteReg8(InstancePtr->Config.BaseAddress, XSDPS_SW_RST_OFFSET,
			XSDPS_SWRST_ALL_MASK);

	/*
	 * Proceed with initialization only after reset is complete
	 */
	while (XSdPs_ReadReg8(InstancePtr->Config.BaseAddress,
			XSDPS_SW_RST_OFFSET) & XSDPS_SWRST_ALL_MASK);

	/*
	 * Read capabilities register and update it in Instance pointer.
	 * It is sufficient to read this once on power on.
	 */
	InstancePtr->Host_Caps = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
						XSDPS_CAPS_OFFSET);

	/*
	 * SD clock frequency divider 128
	 * Enable the internal clock
	 */
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
		XSDPS_CLK_CTRL_OFFSET,
		XSDPS_CC_SDCLK_FREQ_D128_MASK | XSDPS_CC_INT_CLK_EN_MASK);

	/*
	 * Wait for internal clock to stabilize
	 */
	while ((XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
		XSDPS_CLK_CTRL_OFFSET) & XSDPS_CC_INT_CLK_STABLE_MASK) == 0);

	/*
	 * Enable SD clock
	 */
	ClockReg = XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
			XSDPS_CLK_CTRL_OFFSET);
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
		XSDPS_CLK_CTRL_OFFSET, ClockReg | XSDPS_CC_SD_CLK_EN_MASK);

	/*
	 * Select voltage and enable bus power.
	 */
	XSdPs_WriteReg8(InstancePtr->Config.BaseAddress,
			XSDPS_POWER_CTRL_OFFSET,
			XSDPS_PC_BUS_VSEL_3V3_MASK | XSDPS_PC_BUS_PWR_MASK);

	XSdPs_WriteReg8(InstancePtr->Config.BaseAddress,
			XSDPS_HOST_CTRL1_OFFSET,
			XSDPS_HC_DMA_ADMA2_32_MASK);

	/*
	 * Enable all interrupt status except card interrupt initially
	 */
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_NORM_INTR_STS_EN_OFFSET,
			XSDPS_NORM_INTR_ALL_MASK & (~XSDPS_INTR_CARD_MASK));

	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_ERR_INTR_STS_EN_OFFSET,
			XSDPS_ERROR_INTR_ALL_MASK);

	/*
	 * Disable all interrupt signals by default.
	 */
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_NORM_INTR_SIG_EN_OFFSET, 0x0);
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_ERR_INTR_SIG_EN_OFFSET, 0x0);

	/*
	 * Transfer mode register - default value
	 * DMA enabled, block count enabled, data direction card to host(read)
	 */
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_XFER_MODE_OFFSET,
			XSDPS_TM_DMA_EN_MASK | XSDPS_TM_BLK_CNT_EN_MASK |
			XSDPS_TM_DAT_DIR_SEL_MASK);

	/*
	 * Set block size to 512 by default
	 */
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_BLK_SIZE_OFFSET, XSDPS_BLK_SIZE_512_MASK);

	return XST_SUCCESS;
}

/*****************************************************************************/
/**
* SD initialization is done in this function
*
*
* @param	InstancePtr is a pointer to the instance to be worked on.
*
* @return
* 		- XST_SUCCESS if initialization was successful
* 		- XST_FAILURE if failure - could be because
* 			a) SD is already initialized
* 			b) There is no card inserted
* 			c) One of the steps (commands) in the
			   initialization cycle failed
*
* @note		This function initializes the SD card by following its
*		initialization and identification state diagram.
*		CMD0 is sent to reset card.
*		CMD8 and ACDM41 are sent to identify voltage and
*		high capacity support
*		CMD2 and CMD3 are sent to obtain Card ID and
*		Relative card address respectively.
*		CMD9 is sent to read the card specific data.
*
******************************************************************************/
int XSdPs_SdCardInitialize(XSdPs *InstancePtr)
{
	u32 PresentStateReg;
	u32 Status;
	u32 RespOCR = 0x0;
	u32 CSD[4];

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Check the present state register to make sure
	 * card is inserted and detected by host controller
	 */
	PresentStateReg = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
			XSDPS_PRES_STATE_OFFSET);
	if ((PresentStateReg & XSDPS_PSR_CARD_INSRT_MASK) == 0)	{
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	/*
	 * 74 CLK delay after card is powered up, before the first command.
	 */

#ifdef __arm__

	usleep(XSDPS_INIT_DELAY);

#endif

#ifdef __MICROBLAZE__

	/* 2 msec delay */
	MB_Sleep(2);

#endif

	/*
	 * CMD0 no response expected
	 */
	Status = XSdPs_CmdTransfer(InstancePtr, CMD0, 0, 0);
	if (Status != XST_SUCCESS) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	/*
	 * CMD8; response expected
	 * 0x1AA - Supply Voltage 2.7 - 3.6V and AA is pattern
	 */
	Status = XSdPs_CmdTransfer(InstancePtr, CMD8,
			XSDPS_CMD8_VOL_PATTERN, 0);
	if (Status != XST_SUCCESS) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	RespOCR = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
						XSDPS_RESP0_OFFSET);
	if (RespOCR != XSDPS_CMD8_VOL_PATTERN) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	RespOCR = 0;
	/*
	 * Send ACMD41 while card is still busy with power up
	 */
	while ((RespOCR & XSDPS_RESPOCR_READY) == 0) {
		Status = XSdPs_CmdTransfer(InstancePtr, CMD55, 0, 0);
		if (Status != XST_SUCCESS) {
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}

		/*
		 * 0x40300000 - Host High Capacity support & 3.3V window
		 */
		Status = XSdPs_CmdTransfer(InstancePtr, ACMD41,
				(XSDPS_ACMD41_HCS | XSDPS_ACMD41_3V3), 0);
		if (Status != XST_SUCCESS) {
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}

		/*
		 * Response with card capacity
		 */
		RespOCR = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
				XSDPS_RESP0_OFFSET);

	}

	/*
	 * Update HCS support flag based on card capacity response
	 */
	if (RespOCR & XSDPS_ACMD41_HCS)
		InstancePtr->HCS = 1;

	/*
	 * CMD2 for Card ID
	 */
	Status = XSdPs_CmdTransfer(InstancePtr, CMD2, 0, 0);
	if (Status != XST_SUCCESS) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	InstancePtr->CardID[0] =
			XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
			XSDPS_RESP0_OFFSET);
	InstancePtr->CardID[1] =
			XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
			XSDPS_RESP1_OFFSET);
	InstancePtr->CardID[2] =
			XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
			XSDPS_RESP2_OFFSET);
	InstancePtr->CardID[3] =
			XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
			XSDPS_RESP3_OFFSET);

	while (InstancePtr->RelCardAddr == 0) {
		Status = XSdPs_CmdTransfer(InstancePtr, CMD3, 0, 0);
		if (Status != XST_SUCCESS) {
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}

		/*
		 * Relative card address is stored as the upper 16 bits
		 * This is to avoid shifting when sending commands
		 */
		InstancePtr->RelCardAddr =
				XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
					XSDPS_RESP0_OFFSET) & 0xFFFF0000;
	}

	Status = XSdPs_CmdTransfer(InstancePtr, CMD9, (InstancePtr->RelCardAddr), 0);
	if (Status != XST_SUCCESS) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	/*
	 * Card specific data is read.
	 * Currently not used for any operation.
	 */
	CSD[0] = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
			XSDPS_RESP0_OFFSET);
	CSD[1] = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
			XSDPS_RESP1_OFFSET);
	CSD[2] = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
			XSDPS_RESP2_OFFSET);
	CSD[3] = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
			XSDPS_RESP3_OFFSET);

	Status = XST_SUCCESS;

RETURN_PATH:
	return Status;

}

/*****************************************************************************/
/**
* This function does SD command generation.
*
* @param	InstancePtr is a pointer to the instance to be worked on.
* @param	Cmd is the command to be sent.
* @param	Arg is the argument to be sent along with the command.
* 		This could be address or any other information
* @param	BlkCnt - Block count passed by the user.
*
* @return
* 		- XST_SUCCESS if initialization was successful
* 		- XST_FAILURE if failure - could be because another transfer
* 			is in progress or command or data inhibit is set
*
******************************************************************************/
int XSdPs_CmdTransfer(XSdPs *InstancePtr, u32 Cmd, u32 Arg, u32 BlkCnt)
{
	u32 PresentStateReg;
	u32 CommandReg;
	u32 StatusReg;
	u32 Status;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Check the command inhibit to make sure no other
	 * command transfer is in progress
	 */
	PresentStateReg = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
			XSDPS_PRES_STATE_OFFSET);
	if (PresentStateReg & XSDPS_PSR_INHIBIT_CMD_MASK) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	/*
	 * Write block count register
	 */
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_BLK_CNT_OFFSET, BlkCnt);

	XSdPs_WriteReg8(InstancePtr->Config.BaseAddress,
			XSDPS_TIMEOUT_CTRL_OFFSET, 0xE);

	/*
	 * Write argument register
	 */
	XSdPs_WriteReg(InstancePtr->Config.BaseAddress,
			XSDPS_ARGMT_OFFSET, Arg);

	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_NORM_INTR_STS_OFFSET, XSDPS_NORM_INTR_ALL_MASK);
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_ERR_INTR_STS_OFFSET, XSDPS_ERROR_INTR_ALL_MASK);
	/*
	 * Command register is set to trigger transfer of command
	 */
	CommandReg = XSdPs_FrameCmd(Cmd);

	/*
	 * Mask to avoid writing to reserved bits 31-30
	 * This is necessary because 0x80000000 is used  by this software to
	 * distinguish between ACMD and CMD of same number
	 */
	CommandReg = CommandReg & 0x3FFF;

	/*
	 * Check for data inhibit in case of command using DAT lines
	 */
	PresentStateReg = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
			XSDPS_PRES_STATE_OFFSET);
	if ((PresentStateReg & XSDPS_PSR_INHIBIT_CMD_MASK) &&
			(CommandReg & XSDPS_DAT_PRESENT_SEL_MASK)) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress, XSDPS_CMD_OFFSET,
			CommandReg);

	/*
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
	} while((StatusReg & XSDPS_INTR_CC_MASK) == 0);
	/*
	 * Write to clear bit
	 */
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_NORM_INTR_STS_OFFSET,
			XSDPS_INTR_CC_MASK);

	Status = XST_SUCCESS;

	RETURN_PATH:
		return Status;

}

/*****************************************************************************/
/**
* This function frames the Command register for a particular command.
* Note that this generates only the command register value i.e.
* the upper 16 bits of the transfer mode and command register.
* This value is already shifted to be upper 16 bits and can be directly
* OR'ed with transfer mode register value.
*
* @param	Command to be sent.
*
* @return	Command register value complete with response type and
* 		data, CRC and index related flags.
*
******************************************************************************/
u32 XSdPs_FrameCmd(u32 Cmd)
{
		u32 RetVal;

		RetVal = Cmd;

		switch(Cmd) {
		case CMD0:
			RetVal |= RESP_NONE;
		break;
		case CMD1:
			RetVal |= RESP_R3;
		break;
		case CMD2:
			RetVal |= RESP_R2;
		break;
		case CMD3:
			RetVal |= RESP_R6;
		break;
		case CMD4:
			RetVal |= RESP_NONE;
			break;
		case CMD5:
			RetVal |= RESP_R1B;
		break;

#ifndef MMC_CARD
		case CMD6:
			RetVal |= RESP_R1 | XSDPS_DAT_PRESENT_SEL_MASK;
			break;
#else
		case CMD6:
			RetVal |= RESP_R1B;
			break;
#endif

		case ACMD6:
			RetVal |= RESP_R1;
		break;
		case CMD7:
			RetVal |= RESP_R1;
		break;

#ifndef MMC_CARD
		case CMD8:
			RetVal |= RESP_R1;
			break;
#else
		case CMD8:
			RetVal |= RESP_R1 | XSDPS_DAT_PRESENT_SEL_MASK;
			break;
#endif

		case CMD9:
			RetVal |= RESP_R2;
		break;
		case CMD10:
		case CMD12:
		case ACMD13:
		case CMD16:
			RetVal |= RESP_R1;
		break;
		case CMD17:
		case CMD18:
			RetVal |= RESP_R1 | XSDPS_DAT_PRESENT_SEL_MASK;
		break;
		case CMD23:
		case ACMD23:
		case CMD24:
		case CMD25:
			RetVal |= RESP_R1 | XSDPS_DAT_PRESENT_SEL_MASK;
		case ACMD41:
			RetVal |= RESP_R3;
		break;
		case ACMD42:
			RetVal |= RESP_R1;
		break;
		case ACMD51:
			RetVal |= RESP_R1 | XSDPS_DAT_PRESENT_SEL_MASK;
		break;
		case CMD52:
		case CMD55:
			RetVal |= RESP_R1;
		break;
		case CMD58:
		break;
		}

		return RetVal;
}

/*****************************************************************************/
/**
* This function performs SD read in polled mode.
*
* @param	InstancePtr is a pointer to the instance to be worked on.
* @param	Arg is the address passed by the user that is to be sent as
* 		argument along with the command.
* @param	BlkCnt - Block count passed by the user.
* @param	Buff - Pointer to the data buffer for a DMA transfer.
*
* @return
* 		- XST_SUCCESS if initialization was successful
* 		- XST_FAILURE if failure - could be because another transfer
* 		is in progress or command or data inhibit is set
*
******************************************************************************/
int XSdPs_ReadPolled(XSdPs *InstancePtr, u32 Arg, u32 BlkCnt, u8 *Buff)
{
	u32 Status;
	u32 PresentStateReg;
	u32 StatusReg;

	/*
	 * Check status to ensure card is initialized
	 */
	PresentStateReg = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
			XSDPS_PRES_STATE_OFFSET);
	if ((PresentStateReg & XSDPS_PSR_CARD_INSRT_MASK) == 0x0) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	/*
	 * Set block size to 512 if not already set
	 */
	if( XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
			XSDPS_BLK_SIZE_OFFSET) != XSDPS_BLK_SIZE_512_MASK ) {
		Status = XSdPs_SetBlkSize(InstancePtr,
			XSDPS_BLK_SIZE_512_MASK);
		if (Status != XST_SUCCESS) {
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}
	}

	XSdPs_SetupADMA2DescTbl(InstancePtr, BlkCnt, Buff);

	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_XFER_MODE_OFFSET,
			XSDPS_TM_AUTO_CMD12_EN_MASK |
			XSDPS_TM_BLK_CNT_EN_MASK | XSDPS_TM_DAT_DIR_SEL_MASK |
			XSDPS_TM_DMA_EN_MASK | XSDPS_TM_MUL_SIN_BLK_SEL_MASK);

	/*
	 * Send block read command
	 */
	Status = XSdPs_CmdTransfer(InstancePtr, CMD18, Arg, BlkCnt);
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
	} while((StatusReg & XSDPS_INTR_TC_MASK) == 0);

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
* This function performs SD write in polled mode.
*
* @param	InstancePtr is a pointer to the instance to be worked on.
* @param	Arg is the address passed by the user that is to be sent as
* 		argument along with the command.
* @param	BlkCnt - Block count passed by the user.
* @param	Buff - Pointer to the data buffer for a DMA transfer.
*
* @return
* 		- XST_SUCCESS if initialization was successful
* 		- XST_FAILURE if failure - could be because another transfer
* 		is in progress or command or data inhibit is set
*
******************************************************************************/
int XSdPs_WritePolled(XSdPs *InstancePtr, u32 Arg, u32 BlkCnt, const u8 *Buff)
{
	u32 Status;
	u32 PresentStateReg;
	u32 StatusReg;

	/*
	 * Check status to ensure card is initialized
	 */
	PresentStateReg = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
			XSDPS_PRES_STATE_OFFSET);
	if ((PresentStateReg & XSDPS_PSR_CARD_INSRT_MASK) == 0x0) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	/*
	 * Set block size to 512 if not already set
	 */
	if( XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
			XSDPS_BLK_SIZE_OFFSET) != XSDPS_BLK_SIZE_512_MASK ) {
		Status = XSdPs_SetBlkSize(InstancePtr,
			XSDPS_BLK_SIZE_512_MASK);
		if (Status != XST_SUCCESS) {
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}

	}

	XSdPs_SetupADMA2DescTbl(InstancePtr, BlkCnt, Buff);

	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_XFER_MODE_OFFSET,
			XSDPS_TM_AUTO_CMD12_EN_MASK |
			XSDPS_TM_BLK_CNT_EN_MASK |
			XSDPS_TM_MUL_SIN_BLK_SEL_MASK | XSDPS_TM_DMA_EN_MASK);

	/*
	 * Send block write command
	 */
	Status = XSdPs_CmdTransfer(InstancePtr, CMD25, Arg, BlkCnt);
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
	} while((StatusReg & XSDPS_INTR_TC_MASK) == 0);

	/*
	 * Write to clear bit
	 */
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_NORM_INTR_STS_OFFSET, XSDPS_INTR_TC_MASK);

	Status = XST_SUCCESS;

	RETURN_PATH:
		return Status;
}

/*****************************************************************************/
/**
*
* Selects card and sets default block size
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
int XSdPs_Select_Card (XSdPs *InstancePtr)
{
	u32 Status = 0;

	/*
	 * Send CMD7 - Select card
	 */
	Status = XSdPs_CmdTransfer(InstancePtr, CMD7,
			InstancePtr->RelCardAddr, 0);
	if (Status != XST_SUCCESS) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	Status = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
			XSDPS_RESP0_OFFSET);

	/*
	 * Set default block size
	 */
	Status = XSdPs_SetBlkSize(InstancePtr, XSDPS_BLK_SIZE_512_MASK);
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
* API to setup ADMA2 descriptor table
*
*
* @param	InstancePtr is a pointer to the XSdPs instance.
* @param	BlkCnt - block count.
* @param	Buff pointer to data buffer.
*
* @return	None
*
* @note		None.
*
******************************************************************************/
void XSdPs_SetupADMA2DescTbl(XSdPs *InstancePtr, u32 BlkCnt, const u8 *Buff)
{
	u32 TotalDescLines = 0;
	u32 DescNum = 0;
	u32 BlkSize = 0;

	/*
	 * Setup ADMA2 - Write descriptor table and point ADMA SAR to it
	 */
	BlkSize = XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
					XSDPS_BLK_SIZE_OFFSET);
	BlkSize = BlkSize & XSDPS_BLK_SIZE_MASK;

	if((BlkCnt*BlkSize) < XSDPS_DESC_MAX_LENGTH) {

		TotalDescLines = 1;

	}else {

		TotalDescLines = ((BlkCnt*BlkSize) / XSDPS_DESC_MAX_LENGTH);
		if ((BlkCnt * BlkSize) % XSDPS_DESC_MAX_LENGTH)
			TotalDescLines += 1;

	}

	for (DescNum = 0; DescNum < (TotalDescLines-1); DescNum++) {
		InstancePtr->Adma2_DescrTbl[DescNum].Address =
				(u32)(Buff + (DescNum*XSDPS_DESC_MAX_LENGTH));
		InstancePtr->Adma2_DescrTbl[DescNum].Attribute =
				XSDPS_DESC_TRAN | XSDPS_DESC_VALID;
		/*
		 * This will write '0' to length field which indicates 65536
		 */
		InstancePtr->Adma2_DescrTbl[DescNum].Length =
				(u16)XSDPS_DESC_MAX_LENGTH;
	}

	InstancePtr->Adma2_DescrTbl[TotalDescLines-1].Address =
			(u32)(Buff + (DescNum*XSDPS_DESC_MAX_LENGTH));

	InstancePtr->Adma2_DescrTbl[TotalDescLines-1].Attribute =
			XSDPS_DESC_TRAN | XSDPS_DESC_END | XSDPS_DESC_VALID;

	InstancePtr->Adma2_DescrTbl[TotalDescLines-1].Length =
			(BlkCnt*BlkSize) - (DescNum*XSDPS_DESC_MAX_LENGTH);


	XSdPs_WriteReg(InstancePtr->Config.BaseAddress, XSDPS_ADMA_SAR_OFFSET,
			(u32)&(InstancePtr->Adma2_DescrTbl[0]));

}

/*****************************************************************************/
/**
* Mmc initialization is done in this function
*
*
* @param	InstancePtr is a pointer to the instance to be worked on.
*
* @return
* 		- XST_SUCCESS if initialization was successful
* 		- XST_FAILURE if failure - could be because
* 			a) MMC is already initialized
* 			b) There is no card inserted
* 			c) One of the steps (commands) in the initialization
*			   cycle failed
* @note 	This function initializes the SD card by following its
*		initialization and identification state diagram.
*		CMD0 is sent to reset card.
*		CMD1 sent to identify voltage and high capacity support
*		CMD2 and CMD3 are sent to obtain Card ID and
*		Relative card address respectively.
*		CMD9 is sent to read the card specific data.
*
******************************************************************************/
int XSdPs_MmcCardInitialize(XSdPs *InstancePtr)
{
	u32 PresentStateReg;
	u32 Status;
	u32 RespOCR = 0x0;
	u32 CSD[4];

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Check the present state register to make sure
	 * card is inserted and detected by host controller
	 */
	PresentStateReg = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
			XSDPS_PRES_STATE_OFFSET);
	if ((PresentStateReg & XSDPS_PSR_CARD_INSRT_MASK) == 0)	{
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	/*
	 * 74 CLK delay after card is powered up, before the first command.
	 */

#ifdef __arm__

	usleep(XSDPS_INIT_DELAY);

#endif

#ifdef __MICROBLAZE__

	/* 2 msec delay */
	MB_Sleep(2);

#endif

	/*
	 * CMD0 no response expected
	 */
	Status = XSdPs_CmdTransfer(InstancePtr, CMD0, 0, 0);
	if (Status != XST_SUCCESS) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	RespOCR = 0;
	/*
	 * Send CMD1 while card is still busy with power up
	 */
	while ((RespOCR & XSDPS_RESPOCR_READY) == 0) {

		/*
		 * Host High Capacity support & High volage window
		 */
		Status = XSdPs_CmdTransfer(InstancePtr, CMD1,
				XSDPS_ACMD41_HCS | XSDPS_CMD1_HIGH_VOL, 0);
		if (Status != XST_SUCCESS) {
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}

		/*
		 * Response with card capacity
		 */
		RespOCR = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
				XSDPS_RESP0_OFFSET);

	}

	/*
	 * Update HCS support flag based on card capacity response
	 */
	if (RespOCR & XSDPS_ACMD41_HCS)
		InstancePtr->HCS = 1;

	/*
	 * CMD2 for Card ID
	 */
	Status = XSdPs_CmdTransfer(InstancePtr, CMD2, 0, 0);
	if (Status != XST_SUCCESS) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	InstancePtr->CardID[0] =
			XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
			XSDPS_RESP0_OFFSET);
	InstancePtr->CardID[1] =
			XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
			XSDPS_RESP1_OFFSET);
	InstancePtr->CardID[2] =
			XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
			XSDPS_RESP2_OFFSET);
	InstancePtr->CardID[3] =
			XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
			XSDPS_RESP3_OFFSET);

	Status = XSdPs_CmdTransfer(InstancePtr, CMD3, 0, 0);
	if (Status != XST_SUCCESS) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	/*
	 * Relative card address is stored as the upper 16 bits
	 * This is to avoid shifting when sending commands
	 */
	InstancePtr->RelCardAddr =
			XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
				XSDPS_RESP0_OFFSET) & 0xFFFF0000;

	Status = XSdPs_CmdTransfer(InstancePtr, CMD9, (InstancePtr->RelCardAddr), 0);
	if (Status != XST_SUCCESS) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	/*
	 * Card specific data is read.
	 * Currently not used for any operation.
	 */
	CSD[0] = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
			XSDPS_RESP0_OFFSET);
	CSD[1] = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
			XSDPS_RESP1_OFFSET);
	CSD[2] = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
			XSDPS_RESP2_OFFSET);
	CSD[3] = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
			XSDPS_RESP3_OFFSET);

	Status = XST_SUCCESS;

RETURN_PATH:
	return Status;

}


/** @} */
