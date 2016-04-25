/******************************************************************************
*
* Copyright (C) 2013 - 2015 Xilinx, Inc.  All rights reserved.
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
* @addtogroup sdps_v2_5
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
* 2.2   hk     07/28/14 Make changes to enable use of data cache.
* 2.3   sk     09/23/14 Send command for relative card address
*                       when re-initialization is done.CR# 819614.
*						Use XSdPs_Change_ClkFreq API whenever changing
*						clock.CR# 816586.
* 2.4	sk	   12/04/14 Added support for micro SD without
* 						WP/CD. CR# 810655.
*						Checked for DAT Inhibit mask instead of CMD
* 						Inhibit mask in Cmd Transfer API.
*						Added Support for SD Card v1.0
* 2.5 	sg	   07/09/15 Added SD 3.0 features
*       kvn    07/15/15 Modified the code according to MISRAC-2012.
* 2.6   sk     10/12/15 Added support for SD card v1.0 CR# 840601.
* 2.7   sk     11/24/15 Considered the slot type befoe checking CD/WP pins.
*       sk     12/10/15 Added support for MMC cards.
*       sk     02/16/16 Corrected the Tuning logic.
*       sk     03/01/16 Removed Bus Width check for eMMC. CR# 938311.
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/
#include "xsdps.h"
/*
 * The header sleep.h and API usleep() can only be used with an arm design.
 * MB_Sleep() is used for microblaze design.
 */
#if defined (__arm__) || defined (__aarch64__)

#include "sleep.h"

#endif

#ifdef __MICROBLAZE__

#include "microblaze_sleep.h"

#endif

/************************** Constant Definitions *****************************/
#define XSDPS_CMD8_VOL_PATTERN	0x1AAU
#define XSDPS_RESPOCR_READY	0x80000000U
#define XSDPS_ACMD41_HCS	0x40000000U
#define XSDPS_ACMD41_3V3	0x00300000U
#define XSDPS_CMD1_HIGH_VOL	0x00FF8000U
#define XSDPS_CMD1_DUAL_VOL	0x00FF8010U
#define HIGH_SPEED_SUPPORT	0x2U
#define WIDTH_4_BIT_SUPPORT	0x4U
#define SD_CLK_25_MHZ		25000000U
#define SD_CLK_26_MHZ		26000000U
#define EXT_CSD_DEVICE_TYPE_BYTE	196U
#define EXT_CSD_DEVICE_TYPE_HIGH_SPEED			0x2U
#define EXT_CSD_DEVICE_TYPE_DDR_1V8_HIGH_SPEED	0x4U
#define EXT_CSD_DEVICE_TYPE_DDR_1V2_HIGH_SPEED	0x8U
#define EXT_CSD_DEVICE_TYPE_SDR_1V8_HS200		0x10U
#define EXT_CSD_DEVICE_TYPE_SDR_1V2_HS200		0x20U
#define CSD_SPEC_VER_3		0x3U

/* Note: Remove this once fixed */
#define UHS_BROKEN

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/
u32 XSdPs_FrameCmd(XSdPs *InstancePtr, u32 Cmd);
s32 XSdPs_CmdTransfer(XSdPs *InstancePtr, u32 Cmd, u32 Arg, u32 BlkCnt);
void XSdPs_SetupADMA2DescTbl(XSdPs *InstancePtr, u32 BlkCnt, const u8 *Buff);
extern s32 XSdPs_Uhs_ModeInit(XSdPs *InstancePtr, u8 Mode);
static s32 XSdPs_IdentifyCard(XSdPs *InstancePtr);
static s32 XSdPs_Switch_Voltage(XSdPs *InstancePtr);

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
s32 XSdPs_CfgInitialize(XSdPs *InstancePtr, XSdPs_Config *ConfigPtr,
				u32 EffectiveAddr)
{
	s32 Status;
	u8 PowerLevel;
	u8 ReadReg;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(ConfigPtr != NULL);

	/* Set some default values. */
	InstancePtr->Config.BaseAddress = EffectiveAddr;
	InstancePtr->Config.InputClockHz = ConfigPtr->InputClockHz;
	InstancePtr->IsReady = XIL_COMPONENT_IS_READY;
	InstancePtr->Config.CardDetect =  ConfigPtr->CardDetect;
	InstancePtr->Config.WriteProtect =  ConfigPtr->WriteProtect;

	/* Disable bus power */
	XSdPs_WriteReg8(InstancePtr->Config.BaseAddress,
			XSDPS_POWER_CTRL_OFFSET, 0U);

	/* Delay to poweroff card */
#if defined (__arm__) || defined (__aarch64__)

    (void)sleep(1U);

#endif

#ifdef __MICROBLAZE__

    MB_Sleep(1000U);

#endif

	/* "Software reset for all" is initiated */
	XSdPs_WriteReg8(InstancePtr->Config.BaseAddress, XSDPS_SW_RST_OFFSET,
			XSDPS_SWRST_ALL_MASK);

	/* Proceed with initialization only after reset is complete */
	ReadReg = XSdPs_ReadReg8(InstancePtr->Config.BaseAddress,
				XSDPS_SW_RST_OFFSET);
	while ((ReadReg & XSDPS_SWRST_ALL_MASK) != 0U) {
		ReadReg = XSdPs_ReadReg8(InstancePtr->Config.BaseAddress,
				XSDPS_SW_RST_OFFSET);
	}
	/* Host Controller version is read. */
	 InstancePtr->HC_Version =
			(u8)(XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
			XSDPS_HOST_CTRL_VER_OFFSET) & XSDPS_HC_SPEC_VER_MASK);

	/*
	 * Read capabilities register and update it in Instance pointer.
	 * It is sufficient to read this once on power on.
	 */
	InstancePtr->Host_Caps = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
						XSDPS_CAPS_OFFSET);

	/* Select voltage and enable bus power. */
	XSdPs_WriteReg8(InstancePtr->Config.BaseAddress,
			XSDPS_POWER_CTRL_OFFSET,
			XSDPS_PC_BUS_VSEL_3V3_MASK | XSDPS_PC_BUS_PWR_MASK);

	/* Change the clock frequency to 400 KHz */
	Status = XSdPs_Change_ClkFreq(InstancePtr, XSDPS_CLK_400_KHZ);
	if (Status != XST_SUCCESS) {
		Status = XST_FAILURE;
		goto RETURN_PATH ;
	}

    if ((InstancePtr->Host_Caps & XSDPS_CAP_VOLT_3V3_MASK) != 0U) {
		PowerLevel = XSDPS_PC_BUS_VSEL_3V3_MASK;
	} else if ((InstancePtr->Host_Caps & XSDPS_CAP_VOLT_3V0_MASK) != 0U) {
		PowerLevel = XSDPS_PC_BUS_VSEL_3V0_MASK;
	} else if ((InstancePtr->Host_Caps & XSDPS_CAP_VOLT_1V8_MASK) != 0U) {
		PowerLevel = XSDPS_PC_BUS_VSEL_1V8_MASK;
	} else {
		PowerLevel = 0U;
	}

	/* Select voltage based on capability and enable bus power. */
	XSdPs_WriteReg8(InstancePtr->Config.BaseAddress,
			XSDPS_POWER_CTRL_OFFSET,
			PowerLevel | XSDPS_PC_BUS_PWR_MASK);
	/* Enable ADMA2 in 64bit mode. */
	XSdPs_WriteReg8(InstancePtr->Config.BaseAddress,
			XSDPS_HOST_CTRL1_OFFSET,
			XSDPS_HC_DMA_ADMA2_32_MASK);

	/* Enable all interrupt status except card interrupt initially */
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_NORM_INTR_STS_EN_OFFSET,
			XSDPS_NORM_INTR_ALL_MASK & (~XSDPS_INTR_CARD_MASK));

	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_ERR_INTR_STS_EN_OFFSET,
			XSDPS_ERROR_INTR_ALL_MASK);

	/* Disable all interrupt signals by default. */
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_NORM_INTR_SIG_EN_OFFSET, 0x0U);
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_ERR_INTR_SIG_EN_OFFSET, 0x0U);

	/*
	 * Transfer mode register - default value
	 * DMA enabled, block count enabled, data direction card to host(read)
	 */
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_XFER_MODE_OFFSET,
			XSDPS_TM_DMA_EN_MASK | XSDPS_TM_BLK_CNT_EN_MASK |
			XSDPS_TM_DAT_DIR_SEL_MASK);

	/* Set block size to 512 by default */
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_BLK_SIZE_OFFSET, XSDPS_BLK_SIZE_512_MASK);

	Status = XST_SUCCESS;

RETURN_PATH:
	return Status;

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
s32 XSdPs_SdCardInitialize(XSdPs *InstancePtr)
{
	u32 PresentStateReg;
	s32 Status;
	u32 RespOCR;
	u32 CSD[4];
	u32 Arg;
	u8 ReadReg;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	if ((InstancePtr->HC_Version != XSDPS_HC_SPEC_V3) ||
				((InstancePtr->Host_Caps & XSDPS_CAPS_SLOT_TYPE_MASK)
				!= XSDPS_CAPS_EMB_SLOT)) {
		if(InstancePtr->Config.CardDetect != 0U) {
			/*
			 * Check the present state register to make sure
			 * card is inserted and detected by host controller
			 */
			PresentStateReg = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
					XSDPS_PRES_STATE_OFFSET);
			if ((PresentStateReg & XSDPS_PSR_CARD_INSRT_MASK) == 0U)	{
				Status = XST_FAILURE;
				goto RETURN_PATH;
			}
		}
	}

	/* CMD0 no response expected */
	Status = XSdPs_CmdTransfer(InstancePtr, (u32)CMD0, 0U, 0U);
	if (Status != XST_SUCCESS) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	/*
	 * CMD8; response expected
	 * 0x1AA - Supply Voltage 2.7 - 3.6V and AA is pattern
	 */
	Status = XSdPs_CmdTransfer(InstancePtr, CMD8,
			XSDPS_CMD8_VOL_PATTERN, 0U);
	if ((Status != XST_SUCCESS) && (Status != XSDPS_CT_ERROR)) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	if (Status == XSDPS_CT_ERROR) {
		 /* "Software reset for all" is initiated */
		XSdPs_WriteReg8(InstancePtr->Config.BaseAddress, XSDPS_SW_RST_OFFSET,
				XSDPS_SWRST_CMD_LINE_MASK);

		/* Proceed with initialization only after reset is complete */
		ReadReg = XSdPs_ReadReg8(InstancePtr->Config.BaseAddress,
						XSDPS_SW_RST_OFFSET);
		while ((ReadReg & XSDPS_SWRST_CMD_LINE_MASK) != 0U) {
			ReadReg = XSdPs_ReadReg8(InstancePtr->Config.BaseAddress,
						XSDPS_SW_RST_OFFSET);
		}
	}

	RespOCR = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
						XSDPS_RESP0_OFFSET);
	if (RespOCR != XSDPS_CMD8_VOL_PATTERN) {
		InstancePtr->Card_Version = XSDPS_SD_VER_1_0;
	}
	else {
		InstancePtr->Card_Version = XSDPS_SD_VER_2_0;
	}

	RespOCR = 0U;
	/* Send ACMD41 while card is still busy with power up */
	while ((RespOCR & XSDPS_RESPOCR_READY) == 0U) {
		Status = XSdPs_CmdTransfer(InstancePtr, CMD55, 0U, 0U);
		if (Status != XST_SUCCESS) {
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}

        Arg = XSDPS_ACMD41_HCS | XSDPS_ACMD41_3V3 | (0x1FFU << 15U);
		if (InstancePtr->HC_Version == XSDPS_HC_SPEC_V3) {
		    Arg |= XSDPS_OCR_S18;
		}

		/* 0x40300000 - Host High Capacity support & 3.3V window */
		Status = XSdPs_CmdTransfer(InstancePtr, ACMD41,
				Arg, 0U);
		if (Status != XST_SUCCESS) {
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}

		/* Response with card capacity */
		RespOCR = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
				XSDPS_RESP0_OFFSET);

	}

	/* Update HCS support flag based on card capacity response */
	if ((RespOCR & XSDPS_ACMD41_HCS) != 0U) {
		InstancePtr->HCS = 1U;
	}

	/* There is no support to switch to 1.8V and use UHS mode on 1.0 silicon */
#ifndef UHS_BROKEN
    if ((RespOCR & XSDPS_OCR_S18) != 0U) {
		InstancePtr->Switch1v8 = 1U;
		Status = XSdPs_Switch_Voltage(InstancePtr);
		if (Status != XST_SUCCESS) {
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}

	}
#endif

	/* CMD2 for Card ID */
	Status = XSdPs_CmdTransfer(InstancePtr, CMD2, 0U, 0U);
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
	do {
		Status = XSdPs_CmdTransfer(InstancePtr, CMD3, 0U, 0U);
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
					XSDPS_RESP0_OFFSET) & 0xFFFF0000U;
	} while (InstancePtr->RelCardAddr == 0U);

	Status = XSdPs_CmdTransfer(InstancePtr, CMD9, (InstancePtr->RelCardAddr), 0U);
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
*
* Initialize Card with Identification mode sequence
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
*			   initialization cycle failed
*
*
******************************************************************************/
s32 XSdPs_CardInitialize(XSdPs *InstancePtr) {
	u8 Tmp;
	u32 Cnt;
	u32 PresentStateReg;
	u32 CtrlReg;
	u32 CSD[4];
#ifdef __ICCARM__
#pragma data_alignment = 32
static u8 ExtCsd[512];
#pragma data_alignment = 4
#else
static u8 ExtCsd[512] __attribute__ ((aligned(32)));
#endif
	u8 SCR[8] = { 0U };
	u8 ReadBuff[64] = { 0U };
	s32 Status;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/* Default settings */
	InstancePtr->BusWidth = XSDPS_1_BIT_WIDTH;
	InstancePtr->CardType = XSDPS_CARD_SD;
	InstancePtr->Switch1v8 = 0U;
	InstancePtr->BusSpeed = XSDPS_CLK_400_KHZ;

	if ((InstancePtr->HC_Version == XSDPS_HC_SPEC_V3) &&
			((InstancePtr->Host_Caps & XSDPS_CAPS_SLOT_TYPE_MASK)
			== XSDPS_CAPS_EMB_SLOT)) {
		InstancePtr->CardType = XSDPS_CHIP_EMMC;
	} else {
		Status = XSdPs_IdentifyCard(InstancePtr);
		if (Status == XST_FAILURE) {
			goto RETURN_PATH;
		}
	}

	if ((InstancePtr->CardType != XSDPS_CARD_SD) &&
		(InstancePtr->CardType != XSDPS_CARD_MMC) &&
		(InstancePtr->CardType != XSDPS_CHIP_EMMC)) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	if (InstancePtr->CardType == XSDPS_CARD_SD) {
		Status = XSdPs_SdCardInitialize(InstancePtr);
		if (Status != XST_SUCCESS) {
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}

		/* Change clock to default clock 25MHz */
		InstancePtr->BusSpeed = SD_CLK_25_MHZ;
		Status = XSdPs_Change_ClkFreq(InstancePtr, InstancePtr->BusSpeed);
		if (Status != XST_SUCCESS) {
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}

	} else if ((InstancePtr->CardType == XSDPS_CARD_MMC)
			|| (InstancePtr->CardType == XSDPS_CHIP_EMMC)) {
		Status = XSdPs_MmcCardInitialize(InstancePtr);
		if (Status != XST_SUCCESS) {
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}
		/* Change clock to default clock 26MHz */
		InstancePtr->BusSpeed = SD_CLK_26_MHZ;
		Status = XSdPs_Change_ClkFreq(InstancePtr, InstancePtr->BusSpeed);
		if (Status != XST_SUCCESS) {
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}
	} else {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	Status = XSdPs_Select_Card(InstancePtr);
	if (Status != XST_SUCCESS) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	if (InstancePtr->CardType == XSDPS_CARD_SD) {
		/* Pull-up disconnected during data transfer */
		Status = XSdPs_Pullup(InstancePtr);
		if (Status != XST_SUCCESS) {
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}

		Status = XSdPs_Get_BusWidth(InstancePtr, SCR);
		if (Status != XST_SUCCESS) {
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}

		if ((SCR[1] & WIDTH_4_BIT_SUPPORT) != 0U) {
			Status = XSdPs_Change_BusWidth(InstancePtr);
			if (Status != XST_SUCCESS) {
				Status = XST_FAILURE;
				goto RETURN_PATH;
			}
		}

		if ((InstancePtr->Switch1v8 != 0U) &&
				(InstancePtr->BusWidth == XSDPS_4_BIT_WIDTH)) {
			/* Set UHS-I SDR104 mode */
			Status = XSdPs_Uhs_ModeInit(InstancePtr,
					XSDPS_UHS_SPEED_MODE_SDR104);
			if (Status != XST_SUCCESS) {
				Status = XST_FAILURE;
				goto RETURN_PATH;
			}

		} else {

			/*
			 * card supports CMD6 when SD_SPEC field in SCR register
			 * indicates that the Physical Layer Specification Version
			 * is 1.10 or later. So for SD v1.0 cmd6 is not supported.
			 */
			if (SCR[0] != 0U) {
				/* Get speed supported by device */
				Status = XSdPs_Get_BusSpeed(InstancePtr, ReadBuff);
				if (Status != XST_SUCCESS) {
					Status = XST_FAILURE;
					goto RETURN_PATH;
				}

				/* Check for high speed support */
				if ((ReadBuff[13] & HIGH_SPEED_SUPPORT) != 0U) {
					Status = XSdPs_Change_BusSpeed(InstancePtr);
					if (Status != XST_SUCCESS) {
						Status = XST_FAILURE;
						goto RETURN_PATH;
					}
				}
			}
		}

	} else if (((InstancePtr->CardType == XSDPS_CARD_MMC) &&
				(InstancePtr->Card_Version > CSD_SPEC_VER_3)) &&
				(InstancePtr->HC_Version == XSDPS_HC_SPEC_V2)) {

		Status = XSdPs_Change_BusWidth(InstancePtr);
		if (Status != XST_SUCCESS) {
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}

		Status = XSdPs_Get_Mmc_ExtCsd(InstancePtr, ExtCsd);
		if (Status != XST_SUCCESS) {
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}

		if ((ExtCsd[EXT_CSD_DEVICE_TYPE_BYTE] &
				EXT_CSD_DEVICE_TYPE_HIGH_SPEED) != 0U) {
			Status = XSdPs_Change_BusSpeed(InstancePtr);
			if (Status != XST_SUCCESS) {
				Status = XST_FAILURE;
				goto RETURN_PATH;
			}

			Status = XSdPs_Get_Mmc_ExtCsd(InstancePtr, ExtCsd);
			if (Status != XST_SUCCESS) {
				Status = XST_FAILURE;
				goto RETURN_PATH;
			}

			if (ExtCsd[EXT_CSD_HS_TIMING_BYTE] != EXT_CSD_HS_TIMING_HIGH) {
				Status = XST_FAILURE;
				goto RETURN_PATH;
			}
		}
	} else if (InstancePtr->CardType == XSDPS_CHIP_EMMC){
		/* Change bus width to 8-bit */
		Status = XSdPs_Change_BusWidth(InstancePtr);
		if (Status != XST_SUCCESS) {
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}

		/* Get Extended CSD */
		Status = XSdPs_Get_Mmc_ExtCsd(InstancePtr, ExtCsd);
		if (Status != XST_SUCCESS) {
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}

		if ((ExtCsd[EXT_CSD_DEVICE_TYPE_BYTE] &
				(EXT_CSD_DEVICE_TYPE_SDR_1V8_HS200 |
				EXT_CSD_DEVICE_TYPE_SDR_1V2_HS200)) != 0U) {
			Status = XSdPs_Change_BusSpeed(InstancePtr);
			if (Status != XST_SUCCESS) {
				Status = XST_FAILURE;
				goto RETURN_PATH;
			}

			Status = XSdPs_Get_Mmc_ExtCsd(InstancePtr, ExtCsd);
			if (Status != XST_SUCCESS) {
				Status = XST_FAILURE;
				goto RETURN_PATH;
			}

			if (ExtCsd[EXT_CSD_HS_TIMING_BYTE] != EXT_CSD_HS_TIMING_HS200) {
				Status = XST_FAILURE;
				goto RETURN_PATH;
			}
		}
	}

	Status = XSdPs_SetBlkSize(InstancePtr, XSDPS_BLK_SIZE_512_MASK);
	if (Status != XST_SUCCESS) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

RETURN_PATH:
	return Status;
}

/*****************************************************************************/
/**
*
* Identify type of card using CMD0 + CMD1 sequence
*
*
* @param	InstancePtr is a pointer to the XSdPs instance.
*
******************************************************************************/
static s32 XSdPs_IdentifyCard(XSdPs *InstancePtr)
{
	s32 Status;
	u32 OperCondReg;
	u8 ReadReg;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/* 74 CLK delay after card is powered up, before the first command. */
#if defined (__arm__) || defined (__aarch64__)

	usleep(XSDPS_INIT_DELAY);

#endif

#ifdef __MICROBLAZE__

	/* 2 msec delay */
	MB_Sleep(2);

#endif

	/* CMD0 no response expected */
	Status = XSdPs_CmdTransfer(InstancePtr, CMD0, 0U, 0U);
	if (Status != XST_SUCCESS) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	/* Host High Capacity support & High voltage window */
	Status = XSdPs_CmdTransfer(InstancePtr, CMD1,
			XSDPS_ACMD41_HCS | XSDPS_CMD1_HIGH_VOL, 0U);
	if (Status != XST_SUCCESS) {
		InstancePtr->CardType = XSDPS_CARD_SD;
	} else {
		InstancePtr->CardType = XSDPS_CARD_MMC;
	}

	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_NORM_INTR_STS_OFFSET, XSDPS_NORM_INTR_ALL_MASK);
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_ERR_INTR_STS_OFFSET, XSDPS_ERROR_INTR_ALL_MASK);

	/* "Software reset for all" is initiated */
	XSdPs_WriteReg8(InstancePtr->Config.BaseAddress, XSDPS_SW_RST_OFFSET,
			XSDPS_SWRST_CMD_LINE_MASK);

	/* Proceed with initialization only after reset is complete */
	ReadReg = XSdPs_ReadReg8(InstancePtr->Config.BaseAddress,
					XSDPS_SW_RST_OFFSET);
	while ((ReadReg & XSDPS_SWRST_CMD_LINE_MASK) != 0U) {
		ReadReg = XSdPs_ReadReg8(InstancePtr->Config.BaseAddress,
					XSDPS_SW_RST_OFFSET);
	}

	Status = XST_SUCCESS;

RETURN_PATH:
	return Status;
}

/*****************************************************************************/
/**
*
* Switches the SD card voltage from 3v3 to 1v8
*
*
* @param	InstancePtr is a pointer to the XSdPs instance.
*
******************************************************************************/
static s32 XSdPs_Switch_Voltage(XSdPs *InstancePtr)
{
	s32 Status;
	u16 CtrlReg;
	u32 ReadReg;

	/* Send switch voltage command */
	Status = XSdPs_CmdTransfer(InstancePtr, CMD11, 0U, 0U);
	if (Status != XST_SUCCESS) {
		Status = XST_FAILURE;
	}

	/* Wait for CMD and DATA line to go low */
	ReadReg = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
				XSDPS_PRES_STATE_OFFSET);
	while ((ReadReg & (XSDPS_PSR_CMD_SG_LVL_MASK |
					XSDPS_PSR_DAT30_SG_LVL_MASK)) != 0U) {
		ReadReg = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
					XSDPS_PRES_STATE_OFFSET);
	}

	/* Stop the clock */
	CtrlReg = XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
			XSDPS_CLK_CTRL_OFFSET);
	CtrlReg &= ~(XSDPS_CC_SD_CLK_EN_MASK | XSDPS_CC_INT_CLK_EN_MASK);
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress, XSDPS_CLK_CTRL_OFFSET,
			CtrlReg);

	/* Wait minimum 5mSec */
#if defined (__arm__) || defined (__aarch64__)

	(void)usleep(5000U);

#endif

#ifdef __MICROBLAZE__

	MB_Sleep(5U);

#endif

	/* Enabling 1.8V in controller */
	CtrlReg = XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
			XSDPS_HOST_CTRL2_OFFSET);
	CtrlReg |= XSDPS_HC2_1V8_EN_MASK;
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress, XSDPS_HOST_CTRL2_OFFSET,
			CtrlReg);

	/* Start clock */
	Status = XSdPs_Change_ClkFreq(InstancePtr, XSDPS_CLK_400_KHZ);
	if (Status != XST_SUCCESS) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	/* Wait for CMD and DATA line to go high */
	ReadReg = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
				XSDPS_PRES_STATE_OFFSET);
	while ((ReadReg & (XSDPS_PSR_CMD_SG_LVL_MASK | XSDPS_PSR_DAT30_SG_LVL_MASK))
			!= (XSDPS_PSR_CMD_SG_LVL_MASK | XSDPS_PSR_DAT30_SG_LVL_MASK)) {
		ReadReg = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
					XSDPS_PRES_STATE_OFFSET);
	}

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
s32 XSdPs_CmdTransfer(XSdPs *InstancePtr, u32 Cmd, u32 Arg, u32 BlkCnt)
{
	u32 PresentStateReg;
	u32 CommandReg;
	u32 StatusReg;
	s32 Status;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Check the command inhibit to make sure no other
	 * command transfer is in progress
	 */
	PresentStateReg = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
			XSDPS_PRES_STATE_OFFSET);
	if ((PresentStateReg & XSDPS_PSR_INHIBIT_CMD_MASK) != 0U) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	/* Write block count register */
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_BLK_CNT_OFFSET, (u16)BlkCnt);

	XSdPs_WriteReg8(InstancePtr->Config.BaseAddress,
			XSDPS_TIMEOUT_CTRL_OFFSET, 0xEU);

	/* Write argument register */
	XSdPs_WriteReg(InstancePtr->Config.BaseAddress,
			XSDPS_ARGMT_OFFSET, Arg);

	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_NORM_INTR_STS_OFFSET, XSDPS_NORM_INTR_ALL_MASK);
	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_ERR_INTR_STS_OFFSET, XSDPS_ERROR_INTR_ALL_MASK);
	/* Command register is set to trigger transfer of command */
	CommandReg = XSdPs_FrameCmd(InstancePtr, Cmd);

	/*
	 * Mask to avoid writing to reserved bits 31-30
	 * This is necessary because 0x80000000 is used  by this software to
	 * distinguish between ACMD and CMD of same number
	 */
	CommandReg = CommandReg & 0x3FFFU;

	/*
	 * Check for data inhibit in case of command using DAT lines.
	 * For Tuning Commands DAT lines check can be ignored.
	 */
	if ((Cmd != CMD21) && (Cmd != CMD19)) {
		PresentStateReg = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
				XSDPS_PRES_STATE_OFFSET);
		if (((PresentStateReg & (XSDPS_PSR_INHIBIT_DAT_MASK |
									XSDPS_PSR_INHIBIT_DAT_MASK)) != 0U) &&
				((CommandReg & XSDPS_DAT_PRESENT_SEL_MASK) != 0U)) {
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}
	}

	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress, XSDPS_CMD_OFFSET,
			(u16)CommandReg);

	/* Polling for response for now */
	do {
		StatusReg = XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
					XSDPS_NORM_INTR_STS_OFFSET);
		if ((Cmd == CMD21) || (Cmd == CMD19)) {
			if ((XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
					XSDPS_NORM_INTR_STS_OFFSET) & XSDPS_INTR_BRR_MASK) != 0U){
				XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
					XSDPS_NORM_INTR_STS_OFFSET, XSDPS_INTR_BRR_MASK);
				break;
			}
		}

		if ((StatusReg & XSDPS_INTR_ERR_MASK) != 0U) {
			Status = XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
									XSDPS_ERR_INTR_STS_OFFSET);
			if ((Status & ~XSDPS_INTR_ERR_CT_MASK) == 0) {
				Status = XSDPS_CT_ERROR;
			}
			 /* Write to clear error bits */
			XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
					XSDPS_ERR_INTR_STS_OFFSET,
					XSDPS_ERROR_INTR_ALL_MASK);
			goto RETURN_PATH;
		}
	} while((StatusReg & XSDPS_INTR_CC_MASK) == 0U);
	/* Write to clear bit */
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
u32 XSdPs_FrameCmd(XSdPs *InstancePtr, u32 Cmd)
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
		case CMD6:
			if (InstancePtr->CardType == XSDPS_CARD_SD) {
				RetVal |= RESP_R1 | (u32)XSDPS_DAT_PRESENT_SEL_MASK;
			} else {
				RetVal |= RESP_R1B;
			}
			break;
		case ACMD6:
			RetVal |= RESP_R1;
		break;
		case CMD7:
			RetVal |= RESP_R1;
		break;
		case CMD8:
			if (InstancePtr->CardType == XSDPS_CARD_SD) {
				RetVal |= RESP_R1;
			} else {
				RetVal |= RESP_R1 | (u32)XSDPS_DAT_PRESENT_SEL_MASK;
			}
			break;
		case CMD9:
			RetVal |= RESP_R2;
		break;
		case CMD11:
		case CMD10:
		case CMD12:
		case ACMD13:
		case CMD16:
			RetVal |= RESP_R1;
		break;
		case CMD17:
		case CMD18:
		case CMD19:
		case CMD21:
			RetVal |= RESP_R1 | (u32)XSDPS_DAT_PRESENT_SEL_MASK;
		break;
		case CMD23:
		case ACMD23:
		case CMD24:
		case CMD25:
			RetVal |= RESP_R1 | (u32)XSDPS_DAT_PRESENT_SEL_MASK;
		case ACMD41:
			RetVal |= RESP_R3;
		break;
		case ACMD42:
			RetVal |= RESP_R1;
		break;
		case ACMD51:
			RetVal |= RESP_R1 | (u32)XSDPS_DAT_PRESENT_SEL_MASK;
		break;
		case CMD52:
		case CMD55:
			RetVal |= RESP_R1;
		break;
		case CMD58:
		break;
		default :
			RetVal |= Cmd;
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
s32 XSdPs_ReadPolled(XSdPs *InstancePtr, u32 Arg, u32 BlkCnt, u8 *Buff)
{
	s32 Status;
	u32 PresentStateReg;
	u32 StatusReg;

	if ((InstancePtr->HC_Version != XSDPS_HC_SPEC_V3) ||
				((InstancePtr->Host_Caps & XSDPS_CAPS_SLOT_TYPE_MASK)
				!= XSDPS_CAPS_EMB_SLOT)) {
		if(InstancePtr->Config.CardDetect != 0U) {
			/* Check status to ensure card is initialized */
			PresentStateReg = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
					XSDPS_PRES_STATE_OFFSET);
			if ((PresentStateReg & XSDPS_PSR_CARD_INSRT_MASK) == 0x0U) {
				Status = XST_FAILURE;
				goto RETURN_PATH;
			}
		}
	}

	/* Set block size to 512 if not already set */
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

	Xil_DCacheInvalidateRange((INTPTR)Buff, BlkCnt * XSDPS_BLK_SIZE_512_MASK);

	/* Send block read command */
	Status = XSdPs_CmdTransfer(InstancePtr, CMD18, Arg, BlkCnt);
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
	Status = (s32)XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
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
s32 XSdPs_WritePolled(XSdPs *InstancePtr, u32 Arg, u32 BlkCnt, const u8 *Buff)
{
	s32 Status;
	u32 PresentStateReg;
	u32 StatusReg;

	if ((InstancePtr->HC_Version != XSDPS_HC_SPEC_V3) ||
				((InstancePtr->Host_Caps & XSDPS_CAPS_SLOT_TYPE_MASK)
				!= XSDPS_CAPS_EMB_SLOT)) {
		if(InstancePtr->Config.CardDetect != 0U) {
			/* Check status to ensure card is initialized */
			PresentStateReg = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
					XSDPS_PRES_STATE_OFFSET);
			if ((PresentStateReg & XSDPS_PSR_CARD_INSRT_MASK) == 0x0U) {
				Status = XST_FAILURE;
				goto RETURN_PATH;
			}
		}
	}

	/* Set block size to 512 if not already set */
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
	Xil_DCacheFlushRange((INTPTR)Buff, BlkCnt * XSDPS_BLK_SIZE_512_MASK);

	XSdPs_WriteReg16(InstancePtr->Config.BaseAddress,
			XSDPS_XFER_MODE_OFFSET,
			XSDPS_TM_AUTO_CMD12_EN_MASK |
			XSDPS_TM_BLK_CNT_EN_MASK |
			XSDPS_TM_MUL_SIN_BLK_SEL_MASK | XSDPS_TM_DMA_EN_MASK);

	/* Send block write command */
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
s32 XSdPs_Select_Card (XSdPs *InstancePtr)
{
	s32 Status = 0;

	/* Send CMD7 - Select card */
	Status = XSdPs_CmdTransfer(InstancePtr, CMD7,
			InstancePtr->RelCardAddr, 0U);
	if (Status != XST_SUCCESS) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

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
	u32 TotalDescLines = 0U;
	u32 DescNum = 0U;
	u32 BlkSize = 0U;

	/* Setup ADMA2 - Write descriptor table and point ADMA SAR to it */
	BlkSize = XSdPs_ReadReg16(InstancePtr->Config.BaseAddress,
					XSDPS_BLK_SIZE_OFFSET);
	BlkSize = BlkSize & XSDPS_BLK_SIZE_MASK;

	if((BlkCnt*BlkSize) < XSDPS_DESC_MAX_LENGTH) {

		TotalDescLines = 1U;

	}else {

		TotalDescLines = ((BlkCnt*BlkSize) / XSDPS_DESC_MAX_LENGTH);
		if (((BlkCnt * BlkSize) % XSDPS_DESC_MAX_LENGTH) != 0U) {
			TotalDescLines += 1U;
		}

	}

	for (DescNum = 0U; DescNum < (TotalDescLines-1); DescNum++) {
		InstancePtr->Adma2_DescrTbl[DescNum].Address =
				(u32)((UINTPTR)Buff + (DescNum*XSDPS_DESC_MAX_LENGTH));
		InstancePtr->Adma2_DescrTbl[DescNum].Attribute =
				XSDPS_DESC_TRAN | XSDPS_DESC_VALID;
		/* This will write '0' to length field which indicates 65536 */
		InstancePtr->Adma2_DescrTbl[DescNum].Length =
				(u16)XSDPS_DESC_MAX_LENGTH;
	}

	InstancePtr->Adma2_DescrTbl[TotalDescLines-1].Address =
			(u32)((UINTPTR)Buff + (DescNum*XSDPS_DESC_MAX_LENGTH));

	InstancePtr->Adma2_DescrTbl[TotalDescLines-1].Attribute =
			XSDPS_DESC_TRAN | XSDPS_DESC_END | XSDPS_DESC_VALID;

	InstancePtr->Adma2_DescrTbl[TotalDescLines-1].Length =
			(u16)((BlkCnt*BlkSize) - (DescNum*XSDPS_DESC_MAX_LENGTH));


	XSdPs_WriteReg(InstancePtr->Config.BaseAddress, XSDPS_ADMA_SAR_OFFSET,
			(u32)(UINTPTR)&(InstancePtr->Adma2_DescrTbl[0]));

	Xil_DCacheFlushRange((INTPTR)&(InstancePtr->Adma2_DescrTbl[0]),
			sizeof(XSdPs_Adma2Descriptor) * 32U);

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
s32 XSdPs_MmcCardInitialize(XSdPs *InstancePtr)
{
	u32 PresentStateReg;
	s32 Status;
	u32 RespOCR;
	u32 CSD[4];

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	if ((InstancePtr->HC_Version != XSDPS_HC_SPEC_V3) ||
				((InstancePtr->Host_Caps & XSDPS_CAPS_SLOT_TYPE_MASK)
				!= XSDPS_CAPS_EMB_SLOT)) {
		if(InstancePtr->Config.CardDetect != 0U) {
			/*
			 * Check the present state register to make sure
			 * card is inserted and detected by host controller
			 */
			PresentStateReg = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
					XSDPS_PRES_STATE_OFFSET);
			if ((PresentStateReg & XSDPS_PSR_CARD_INSRT_MASK) == 0U)	{
				Status = XST_FAILURE;
				goto RETURN_PATH;
			}
		}
	}

	/* CMD0 no response expected */
	Status = XSdPs_CmdTransfer(InstancePtr, CMD0, 0U, 0U);
	if (Status != XST_SUCCESS) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	RespOCR = 0U;
	/* Send CMD1 while card is still busy with power up */
	while ((RespOCR & XSDPS_RESPOCR_READY) == 0U) {

		/* Host High Capacity support & High volage window */
		Status = XSdPs_CmdTransfer(InstancePtr, CMD1,
				XSDPS_ACMD41_HCS | XSDPS_CMD1_HIGH_VOL, 0U);
		if (Status != XST_SUCCESS) {
			Status = XST_FAILURE;
			goto RETURN_PATH;
		}

		/* Response with card capacity */
		RespOCR = XSdPs_ReadReg(InstancePtr->Config.BaseAddress,
				XSDPS_RESP0_OFFSET);

	}

	/* Update HCS support flag based on card capacity response */
	if ((RespOCR & XSDPS_ACMD41_HCS) != 0U) {
		InstancePtr->HCS = 1U;
	}

	/* CMD2 for Card ID */
	Status = XSdPs_CmdTransfer(InstancePtr, CMD2, 0U, 0U);
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

	/* Set relative card address */
	InstancePtr->RelCardAddr = 0x12340000U;
	Status = XSdPs_CmdTransfer(InstancePtr, CMD3, (InstancePtr->RelCardAddr), 0U);
	if (Status != XST_SUCCESS) {
		Status = XST_FAILURE;
		goto RETURN_PATH;
	}

	Status = XSdPs_CmdTransfer(InstancePtr, CMD9, (InstancePtr->RelCardAddr), 0U);
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

	InstancePtr->Card_Version =  (CSD[3] & CSD_SPEC_VER_MASK) >>18U;

	Status = XST_SUCCESS;

RETURN_PATH:
	return Status;

}
/** @} */
