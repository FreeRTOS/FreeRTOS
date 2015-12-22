/******************************************************************************
*
* Copyright (C) 2015 Xilinx, Inc. All rights reserved.
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
* @file xnandpsu.c
*
* This file contains the implementation of the interface functions for
* XNandPsu driver. Refer to the header file xnandpsu.h for more detailed
* information.
*
* This module supports for NAND flash memory devices that conform to the
* "Open NAND Flash Interface" (ONFI) 3.0 Specification. This modules
* implements basic flash operations like read, write and erase.
*
* @note		Driver has been renamed to nandpsu after change in
*		naming convention.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date	   Changes
* ----- ----   ----------  -----------------------------------------------
* 1.0   nm     05/06/2014  First release
* 2.0   sb     01/12/2015  Removed Null checks for Buffer passed
*			   as parameter to Read API's
*			   - XNandPsu_Read()
*			   - XNandPsu_ReadPage
*			   Modified
*			   - XNandPsu_SetFeature()
*			   - XNandPsu_GetFeature()
*			   and made them public.
*			   Removed Failure Return for BCF Error check in
*			   XNandPsu_ReadPage() and added BCH_Error counter
*			   in the instance pointer structure.
* 			   Added XNandPsu_Prepare_Cmd API
*			   Replaced
*			   - XNandPsu_IntrStsEnable
*			   - XNandPsu_IntrStsClear
*			   - XNandPsu_IntrClear
*			   - XNandPsu_SetProgramReg
*			   with XNandPsu_WriteReg call
*			   Modified xnandpsu.c file API's with above changes.
*  			   Corrected the program command for Set Feature API.
*			   Modified
*			   - XNandPsu_OnfiReadStatus
*			   - XNandPsu_GetFeature
*			   - XNandPsu_SetFeature
*			   to add support for DDR mode.
*			   Changed Convention for SLC/MLC
*			   SLC --> HAMMING
*			   MLC --> BCH
*			   SlcMlc --> IsBCH
*			   Removed extra DMA mode initialization from
*			   the XNandPsu_CfgInitialize API.
*			   Modified
*			   - XNandPsu_SetEccAddrSize
*			   ECC address now is calculated based upon the
*			   size of spare area
*			   Modified Block Erase API, removed clearing of
*			   packet register before erase.
*			   Clearing Data Interface Register before
*			   XNandPsu_OnfiReset call.
*			   Modified XNandPsu_ChangeTimingMode API supporting
*			   SDR and NVDDR interface for timing modes 0 to 5.
*			   Modified Bbt Signature and Version Offset value for
*			   Oob and No-Oob region.
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/
#include "xnandpsu.h"
#include "xnandpsu_bbm.h"
/************************** Constant Definitions *****************************/

const XNandPsu_EccMatrix EccMatrix[] = {
	/*
	 * 512 byte page
	 */
	{XNANDPSU_PAGE_SIZE_512, 9U, 1U, XNANDPSU_HAMMING, 0x20DU, 0x3U},
	{XNANDPSU_PAGE_SIZE_512, 9U, 4U, XNANDPSU_BCH, 0x209U, 0x7U},
	{XNANDPSU_PAGE_SIZE_512, 9U, 8U, XNANDPSU_BCH, 0x203U, 0xDU},
	/*
	 * 2K byte page
	 */
	{XNANDPSU_PAGE_SIZE_2K, 9U, 1U, XNANDPSU_HAMMING, 0x834U, 0xCU},
	{XNANDPSU_PAGE_SIZE_2K, 9U, 4U, XNANDPSU_BCH, 0x826U, 0x1AU},
	{XNANDPSU_PAGE_SIZE_2K, 9U, 8U, XNANDPSU_BCH, 0x80cU, 0x34U},
	{XNANDPSU_PAGE_SIZE_2K, 9U, 12U, XNANDPSU_BCH, 0x822U, 0x4EU},
	{XNANDPSU_PAGE_SIZE_2K, 10U, 24U, XNANDPSU_BCH, 0x81cU, 0x54U},
	/*
	 * 4K byte page
	 */
	{XNANDPSU_PAGE_SIZE_4K, 9U, 1U, XNANDPSU_HAMMING, 0x1068U, 0x18U},
	{XNANDPSU_PAGE_SIZE_4K, 9U, 4U, XNANDPSU_BCH, 0x104cU, 0x34U},
	{XNANDPSU_PAGE_SIZE_4K, 9U, 8U, XNANDPSU_BCH, 0x1018U, 0x68U},
	{XNANDPSU_PAGE_SIZE_4K, 9U, 12U, XNANDPSU_BCH, 0x1044U, 0x9CU},
	{XNANDPSU_PAGE_SIZE_4K, 10U, 24U, XNANDPSU_BCH, 0x1038U, 0xA8U},
	/*
	 * 8K byte page
	 */
	{XNANDPSU_PAGE_SIZE_8K, 9U, 1U, XNANDPSU_HAMMING, 0x20d0U, 0x30U},
	{XNANDPSU_PAGE_SIZE_8K, 9U, 4U, XNANDPSU_BCH, 0x2098U, 0x68U},
	{XNANDPSU_PAGE_SIZE_8K, 9U, 8U, XNANDPSU_BCH, 0x2030U, 0xD0U},
	{XNANDPSU_PAGE_SIZE_8K, 9U, 12U, XNANDPSU_BCH, 0x2088U, 0x138U},
	{XNANDPSU_PAGE_SIZE_8K, 10U, 24U, XNANDPSU_BCH, 0x2070U, 0x150U},
	/*
	 * 16K byte page
	 */
	{XNANDPSU_PAGE_SIZE_16K, 9U, 1U, XNANDPSU_HAMMING, 0x4460U, 0x60U},
	{XNANDPSU_PAGE_SIZE_16K, 9U, 4U, XNANDPSU_BCH, 0x43f0U, 0xD0U},
	{XNANDPSU_PAGE_SIZE_16K, 9U, 8U, XNANDPSU_BCH, 0x4320U, 0x1A0U},
	{XNANDPSU_PAGE_SIZE_16K, 9U, 12U, XNANDPSU_BCH, 0x4250U, 0x270U},
	{XNANDPSU_PAGE_SIZE_16K, 10U, 24U, XNANDPSU_BCH, 0x4220U, 0x2A0U}
};

/**************************** Type Definitions *******************************/
static u8 isQemuPlatform = 0U;
/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/

static s32 XNandPsu_FlashInit(XNandPsu *InstancePtr);

static void XNandPsu_InitGeometry(XNandPsu *InstancePtr, OnfiParamPage *Param);

static void XNandPsu_InitFeatures(XNandPsu *InstancePtr, OnfiParamPage *Param);

static s32 XNandPsu_PollRegTimeout(XNandPsu *InstancePtr, u32 RegOffset,
					u32 Mask, u32 Timeout);

static void XNandPsu_SetPktSzCnt(XNandPsu *InstancePtr, u32 PktSize,
						u32 PktCount);

static void XNandPsu_SetPageColAddr(XNandPsu *InstancePtr, u32 Page, u16 Col);

static void XNandPsu_SetPageSize(XNandPsu *InstancePtr);

static void XNandPsu_SetBusWidth(XNandPsu *InstancePtr);

static void XNandPsu_SelectChip(XNandPsu *InstancePtr, u32 Target);

static s32 XNandPsu_OnfiReset(XNandPsu *InstancePtr, u32 Target);

static s32 XNandPsu_OnfiReadStatus(XNandPsu *InstancePtr, u32 Target,
							u16 *OnfiStatus);

static s32 XNandPsu_OnfiReadId(XNandPsu *InstancePtr, u32 Target, u8 IdAddr,
							u32 IdLen, u8 *Buf);

static s32 XNandPsu_OnfiReadParamPage(XNandPsu *InstancePtr, u32 Target,
						u8 *Buf);

static s32 XNandPsu_ProgramPage(XNandPsu *InstancePtr, u32 Target, u32 Page,
							u32 Col, u8 *Buf);

static s32 XNandPsu_ReadPage(XNandPsu *InstancePtr, u32 Target, u32 Page,
							u32 Col, u8 *Buf);

static s32 XNandPsu_CheckOnDie(XNandPsu *InstancePtr, OnfiParamPage *Param);

static void XNandPsu_SetEccAddrSize(XNandPsu *InstancePtr);

static s32 XNandPsu_ChangeReadColumn(XNandPsu *InstancePtr, u32 Target,
					u32 Col, u32 PktSize, u32 PktCount,
					u8 *Buf);

static s32 XNandPsu_ChangeWriteColumn(XNandPsu *InstancePtr, u32 Target,
					u32 Col, u32 PktSize, u32 PktCount,
					u8 *Buf);

static s32 XNandPsu_InitExtEcc(XNandPsu *InstancePtr, OnfiExtPrmPage *ExtPrm);

/*****************************************************************************/
/**
*
* This function initializes a specific XNandPsu instance. This function must
* be called prior to using the NAND flash device to read or write any data.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
* @param	ConfigPtr points to XNandPsu device configuration structure.
* @param	EffectiveAddr is the base address of NAND flash controller.
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_FAILURE if fail.
*
* @note		The user needs to first call the XNandPsu_LookupConfig() API
*		which returns the Configuration structure pointer which is
*		passed as a parameter to the XNandPsu_CfgInitialize() API.
*
******************************************************************************/
s32 XNandPsu_CfgInitialize(XNandPsu *InstancePtr, XNandPsu_Config *ConfigPtr,
				u32 EffectiveAddr)
{
	s32 Status = XST_FAILURE;

	/*
	 * Assert the input arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(ConfigPtr != NULL);

	/*
	 * Initialize InstancePtr Config structure
	 */
	InstancePtr->Config.DeviceId = ConfigPtr->DeviceId;
	InstancePtr->Config.BaseAddress = EffectiveAddr;
	/*
	 * Operate in Polling Mode
	 */
	InstancePtr->Mode = XNANDPSU_POLLING;
	/*
	 * Enable MDMA mode by default
	 */
	InstancePtr->DmaMode = XNANDPSU_MDMA;
	InstancePtr->IsReady = XIL_COMPONENT_IS_READY;

	/*
	 * Temporary hack for disabling the ecc on qemu as currently there
	 * is no support in the utility for writing images with ecc enabled.
	 */
	#define CSU_VER_REG 0xFFCA0044U
	#define CSU_VER_PLATFORM_MASK 0xF000U
	#define CSU_VER_PLATFORM_QEMU_VAL 0x3000U
	if ((*(u32 *)CSU_VER_REG & CSU_VER_PLATFORM_MASK) ==
					CSU_VER_PLATFORM_QEMU_VAL) {
		isQemuPlatform = 1U;
	}
	/*
	 * Initialize the NAND flash targets
	 */
	Status = XNandPsu_FlashInit(InstancePtr);
	if (Status != XST_SUCCESS) {
#ifdef XNANDPSU_DEBUG
		xil_printf("%s: Flash init failed\r\n",__func__);
#endif
		goto Out;
	}
	/*
	 * Set ECC mode
	 */
	if (InstancePtr->Features.EzNand != 0U) {
		InstancePtr->EccMode = XNANDPSU_EZNAND;
	} else if (InstancePtr->Features.OnDie != 0U) {
		InstancePtr->EccMode = XNANDPSU_ONDIE;
	} else {
		InstancePtr->EccMode = XNANDPSU_HWECC;
	}

	if (isQemuPlatform != 0U) {
		InstancePtr->EccMode = XNANDPSU_NONE;
		goto Out;
	}

	/*
	 * Initialize Ecc Error flip counters
	 */
	 InstancePtr->Ecc_Stat_PerPage_flips = 0U;
	 InstancePtr->Ecc_Stats_total_flips = 0U;

	/*
	 * Scan for the bad block table(bbt) stored in the flash & load it in
	 * memory(RAM).  If bbt is not found, create bbt by scanning factory
	 * marked bad blocks and store it in last good blocks of flash.
	 */
	XNandPsu_InitBbtDesc(InstancePtr);
	Status = XNandPsu_ScanBbt(InstancePtr);
	if (Status != XST_SUCCESS) {
#ifdef XNANDPSU_DEBUG
		xil_printf("%s: BBT scan failed\r\n",__func__);
#endif
		goto Out;
	}

Out:
	return Status;
}

/*****************************************************************************/
/**
*
* This function initializes the NAND flash and gets the geometry information.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_FAILURE if failed.
*
* @note		None
*
******************************************************************************/
static s32 XNandPsu_FlashInit(XNandPsu *InstancePtr)
{
	u32 Target;
	u8 Id[ONFI_SIG_LEN] = {0U};
	OnfiParamPage Param = {0U};
	s32 Status = XST_FAILURE;
	u32 Index;
	u32 Crc;
	u32 PrmPgOff;
	u32 PrmPgLen;
	OnfiExtPrmPage ExtParam __attribute__ ((aligned(64)));

	/*
	 * Assert the input arguments.
	 */
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Clear Data Interface Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_DATA_INTF_OFFSET, 0U);

	/* Clear DMA Buffer Boundary Register */
	XNandPsu_WriteReg(InstancePtr->Config.BaseAddress,
			XNANDPSU_DMA_BUF_BND_OFFSET, 0U);

	for (Target = 0U; Target < XNANDPSU_MAX_TARGETS; Target++) {
		/*
		 * Reset the Target
		 */
		Status = XNandPsu_OnfiReset(InstancePtr, Target);
		if (Status != XST_SUCCESS) {
			goto Out;
		}
		/*
		 * Read ONFI ID
		 */
		Status = XNandPsu_OnfiReadId(InstancePtr, Target,
						ONFI_READ_ID_ADDR,
						ONFI_SIG_LEN,
						(u8 *)&Id[0]);
		if (Status != XST_SUCCESS) {
			goto Out;
		}

		if (!IS_ONFI(Id)) {
			if (Target == 0U) {
#ifdef XNANDPSU_DEBUG
				xil_printf("%s: ONFI ID doesn't match\r\n",
								__func__);
#endif
				Status = XST_FAILURE;
				goto Out;
			}
		}

		/* Read Parameter Page */
		for(Index = 0U; Index < ONFI_MND_PRM_PGS; Index++) {
			if (Index == 0U) {
				Status = XNandPsu_OnfiReadParamPage(InstancePtr,
							Target, (u8 *)&Param);
			} else {
				PrmPgOff = Index * ONFI_PRM_PG_LEN;
				PrmPgLen = ONFI_PRM_PG_LEN;
				Status = XNandPsu_ChangeReadColumn(InstancePtr,
							Target,PrmPgOff,
							ONFI_PRM_PG_LEN, 1U,
							(u8 *) &Param);
			}
			if (Status != XST_SUCCESS) {
				goto Out;
			}
			/* Check CRC */
			Crc = XNandPsu_OnfiParamPageCrc((u8*)&Param, 0U,
								ONFI_CRC_LEN);
			if (Crc != Param.Crc) {
#ifdef XNANDPSU_DEBUG
				xil_printf("%s: ONFI parameter page (%d) crc check failed\r\n",
							__func__, Index);
#endif
				continue;
			} else {
				break;
			}
		}
		if (Index >= ONFI_MND_PRM_PGS) {
			Status = XST_FAILURE;
			goto Out;
		}
		/* Fill Geometry for the first target */
		if (Target == 0U) {
			XNandPsu_InitGeometry(InstancePtr, &Param);
			XNandPsu_InitFeatures(InstancePtr, &Param);
			if ((!InstancePtr->Features.EzNand) != 0U) {
				Status =XNandPsu_CheckOnDie(InstancePtr,&Param);
				if (Status != XST_SUCCESS) {
					InstancePtr->Features.OnDie = 0U;
				}
			}
			if (isQemuPlatform != 0U) {
				InstancePtr->Geometry.NumTargets++;
				break;
			}
			if ((InstancePtr->Geometry.NumBitsECC == 0xFFU) &&
				(InstancePtr->Features.ExtPrmPage != 0U)) {
				/* ONFI 3.1 section 5.7.1.6 & 5.7.1.7 */
				PrmPgLen = (u32)Param.ExtParamPageLen * 16U;
					PrmPgOff = (u32)((u32)Param.NumOfParamPages *
							ONFI_PRM_PG_LEN) +
							(Index * (u32)PrmPgLen);
					Status = XNandPsu_ChangeReadColumn(
							InstancePtr,
							Target,
							PrmPgOff,
							PrmPgLen, 1U,
							(u8 *)(void *)&ExtParam);
					if (Status != XST_SUCCESS) {
						goto Out;
					}
					/*
					 * Check CRC
					 */
					Crc = XNandPsu_OnfiParamPageCrc(
							(u8 *)&ExtParam,
							2U,
							PrmPgLen);
					if (Crc != ExtParam.Crc) {
#ifdef XNANDPSU_DEBUG
	xil_printf("%s: ONFI extended parameter page (%d) crc check failed\r\n",
							__func__, Index);
#endif
						Status = XST_FAILURE;
						goto Out;
					}
					/*
					 * Initialize Extended ECC info
					 */
					Status = XNandPsu_InitExtEcc(
							InstancePtr,
							&ExtParam);
					if (Status != XST_SUCCESS) {
#ifdef XNANDPSU_DEBUG
	xil_printf("%s: Init extended ecc failed\r\n",__func__);
#endif
						goto Out;
				}
			}
			/* Configure ECC settings */
			XNandPsu_SetEccAddrSize(InstancePtr);
		}
		InstancePtr->Geometry.NumTargets++;
	}
	/*
	 * Calculate total number of blocks and total size of flash
	 */
	InstancePtr->Geometry.NumPages = InstancePtr->Geometry.NumTargets *
					InstancePtr->Geometry.NumTargetPages;
	InstancePtr->Geometry.NumBlocks = InstancePtr->Geometry.NumTargets *
					InstancePtr->Geometry.NumTargetBlocks;
	InstancePtr->Geometry.DeviceSize =
					(u64)InstancePtr->Geometry.NumTargets *
					InstancePtr->Geometry.TargetSize;

	Status = XST_SUCCESS;
Out:
	return Status;
}

/*****************************************************************************/
/**
*
* This function initializes the geometry information from ONFI parameter page.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
* @param	Param is pointer to the ONFI parameter page.
*
* @return
*		None
*
* @note		None
*
******************************************************************************/
static void XNandPsu_InitGeometry(XNandPsu *InstancePtr, OnfiParamPage *Param)
{
	/*
	 * Assert the input arguments.
	 */
	Xil_AssertVoid(Param != NULL);

	InstancePtr->Geometry.BytesPerPage = Param->BytesPerPage;
	InstancePtr->Geometry.SpareBytesPerPage = Param->SpareBytesPerPage;
	InstancePtr->Geometry.PagesPerBlock = Param->PagesPerBlock;
	InstancePtr->Geometry.BlocksPerLun = Param->BlocksPerLun;
	InstancePtr->Geometry.NumLuns = Param->NumLuns;
	InstancePtr->Geometry.RowAddrCycles = Param->AddrCycles & 0xFU;
	InstancePtr->Geometry.ColAddrCycles = (Param->AddrCycles >> 4U) & 0xFU;
	InstancePtr->Geometry.NumBitsPerCell = Param->BitsPerCell;
	InstancePtr->Geometry.NumBitsECC = Param->EccBits;
	InstancePtr->Geometry.BlockSize = (Param->PagesPerBlock *
						Param->BytesPerPage);
	InstancePtr->Geometry.NumTargetBlocks = (Param->BlocksPerLun *
						(u32)Param->NumLuns);
	InstancePtr->Geometry.NumTargetPages = (Param->BlocksPerLun *
						(u32)Param->NumLuns *
						Param->PagesPerBlock);
	InstancePtr->Geometry.TargetSize = ((u64)Param->BlocksPerLun *
						(u64)Param->NumLuns *
						(u64)Param->PagesPerBlock *
						(u64)Param->BytesPerPage);
	InstancePtr->Geometry.EccCodeWordSize = 9U; /* 2 power of 9 = 512 */

#ifdef XNANDPSU_DEBUG
	xil_printf("Manufacturer: %s\r\n", Param->DeviceManufacturer);
	xil_printf("Device Model: %s\r\n", Param->DeviceModel);
	xil_printf("Jedec ID: 0x%x\r\n", Param->JedecManufacturerId);
	xil_printf("Bytes Per Page: 0x%x\r\n", Param->BytesPerPage);
	xil_printf("Spare Bytes Per Page: 0x%x\r\n", Param->SpareBytesPerPage);
	xil_printf("Pages Per Block: 0x%x\r\n", Param->PagesPerBlock);
	xil_printf("Blocks Per LUN: 0x%x\r\n", Param->BlocksPerLun);
	xil_printf("Number of LUNs: 0x%x\r\n", Param->NumLuns);
	xil_printf("Number of bits per cell: 0x%x\r\n", Param->BitsPerCell);
	xil_printf("Number of ECC bits: 0x%x\r\n", Param->EccBits);
	xil_printf("Block Size: 0x%x\r\n", InstancePtr->Geometry.BlockSize);

	xil_printf("Number of Target Blocks: 0x%x\r\n",
					InstancePtr->Geometry.NumTargetBlocks);
	xil_printf("Number of Target Pages: 0x%x\r\n",
					InstancePtr->Geometry.NumTargetPages);

#endif
}

/*****************************************************************************/
/**
*
* This function initializes the feature list from ONFI parameter page.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
* @param	Param is pointer to ONFI parameter page buffer.
*
* @return
*		None
*
* @note		None
*
******************************************************************************/
static void XNandPsu_InitFeatures(XNandPsu *InstancePtr, OnfiParamPage *Param)
{
	/*
	 * Assert the input arguments.
	 */
	Xil_AssertVoid(Param != NULL);

	InstancePtr->Features.BusWidth = ((Param->Features & (1U << 0U)) != 0U) ?
						XNANDPSU_BUS_WIDTH_16 :
						XNANDPSU_BUS_WIDTH_8;
	InstancePtr->Features.NvDdr = ((Param->Features & (1U << 5)) != 0U) ?
								1U : 0U;
	InstancePtr->Features.EzNand = ((Param->Features & (1U << 9)) != 0U) ?
								1U : 0U;
	InstancePtr->Features.ExtPrmPage = ((Param->Features & (1U << 7)) != 0U) ?
								1U : 0U;
}

/*****************************************************************************/
/**
*
* This function checks if the flash supports on-die ECC.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
* @param	Param is pointer to ONFI parameter page.
*
* @return
*		None
*
* @note		None
*
******************************************************************************/
static s32 XNandPsu_CheckOnDie(XNandPsu *InstancePtr, OnfiParamPage *Param)
{
	s32 Status = XST_FAILURE;
	u8 JedecId[2] = {0U};
	u8 EccSetFeature[4] = {0x08U, 0x00U, 0x00U, 0x00U};
	u8 EccGetFeature[4] ={0U};

	/*
	 * Assert the input arguments.
	 */
	Xil_AssertNonvoid(Param != NULL);

	/*
	 * Check if this flash supports On-Die ECC.
	 * For more information, refer to Micron TN2945.
	 * Micron Flash: MT29F1G08ABADA, MT29F1G08ABBDA
	 *		 MT29F1G16ABBDA,
	 *		 MT29F2G08ABBEA, MT29F2G16ABBEA,
	 *		 MT29F2G08ABAEA, MT29F2G16ABAEA,
	 *		 MT29F4G08ABBDA, MT29F4G16ABBDA,
	 *		 MT29F4G08ABADA, MT29F4G16ABADA,
	 *		 MT29F8G08ADBDA, MT29F8G16ADBDA,
	 *		 MT29F8G08ADADA, MT29F8G16ADADA
	 */

	/*
	 * Read JEDEC ID
	 */
	Status = XNandPsu_OnfiReadId(InstancePtr, 0U, 0x00U, 2U, &JedecId[0]);
	if (Status != XST_SUCCESS) {
		goto Out;
	}

	if ((JedecId[0] == 0x2CU) &&
	/*
	 * 1 Gb flash devices
	 */
	((JedecId[1] == 0xF1U) ||
	(JedecId[1] == 0xA1U) ||
	(JedecId[1] == 0xB1U) ||
	/*
	 * 2 Gb flash devices
	 */
	(JedecId[1] == 0xAAU) ||
	(JedecId[1] == 0xBAU) ||
	(JedecId[1] == 0xDAU) ||
	(JedecId[1] == 0xCAU) ||
	/*
	 * 4 Gb flash devices
	 */
	(JedecId[1] == 0xACU) ||
	(JedecId[1] == 0xBCU) ||
	(JedecId[1] == 0xDCU) ||
	(JedecId[1] == 0xCCU) ||
	/*
	 * 8 Gb flash devices
	 */
	(JedecId[1] == 0xA3U) ||
	(JedecId[1] == 0xB3U) ||
	(JedecId[1] == 0xD3U) ||
	(JedecId[1] == 0xC3U))) {
#ifdef XNANDPSU_DEBUG
		xil_printf("%s: Ondie flash detected, jedec id 0x%x 0x%x\r\n",
					__func__, JedecId[0], JedecId[1]);
#endif
		/*
		 * On-Die Set Feature
		 */
		Status = XNandPsu_SetFeature(InstancePtr, 0U, 0x90U,
						&EccSetFeature[0]);
		if (Status != XST_SUCCESS) {
#ifdef XNANDPSU_DEBUG
			xil_printf("%s: Ondie set_feature failed\r\n",
								__func__);
#endif
			goto Out;
		}
		/*
		 * Check to see if ECC feature is set
		 */
		Status = XNandPsu_GetFeature(InstancePtr, 0U, 0x90U,
						&EccGetFeature[0]);
		if (Status != XST_SUCCESS) {
#ifdef XNANDPSU_DEBUG
			xil_printf("%s: Ondie get_feature failed\r\n",
								__func__);
#endif
			goto Out;
		}
		if ((EccGetFeature[0] & 0x08U) != 0U) {
			InstancePtr->Features.OnDie = 1U;
			Status = XST_SUCCESS;
		}
	} else {
		/*
		 * On-Die flash not found
		 */
		Status = XST_FAILURE;
	}
Out:
	return Status;
}

/*****************************************************************************/
/**
*
* This function enables DMA mode of controller operation.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
*
* @return
*		None
*
* @note		None
*
******************************************************************************/
void XNandPsu_EnableDmaMode(XNandPsu *InstancePtr)
{
	/*
	 * Assert the input arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	InstancePtr->DmaMode = XNANDPSU_MDMA;
}

/*****************************************************************************/
/**
*
* This function disables DMA mode of driver/controller operation.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
*
* @return
*		None
*
* @note		None
*
******************************************************************************/
void XNandPsu_DisableDmaMode(XNandPsu *InstancePtr)
{
	/*
	 * Assert the input arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	InstancePtr->DmaMode = XNANDPSU_PIO;
}

/*****************************************************************************/
/**
*
* This function enables ECC mode of driver/controller operation.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
*
* @return
*		None
*
* @note		None
*
******************************************************************************/
void XNandPsu_EnableEccMode(XNandPsu *InstancePtr)
{
	/*
	 * Assert the input arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	InstancePtr->EccMode = XNANDPSU_HWECC;
}

/*****************************************************************************/
/**
*
* This function disables ECC mode of driver/controller operation.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
*
* @return
*		None
*
* @note		None
*
******************************************************************************/
void XNandPsu_DisableEccMode(XNandPsu *InstancePtr)
{
	/*
	 * Assert the input arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	InstancePtr->EccMode = XNANDPSU_NONE;
}

/*****************************************************************************/
/**
*
* This function enables storing bbt version in oob area.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
*
* @return
*			None
*
* @note		None
*
******************************************************************************/
void XNandPsu_EnableBbtOobMode(XNandPsu *InstancePtr)
{
	/*
	 * Assert the input arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	InstancePtr->BbtDesc.Option = XNANDPSU_BBT_OOB;
	InstancePtr->BbtMirrorDesc.Option = XNANDPSU_BBT_OOB;
	/*
	 * Setting the Signature and Version Offset
	 */
	InstancePtr->BbtDesc.SigOffset = XNANDPSU_BBT_DESC_SIG_OFFSET;
	InstancePtr->BbtMirrorDesc.SigOffset = XNANDPSU_BBT_DESC_SIG_OFFSET;
	InstancePtr->BbtDesc.VerOffset = XNANDPSU_BBT_DESC_VER_OFFSET;
	InstancePtr->BbtMirrorDesc.VerOffset = XNANDPSU_BBT_DESC_VER_OFFSET;
}

/*****************************************************************************/
/**
*
* This function enables storing bbt version in no oob area i.e. page memory.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
*
* @return
*			None
*
* @note		None
*
******************************************************************************/
void XNandPsu_DisableBbtOobMode(XNandPsu *InstancePtr)
{
	/*
	 * Assert the input arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	InstancePtr->BbtDesc.Option = XNANDPSU_BBT_NO_OOB;
	InstancePtr->BbtMirrorDesc.Option = XNANDPSU_BBT_NO_OOB;
	/*
	 * Setting the Signature and Version Offset
	 */
	InstancePtr->BbtDesc.SigOffset = XNANDPSU_NO_OOB_BBT_DESC_SIG_OFFSET;
	InstancePtr->BbtMirrorDesc.SigOffset =
					XNANDPSU_NO_OOB_BBT_DESC_SIG_OFFSET;
	InstancePtr->BbtDesc.VerOffset = XNANDPSU_NO_OOB_BBT_DESC_VER_OFFSET;
	InstancePtr->BbtMirrorDesc.VerOffset =
					XNANDPSU_NO_OOB_BBT_DESC_VER_OFFSET;
}

/*****************************************************************************/
/**
*
* This function polls for a register bit set status till the timeout.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
* @param	RegOffset is the offset of register.
* @param	Mask is the bitmask.
* @param	Timeout is the timeout value.
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_FAILURE if failed.
*
* @note		None
*
******************************************************************************/
static s32 XNandPsu_PollRegTimeout(XNandPsu *InstancePtr, u32 RegOffset,
					u32 Mask, u32 Timeout)
{
	s32 Status = XST_FAILURE;
	volatile u32 RegVal;
	u32 TimeoutVar = Timeout;

	while (TimeoutVar > 0U) {
		RegVal = XNandPsu_ReadReg(InstancePtr->Config.BaseAddress,
						RegOffset);
		if ((RegVal & Mask) != 0U) {
			break;
		}
		TimeoutVar--;
	}

	if (TimeoutVar <= 0U) {
		Status = XST_FAILURE;
	} else {
		Status = XST_SUCCESS;
	}

	return Status;
}

/*****************************************************************************/
/**
*
* This function sets packet size and packet count values in packet register.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
* @param	PktSize is the packet size.
* @param	PktCount is the packet count.
*
* @return
*		None
*
* @note		None
*
******************************************************************************/
static void XNandPsu_SetPktSzCnt(XNandPsu *InstancePtr, u32 PktSize,
						u32 PktCount)
{
	/*
	 * Assert the input arguments.
	 */
	Xil_AssertVoid(PktSize <= XNANDPSU_MAX_PKT_SIZE);
	Xil_AssertVoid(PktCount <= XNANDPSU_MAX_PKT_COUNT);

	/*
	 * Update Packet Register with pkt size and count
	 */
	XNandPsu_ReadModifyWrite(InstancePtr, XNANDPSU_PKT_OFFSET,
				((u32)XNANDPSU_PKT_PKT_SIZE_MASK |
				(u32)XNANDPSU_PKT_PKT_CNT_MASK),
				((PktSize & XNANDPSU_PKT_PKT_SIZE_MASK) |
				((PktCount << XNANDPSU_PKT_PKT_CNT_SHIFT) &
				XNANDPSU_PKT_PKT_CNT_MASK)));
}

/*****************************************************************************/
/**
*
* This function sets Page and Column values in the Memory address registers.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
* @param	Page is the page value.
* @param	Col is the column value.
*
* @return
*		None
*
* @note		None
*
******************************************************************************/
static void XNandPsu_SetPageColAddr(XNandPsu *InstancePtr, u32 Page, u16 Col)
{
	/*
	 * Program Memory Address Register 1
	 */
	XNandPsu_WriteReg(InstancePtr->Config.BaseAddress,
				XNANDPSU_MEM_ADDR1_OFFSET,
				((Col & XNANDPSU_MEM_ADDR1_COL_ADDR_MASK) |
				((Page << (u32)XNANDPSU_MEM_ADDR1_PG_ADDR_SHIFT) &
				XNANDPSU_MEM_ADDR1_PG_ADDR_MASK)));
	/*
	 * Program Memory Address Register 2
	 */
	XNandPsu_ReadModifyWrite(InstancePtr, XNANDPSU_MEM_ADDR2_OFFSET,
				XNANDPSU_MEM_ADDR2_MEM_ADDR_MASK,
				((Page >> XNANDPSU_MEM_ADDR1_PG_ADDR_SHIFT) &
				XNANDPSU_MEM_ADDR2_MEM_ADDR_MASK));
}

/*****************************************************************************/
/**
*
* This function sets the size of page in Command Register.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
*
* @return
*		None
*
* @note		None
*
******************************************************************************/
static void XNandPsu_SetPageSize(XNandPsu *InstancePtr)
{
	u32 PageSizeMask = 0;
	u32 PageSize = InstancePtr->Geometry.BytesPerPage;

	/*
	 * Calculate page size mask
	 */
	switch(PageSize) {
		case XNANDPSU_PAGE_SIZE_512:
			PageSizeMask = (0U << XNANDPSU_CMD_PG_SIZE_SHIFT);
			break;
		case XNANDPSU_PAGE_SIZE_2K:
			PageSizeMask = (1U << XNANDPSU_CMD_PG_SIZE_SHIFT);
			break;
		case XNANDPSU_PAGE_SIZE_4K:
			PageSizeMask = (2U << XNANDPSU_CMD_PG_SIZE_SHIFT);
			break;
		case XNANDPSU_PAGE_SIZE_8K:
			PageSizeMask = (3U << XNANDPSU_CMD_PG_SIZE_SHIFT);
			break;
		case XNANDPSU_PAGE_SIZE_16K:
			PageSizeMask = (4U << XNANDPSU_CMD_PG_SIZE_SHIFT);
			break;
		case XNANDPSU_PAGE_SIZE_1K_16BIT:
			PageSizeMask = (5U << XNANDPSU_CMD_PG_SIZE_SHIFT);
			break;
		default:
			/*
			 * Not supported
			 */
			break;
	}
	/*
	 * Update Command Register
	 */
	XNandPsu_ReadModifyWrite(InstancePtr, XNANDPSU_CMD_OFFSET,
				XNANDPSU_CMD_PG_SIZE_MASK, PageSizeMask);
}

/*****************************************************************************/
/**
*
* This function setup the Ecc Register.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
*
* @return
*		None
*
* @note		None
*
******************************************************************************/
static void XNandPsu_SetEccAddrSize(XNandPsu *InstancePtr)
{
	u32 PageSize = InstancePtr->Geometry.BytesPerPage;
	u32 CodeWordSize = InstancePtr->Geometry.EccCodeWordSize;
	u32 NumEccBits = InstancePtr->Geometry.NumBitsECC;
	u32 Index;
	u32 Found = 0U;
	u8 BchModeVal = 0U;

	for (Index = 0U; Index < (sizeof(EccMatrix)/sizeof(XNandPsu_EccMatrix));
						Index++) {
		if ((EccMatrix[Index].PageSize == PageSize) &&
			(EccMatrix[Index].CodeWordSize >= CodeWordSize)) {
			if (EccMatrix[Index].NumEccBits >= NumEccBits) {
				Found = Index;
				break;
			}
			else {
				Found = Index;
			}
		}
	}

	if (Found != 0U) {
		if(InstancePtr->Geometry.SpareBytesPerPage < 64U) {
			InstancePtr->EccCfg.EccAddr = PageSize;
		}
		else {
			InstancePtr->EccCfg.EccAddr = PageSize +
				(InstancePtr->Geometry.SpareBytesPerPage
						- EccMatrix[Found].EccSize);
		}
		InstancePtr->EccCfg.EccSize = EccMatrix[Found].EccSize;
		InstancePtr->EccCfg.NumEccBits = EccMatrix[Found].NumEccBits;
		InstancePtr->EccCfg.CodeWordSize =
						EccMatrix[Found].CodeWordSize;
#ifdef XNANDPSU_DEBUG
		xil_printf("ECC: addr 0x%x size 0x%x numbits %d "
				   "codesz %d\r\n",
				   InstancePtr->EccCfg.EccAddr,
				   InstancePtr->EccCfg.EccSize,
				   InstancePtr->EccCfg.NumEccBits,
				   InstancePtr->EccCfg.CodeWordSize);
#endif
		if (EccMatrix[Found].IsBCH == XNANDPSU_HAMMING) {
			InstancePtr->EccCfg.IsBCH = 0U;
		} else {
			InstancePtr->EccCfg.IsBCH = 1U;
		}
		/*
		 * Write ECC register
		 */
		XNandPsu_WriteReg(InstancePtr->Config.BaseAddress,
				(u32)XNANDPSU_ECC_OFFSET,
				((u32)InstancePtr->EccCfg.EccAddr |
				((u32)InstancePtr->EccCfg.EccSize << (u32)16) |
				((u32)InstancePtr->EccCfg.IsBCH << (u32)27)));

		if (EccMatrix[Found].IsBCH == XNANDPSU_BCH) {
			/*
			 * Write memory address register 2
			 */
			switch(InstancePtr->EccCfg.NumEccBits) {
				case 16U:
					BchModeVal = 0x0U;
					break;
				case 12U:
					BchModeVal = 0x1U;
					break;
				case 8U:
					BchModeVal = 0x2U;
					break;
				case 4U:
					BchModeVal = 0x3U;
					break;
				case 24U:
					BchModeVal = 0x4U;
					break;
				default:
					BchModeVal = 0x0U;
			}
			XNandPsu_ReadModifyWrite(InstancePtr,
				XNANDPSU_MEM_ADDR2_OFFSET,
				XNANDPSU_MEM_ADDR2_NFC_BCH_MODE_MASK,
				(BchModeVal <<
				(u32)XNANDPSU_MEM_ADDR2_NFC_BCH_MODE_SHIFT));
		}
	}
}

/*****************************************************************************/
/**
*
* This function setup the Ecc Spare Command Register.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
*
* @return
*		None
*
* @note		None
*
******************************************************************************/
static void XNandPsu_SetEccSpareCmd(XNandPsu *InstancePtr, u16 SpareCmd,
								u8 AddrCycles)
{
	XNandPsu_WriteReg(InstancePtr->Config.BaseAddress,
				(u32)XNANDPSU_ECC_SPR_CMD_OFFSET,
				(u32)SpareCmd | ((u32)AddrCycles << 28U));
}

/*****************************************************************************/
/**
*
* This function sets the flash bus width in memory address2 register.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
*
* @return
*		None
*
* @note		None
*
******************************************************************************/
static void XNandPsu_SetBusWidth(XNandPsu *InstancePtr)
{
	/*
	 * Update Memory Address2 register with bus width
	 */
	XNandPsu_ReadModifyWrite(InstancePtr, XNANDPSU_MEM_ADDR2_OFFSET,
				XNANDPSU_MEM_ADDR2_BUS_WIDTH_MASK,
				(InstancePtr->Features.BusWidth <<
				XNANDPSU_MEM_ADDR2_BUS_WIDTH_SHIFT));

}

/*****************************************************************************/
/**
*
* This function sets the chip select value in memory address2 register.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
* @param	Target is the chip select value.
*
* @return
*		None
*
* @note		None
*
******************************************************************************/
static void XNandPsu_SelectChip(XNandPsu *InstancePtr, u32 Target)
{
	/*
	 * Update Memory Address2 register with chip select
	 */
	XNandPsu_ReadModifyWrite(InstancePtr, XNANDPSU_MEM_ADDR2_OFFSET,
			XNANDPSU_MEM_ADDR2_CHIP_SEL_MASK,
			((Target << XNANDPSU_MEM_ADDR2_CHIP_SEL_SHIFT) &
			XNANDPSU_MEM_ADDR2_CHIP_SEL_MASK));
}

/*****************************************************************************/
/**
*
* This function sends ONFI Reset command to the flash.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
* @param	Target is the chip select value.
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_FAILURE if failed.
*
* @note		None
*
******************************************************************************/
static s32 XNandPsu_OnfiReset(XNandPsu *InstancePtr, u32 Target)
{
	s32 Status = XST_FAILURE;

	/*
	 * Assert the input arguments.
	 */
	Xil_AssertNonvoid(Target < XNANDPSU_MAX_TARGETS);

	/*
	 * Enable Transfer Complete Interrupt in Interrupt Status Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
		XNANDPSU_INTR_STS_EN_OFFSET,
		XNANDPSU_INTR_STS_EN_TRANS_COMP_STS_EN_MASK);
	/*
	 * Program Command Register
	 */
	XNandPsu_Prepare_Cmd(InstancePtr, ONFI_CMD_RST, ONFI_CMD_INVALID, 0U,
			0U, 0U);
	/*
	 * Program Memory Address Register2 for chip select
	 */
	XNandPsu_SelectChip(InstancePtr, Target);
	/*
	 * Set Reset in Program Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
		XNANDPSU_PROG_OFFSET, XNANDPSU_PROG_RST_MASK);

	/*
	 * Poll for Transfer Complete event
	 */
	Status = XNandPsu_PollRegTimeout(
			InstancePtr,
			XNANDPSU_INTR_STS_OFFSET,
			XNANDPSU_INTR_STS_TRANS_COMP_STS_EN_MASK,
			XNANDPSU_INTR_POLL_TIMEOUT);
	if (Status != XST_SUCCESS) {
#ifdef XNANDPSU_DEBUG
		xil_printf("%s: Poll for xfer complete timeout\r\n",
							__func__);
#endif
		goto Out;
	}
	/*
	 * Clear Transfer Complete Interrupt in Interrupt Status Enable
	 * Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
		(XNANDPSU_INTR_STS_EN_OFFSET), 0U);
	/*
	 * Clear Transfer Complete Interrupt in Interrupt Status Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_INTR_STS_OFFSET,
			XNANDPSU_INTR_STS_TRANS_COMP_STS_EN_MASK);

Out:
	return Status;
}

/*****************************************************************************/
/**
*
* This function sends ONFI Read Status command to the flash.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
* @param	Target is the chip select value.
* @param	OnfiStatus is the ONFI status value to return.
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_FAILURE if failed.
*
* @note		None
*
******************************************************************************/
static s32 XNandPsu_OnfiReadStatus(XNandPsu *InstancePtr, u32 Target,
							u16 *OnfiStatus)
{
	s32 Status = XST_FAILURE;

	/*
	 * Assert the input arguments.
	 */
	Xil_AssertNonvoid(Target < XNANDPSU_MAX_TARGETS);
	Xil_AssertNonvoid(OnfiStatus != NULL);
	/*
	 * Enable Transfer Complete Interrupt in Interrupt Status Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
		XNANDPSU_INTR_STS_EN_OFFSET,
		XNANDPSU_INTR_STS_EN_TRANS_COMP_STS_EN_MASK);
	/*
	 * Program Command Register
	 */
	XNandPsu_Prepare_Cmd(InstancePtr, ONFI_CMD_RD_STS, ONFI_CMD_INVALID,
				0U, 0U, 0U);
	/*
	 * Program Memory Address Register2 for chip select
	 */
	XNandPsu_SelectChip(InstancePtr, Target);
	/*
	 * Program Packet Size and Packet Count
	 */
	if(InstancePtr->DataInterface == XNANDPSU_SDR){
		XNandPsu_SetPktSzCnt(InstancePtr, 1U, 1U);
	}
	else{
		XNandPsu_SetPktSzCnt(InstancePtr, 2U, 1U);
	}

	/*
	 * Set Read Status in Program Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_PROG_OFFSET,XNANDPSU_PROG_RD_STS_MASK);
	/*
	 * Poll for Transfer Complete event
	 */
	Status = XNandPsu_PollRegTimeout(
			InstancePtr,
			XNANDPSU_INTR_STS_OFFSET,
			XNANDPSU_INTR_STS_TRANS_COMP_STS_EN_MASK,
			XNANDPSU_INTR_POLL_TIMEOUT);
	if (Status != XST_SUCCESS) {
#ifdef XNANDPSU_DEBUG
		xil_printf("%s: Poll for xfer complete timeout\r\n",
							__func__);
#endif
		goto Out;
	}
	/*
	 * Clear Transfer Complete Interrupt in Interrupt Status Enable
	 * Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
		XNANDPSU_INTR_STS_EN_OFFSET, 0U);
	/*
	 * Clear Transfer Complete Interrupt in Interrupt Status Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_INTR_STS_OFFSET,
			XNANDPSU_INTR_STS_TRANS_COMP_STS_EN_MASK);
	/*
	 * Read Flash Status
	 */
	*OnfiStatus = (u8) XNandPsu_ReadReg(InstancePtr->Config.BaseAddress,
						XNANDPSU_FLASH_STS_OFFSET);

Out:

	return Status;
}

/*****************************************************************************/
/**
*
* This function sends ONFI Read ID command to the flash.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
* @param	Target is the chip select value.
* @param	Buf is the ONFI ID value to return.
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_FAILURE if failed.
*
* @note		None
*
******************************************************************************/
static s32 XNandPsu_OnfiReadId(XNandPsu *InstancePtr, u32 Target, u8 IdAddr,
							u32 IdLen, u8 *Buf)
{
	s32 Status = XST_FAILURE;
	u32 Index;
	u32 Rem;
	u32 *BufPtr = (u32 *)(void *)Buf;
	u32 RegVal;
	u32 RemIdx;

	/*
	 * Assert the input arguments.
	 */
	Xil_AssertNonvoid(Target < XNANDPSU_MAX_TARGETS);
	Xil_AssertNonvoid(Buf != NULL);

	/*
	 * Enable Buffer Read Ready Interrupt in Interrupt Status Enable
	 * Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
		XNANDPSU_INTR_STS_EN_OFFSET,
		XNANDPSU_INTR_STS_EN_BUFF_RD_RDY_STS_EN_MASK);
	/*
	 * Program Command
	 */
	XNandPsu_Prepare_Cmd(InstancePtr, ONFI_CMD_RD_ID, ONFI_CMD_INVALID, 0U,
					0U, ONFI_READ_ID_ADDR_CYCLES);

	/*
	 * Program Column, Page, Block address
	 */
	XNandPsu_SetPageColAddr(InstancePtr, 0U, IdAddr);
	/*
	 * Program Memory Address Register2 for chip select
	 */
	XNandPsu_SelectChip(InstancePtr, Target);
	/*
	 * Program Packet Size and Packet Count
	 */
	XNandPsu_SetPktSzCnt(InstancePtr, IdLen, 1U);
	/*
	 * Set Read ID in Program Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_PROG_OFFSET,XNANDPSU_PROG_RD_ID_MASK);

	/*
	 * Poll for Buffer Read Ready event
	 */
	Status = XNandPsu_PollRegTimeout(
		InstancePtr,
		XNANDPSU_INTR_STS_OFFSET,
		XNANDPSU_INTR_STS_BUFF_RD_RDY_STS_EN_MASK,
		XNANDPSU_INTR_POLL_TIMEOUT);
	if (Status != XST_SUCCESS) {
#ifdef XNANDPSU_DEBUG
		xil_printf("%s: Poll for buf read ready timeout\r\n",
							__func__);
#endif
		goto Out;
	}
	/*
	 * Enable Transfer Complete Interrupt in Interrupt
	 * Status Enable Register
	 */

		XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
		XNANDPSU_INTR_STS_EN_OFFSET,
		XNANDPSU_INTR_STS_EN_TRANS_COMP_STS_EN_MASK);

	/*
	 * Clear Buffer Read Ready Interrupt in Interrupt Status
	 * Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_INTR_STS_OFFSET,
			XNANDPSU_INTR_STS_BUFF_RD_RDY_STS_EN_MASK);
	/*
	 * Read Packet Data from Data Port Register
	 */
	for (Index = 0U; Index < (IdLen/4); Index++) {
		BufPtr[Index] = XNandPsu_ReadReg(
					InstancePtr->Config.BaseAddress,
					XNANDPSU_BUF_DATA_PORT_OFFSET);
	}
	Rem = IdLen % 4;
	if (Rem != 0U) {
		RegVal = XNandPsu_ReadReg(
					InstancePtr->Config.BaseAddress,
					XNANDPSU_BUF_DATA_PORT_OFFSET);
		for (RemIdx = 0U; RemIdx < Rem; RemIdx++) {
			Buf[(Index * 4U) + RemIdx] = (u8) (RegVal >>
						(RemIdx * 8U)) & 0xFFU;
		}
	}

	/*
	 * Poll for Transfer Complete event
	 */
	Status = XNandPsu_PollRegTimeout(
			InstancePtr,
			XNANDPSU_INTR_STS_OFFSET,
			XNANDPSU_INTR_STS_TRANS_COMP_STS_EN_MASK,
			XNANDPSU_INTR_POLL_TIMEOUT);
	if (Status != XST_SUCCESS) {
#ifdef XNANDPSU_DEBUG
		xil_printf("%s: Poll for xfer complete timeout\r\n",
							__func__);
#endif
		goto Out;
	}
	/*
	 * Clear Transfer Complete Interrupt in Interrupt Status Enable
	 * Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
		XNANDPSU_INTR_STS_EN_OFFSET,0U);
	/*
	 * Clear Transfer Complete Interrupt in Interrupt Status Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_INTR_STS_OFFSET,
			XNANDPSU_INTR_STS_TRANS_COMP_STS_EN_MASK);

Out:
	return Status;
}

/*****************************************************************************/
/**
*
* This function sends the ONFI Read Parameter Page command to flash.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
* @param	Target is the chip select value.
* @param	PrmIndex is the index of parameter page.
* @param	Buf is the parameter page information to return.
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_FAILURE if failed.
*
* @note		None
*
******************************************************************************/
static s32 XNandPsu_OnfiReadParamPage(XNandPsu *InstancePtr, u32 Target,
						u8 *Buf)
{
	s32 Status = XST_FAILURE;
	u32 *BufPtr = (u32 *)(void *)Buf;
	u32 Index;

	/*
	 * Assert the input arguments.
	 */
	Xil_AssertNonvoid(Target < XNANDPSU_MAX_TARGETS);
	Xil_AssertNonvoid(Buf != NULL);

	/*
	 * Enable Buffer Read Ready Interrupt in Interrupt Status Enable
	 * Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
		XNANDPSU_INTR_STS_EN_OFFSET,
		XNANDPSU_INTR_STS_EN_BUFF_RD_RDY_STS_EN_MASK);
	/*
	 * Program Command
	 */
	XNandPsu_Prepare_Cmd(InstancePtr, ONFI_CMD_RD_PRM_PG, ONFI_CMD_INVALID,
					0U, 0U, ONFI_PRM_PG_ADDR_CYCLES);
	/*
	 * Program Column, Page, Block address
	 */
	XNandPsu_SetPageColAddr(InstancePtr, 0U, 0U);
	/*
	 * Program Memory Address Register2 for chip select
	 */
	XNandPsu_SelectChip(InstancePtr, Target);
	/*
	 * Program Packet Size and Packet Count
	 */
	XNandPsu_SetPktSzCnt(InstancePtr, ONFI_PRM_PG_LEN, 1U);
	/*
	 * Set Read Parameter Page in Program Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_PROG_OFFSET,XNANDPSU_PROG_RD_PRM_PG_MASK);

	/*
	 * Poll for Buffer Read Ready event
	 */
	 Status = XNandPsu_PollRegTimeout(
			InstancePtr,
			XNANDPSU_INTR_STS_OFFSET,
			XNANDPSU_INTR_STS_BUFF_RD_RDY_STS_EN_MASK,
			XNANDPSU_INTR_POLL_TIMEOUT);
	 if (Status != XST_SUCCESS) {
#ifdef XNANDPSU_DEBUG
			xil_printf("%s: Poll for buf read ready timeout\r\n",
							__func__);
#endif
			goto Out;
		}


			/*
			 * Enable Transfer Complete Interrupt in Interrupt
			 * Status Enable Register
			 */
			XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
				(XNANDPSU_INTR_STS_EN_OFFSET),
				XNANDPSU_INTR_STS_EN_TRANS_COMP_STS_EN_MASK);
		/*
		 * Clear Buffer Read Ready Interrupt in Interrupt Status
		 * Register
		 */
		XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
				XNANDPSU_INTR_STS_OFFSET,
				XNANDPSU_INTR_STS_BUFF_RD_RDY_STS_EN_MASK);
		/*
		 * Read Packet Data from Data Port Register
		 */
		for (Index = 0U; Index < (ONFI_PRM_PG_LEN/4); Index++) {
			BufPtr[Index] = XNandPsu_ReadReg(
					InstancePtr->Config.BaseAddress,
						XNANDPSU_BUF_DATA_PORT_OFFSET);
		}

	/*
	 * Poll for Transfer Complete event
	 */
	Status = XNandPsu_PollRegTimeout(
			InstancePtr,
			XNANDPSU_INTR_STS_OFFSET,
			XNANDPSU_INTR_STS_TRANS_COMP_STS_EN_MASK,
			XNANDPSU_INTR_POLL_TIMEOUT);
	if (Status != XST_SUCCESS) {
#ifdef XNANDPSU_DEBUG
		xil_printf("%s: Poll for xfer complete timeout\r\n",
							__func__);
#endif
		goto Out;
	}
	/*
	 * Clear Transfer Complete Interrupt in Interrupt Status Enable
	 * Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
		XNANDPSU_INTR_STS_EN_OFFSET, 0U);
	/*
	 * Clear Transfer Complete Interrupt in Interrupt Status Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_INTR_STS_OFFSET,
			XNANDPSU_INTR_STS_TRANS_COMP_STS_EN_MASK);

Out:
	return Status;
}

/*****************************************************************************/
/**
*
* This function returns the length including bad blocks from a given offset and
* length.
*
* @param	InstancePtr is the pointer to the XNandPsu instance.
* @param	Offset is the flash data address to read from.
* @param	Length is number of bytes to read.
*
* @return
*		- Return actual length including bad blocks.
*
* @note		None.
*
******************************************************************************/
static s32 XNandPsu_CalculateLength(XNandPsu *InstancePtr, u64 Offset,
							u64 Length)
{
	s32 Status;
	u32 BlockSize;
	u32 BlockLen;
	u32 Block;
	u32 TempLen = 0;
	u64 OffsetVar = Offset;

	BlockSize = InstancePtr->Geometry.BlockSize;

	while (TempLen < Length) {
		Block = (u32) ((u32)OffsetVar/BlockSize);
		BlockLen = BlockSize - ((u32)OffsetVar % BlockSize);
		/*
		 * Check if the block is bad
		 */
		Status = XNandPsu_IsBlockBad(InstancePtr, Block);
		if (Status != XST_SUCCESS) {
			/*
			 * Good block
			 */
			TempLen += BlockLen;
		}
		if (OffsetVar >= InstancePtr->Geometry.DeviceSize) {
			Status = XST_FAILURE;
			goto Out;
		}
		OffsetVar += BlockLen;
	}

	Status = XST_SUCCESS;
Out:
	return Status;
}

/*****************************************************************************/
/**
*
* This function writes to the flash.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
* @param	Offset is the starting offset of flash to write.
* @param	Length is the number of bytes to write.
* @param	SrcBuf is the source data buffer to write.
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_FAILURE if failed.
*
* @note		None
*
******************************************************************************/
s32 XNandPsu_Write(XNandPsu *InstancePtr, u64 Offset, u64 Length, u8 *SrcBuf)
{
	s32 Status = XST_FAILURE;
	u32 Page;
	u32 Col;
	u32 Target;
	u32 Block;
	u32 PartialBytes = 0;
	u32 NumBytes;
	u32 RemLen;
	u8 *BufPtr;
	u8 *Ptr = (u8 *)SrcBuf;
	u16 OnfiStatus;
	u64 OffsetVar = Offset;
	u64 LengthVar = Length;

	/*
	 * Assert the input arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(SrcBuf != NULL);
	Xil_AssertNonvoid(LengthVar != 0U);
	Xil_AssertNonvoid((OffsetVar + LengthVar) <
				InstancePtr->Geometry.DeviceSize);

	/*
	 * Check if write operation exceeds flash size when including
	 * bad blocks.
	 */
	Status = XNandPsu_CalculateLength(InstancePtr, OffsetVar, LengthVar);
	if (Status != XST_SUCCESS) {
		goto Out;
	}

	while (LengthVar > 0U) {
		Block = (u32) (OffsetVar/InstancePtr->Geometry.BlockSize);
		/*
		 * Skip the bad blocks. Increment the offset by block size.
		 * For better results, always program the flash starting at
		 * a block boundary.
		 */
		if (XNandPsu_IsBlockBad(InstancePtr, Block) == XST_SUCCESS) {
			OffsetVar += (u64)InstancePtr->Geometry.BlockSize;
			continue;
		}
		/*
		 * Calculate Page and Column address values
		 */
		Page = (u32) (OffsetVar/InstancePtr->Geometry.BytesPerPage);
		Col = (u32) (OffsetVar &
				(InstancePtr->Geometry.BytesPerPage - 1U));
		PartialBytes = 0U;
		/*
		 * Check if partial write.
		 * If column address is > 0 or Length is < page size
		 */
		if ((Col > 0U) ||
			(LengthVar < InstancePtr->Geometry.BytesPerPage)) {
			RemLen = InstancePtr->Geometry.BytesPerPage - Col;
			PartialBytes = (RemLen < (u32)LengthVar) ?
					RemLen : (u32)LengthVar;
		}

		Target = (u32) (OffsetVar/InstancePtr->Geometry.TargetSize);
		if (Page > InstancePtr->Geometry.NumTargetPages) {
			Page %= InstancePtr->Geometry.NumTargetPages;
		}

		/*
		 * Check if partial write
		 */
		if (PartialBytes > 0U) {
			BufPtr = &InstancePtr->PartialDataBuf[0];
			memset(BufPtr, 0xFF,
					InstancePtr->Geometry.BytesPerPage);
			memcpy(BufPtr + Col, Ptr, PartialBytes);

			NumBytes = PartialBytes;
		} else {
			BufPtr = (u8 *)Ptr;
			NumBytes = (InstancePtr->Geometry.BytesPerPage <
					(u32)LengthVar) ?
					InstancePtr->Geometry.BytesPerPage :
					(u32)LengthVar;
		}
		/*
		 * Program page
		 */
		Status = XNandPsu_ProgramPage(InstancePtr, Target, Page, 0U,
								BufPtr);
		if (Status != XST_SUCCESS) {
			goto Out;
		}
		/*
		 * ONFI ReadStatus
		 */
		do {
			Status = XNandPsu_OnfiReadStatus(InstancePtr, Target,
								&OnfiStatus);
			if (Status != XST_SUCCESS) {
				goto Out;
			}
			if ((OnfiStatus & (1U << 6U)) != 0U) {
				if ((OnfiStatus & (1U << 0U)) != 0U) {
					Status = XST_FAILURE;
					goto Out;
				}
			}
		} while (((OnfiStatus >> 6U) & 0x1U) == 0U);

		Ptr += NumBytes;
		OffsetVar += NumBytes;
		LengthVar -= NumBytes;
	}

	Status = XST_SUCCESS;
Out:
	return Status;
}

/*****************************************************************************/
/**
*
* This function reads from the flash.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
* @param	Offset is the starting offset of flash to read.
* @param	Length is the number of bytes to read.
* @param	DestBuf is the destination data buffer to fill in.
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_FAILURE if failed.
*
* @note		None
*
******************************************************************************/
s32 XNandPsu_Read(XNandPsu *InstancePtr, u64 Offset, u64 Length, u8 *DestBuf)
{
	s32 Status = XST_FAILURE;
	u32 Page;
	u32 Col;
	u32 Target;
	u32 Block;
	u32 PartialBytes = 0U;
	u32 RemLen;
	u32 NumBytes;
	u8 *BufPtr;
	u8 *Ptr = (u8 *)DestBuf;
	u64 OffsetVar = Offset;
	u64 LengthVar = Length;

	/*
	 * Assert the input arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(LengthVar != 0U);
	Xil_AssertNonvoid((OffsetVar + LengthVar) <
				InstancePtr->Geometry.DeviceSize);

	/*
	 * Check if read operation exceeds flash size when including
	 * bad blocks.
	 */
	Status = XNandPsu_CalculateLength(InstancePtr, OffsetVar, LengthVar);
	if (Status != XST_SUCCESS) {
		goto Out;
	}

	while (LengthVar > 0U) {
		Block = (u32) (OffsetVar/InstancePtr->Geometry.BlockSize);
		/*
		 * Skip the bad block. Increment the offset by block size.
		 * The flash programming utility must make sure to start
		 * writing always at a block boundary and skip blocks if any.
		 */
		if (XNandPsu_IsBlockBad(InstancePtr, Block) == XST_SUCCESS) {
			OffsetVar += (u64)InstancePtr->Geometry.BlockSize;
			continue;
		}
		/*
		 * Calculate Page and Column address values
		 */
		Page = (u32) (OffsetVar/InstancePtr->Geometry.BytesPerPage);
		Col = (u32) (OffsetVar &
				(InstancePtr->Geometry.BytesPerPage - 1U));
		PartialBytes = 0U;
		/*
		 * Check if partial write.
		 * If column address is > 0 or Length is < page size
		 */
		if ((Col > 0U) ||
			(LengthVar < InstancePtr->Geometry.BytesPerPage)) {
			RemLen = InstancePtr->Geometry.BytesPerPage - Col;
			PartialBytes = ((u32)RemLen < (u32)LengthVar) ?
						(u32)RemLen : (u32)LengthVar;
		}

		Target = (u32) (OffsetVar/InstancePtr->Geometry.TargetSize);
		if (Page > InstancePtr->Geometry.NumTargetPages) {
			Page %= InstancePtr->Geometry.NumTargetPages;
		}
		/*
		 * Check if partial read
		 */
		if (PartialBytes > 0U) {
			BufPtr = &InstancePtr->PartialDataBuf[0];
			NumBytes = PartialBytes;
		} else {
			BufPtr = Ptr;
			NumBytes = (InstancePtr->Geometry.BytesPerPage <
					(u32)LengthVar) ?
					InstancePtr->Geometry.BytesPerPage :
					(u32)LengthVar;
		}
		/*
		 * Read page
		 */
		Status = XNandPsu_ReadPage(InstancePtr, Target, Page, 0U,
								BufPtr);
		if (Status != XST_SUCCESS) {
			goto Out;
		}
		if (PartialBytes > 0U) {
			memcpy(Ptr, BufPtr + Col, NumBytes);
		}
		Ptr += NumBytes;
		OffsetVar += NumBytes;
		LengthVar -= NumBytes;
	}

	Status = XST_SUCCESS;
Out:
	return Status;
}

/*****************************************************************************/
/**
*
* This function erases the flash.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
* @param	Offset is the starting offset of flash to erase.
* @param	Length is the number of bytes to erase.
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_FAILURE if failed.
*
* @note
*		The Offset and Length should be aligned to block size boundary
*		to get better results.
*
******************************************************************************/
s32 XNandPsu_Erase(XNandPsu *InstancePtr, u64 Offset, u64 Length)
{
	s32 Status = XST_FAILURE;
	u32 Target = 0;
	u32 StartBlock;
	u32 NumBlocks = 0;
	u32 Block;
	u32 AlignOff;
	u32 EraseLen;
	u32 BlockRemLen;
	u16 OnfiStatus;
	u64 OffsetVar = Offset;
	u64 LengthVar = Length;

	/*
	 * Assert the input arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(LengthVar != 0U);
	Xil_AssertNonvoid((OffsetVar + LengthVar) <
			InstancePtr->Geometry.DeviceSize);

	/*
	 * Check if erase operation exceeds flash size when including
	 * bad blocks.
	 */
	Status = XNandPsu_CalculateLength(InstancePtr, OffsetVar, LengthVar);
	if (Status != XST_SUCCESS) {
		goto Out;
	}
	/*
	 * Calculate number of blocks to erase
	 */
	StartBlock = (u32) (OffsetVar/InstancePtr->Geometry.BlockSize);

	while (LengthVar > 0U) {
		Block = (u32) (OffsetVar/InstancePtr->Geometry.BlockSize);
		if (XNandPsu_IsBlockBad(InstancePtr, Block) ==
							XST_SUCCESS) {
			OffsetVar += (u64)InstancePtr->Geometry.BlockSize;
			NumBlocks++;
			continue;
		}

		AlignOff = (u32)OffsetVar &
				(InstancePtr->Geometry.BlockSize - (u32)1);
		if (AlignOff > 0U) {
			BlockRemLen = InstancePtr->Geometry.BlockSize -
								AlignOff;
			EraseLen = (BlockRemLen < (u32)LengthVar) ?
						BlockRemLen :(u32)LengthVar;
		} else {
			EraseLen = (InstancePtr->Geometry.BlockSize <
						(u32)LengthVar) ?
					InstancePtr->Geometry.BlockSize:
						(u32)LengthVar;
		}
		NumBlocks++;
		OffsetVar += EraseLen;
		LengthVar -= EraseLen;
	}

	for (Block = StartBlock; Block < (StartBlock + NumBlocks); Block++) {
		Target = Block/InstancePtr->Geometry.NumTargetBlocks;
		Block %= InstancePtr->Geometry.NumTargetBlocks;
		if (XNandPsu_IsBlockBad(InstancePtr, Block) ==
							XST_SUCCESS) {
			/*
			 * Don't erase bad block
			 */
			continue;
		}
		/*
		 * Block Erase
		 */
		Status = XNandPsu_EraseBlock(InstancePtr, Target, Block);
		if (Status != XST_SUCCESS) {
			goto Out;
		}
		/*
		 * ONFI ReadStatus
		 */
		do {
			Status = XNandPsu_OnfiReadStatus(InstancePtr, Target,
								&OnfiStatus);
			if (Status != XST_SUCCESS) {
				goto Out;
			}
			if ((OnfiStatus & (1U << 6U)) != 0U) {
				if ((OnfiStatus & (1U << 0U)) != 0U) {
					Status = XST_FAILURE;
					goto Out;
				}
			}
		} while (((OnfiStatus >> 6U) & 0x1U) == 0U);
	}

	Status = XST_SUCCESS;
Out:
	return Status;
}

/*****************************************************************************/
/**
*
* This function sends ONFI Program Page command to flash.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
* @param	Target is the chip select value.
* @param	Page is the page address value to program.
* @param	Col is the column address value to program.
* @param	Buf is the data buffer to program.
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_FAILURE if failed.
*
* @note		None
*
******************************************************************************/
static s32 XNandPsu_ProgramPage(XNandPsu *InstancePtr, u32 Target, u32 Page,
							u32 Col, u8 *Buf)
{
	u32 AddrCycles = InstancePtr->Geometry.RowAddrCycles +
				InstancePtr->Geometry.ColAddrCycles;
	u32 PktSize;
	u32 PktCount;
	u32 BufWrCnt = 0U;
	u32 *BufPtr = (u32 *)(void *)Buf;
	s32 Status = XST_FAILURE;
	u32 Index;

	/*
	 * Assert the input arguments.
	 */
	Xil_AssertNonvoid(Page < InstancePtr->Geometry.NumPages);
	Xil_AssertNonvoid(Buf != NULL);

	if (InstancePtr->EccCfg.CodeWordSize > 9U) {
		PktSize = 1024U;
	} else {
		PktSize = 512U;
	}
	PktCount = InstancePtr->Geometry.BytesPerPage/PktSize;

	XNandPsu_Prepare_Cmd(InstancePtr, ONFI_CMD_PG_PROG1, ONFI_CMD_PG_PROG2,
					1U, 1U, (u8)AddrCycles);

	if (InstancePtr->DmaMode == XNANDPSU_MDMA) {

		/*
		 * Enable DMA boundary Interrupt in Interrupt Status
		 * Enable Register
		 */
		XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_INTR_STS_EN_OFFSET,
			XNANDPSU_INTR_STS_EN_TRANS_COMP_STS_EN_MASK |
			XNANDPSU_INTR_STS_EN_DMA_INT_STS_EN_MASK);
	} else {
		/*
		 * Enable Buffer Write Ready Interrupt in Interrupt Status
		 * Enable Register
		 */
		XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_INTR_STS_EN_OFFSET,
			XNANDPSU_INTR_STS_EN_BUFF_WR_RDY_STS_EN_MASK);
	}
	/*
	 * Program Page Size
	 */
	XNandPsu_SetPageSize(InstancePtr);
	/*
	 * Program Packet Size and Packet Count
	 */
	XNandPsu_SetPktSzCnt(InstancePtr, PktSize, PktCount);
	/*
	 * Program DMA system address and DMA buffer boundary
	 */
	if (InstancePtr->DmaMode == XNANDPSU_MDMA) {
		/*
		 * Flush the Data Cache
		 */
		Xil_DCacheFlushRange((INTPTR)Buf, (PktSize * PktCount));

#ifdef __aarch64__
		XNandPsu_WriteReg(InstancePtr->Config.BaseAddress,
				XNANDPSU_DMA_SYS_ADDR1_OFFSET,
				(u32) (((INTPTR)Buf >> 32) & 0xFFFFFFFFU));
#endif
		XNandPsu_WriteReg(InstancePtr->Config.BaseAddress,
				XNANDPSU_DMA_SYS_ADDR0_OFFSET,
				(u32) ((INTPTR)(void *)Buf & 0xFFFFFFFFU));
	}
	/*
	 * Program Column, Page, Block address
	 */
	XNandPsu_SetPageColAddr(InstancePtr, Page, (u16)Col);
	/*
	 * Set Bus Width
	 */
	XNandPsu_SetBusWidth(InstancePtr);
	/*
	 * Program Memory Address Register2 for chip select
	 */
	XNandPsu_SelectChip(InstancePtr, Target);
	/*
	 * Set ECC
	 */
	if (InstancePtr->EccMode == XNANDPSU_HWECC) {
		XNandPsu_SetEccSpareCmd(InstancePtr, ONFI_CMD_CHNG_WR_COL,
					InstancePtr->Geometry.ColAddrCycles);
	}
	/*
	 * Set Page Program in Program Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_PROG_OFFSET,XNANDPSU_PROG_PG_PROG_MASK);

	if (InstancePtr->DmaMode == XNANDPSU_MDMA) {
		goto WriteDmaDone;
	}

	while (BufWrCnt < PktCount) {
		/*
		 * Poll for Buffer Write Ready event
		 */
		Status = XNandPsu_PollRegTimeout(
			InstancePtr,
			XNANDPSU_INTR_STS_OFFSET,
			XNANDPSU_INTR_STS_BUFF_WR_RDY_STS_EN_MASK,
			XNANDPSU_INTR_POLL_TIMEOUT);
		if (Status != XST_SUCCESS) {
#ifdef XNANDPSU_DEBUG
			xil_printf("%s: Poll for buf write ready timeout\r\n",
							__func__);
#endif
			goto Out;
		}
		/*
		 * Increment Buffer Write Interrupt Count
		 */
		BufWrCnt++;

		if (BufWrCnt == PktCount) {
			/*
			 * Enable Transfer Complete Interrupt in Interrupt
			 * Status Enable Register
			 */
			XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
				XNANDPSU_INTR_STS_EN_OFFSET,
				XNANDPSU_INTR_STS_EN_TRANS_COMP_STS_EN_MASK);
		} else {
			/*
			 * Clear Buffer Write Ready Interrupt in Interrupt
			 * Status Enable Register
			 */
			XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
				XNANDPSU_INTR_STS_EN_OFFSET, 0U);

		}
		/*
		 * Clear Buffer Write Ready Interrupt in Interrupt Status
		 * Register
		 */
		XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
				XNANDPSU_INTR_STS_OFFSET,
				XNANDPSU_INTR_STS_BUFF_WR_RDY_STS_EN_MASK);
		/*
		 * Write Packet Data to Data Port Register
		 */
		for (Index = 0U; Index < (PktSize/4U); Index++) {
			XNandPsu_WriteReg(InstancePtr->Config.BaseAddress,
						XNANDPSU_BUF_DATA_PORT_OFFSET,
						BufPtr[Index]);
		}
		BufPtr += (PktSize/4U);

		if (BufWrCnt < PktCount) {
			/*
			 * Enable Buffer Write Ready Interrupt in Interrupt
			 * Status Enable Register
			 */
			XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
				XNANDPSU_INTR_STS_EN_OFFSET,
				XNANDPSU_INTR_STS_EN_BUFF_WR_RDY_STS_EN_MASK);
		} else {
			break;
		}
	}
WriteDmaDone:
	/*
	 * Poll for Transfer Complete event
	 */
	Status = XNandPsu_PollRegTimeout(
			InstancePtr,
			XNANDPSU_INTR_STS_OFFSET,
			XNANDPSU_INTR_STS_TRANS_COMP_STS_EN_MASK,
			XNANDPSU_INTR_POLL_TIMEOUT);
	if (Status != XST_SUCCESS) {
#ifdef XNANDPSU_DEBUG
		xil_printf("%s: Poll for xfer complete timeout\r\n",
							__func__);
#endif
		goto Out;
	}
	/*
	 * Clear Transfer Complete Interrupt in Interrupt Status Enable
	 * Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
		XNANDPSU_INTR_STS_EN_OFFSET, 0U);

	/*
	 * Clear Transfer Complete Interrupt in Interrupt Status Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_INTR_STS_OFFSET,
			XNANDPSU_INTR_STS_TRANS_COMP_STS_EN_MASK);

Out:
	return Status;
}

/*****************************************************************************/
/**
*
* This function sends ONFI Program Page command to flash.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
* @param	Target is the chip select value.
* @param	Page is the page address value to program.
* @param	Col is the column address value to program.
* @param	Buf is the data buffer to program.
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_FAILURE if failed.
*
* @note		None
*
******************************************************************************/
s32 XNandPsu_WriteSpareBytes(XNandPsu *InstancePtr, u32 Page, u8 *Buf)
{
	u32 AddrCycles = InstancePtr->Geometry.RowAddrCycles +
				InstancePtr->Geometry.ColAddrCycles;
	u32 Col = InstancePtr->Geometry.BytesPerPage;
	u32 Target = Page/InstancePtr->Geometry.NumTargetPages;
	u32 PktSize = InstancePtr->Geometry.SpareBytesPerPage;
	u32 PktCount = 1U;
	u32 BufWrCnt = 0U;
	u32 *BufPtr = (u32 *)(void *)Buf;
	u16 PreEccSpareCol = 0U;
	u16 PreEccSpareWrCnt = 0U;
	u16 PostEccSpareCol = 0U;
	u16 PostEccSpareWrCnt = 0U;
	u32 PostWrite = 0U;
	OnfiCmdFormat Cmd;
	s32 Status = XST_FAILURE;
	u32 Index;
	u32 PageVar = Page;

	/*
	 * Assert the input arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(PageVar < InstancePtr->Geometry.NumPages);
	Xil_AssertNonvoid(Buf != NULL);

	PageVar %= InstancePtr->Geometry.NumTargetPages;

	if (InstancePtr->EccMode == XNANDPSU_HWECC) {
		/*
		 * Calculate ECC free positions before and after ECC code
		 */
		PreEccSpareCol = 0x0U;
		PreEccSpareWrCnt = InstancePtr->EccCfg.EccAddr -
				(u16)InstancePtr->Geometry.BytesPerPage;

		PostEccSpareCol = PreEccSpareWrCnt +
					InstancePtr->EccCfg.EccSize;
		PostEccSpareWrCnt = InstancePtr->Geometry.SpareBytesPerPage -
					PostEccSpareCol;

		PreEccSpareWrCnt = (PreEccSpareWrCnt/4U) * 4U;
		PostEccSpareWrCnt = (PostEccSpareWrCnt/4U) * 4U;

		if (PreEccSpareWrCnt > 0U) {
			PktSize = PreEccSpareWrCnt;
			PktCount = 1U;
			Col = InstancePtr->Geometry.BytesPerPage +
							PreEccSpareCol;
			BufPtr = (u32 *)(void *)Buf;
			if (PostEccSpareWrCnt > 0U) {
				PostWrite = 1U;
			}
		} else if (PostEccSpareWrCnt > 0U) {
			PktSize = PostEccSpareWrCnt;
			PktCount = 1U;
			Col = InstancePtr->Geometry.BytesPerPage +
							PostEccSpareCol;
			BufPtr = (u32 *)(void *)&Buf[Col];
		} else {
			/*
			 * No free spare bytes available for writing
			 */
			Status = XST_FAILURE;
			goto Out;
		}
	}

	if (InstancePtr->DmaMode == XNANDPSU_MDMA) {
		/*
		 * Enable Transfer Complete Interrupt in Interrupt Status
		 * Enable Register
		 */
		XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_INTR_STS_EN_OFFSET,
			XNANDPSU_INTR_STS_EN_TRANS_COMP_STS_EN_MASK);

	} else {
		/*
		 * Enable Buffer Write Ready Interrupt in Interrupt Status
		 * Enable Register
		 */
		XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_INTR_STS_EN_OFFSET,
			XNANDPSU_INTR_STS_EN_BUFF_WR_RDY_STS_EN_MASK);

	}
	/*
	 * Program Command hack for change write column
	 */
	if (PostWrite > 0U) {
		Cmd.Command1 = 0x80U;
		Cmd.Command2 = 0x00U;
		XNandPsu_Prepare_Cmd(InstancePtr, Cmd.Command1, Cmd.Command2,
				0U , 1U, (u8)AddrCycles);

	} else {
		XNandPsu_Prepare_Cmd(InstancePtr, ONFI_CMD_PG_PROG1,
				ONFI_CMD_PG_PROG2, 0U , 1U, (u8)AddrCycles);
	}
	/*
	 * Program Page Size
	 */
	XNandPsu_SetPageSize(InstancePtr);
	/*
	 * Program Packet Size and Packet Count
	 */
	XNandPsu_SetPktSzCnt(InstancePtr, PktSize, PktCount);
	/*
	 * Program DMA system address and DMA buffer boundary
	 */
	if (InstancePtr->DmaMode == XNANDPSU_MDMA) {
		/*
		 * Flush the Data Cache
		 */
		Xil_DCacheFlushRange((INTPTR)BufPtr, (PktSize * PktCount));

#ifdef __aarch64__
		XNandPsu_WriteReg(InstancePtr->Config.BaseAddress,
				XNANDPSU_DMA_SYS_ADDR1_OFFSET,
				(u32) (((INTPTR)BufPtr >> 32) & 0xFFFFFFFFU));
#endif
		XNandPsu_WriteReg(InstancePtr->Config.BaseAddress,
				XNANDPSU_DMA_SYS_ADDR0_OFFSET,
				(u32) ((INTPTR)(void *)BufPtr & 0xFFFFFFFFU));

		XNandPsu_WriteReg(InstancePtr->Config.BaseAddress,
				XNANDPSU_DMA_BUF_BND_OFFSET,
				XNANDPSU_DMA_BUF_BND_512K);
	}
	/*
	 * Program Column, Page, Block address
	 */
	XNandPsu_SetPageColAddr(InstancePtr, PageVar, (u16)Col);
	/*
	 * Set Bus Width
	 */
	XNandPsu_SetBusWidth(InstancePtr);
	/*
	 * Program Memory Address Register2 for chip select
	 */
	XNandPsu_SelectChip(InstancePtr, Target);
	/*
	 * Set Page Program in Program Register
	 */
	if (PostWrite > 0U) {
		XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_PROG_OFFSET,((u32)XNANDPSU_PROG_PG_PROG_MASK |
				(u32)XNANDPSU_PROG_CHNG_ROW_ADDR_MASK));
	} else {
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_PROG_OFFSET,XNANDPSU_PROG_PG_PROG_MASK);
	}

	if (InstancePtr->DmaMode == XNANDPSU_MDMA) {
		goto WriteDmaDone;
	}

	while (BufWrCnt < PktCount) {
		/*
		 * Poll for Buffer Write Ready event
		 */
		Status = XNandPsu_PollRegTimeout(
			InstancePtr,
			XNANDPSU_INTR_STS_OFFSET,
			XNANDPSU_INTR_STS_BUFF_WR_RDY_STS_EN_MASK,
			XNANDPSU_INTR_POLL_TIMEOUT);
		if (Status != XST_SUCCESS) {
#ifdef XNANDPSU_DEBUG
			xil_printf("%s: Poll for buf write ready timeout\r\n",
							__func__);
#endif
			goto Out;
		}
		/*
		 * Increment Buffer Write Interrupt Count
		 */
		BufWrCnt++;

		if (BufWrCnt == PktCount) {
			/*
			 * Enable Transfer Complete Interrupt in Interrupt
			 * Status Enable Register
			 */
			XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
				XNANDPSU_INTR_STS_EN_OFFSET,
				XNANDPSU_INTR_STS_EN_TRANS_COMP_STS_EN_MASK);

		} else {
			/*
			 * Clear Buffer Write Ready Interrupt in Interrupt
			 * Status Enable Register
			 */
			XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
				XNANDPSU_INTR_STS_EN_OFFSET, 0U);
		}
		/*
		 * Clear Buffer Write Ready Interrupt in Interrupt Status
		 * Register
		 */
		XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
				XNANDPSU_INTR_STS_OFFSET,
				XNANDPSU_INTR_STS_BUFF_WR_RDY_STS_EN_MASK);
		/*
		 * Write Packet Data to Data Port Register
		 */
		for (Index = 0U; Index < (PktSize/4U); Index++) {
			XNandPsu_WriteReg(InstancePtr->Config.BaseAddress,
						XNANDPSU_BUF_DATA_PORT_OFFSET,
						BufPtr[Index]);
		}
		BufPtr += (PktSize/4U);

		if (BufWrCnt < PktCount) {
			/*
			 * Enable Buffer Write Ready Interrupt in Interrupt
			 * Status Enable Register
			 */
			XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
				XNANDPSU_INTR_STS_EN_OFFSET,
				XNANDPSU_INTR_STS_EN_BUFF_WR_RDY_STS_EN_MASK);
		} else {
			break;
		}
	}
WriteDmaDone:
	/*
	 * Poll for Transfer Complete event
	 */
	Status = XNandPsu_PollRegTimeout(
			InstancePtr,
			XNANDPSU_INTR_STS_OFFSET,
			XNANDPSU_INTR_STS_TRANS_COMP_STS_EN_MASK,
			XNANDPSU_INTR_POLL_TIMEOUT);
	if (Status != XST_SUCCESS) {
#ifdef XNANDPSU_DEBUG
		xil_printf("%s: Poll for xfer complete timeout\r\n",
							__func__);
#endif
		goto Out;
	}
	/*
	 * Clear Transfer Complete Interrupt in Interrupt Status Enable
	 * Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
		XNANDPSU_INTR_STS_EN_OFFSET, 0U);

	/*
	 * Clear Transfer Complete Interrupt in Interrupt Status Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
				XNANDPSU_INTR_STS_OFFSET,
				XNANDPSU_INTR_STS_TRANS_COMP_STS_EN_MASK);

	if (InstancePtr->EccMode == XNANDPSU_HWECC) {
		if (PostWrite > 0U) {
			BufPtr = (u32 *)(void *)&Buf[PostEccSpareCol];
			Status = XNandPsu_ChangeWriteColumn(InstancePtr,
					Target,
					PostEccSpareCol, PostEccSpareWrCnt, 1U,
					(u8 *)(void *)BufPtr);
			if (Status != XST_SUCCESS) {
				goto Out;
			}
		}
	}
Out:

	return Status;
}

/*****************************************************************************/
/**
*
* This function sends ONFI Read Page command to flash.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
* @param	Target is the chip select value.
* @param	Page is the page address value to read.
* @param	Col is the column address value to read.
* @param	Buf is the data buffer to fill in.
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_FAILURE if failed.
*
* @note		None
*
******************************************************************************/
static s32 XNandPsu_ReadPage(XNandPsu *InstancePtr, u32 Target, u32 Page,
							u32 Col, u8 *Buf)
{
	u32 AddrCycles = InstancePtr->Geometry.RowAddrCycles +
				InstancePtr->Geometry.ColAddrCycles;
	u32 PktSize;
	u32 PktCount;
	u32 BufRdCnt = 0U;
	u32 *BufPtr = (u32 *)(void *)Buf;
	s32 Status = XST_FAILURE;
	u32 Index, RegVal;

	/*
	 * Assert the input arguments.
	 */
	Xil_AssertNonvoid(Page < InstancePtr->Geometry.NumPages);
	Xil_AssertNonvoid(Target < XNANDPSU_MAX_TARGETS);

	if (InstancePtr->EccCfg.CodeWordSize > 9U) {
		PktSize = 1024U;
	} else {
		PktSize = 512U;
	}
	PktCount = InstancePtr->Geometry.BytesPerPage/PktSize;

	XNandPsu_Prepare_Cmd(InstancePtr, ONFI_CMD_RD1, ONFI_CMD_RD2,
					1U, 1U, (u8)AddrCycles);

	if (InstancePtr->DmaMode == XNANDPSU_MDMA) {

		/*
		 * Enable DMA boundary Interrupt in Interrupt Status
		 * Enable Register
		 */
		XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_INTR_STS_EN_OFFSET,
			XNANDPSU_INTR_STS_EN_TRANS_COMP_STS_EN_MASK |
			XNANDPSU_INTR_STS_EN_DMA_INT_STS_EN_MASK);

	} else {
		/*
		 * Enable Buffer Read Ready Interrupt in Interrupt Status
		 * Enable Register
		 */
		XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_INTR_STS_EN_OFFSET,
			XNANDPSU_INTR_STS_EN_BUFF_RD_RDY_STS_EN_MASK);

	}
	/*
	 * Enable Single bit error and Multi bit error
	 */
	if (InstancePtr->EccMode == XNANDPSU_HWECC) {
		/*
		 * Interrupt Status Enable Register
		 */
		XNandPsu_IntrStsEnable(InstancePtr,
			(XNANDPSU_INTR_STS_EN_MUL_BIT_ERR_STS_EN_MASK |
			XNANDPSU_INTR_STS_EN_ERR_INTR_STS_EN_MASK));
	}
	/*
	 * Program Page Size
	 */
	XNandPsu_SetPageSize(InstancePtr);
	/*
	 * Program Column, Page, Block address
	 */
	XNandPsu_SetPageColAddr(InstancePtr, Page, (u16)Col);
	/*
	 * Program Packet Size and Packet Count
	 */
	XNandPsu_SetPktSzCnt(InstancePtr, PktSize, PktCount);
	/*
	 * Program DMA system address and DMA buffer boundary
	 */
	if (InstancePtr->DmaMode == XNANDPSU_MDMA) {
		/*
		 * Invalidate the Data Cache
		 */
		Xil_DCacheInvalidateRange((INTPTR)Buf, (PktSize * PktCount));

#ifdef __aarch64__
		XNandPsu_WriteReg(InstancePtr->Config.BaseAddress,
				XNANDPSU_DMA_SYS_ADDR1_OFFSET,
				(u32) (((INTPTR)(void *)Buf >> 32) &
				0xFFFFFFFFU));
#endif
		XNandPsu_WriteReg(InstancePtr->Config.BaseAddress,
				XNANDPSU_DMA_SYS_ADDR0_OFFSET,
				(u32) ((INTPTR)(void *)Buf & 0xFFFFFFFFU));
	}
	/*
	 * Set Bus Width
	 */
	XNandPsu_SetBusWidth(InstancePtr);
	/*
	 * Program Memory Address Register2 for chip select
	 */
	XNandPsu_SelectChip(InstancePtr, Target);
	/*
	 * Set ECC
	 */
	if (InstancePtr->EccMode == XNANDPSU_HWECC) {
		XNandPsu_SetEccSpareCmd(InstancePtr,
					(ONFI_CMD_CHNG_RD_COL1 |
					(ONFI_CMD_CHNG_RD_COL2 << (u8)8U)),
					InstancePtr->Geometry.ColAddrCycles);
	}

	/*
	 * Set Read command in Program Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
				XNANDPSU_PROG_OFFSET,XNANDPSU_PROG_RD_MASK);

	if (InstancePtr->DmaMode == XNANDPSU_MDMA) {
		goto ReadDmaDone;
	}

	while (BufRdCnt < PktCount) {
		/*
		 * Poll for Buffer Read Ready event
		 */
		Status = XNandPsu_PollRegTimeout(
			InstancePtr,
			XNANDPSU_INTR_STS_OFFSET,
			XNANDPSU_INTR_STS_BUFF_RD_RDY_STS_EN_MASK,
			XNANDPSU_INTR_POLL_TIMEOUT);
		if (Status != XST_SUCCESS) {
#ifdef XNANDPSU_DEBUG
			xil_printf("%s: Poll for buf read ready timeout\r\n",
							__func__);
#endif
			goto CheckEccError;
		}
		/*
		 * Increment Buffer Read Interrupt Count
		 */
		BufRdCnt++;

		if (BufRdCnt == PktCount) {
			/*
			 * Enable Transfer Complete Interrupt in Interrupt
			 * Status Enable Register
			 */
			RegVal = XNandPsu_ReadReg(
					(InstancePtr)->Config.BaseAddress,
					XNANDPSU_INTR_STS_EN_OFFSET);
			RegVal &= ~XNANDPSU_INTR_STS_BUFF_RD_RDY_STS_EN_MASK;
			RegVal |= XNANDPSU_INTR_STS_EN_TRANS_COMP_STS_EN_MASK;
			XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
				XNANDPSU_INTR_STS_EN_OFFSET, RegVal);
		} else {
			/*
			 * Clear Buffer Read Ready Interrupt in Interrupt
			 * Status Enable Register
			 */
			RegVal = XNandPsu_ReadReg(
					(InstancePtr)->Config.BaseAddress,
					XNANDPSU_INTR_STS_EN_OFFSET);
			RegVal &= ~XNANDPSU_INTR_STS_BUFF_RD_RDY_STS_EN_MASK;
			XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
					XNANDPSU_INTR_STS_EN_OFFSET, RegVal);
		}
		/*
		 * Clear Buffer Read Ready Interrupt in Interrupt Status
		 * Register
		 */
		RegVal = XNandPsu_ReadReg(
				(InstancePtr)->Config.BaseAddress,
				XNANDPSU_INTR_STS_OFFSET);
		RegVal |= XNANDPSU_INTR_STS_BUFF_RD_RDY_STS_EN_MASK;
		XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
				XNANDPSU_INTR_STS_OFFSET, RegVal);
		/*
		 * Read Packet Data from Data Port Register
		 */
		for (Index = 0U; Index < (PktSize/4); Index++) {
			BufPtr[Index] = XNandPsu_ReadReg(
					InstancePtr->Config.BaseAddress,
					XNANDPSU_BUF_DATA_PORT_OFFSET);
		}
		BufPtr += (PktSize/4);

		if (BufRdCnt < PktCount) {
			/*
			 * Enable Buffer Read Ready Interrupt in Interrupt
			 * Status Enable Register
			 */
			RegVal = XNandPsu_ReadReg(
					(InstancePtr)->Config.BaseAddress,
					XNANDPSU_INTR_STS_EN_OFFSET);
			RegVal |= XNANDPSU_INTR_STS_EN_BUFF_RD_RDY_STS_EN_MASK;
			XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
				XNANDPSU_INTR_STS_EN_OFFSET, RegVal);
		} else {
			break;
		}
	}
ReadDmaDone:
	/*
	 * Poll for Transfer Complete event
	 */
	Status = XNandPsu_PollRegTimeout(
			InstancePtr,
			XNANDPSU_INTR_STS_OFFSET,
			XNANDPSU_INTR_STS_TRANS_COMP_STS_EN_MASK,
			XNANDPSU_INTR_POLL_TIMEOUT);
	if (Status != XST_SUCCESS) {
#ifdef XNANDPSU_DEBUG
		xil_printf("%s: Poll for xfer complete timeout\r\n",
							__func__);
#endif
		goto CheckEccError;
	}
	/*
	 * Clear Transfer Complete Interrupt in Interrupt Status Enable
	 * Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_INTR_STS_EN_OFFSET, 0U);

	/*
	 * Clear Transfer Complete Interrupt in Interrupt Status Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_INTR_STS_OFFSET,
			XNANDPSU_INTR_STS_TRANS_COMP_STS_EN_MASK);

CheckEccError:
	/*
	 * Check ECC Errors
	 */
	if (InstancePtr->EccMode == XNANDPSU_HWECC) {
		/*
		 * Hamming Multi Bit Errors
		 */
		if (((u32)XNandPsu_ReadReg(InstancePtr->Config.BaseAddress,
				XNANDPSU_INTR_STS_OFFSET) &
			(u32)XNANDPSU_INTR_STS_MUL_BIT_ERR_STS_EN_MASK) != 0U) {

			XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
				XNANDPSU_INTR_STS_OFFSET,
				XNANDPSU_INTR_STS_MUL_BIT_ERR_STS_EN_MASK);

#ifdef XNANDPSU_DEBUG
			xil_printf("%s: ECC Hamming multi bit error\r\n",
							__func__);
#endif
			InstancePtr->Ecc_Stat_PerPage_flips =
					((XNandPsu_ReadReg(
					InstancePtr->Config.BaseAddress,
					XNANDPSU_ECC_ERR_CNT_OFFSET) &
					0x1FF00U) >> 8U);
			InstancePtr->Ecc_Stats_total_flips +=
					InstancePtr->Ecc_Stat_PerPage_flips;
			Status = XST_FAILURE;
		}
		/*
		 * Hamming Single Bit or BCH Errors
		 */
		if (((u32)XNandPsu_ReadReg(InstancePtr->Config.BaseAddress,
				XNANDPSU_INTR_STS_OFFSET) &
			(u32)XNANDPSU_INTR_STS_ERR_INTR_STS_EN_MASK) != 0U) {

			XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
					XNANDPSU_INTR_STS_OFFSET,
					XNANDPSU_INTR_STS_ERR_INTR_STS_EN_MASK);

			if (InstancePtr->EccCfg.IsBCH == 1U) {
				InstancePtr->Ecc_Stat_PerPage_flips =
						((XNandPsu_ReadReg(
						InstancePtr->Config.BaseAddress,
						XNANDPSU_ECC_ERR_CNT_OFFSET)&
						0x1FF00U) >> 8U);
				InstancePtr->Ecc_Stats_total_flips +=
					InstancePtr->Ecc_Stat_PerPage_flips;
				Status = XST_SUCCESS;
			}
		}
	}
Out:
	return Status;
}

/*****************************************************************************/
/**
*
* This function reads spare bytes from flash.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
* @param	Target is the chip select value.
* @param	Page is the page address value to read.
* @param	Buf is the data buffer to fill in.
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_FAILURE if failed.
*
* @note		None
*
******************************************************************************/
s32 XNandPsu_ReadSpareBytes(XNandPsu *InstancePtr, u32 Page, u8 *Buf)
{
	u32 AddrCycles = InstancePtr->Geometry.RowAddrCycles +
				InstancePtr->Geometry.ColAddrCycles;
	u32 Col = InstancePtr->Geometry.BytesPerPage;
	u32 Target = Page/InstancePtr->Geometry.NumTargetPages;
	u32 PktSize = InstancePtr->Geometry.SpareBytesPerPage;
	u32 PktCount = 1U;
	u32 BufRdCnt = 0U;
	u32 *BufPtr = (u32 *)(void *)Buf;
	s32 Status = XST_FAILURE;
	u32 Index;
	u32 PageVar = Page;

	/*
	 * Assert the input arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(PageVar < InstancePtr->Geometry.NumPages);
	Xil_AssertNonvoid(Buf != NULL);

	PageVar %= InstancePtr->Geometry.NumTargetPages;

	if (InstancePtr->DmaMode == XNANDPSU_MDMA) {
		/*
		 * Enable Transfer Complete Interrupt in Interrupt Status
		 * Enable Register
		 */
		XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
				XNANDPSU_INTR_STS_EN_OFFSET,
				XNANDPSU_INTR_STS_EN_TRANS_COMP_STS_EN_MASK);
	} else {
		/*
		 * Enable Buffer Read Ready Interrupt in Interrupt Status
		 * Enable Register
		 */
		XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
				XNANDPSU_INTR_STS_EN_OFFSET,
				XNANDPSU_INTR_STS_EN_BUFF_RD_RDY_STS_EN_MASK);
	}
	/*
	 * Program Command
	 */
	XNandPsu_Prepare_Cmd(InstancePtr, ONFI_CMD_RD1, ONFI_CMD_RD2, 0U,
						1U, (u8)AddrCycles);
	/*
	 * Program Page Size
	 */
	XNandPsu_SetPageSize(InstancePtr);
	/*
	 * Program Column, Page, Block address
	 */
	XNandPsu_SetPageColAddr(InstancePtr, PageVar, (u16)Col);
	/*
	 * Program Packet Size and Packet Count
	 */
	XNandPsu_SetPktSzCnt(InstancePtr, PktSize, PktCount);
	/*
	 * Program DMA system address and DMA buffer boundary
	 */
	if (InstancePtr->DmaMode == XNANDPSU_MDMA) {

		/*
		 * Invalidate the Data Cache
		 */
		Xil_DCacheInvalidateRange((INTPTR)Buf, (PktSize * PktCount));
#ifdef __aarch64__
		XNandPsu_WriteReg(InstancePtr->Config.BaseAddress,
				XNANDPSU_DMA_SYS_ADDR1_OFFSET,
				(u32) (((INTPTR)(void *)Buf >> 32) &
				0xFFFFFFFFU));
#endif
		XNandPsu_WriteReg(InstancePtr->Config.BaseAddress,
				XNANDPSU_DMA_SYS_ADDR0_OFFSET,
				(u32) ((INTPTR)(void *)Buf & 0xFFFFFFFFU));
	}
	/*
	 * Set Bus Width
	 */
	XNandPsu_SetBusWidth(InstancePtr);
	/*
	 * Program Memory Address Register2 for chip select
	 */
	XNandPsu_SelectChip(InstancePtr, Target);
	/*
	 * Set Read command in Program Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
				XNANDPSU_PROG_OFFSET,XNANDPSU_PROG_RD_MASK);

	if (InstancePtr->DmaMode == XNANDPSU_MDMA) {
		goto ReadDmaDone;
	}

	while (BufRdCnt < PktCount) {
		/*
		 * Poll for Buffer Read Ready event
		 */
		Status = XNandPsu_PollRegTimeout(
			InstancePtr,
			XNANDPSU_INTR_STS_OFFSET,
			XNANDPSU_INTR_STS_BUFF_RD_RDY_STS_EN_MASK,
			XNANDPSU_INTR_POLL_TIMEOUT);
		if (Status != XST_SUCCESS) {
#ifdef XNANDPSU_DEBUG
			xil_printf("%s: Poll for buf read ready timeout\r\n",
							__func__);
#endif
			goto Out;
		}
		/*
		 * Increment Buffer Read Interrupt Count
		 */
		BufRdCnt++;

		if (BufRdCnt == PktCount) {
			/*
			 * Enable Transfer Complete Interrupt in Interrupt
			 * Status Enable Register
			 */
			XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
				XNANDPSU_INTR_STS_EN_OFFSET,
				XNANDPSU_INTR_STS_EN_TRANS_COMP_STS_EN_MASK);

		} else {
			/*
			 * Clear Buffer Read Ready Interrupt in Interrupt
			 * Status Enable Register
			 */
			XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
					XNANDPSU_INTR_STS_EN_OFFSET, 0U);

		}
		/*
		 * Clear Buffer Read Ready Interrupt in Interrupt Status
		 * Register
		 */
		XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
				XNANDPSU_INTR_STS_OFFSET,
				XNANDPSU_INTR_STS_BUFF_RD_RDY_STS_EN_MASK);
		/*
		 * Read Packet Data from Data Port Register
		 */
		for (Index = 0U; Index < (PktSize/4); Index++) {
			BufPtr[Index] = XNandPsu_ReadReg(
					InstancePtr->Config.BaseAddress,
					XNANDPSU_BUF_DATA_PORT_OFFSET);
		}
		BufPtr += (PktSize/4);

		if (BufRdCnt < PktCount) {
			/*
			 * Enable Buffer Read Ready Interrupt in Interrupt
			 * Status Enable Register
			 */
			XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
				XNANDPSU_INTR_STS_EN_OFFSET,
				XNANDPSU_INTR_STS_EN_BUFF_RD_RDY_STS_EN_MASK);
		} else {
			break;
		}
	}
ReadDmaDone:
	/*
	 * Poll for Transfer Complete event
	 */
	Status = XNandPsu_PollRegTimeout(
			InstancePtr,
			XNANDPSU_INTR_STS_OFFSET,
			XNANDPSU_INTR_STS_TRANS_COMP_STS_EN_MASK,
			XNANDPSU_INTR_POLL_TIMEOUT);
	if (Status != XST_SUCCESS) {
#ifdef XNANDPSU_DEBUG
		xil_printf("%s: Poll for xfer complete timeout\r\n",
							__func__);
#endif
		goto Out;
	}
	/*
	 * Clear Transfer Complete Interrupt in Interrupt Status Enable
	 * Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_INTR_STS_EN_OFFSET, 0U);

	/*
	 * Clear Transfer Complete Interrupt in Interrupt Status Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_INTR_STS_OFFSET,
				XNANDPSU_INTR_STS_TRANS_COMP_STS_EN_MASK);
Out:

	return Status;
}

/*****************************************************************************/
/**
*
* This function sends ONFI block erase command to the flash.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
* @param	Target is the chip select value.
* @param	Block is the block to erase.
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_FAILURE if failed.
*
* @note		None
*
******************************************************************************/
s32 XNandPsu_EraseBlock(XNandPsu *InstancePtr, u32 Target, u32 Block)
{
	s32 Status = XST_FAILURE;
	u32 AddrCycles = InstancePtr->Geometry.RowAddrCycles;
	u32 Page;
	u32 ErasePage;
	u32 EraseCol;

	/*
	 * Assert the input arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(Target < XNANDPSU_MAX_TARGETS);
	Xil_AssertNonvoid(Block < InstancePtr->Geometry.NumBlocks);

	Page = Block * InstancePtr->Geometry.PagesPerBlock;
	ErasePage = (Page >> 16U) & 0xFFFFU;
	EraseCol = Page & 0xFFFFU;

	/*
	 * Enable Transfer Complete Interrupt in Interrupt Status Enable
	 * Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_INTR_STS_EN_OFFSET,
			XNANDPSU_INTR_STS_EN_TRANS_COMP_STS_EN_MASK);

	/*
	 * Program Command
	 */
	XNandPsu_Prepare_Cmd(InstancePtr, ONFI_CMD_BLK_ERASE1,
			ONFI_CMD_BLK_ERASE2, 0U , 0U, (u8)AddrCycles);
	/*
	 * Program Column, Page, Block address
	 */
	XNandPsu_SetPageColAddr(InstancePtr, ErasePage, (u16)EraseCol);
	/*
	 * Program Memory Address Register2 for chip select
	 */
	XNandPsu_SelectChip(InstancePtr, Target);
	/*
	 * Set Block Erase in Program Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_PROG_OFFSET,XNANDPSU_PROG_BLK_ERASE_MASK);
	/*
	 * Poll for Transfer Complete event
	 */
	Status = XNandPsu_PollRegTimeout(
			InstancePtr,
			XNANDPSU_INTR_STS_OFFSET,
			XNANDPSU_INTR_STS_TRANS_COMP_STS_EN_MASK,
			XNANDPSU_INTR_POLL_TIMEOUT);
	if (Status != XST_SUCCESS) {
#ifdef XNANDPSU_DEBUG
		xil_printf("%s: Poll for xfer complete timeout\r\n",
							__func__);
#endif
		goto Out;
	}
	/*
	 * Clear Transfer Complete Interrupt in Interrupt Status Enable
	 * Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_INTR_STS_EN_OFFSET, 0U);

	/*
	 * Clear Transfer Complete Interrupt in Interrupt Status Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_INTR_STS_OFFSET,
				XNANDPSU_INTR_STS_TRANS_COMP_STS_EN_MASK);

Out:
	return Status;
}

/*****************************************************************************/
/**
*
* This function sends ONFI Get Feature command to flash.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
* @param	Target is the chip select value.
* @param	Feature is the feature selector.
* @param	Buf is the buffer to fill feature value.
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_FAILURE if failed.
*
* @note		None
*
******************************************************************************/
s32 XNandPsu_GetFeature(XNandPsu *InstancePtr, u32 Target, u8 Feature,
								u8 *Buf)
{
	s32 Status;
	u32 Index;
	u32 PktSize = 4;
	u32 PktCount = 1;
	u32 *BufPtr = (u32 *)(void *)Buf;

	/*
	 * Assert the input arguments.
	 */
	Xil_AssertNonvoid(Buf != NULL);

	if (InstancePtr->DataInterface == XNANDPSU_NVDDR) {
		PktSize = 8U;
	}

	/*
	 * Enable Buffer Read Ready Interrupt in Interrupt Status
	 * Enable Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_INTR_STS_EN_OFFSET,
			XNANDPSU_INTR_STS_EN_BUFF_RD_RDY_STS_EN_MASK);
	/*
	 * Program Command
	 */
	XNandPsu_Prepare_Cmd(InstancePtr, ONFI_CMD_GET_FEATURES,
				ONFI_CMD_INVALID, 0U, 0U, 1U);
	/*
	 * Program Column, Page, Block address
	 */
	XNandPsu_SetPageColAddr(InstancePtr, 0x0U, Feature);
	/*
	 * Program Memory Address Register2 for chip select
	 */
	XNandPsu_SelectChip(InstancePtr, Target);
	/*
	 * Program Packet Size and Packet Count
	 */
	XNandPsu_SetPktSzCnt(InstancePtr, PktSize, PktCount);
	/*
	 * Set Read Parameter Page in Program Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_PROG_OFFSET,XNANDPSU_PROG_GET_FEATURES_MASK);
	/*
	 * Poll for Buffer Read Ready event
	 */
	Status = XNandPsu_PollRegTimeout(
		InstancePtr,
		XNANDPSU_INTR_STS_OFFSET,
		XNANDPSU_INTR_STS_BUFF_RD_RDY_STS_EN_MASK,
		XNANDPSU_INTR_POLL_TIMEOUT);
	if (Status != XST_SUCCESS) {
#ifdef XNANDPSU_DEBUG
		xil_printf("%s: Poll for buf read ready timeout\r\n",
							__func__);
#endif
		goto Out;
	}
	/*
	 * Clear Buffer Read Ready Interrupt in Interrupt Status Enable
	 * Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_INTR_STS_EN_OFFSET, 0U);

	/*
	 * Clear Buffer Read Ready Interrupt in Interrupt Status Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_INTR_STS_OFFSET,
				XNANDPSU_INTR_STS_BUFF_RD_RDY_STS_EN_MASK);
	/*
	 * Enable Transfer Complete Interrupt in Interrupt Status Enable
	 * Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_INTR_STS_EN_OFFSET,
			XNANDPSU_INTR_STS_EN_TRANS_COMP_STS_EN_MASK);

	/*
	 * Read Data from Data Port Register
	 */
	for (Index = 0U; Index < (PktSize/4U); Index++) {
		BufPtr[Index] = XNandPsu_ReadReg(
					InstancePtr->Config.BaseAddress,
					XNANDPSU_BUF_DATA_PORT_OFFSET);
	}
	/*
	 * Poll for Transfer Complete event
	 */
	Status = XNandPsu_PollRegTimeout(
			InstancePtr,
			XNANDPSU_INTR_STS_OFFSET,
			XNANDPSU_INTR_STS_TRANS_COMP_STS_EN_MASK,
			XNANDPSU_INTR_POLL_TIMEOUT);
	if (Status != XST_SUCCESS) {
#ifdef XNANDPSU_DEBUG
		xil_printf("%s: Poll for xfer complete timeout\r\n",
							__func__);
#endif
		goto Out;
	}
	/*
	 * Clear Transfer Complete Interrupt in Interrupt Status Enable
	 * Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_INTR_STS_EN_OFFSET, 0U);

	/*
	 * Clear Transfer Complete Interrupt in Interrupt Status Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_INTR_STS_OFFSET,
				XNANDPSU_INTR_STS_TRANS_COMP_STS_EN_MASK);

Out:
	return Status;
}

/*****************************************************************************/
/**
*
* This function sends ONFI Set Feature command to flash.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
* @param	Target is the chip select value.
* @param	Feature is the feature selector.
* @param	Buf is the feature value to send.
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_FAILURE if failed.
*
* @note		None
*
******************************************************************************/
s32 XNandPsu_SetFeature(XNandPsu *InstancePtr, u32 Target, u8 Feature,
								u8 *Buf)
{
	s32 Status;
	u32 Index;
	u32 PktSize = 4U;
	u32 PktCount = 1U;
	u32 *BufPtr = (u32 *)(void *)Buf;

	/*
	 * Assert the input arguments.
	 */
	Xil_AssertNonvoid(Buf != NULL);
	if (InstancePtr->DataInterface == XNANDPSU_NVDDR) {
		PktSize = 8U;
	}

	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_INTR_STS_EN_OFFSET, 0U);

	/*
	 * Enable Buffer Write Ready Interrupt in Interrupt Status
	 * Enable Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_INTR_STS_EN_OFFSET,
			XNANDPSU_INTR_STS_EN_BUFF_WR_RDY_STS_EN_MASK);

	/*
	 * Program Command
	 */
	XNandPsu_Prepare_Cmd(InstancePtr, ONFI_CMD_SET_FEATURES,
				ONFI_CMD_INVALID, 0U , 0U, 1U);
	/*
	 * Program Column, Page, Block address
	 */
	XNandPsu_SetPageColAddr(InstancePtr, 0x0U, Feature);
	/*
	 * Program Memory Address Register2 for chip select
	 */
	XNandPsu_SelectChip(InstancePtr, Target);
	/*
	 * Program Packet Size and Packet Count
	 */
	XNandPsu_SetPktSzCnt(InstancePtr, PktSize, PktCount);
	/*
	 * Set Read Parameter Page in Program Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_PROG_OFFSET,XNANDPSU_PROG_SET_FEATURES_MASK);
	/*
	 * Poll for Buffer Write Ready event
	 */
	Status = XNandPsu_PollRegTimeout(
		InstancePtr,
		XNANDPSU_INTR_STS_OFFSET,
		XNANDPSU_INTR_STS_BUFF_WR_RDY_STS_EN_MASK,
		XNANDPSU_INTR_POLL_TIMEOUT);
	if (Status != XST_SUCCESS) {
#ifdef XNANDPSU_DEBUG
		xil_printf("%s: Poll for buf write ready timeout\r\n",
							__func__);
#endif
		goto Out;
	}
	/*
	 * Clear Buffer Write Ready Interrupt in Interrupt Status Enable
	 * Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_INTR_STS_EN_OFFSET, 0U);

	/*
	 * Clear Buffer Write Ready Interrupt in Interrupt Status Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_INTR_STS_OFFSET,
				XNANDPSU_INTR_STS_BUFF_WR_RDY_STS_EN_MASK);
	/*
	 * Enable Transfer Complete Interrupt in Interrupt Status Enable
	 * Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			(XNANDPSU_INTR_STS_EN_OFFSET),
			XNANDPSU_INTR_STS_EN_TRANS_COMP_STS_EN_MASK);
	/*
	 * Write Data to Data Port Register
	 */
	for (Index = 0U; Index < (PktSize/4U); Index++) {
		XNandPsu_WriteReg(InstancePtr->Config.BaseAddress,
					XNANDPSU_BUF_DATA_PORT_OFFSET,
					BufPtr[Index]);
	}
	/*
	 * Poll for Transfer Complete event
	 */
	Status = XNandPsu_PollRegTimeout(
			InstancePtr,
			XNANDPSU_INTR_STS_OFFSET,
			XNANDPSU_INTR_STS_TRANS_COMP_STS_EN_MASK,
			XNANDPSU_INTR_POLL_TIMEOUT);
	if (Status != XST_SUCCESS) {
#ifdef XNANDPSU_DEBUG
		xil_printf("%s: Poll for xfer complete timeout\r\n",
							__func__);
#endif
		goto Out;
	}
	/*
	 * Clear Transfer Complete Interrupt in Interrupt Status Enable
	 * Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_INTR_STS_EN_OFFSET, 0U);

	/*
	 * Clear Transfer Complete Interrupt in Interrupt Status Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_INTR_STS_OFFSET,
				XNANDPSU_INTR_STS_TRANS_COMP_STS_EN_MASK);

Out:
	return Status;
}

/*****************************************************************************/
/**
*
* This function changes clock frequency of flash controller.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
* @param	ClockFreq is the clock frequency to change.
*
* @return
*		None
*
* @note		None
*
******************************************************************************/
static void XNandPsu_ChangeClockFreq(XNandPsu *InstancePtr, u32 ClockFreq)
{
	/*
	 * Not implemented
	 */
}
/*****************************************************************************/
/**
*
* This function changes the data interface and timing mode.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
* @param	NewIntf is the new data interface.
* @param	NewMode is the new timing mode.
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_FAILURE if failed.
*
* @note		None
*
******************************************************************************/
s32 XNandPsu_ChangeTimingMode(XNandPsu *InstancePtr,
				XNandPsu_DataInterface NewIntf,
				XNandPsu_TimingMode NewMode)
{
	s32 Status;
	u32 Target;
	u32 Index;
	u32 Found = 0U;
	u32 RegVal;
	u8 Buf[4] = {0U};
	u32 *Feature = (u32 *)(void *)&Buf[0];
	u32 SetFeature = 0U;
	u32 NewModeVar = NewMode;

	/*
	 * Assert the input arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Check for valid input arguments
	 */
	if((NewIntf != XNANDPSU_SDR && NewIntf != XNANDPSU_NVDDR) ||
			(NewModeVar > 5U)){
		Status = XST_FAILURE;
		goto Out;
	}

	if(NewIntf == XNANDPSU_NVDDR){
		NewModeVar = NewModeVar | 0x10U;
	}
	/*
	 * Get current data interface type and timing mode
	 */
	XNandPsu_DataInterface CurIntf = InstancePtr->DataInterface;
	XNandPsu_TimingMode CurMode = InstancePtr->TimingMode;

	/*
	 * Check if the flash is in same mode
	 */
	if ((CurIntf == NewIntf) && (CurMode == NewModeVar)) {
		Status = XST_SUCCESS;
		goto Out;
	}

	if ((CurIntf == XNANDPSU_NVDDR) && (NewIntf == XNANDPSU_SDR)) {

		NewModeVar = XNANDPSU_SDR0;

		/*
		 * Change the clock frequency
		 */
		XNandPsu_ChangeClockFreq(InstancePtr, XNANDPSU_SDR_CLK);

		/*
		 * Update Data Interface Register
		 */
		RegVal = ((NewModeVar % 6U) << ((NewIntf == XNANDPSU_NVDDR) ? 3U : 0U)) |
				((u32)NewIntf << XNANDPSU_DATA_INTF_DATA_INTF_SHIFT);
		XNandPsu_WriteReg(InstancePtr->Config.BaseAddress,
					XNANDPSU_DATA_INTF_OFFSET, RegVal);

		for (Target = 0U; Target < InstancePtr->Geometry.NumTargets;
							Target++) {
			Status = XNandPsu_OnfiReset(InstancePtr, Target);
			if (Status != XST_SUCCESS) {
				goto Out;
			}
		}

		/*
		 * Set Feature
		 */
		for (Target = 0U; Target < InstancePtr->Geometry.NumTargets;
								Target++) {
			Status = XNandPsu_SetFeature(InstancePtr, Target, 0x01U,
							(u8 *)&NewModeVar);
			if (Status != XST_SUCCESS) {
				goto Out;
			}
		}

		InstancePtr->DataInterface = NewIntf;
		InstancePtr->TimingMode = NewModeVar;

		for (Target = 0U; Target < InstancePtr->Geometry.NumTargets;
								Target++) {
			Status = XNandPsu_GetFeature(InstancePtr, Target, 0x01U,
								&Buf[0]);
			if (Status != XST_SUCCESS) {
				goto Out;
			}
			/*
			 * Check if set_feature was successful
			 */
			if ((u32)*Feature != (u32)NewModeVar) {
				Status = XST_FAILURE;
				goto Out;
			}
		}

		goto Out;
	}

	SetFeature = NewModeVar;
	if(CurIntf == XNANDPSU_NVDDR && NewIntf == XNANDPSU_NVDDR){
		SetFeature |= SetFeature << 8U;
	}
	/*
	 * Set Feature
	 */
	for (Target = 0U; Target < InstancePtr->Geometry.NumTargets;
							Target++) {
		Status = XNandPsu_SetFeature(InstancePtr, Target, 0x01U,
						(u8 *)&SetFeature);
		if (Status != XST_SUCCESS) {
			goto Out;
		}
	}

	InstancePtr->DataInterface = NewIntf;
	InstancePtr->TimingMode = NewModeVar;
	/*
	 * Update Data Interface Register
	 */
	RegVal = ((NewMode % 6U) << ((NewIntf == XNANDPSU_NVDDR) ? 3U : 0U)) |
			((u32)NewIntf << XNANDPSU_DATA_INTF_DATA_INTF_SHIFT);
	XNandPsu_WriteReg(InstancePtr->Config.BaseAddress,
				XNANDPSU_DATA_INTF_OFFSET, RegVal);

	/*
	 * Get Feature
	 */
	for (Target = 0U; Target < InstancePtr->Geometry.NumTargets;
							Target++) {
		Status = XNandPsu_GetFeature(InstancePtr, Target, 0x01U,
							&Buf[0]);
		if (Status != XST_SUCCESS) {
			goto Out;
		}

		/*
		 * Check if set_feature was successful
		 */
		if (*Feature != NewModeVar) {
			Status = XST_FAILURE;
			goto Out;
		}
	}

	Status = XST_SUCCESS;
Out:
	return Status;
}

/*****************************************************************************/
/**
*
* This function issues change read column and reads the data into buffer
* specified by user.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
* @param	Target is the chip select value.
* @param	Col is the coulmn address.
* @param	PktSize is the number of bytes to read.
* @param	PktCount is the number of transactions to read.
* @param	Buf is the data buffer to fill in.
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_FAILURE if failed.
*
* @note		None
*
******************************************************************************/
static s32 XNandPsu_ChangeReadColumn(XNandPsu *InstancePtr, u32 Target,
					u32 Col, u32 PktSize, u32 PktCount,
					u8 *Buf)
{
	u32 AddrCycles = InstancePtr->Geometry.ColAddrCycles;
	u32 BufRdCnt = 0U;
	u32 *BufPtr = (u32 *)(void *)Buf;
	s32 Status = XST_FAILURE;
	u32 Index;

	/*
	 * Assert the input arguments.
	 */
	Xil_AssertNonvoid(Target < XNANDPSU_MAX_TARGETS);
	Xil_AssertNonvoid(Buf != NULL);

	if (InstancePtr->DmaMode == XNANDPSU_MDMA) {
		/*
		 * Enable DMA boundary Interrupt in Interrupt Status
		 * Enable Register
		 */
		XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
				XNANDPSU_INTR_STS_EN_OFFSET,
				XNANDPSU_INTR_STS_EN_TRANS_COMP_STS_EN_MASK |
				XNANDPSU_INTR_STS_EN_DMA_INT_STS_EN_MASK);
	} else {
		/*
		 * Enable Buffer Read Ready Interrupt in Interrupt Status
		 * Enable Register
		 */
		XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
				XNANDPSU_INTR_STS_EN_OFFSET,
				XNANDPSU_INTR_STS_EN_BUFF_RD_RDY_STS_EN_MASK);
	}
	/*
	 * Program Command
	 */
	XNandPsu_Prepare_Cmd(InstancePtr, ONFI_CMD_CHNG_RD_COL1,
			ONFI_CMD_CHNG_RD_COL2, 0U , 1U, (u8)AddrCycles);
	/*
	 * Program Page Size
	 */
	XNandPsu_SetPageSize(InstancePtr);
	/*
	 * Program Column, Page, Block address
	 */
	XNandPsu_SetPageColAddr(InstancePtr, 0U, (u16)Col);
	/*
	 * Program Packet Size and Packet Count
	 */
	XNandPsu_SetPktSzCnt(InstancePtr, PktSize, PktCount);
	/*
	 * Program DMA system address and DMA buffer boundary
	 */
	if (InstancePtr->DmaMode == XNANDPSU_MDMA) {
		/*
		 * Invalidate the Data Cache
		 */
		Xil_DCacheInvalidateRange((INTPTR)Buf, (PktSize * PktCount));
#ifdef __aarch64__
		XNandPsu_WriteReg(InstancePtr->Config.BaseAddress,
				XNANDPSU_DMA_SYS_ADDR1_OFFSET,
				(u32) (((INTPTR)Buf >> 32) & 0xFFFFFFFFU));
#endif
		XNandPsu_WriteReg(InstancePtr->Config.BaseAddress,
				XNANDPSU_DMA_SYS_ADDR0_OFFSET,
				(u32) ((INTPTR)(void *)Buf & 0xFFFFFFFFU));
	}
	/*
	 * Set Bus Width
	 */
	XNandPsu_SetBusWidth(InstancePtr);
	/*
	 * Program Memory Address Register2 for chip select
	 */
	XNandPsu_SelectChip(InstancePtr, Target);
	/*
	 * Set Read command in Program Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_PROG_OFFSET,XNANDPSU_PROG_RD_MASK);

	if (InstancePtr->DmaMode == XNANDPSU_MDMA) {
		goto ReadDmaDone;
	}

	while (BufRdCnt < PktCount) {
		/*
		 * Poll for Buffer Read Ready event
		 */
		Status = XNandPsu_PollRegTimeout(
			InstancePtr,
			XNANDPSU_INTR_STS_OFFSET,
			XNANDPSU_INTR_STS_BUFF_RD_RDY_STS_EN_MASK,
			XNANDPSU_INTR_POLL_TIMEOUT);
		if (Status != XST_SUCCESS) {
#ifdef XNANDPSU_DEBUG
			xil_printf("%s: Poll for buf read ready timeout\r\n",
							__func__);
#endif
			goto Out;
		}
		/*
		 * Increment Buffer Read Interrupt Count
		 */
		BufRdCnt++;

		if (BufRdCnt == PktCount) {
			/*
			 * Enable Transfer Complete Interrupt in Interrupt
			 * Status Enable Register
			 */
			XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
				XNANDPSU_INTR_STS_EN_OFFSET,
				XNANDPSU_INTR_STS_EN_TRANS_COMP_STS_EN_MASK);
		} else {
			/*
			 * Clear Buffer Read Ready Interrupt in Interrupt
			 * Status Enable Register
			 */
			XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
				XNANDPSU_INTR_STS_EN_OFFSET, 0U);

		}
		/*
		 * Clear Buffer Read Ready Interrupt in Interrupt Status
		 * Register
		 */
		XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
				XNANDPSU_INTR_STS_OFFSET,
				XNANDPSU_INTR_STS_BUFF_RD_RDY_STS_EN_MASK);
		/*
		 * Read Packet Data from Data Port Register
		 */
		for (Index = 0U; Index < (PktSize/4); Index++) {
			BufPtr[Index] = XNandPsu_ReadReg(
						InstancePtr->Config.BaseAddress,
						XNANDPSU_BUF_DATA_PORT_OFFSET);
		}
		BufPtr += (PktSize/4U);

		if (BufRdCnt < PktCount) {
			/*
			 * Enable Buffer Read Ready Interrupt in Interrupt
			 * Status Enable Register
			 */
			XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
				XNANDPSU_INTR_STS_EN_OFFSET,
				XNANDPSU_INTR_STS_EN_BUFF_RD_RDY_STS_EN_MASK);
		} else {
			break;
		}
	}
ReadDmaDone:
	/*
	 * Poll for Transfer Complete event
	 */
	Status = XNandPsu_PollRegTimeout(
			InstancePtr,
			XNANDPSU_INTR_STS_OFFSET,
			XNANDPSU_INTR_STS_TRANS_COMP_STS_EN_MASK,
			XNANDPSU_INTR_POLL_TIMEOUT);
	if (Status != XST_SUCCESS) {
#ifdef XNANDPSU_DEBUG
		xil_printf("%s: Poll for xfer complete timeout\r\n",
							__func__);
#endif
		goto Out;
	}
	/*
	 * Clear Transfer Complete Interrupt in Interrupt Status Enable
	 * Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
		XNANDPSU_INTR_STS_EN_OFFSET, 0U);

	/*
	 * Clear Transfer Complete Interrupt in Interrupt Status Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
				XNANDPSU_INTR_STS_OFFSET,
				XNANDPSU_INTR_STS_TRANS_COMP_STS_EN_MASK);
Out:
	return Status;
}

/*****************************************************************************/
/**
*
* This function issues change read column and reads the data into buffer
* specified by user.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
* @param	Target is the chip select value.
* @param	Col is the coulmn address.
* @param	PktSize is the number of bytes to read.
* @param	PktCount is the number of transactions to read.
* @param	Buf is the data buffer to fill in.
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_FAILURE if failed.
*
* @note		None
*
******************************************************************************/
static s32 XNandPsu_ChangeWriteColumn(XNandPsu *InstancePtr, u32 Target,
					u32 Col, u32 PktSize, u32 PktCount,
					u8 *Buf)
{
	u32 AddrCycles = InstancePtr->Geometry.ColAddrCycles;
	u32 BufWrCnt = 0U;
	u32 *BufPtr = (u32 *)(void *)Buf;
	s32 Status = XST_FAILURE;
	OnfiCmdFormat OnfiCommand;
	u32 Index;

	/*
	 * Assert the input arguments.
	 */
	Xil_AssertNonvoid(Target < XNANDPSU_MAX_TARGETS);
	Xil_AssertNonvoid(Buf != NULL);

	if (PktCount == 0U) {
		return XST_SUCCESS;
	}

	if (InstancePtr->DmaMode == XNANDPSU_MDMA) {
		/*
		 * Enable DMA boundary Interrupt in Interrupt Status
		 * Enable Register
		 */
		XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
				XNANDPSU_INTR_STS_EN_OFFSET,
				XNANDPSU_INTR_STS_EN_TRANS_COMP_STS_EN_MASK |
				XNANDPSU_INTR_STS_EN_DMA_INT_STS_EN_MASK);
	} else {
		/*
		 * Enable Buffer Write Ready Interrupt in Interrupt Status
		 * Enable Register
		 */
		XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
				XNANDPSU_INTR_STS_EN_OFFSET,
				XNANDPSU_INTR_STS_EN_BUFF_WR_RDY_STS_EN_MASK);
	}
	/*
	 * Change write column hack
	 */
	OnfiCommand.Command1 = 0x85U;
	OnfiCommand.Command2 = 0x10U;
	XNandPsu_Prepare_Cmd(InstancePtr, OnfiCommand.Command1,
				OnfiCommand.Command2, 0U , 0U, (u8)AddrCycles);

	/*
	 * Program Page Size
	 */
	XNandPsu_SetPageSize(InstancePtr);
	/*
	 * Program Column, Page, Block address
	 */
	XNandPsu_SetPageColAddr(InstancePtr, 0U, (u16)Col);
	/*
	 * Program Packet Size and Packet Count
	 */
	XNandPsu_SetPktSzCnt(InstancePtr, PktSize, PktCount);
	/*
	 * Program DMA system address and DMA buffer boundary
	 */
	if (InstancePtr->DmaMode == XNANDPSU_MDMA) {
#ifdef __aarch64__
		XNandPsu_WriteReg(InstancePtr->Config.BaseAddress,
				XNANDPSU_DMA_SYS_ADDR1_OFFSET,
				(u32) (((INTPTR)Buf >> 32U) & 0xFFFFFFFFU));
#endif
		XNandPsu_WriteReg(InstancePtr->Config.BaseAddress,
				XNANDPSU_DMA_SYS_ADDR0_OFFSET,
				(u32) ((INTPTR)(void *)Buf & 0xFFFFFFFFU));
	}
	/*
	 * Set Bus Width
	 */
	XNandPsu_SetBusWidth(InstancePtr);
	/*
	 * Program Memory Address Register2 for chip select
	 */
	XNandPsu_SelectChip(InstancePtr, Target);
	/*
	 * Set Page Program in Program Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
		XNANDPSU_PROG_OFFSET,XNANDPSU_PROG_CHNG_ROW_ADDR_END_MASK);

	if (InstancePtr->DmaMode == XNANDPSU_MDMA) {
		goto WriteDmaDone;
	}

	while (BufWrCnt < PktCount) {
		/*
		 * Poll for Buffer Write Ready event
		 */
		Status = XNandPsu_PollRegTimeout(
			InstancePtr,
			XNANDPSU_INTR_STS_OFFSET,
			XNANDPSU_INTR_STS_BUFF_WR_RDY_STS_EN_MASK,
			XNANDPSU_INTR_POLL_TIMEOUT);
		if (Status != XST_SUCCESS) {
#ifdef XNANDPSU_DEBUG
			xil_printf("%s: Poll for buf write ready timeout\r\n",
							__func__);
#endif
			goto Out;
		}
		/*
		 * Increment Buffer Write Interrupt Count
		 */
		BufWrCnt++;

		if (BufWrCnt == PktCount) {
			/*
			 * Enable Transfer Complete Interrupt in Interrupt
			 * Status Enable Register
			 */
			XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
				XNANDPSU_INTR_STS_EN_OFFSET,
				XNANDPSU_INTR_STS_EN_TRANS_COMP_STS_EN_MASK);
		} else {
			/*
			 * Clear Buffer Write Ready Interrupt in Interrupt
			 * Status Enable Register
			 */
			XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
				XNANDPSU_INTR_STS_EN_OFFSET, 0U);
		}
		/*
		 * Clear Buffer Write Ready Interrupt in Interrupt Status
		 * Register
		 */
		XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
				XNANDPSU_INTR_STS_OFFSET,
				XNANDPSU_INTR_STS_BUFF_WR_RDY_STS_EN_MASK);
		/*
		 * Write Packet Data to Data Port Register
		 */
		for (Index = 0U; Index < (PktSize/4U); Index++) {
			XNandPsu_WriteReg(InstancePtr->Config.BaseAddress,
						XNANDPSU_BUF_DATA_PORT_OFFSET,
						BufPtr[Index]);
		}
		BufPtr += (PktSize/4U);

		if (BufWrCnt < PktCount) {
			/*
			 * Enable Buffer Write Ready Interrupt in Interrupt
			 * Status Enable Register
			 */
			XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
				XNANDPSU_INTR_STS_EN_OFFSET,
				XNANDPSU_INTR_STS_EN_BUFF_WR_RDY_STS_EN_MASK);
		} else {
			break;
		}
	}
WriteDmaDone:
	/*
	 * Poll for Transfer Complete event
	 */
	Status = XNandPsu_PollRegTimeout(
			InstancePtr,
			XNANDPSU_INTR_STS_OFFSET,
			XNANDPSU_INTR_STS_TRANS_COMP_STS_EN_MASK,
			XNANDPSU_INTR_POLL_TIMEOUT);
	if (Status != XST_SUCCESS) {
#ifdef XNANDPSU_DEBUG
		xil_printf("%s: Poll for xfer complete timeout\r\n",
							__func__);
#endif
		goto Out;
	}
	/*
	 * Clear Transfer Complete Interrupt in Interrupt Status Enable
	 * Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
		XNANDPSU_INTR_STS_EN_OFFSET, 0U);

	/*
	 * Clear Transfer Complete Interrupt in Interrupt Status Register
	 */
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
		XNANDPSU_INTR_STS_OFFSET,
			XNANDPSU_INTR_STS_TRANS_COMP_STS_EN_MASK);

Out:
	return Status;
}

/*****************************************************************************/
/**
*
* This function initializes extended parameter page ECC information.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
* @param	ExtPrm is the Extended parameter page buffer.
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_FAILURE if failed.
*
* @note		None
*
******************************************************************************/
static s32 XNandPsu_InitExtEcc(XNandPsu *InstancePtr, OnfiExtPrmPage *ExtPrm)
{
	s32 Status = XST_FAILURE;
	u32 Index;
	u32 SectionType;
	u32 SectionLen;
	u32 Offset = 0U;
	u32 Found = 0U;
	OnfiExtEccBlock *EccBlock;

	if (ExtPrm->Section0Type != 0x2U) {
		Offset += (u32)ExtPrm->Section0Len;
		if (ExtPrm->Section1Type != 0x2U) {
#ifdef XNANDPSU_DEBUG
		xil_printf("%s: Extended ECC section not found\r\n",__func__);
#endif
			Status = XST_FAILURE;
		} else {
			Found = 1U;
		}
	} else {
		Found = 1U;
	}

	if (Found != 0U) {
		EccBlock = (OnfiExtEccBlock *)&ExtPrm->SectionData[Offset];
		Xil_AssertNonvoid(EccBlock != NULL);
		if (EccBlock->CodeWordSize == 0U) {
			Status = XST_FAILURE;
		} else {
			InstancePtr->Geometry.NumBitsECC =
						EccBlock->NumBitsEcc;
			InstancePtr->Geometry.EccCodeWordSize =
						(u32)EccBlock->CodeWordSize;
			Status = XST_SUCCESS;
		}
	}
	return Status;
}

/*****************************************************************************/
/**
*
* This function prepares command to be written into command register.
*
* @param	InstancePtr is a pointer to the XNandPsu instance.
* @param	Cmd1 is the first Onfi Command.
* @param	Cmd1 is the second Onfi Command.
* @param	EccState is the flag to set Ecc State.
* @param	DmaMode is the flag to set DMA mode.
*
* @return
*		None
*
* @note		None
*
******************************************************************************/
void XNandPsu_Prepare_Cmd(XNandPsu *InstancePtr, u8 Cmd1, u8 Cmd2, u8 EccState,
			u8 DmaMode, u8 AddrCycles)
{
	u32 RegValue = 0U;

	Xil_AssertVoid(InstancePtr != NULL);

	RegValue = (u32)Cmd1 | (((u32)Cmd2 << (u32)XNANDPSU_CMD_CMD2_SHIFT) &
			(u32)XNANDPSU_CMD_CMD2_MASK);

	if ((EccState != 0U) && (InstancePtr->EccMode == XNANDPSU_HWECC)) {
		RegValue |= 1U << XNANDPSU_CMD_ECC_ON_SHIFT;
	}

	if ((DmaMode != 0U) && (InstancePtr->DmaMode == XNANDPSU_MDMA)) {
		RegValue |= XNANDPSU_MDMA << XNANDPSU_CMD_DMA_EN_SHIFT;
	}

	if (AddrCycles != 0U) {
		RegValue |= (u32)AddrCycles <<
				(u32)XNANDPSU_CMD_ADDR_CYCLES_SHIFT;
	}

	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,
			XNANDPSU_CMD_OFFSET, RegValue);
}
