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
* @file xnandpsu.h
*
* This file implements a driver to support Arasan NAND controller
* present in Zynq Ultrascale Mp.
*
* <b>Driver Initialization</b>
*
* The function call XNandPsu_CfgInitialize() should be called by the application
* before any other function in the driver. The initialization function takes
* device specific data (like device id, instance id, and base address) and
* initializes the XNandPsu instance with the device specific data.
*
* <b>Device Geometry</b>
*
* NAND flash device is memory device and it is segmented into areas called
* Logical Unit(s) (LUN) and further in to blocks and pages. A NAND flash device
* can have multiple LUN. LUN is sequential raw of multiple blocks of the same
* size. A block is the smallest erasable unit of data within the Flash array of
* a LUN. The size of each block is based on a power of 2. There is no
* restriction on the number of blocks within the LUN. A block contains a number
* of pages. A page is the smallest addressable unit for read and program
* operations. The arrangement of LUN, blocks, and pages is referred to by this
* module as the part's geometry.
*
* The cells within the part can be programmed from a logic 1 to a logic 0
* and not the other way around. To change a cell back to a logic 1, the
* entire block containing that cell must be erased. When a block is erased
* all bytes contain the value 0xFF. The number of times a block can be
* erased is finite. Eventually the block will wear out and will no longer
* be capable of erasure. As of this writing, the typical flash block can
* be erased 100,000 or more times.
*
* The jobs done by this driver typically are:
*	- 8-bit operational mode
*	- Read, Write, and Erase operation
*
* <b>Write Operation</b>
*
* The write call can be used to write a minimum of one byte and a maximum
* entire flash. If the address offset specified to write is out of flash or if
* the number of bytes specified from the offset exceed flash boundaries
* an error is reported back to the user. The write is blocking in nature in that
* the control is returned back to user only after the write operation is
* completed successfully or an error is reported.
*
* <b>Read Operation</b>
*
* The read call can be used to read a minimum of one byte and maximum of
* entire flash. If the address offset specified to read is out of flash or if
* the number of bytes specified from the offset exceed flash boundaries
* an error is reported back to the user. The read is blocking in nature in that
* the control is returned back to user only after the read operation is
* completed successfully or an error is reported.
*
* <b>Erase Operation</b>
*
* The erase operations are provided to erase a Block in the Flash memory. The
* erase call is blocking in nature in that the control is returned back to user
* only after the erase operation is completed successfully or an error is
* reported.
*
* @note		Driver has been renamed to nandpsu after change in
*		naming convention.
*
* This driver is intended to be RTOS and processor independent. It works with
* physical addresses only. Any needs for dynamic memory management, threads,
* mutual exclusion, virtual memory, cache control, or HW write protection
* management must be satisfied by the layer above this driver.
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
* 			   Corrected the program command for Set Feature API.
*			   Modified
*			   - XNandPsu_OnfiReadStatus
*			   - XNandPsu_GetFeature
*			   - XNandPsu_SetFeature
*			   to add support for DDR mode.
*			   Changed Convention for SLC/MLC
*			   SLC --> HAMMING
*			   MLC --> BCH
*			   SlcMlc --> IsBCH
*			   Added support for writing BBT signature and version
*			   in page section by enabling XNANDPSU_BBT_NO_OOB.
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

#ifndef XNANDPSU_H		/* prevent circular inclusions */
#define XNANDPSU_H		/* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/
#include "xil_types.h"
#include <string.h>
#include "xstatus.h"
#include "xil_assert.h"
#include "xnandpsu_hw.h"
#include "xnandpsu_onfi.h"
#include "xil_cache.h"
/************************** Constant Definitions *****************************/

#define XNANDPSU_DEBUG

#define XNANDPSU_MAX_TARGETS		1U	/**< ce_n0, ce_n1 */
#define XNANDPSU_MAX_PKT_SIZE		0x7FFU	/**< Max packet size */
#define XNANDPSU_MAX_PKT_COUNT		0xFFFU	/**< Max packet count */

#define XNANDPSU_PAGE_SIZE_512		512U	/**< 512 bytes page */
#define XNANDPSU_PAGE_SIZE_2K		2048U	/**< 2K bytes page */
#define XNANDPSU_PAGE_SIZE_4K		4096U	/**< 4K bytes page */
#define XNANDPSU_PAGE_SIZE_8K		8192U	/**< 8K bytes page */
#define XNANDPSU_PAGE_SIZE_16K		16384U	/**< 16K bytes page */
#define XNANDPSU_PAGE_SIZE_1K_16BIT	1024U	/**< 16-bit 2K bytes page */
#define XNANDPSU_MAX_PAGE_SIZE		16384U	/**< Max page size supported */

#define XNANDPSU_BUS_WIDTH_8		0U	/**< 8-bit bus width */
#define XNANDPSU_BUS_WIDTH_16		1U	/**< 16-bit bus width */

#define XNANDPSU_HAMMING		0x1U	/**< Hamming Flash */
#define XNANDPSU_BCH			0x2U	/**< BCH Flash */

#define XNANDPSU_MAX_BLOCKS		32768U	/**< Max number of Blocks */
#define XNANDPSU_MAX_SPARE_SIZE		0x800U	/**< Max spare bytes of a NAND
						  flash page of 16K */

#define XNANDPSU_INTR_POLL_TIMEOUT	10000U

#define XNANDPSU_SDR_CLK		((u16)100U * (u16)1000U * (u16)1000U)
#define XNANDPSU_NVDDR_CLK_0		((u16)20U * (u16)1000U * (u16)1000U)
#define XNANDPSU_NVDDR_CLK_1		((u16)33U * (u16)1000U * (u16)1000U)
#define XNANDPSU_NVDDR_CLK_2		((u16)50U * (u16)1000U * (u16)1000U)
#define XNANDPSU_NVDDR_CLK_3		((u16)66U * (u16)1000U * (u16)1000U)
#define XNANDPSU_NVDDR_CLK_4		((u16)83U * (u16)1000U * (u16)1000U)
#define XNANDPSU_NVDDR_CLK_5		((u16)100U * (u16)1000U * (u16)1000U)

/**
 * The XNandPsu_Config structure contains configuration information for NAND
 * controller.
 */
typedef struct {
	u16 DeviceId;		/**< Instance ID of NAND flash controller */
	u32 BaseAddress;	/**< Base address of NAND flash controller */
} XNandPsu_Config;

/**
 * The XNandPsu_DataInterface enum contains flash operating mode.
 */
typedef enum {
	XNANDPSU_SDR = 0U,		/**< Single Data Rate */
	XNANDPSU_NVDDR			/**< Double Data Rate */
} XNandPsu_DataInterface;

/**
 * XNandPsu_TimingMode enum contains timing modes.
 */
typedef enum {
	XNANDPSU_SDR0 = 0U,
	XNANDPSU_SDR1,
	XNANDPSU_SDR2,
	XNANDPSU_SDR3,
	XNANDPSU_SDR4,
	XNANDPSU_SDR5,
	XNANDPSU_NVDDR0,
	XNANDPSU_NVDDR1,
	XNANDPSU_NVDDR2,
	XNANDPSU_NVDDR3,
	XNANDPSU_NVDDR4,
	XNANDPSU_NVDDR5
} XNandPsu_TimingMode;

/**
 * The XNandPsu_SWMode enum contains the driver operating mode.
 */
typedef enum {
	XNANDPSU_POLLING = 0,		/**< Polling */
	XNANDPSU_INTERRUPT		/**< Interrupt */
} XNandPsu_SWMode;

/**
 * The XNandPsu_DmaMode enum contains the controller MDMA mode.
 */
typedef enum {
	XNANDPSU_PIO = 0,		/**< PIO Mode */
	XNANDPSU_SDMA,			/**< SDMA Mode */
	XNANDPSU_MDMA			/**< MDMA Mode */
} XNandPsu_DmaMode;

/**
 * The XNandPsu_EccMode enum contains ECC functionality.
 */
typedef enum {
	XNANDPSU_NONE = 0,
	XNANDPSU_HWECC,
	XNANDPSU_EZNAND,
	XNANDPSU_ONDIE
} XNandPsu_EccMode;

/**
 * The XNandPsu_BbtOption enum contains the BBT storage option.
 */
typedef enum {
	XNANDPSU_BBT_OOB = 0,		/**< OOB area */
	XNANDPSU_BBT_NO_OOB,		/**< No OOB i.e page area */
} XNandPsu_BbtOption;

/**
 * Bad block table descriptor
 */
typedef struct {
	u32 PageOffset[XNANDPSU_MAX_TARGETS];
				/**< Page offset where BBT resides */
	u32 SigOffset;		/**< Signature offset in Spare area */
	u32 VerOffset;		/**< Offset of BBT version */
	u32 SigLength;		/**< Length of the signature */
	u32 MaxBlocks;		/**< Max blocks to search for BBT */
	char Signature[4];	/**< BBT signature */
	u8 Version[XNANDPSU_MAX_TARGETS];
				/**< BBT version */
	u32 Valid;		/**< BBT descriptor is valid or not */
	XNandPsu_BbtOption Option;	/**< BBT Oob option enabled/disabled */
} XNandPsu_BbtDesc;

/**
 * Bad block pattern
 */
typedef struct {
	u32 Options;		/**< Options to search the bad block pattern */
	u32 Offset;		/**< Offset to search for specified pattern */
	u32 Length;		/**< Number of bytes to check the pattern */
	u8 Pattern[2];		/**< Pattern format to search for */
} XNandPsu_BadBlockPattern;

/**
 * The XNandPsu_Geometry structure contains the ONFI geometry information.
 */
typedef struct {
	/*
	 * Parameter page information
	 */
	u32 BytesPerPage;	/**< Number of bytes per page */
	u16 SpareBytesPerPage;	/**< Number of spare bytes per page */
	u32 PagesPerBlock;	/**< Number of pages per block */
	u32 BlocksPerLun;	/**< Number of blocks per LUN */
	u8 NumLuns;		/**< Number of LUN's */
	u8 RowAddrCycles;	/**< Row address cycles */
	u8 ColAddrCycles;	/**< Column address cycles */
	u8 NumBitsPerCell;	/**< Number of bits per cell (Hamming/BCH) */
	u8 NumBitsECC;		/**< Number of bits ECC correctability */
	u32 EccCodeWordSize;	/**< ECC codeword size */
	/*
	 * Driver specific information
	 */
	u32 BlockSize;		/**< Block size */
	u32 NumTargetPages;	/**< Total number of pages in a Target */
	u32 NumTargetBlocks;	/**< Total number of blocks in a Target */
	u64 TargetSize;		/**< Target size in bytes */
	u8 NumTargets;		/**< Number of targets present */
	u32 NumPages;		/**< Total number of pages */
	u32 NumBlocks;		/**< Total number of blocks */
	u64 DeviceSize;		/**< Total flash size in bytes */
} XNandPsu_Geometry;

/**
 * The XNandPsu_Features structure contains the ONFI features information.
 */
typedef struct {
	u32 BusWidth;
	u32 NvDdr;
	u32 EzNand;
	u32 OnDie;
	u32 ExtPrmPage;
} XNandPsu_Features;

/**
 * The XNandPsu_EccMatrix structure contains ECC features information.
 */
typedef struct {
	u16 PageSize;
	u16 CodeWordSize;
	u8 NumEccBits;
	u8 IsBCH;
	u16 EccAddr;
	u16 EccSize;
} XNandPsu_EccMatrix;

/**
 * The XNandPsu_EccCfg structure contains ECC configuration.
 */
typedef struct {
	u16 EccAddr;
	u16 EccSize;
	u16 CodeWordSize;
	u8 NumEccBits;
	u8 IsBCH;
} XNandPsu_EccCfg;

/**
 * The XNandPsu structure contains the driver instance data. The user is
 * required to allocate a variable of this type for the NAND controller.
 * A pointer to a variable of this type is then passed to the driver API
 * functions.
 */
typedef struct {
	u32 IsReady;		/**< Device is initialized and ready */
	XNandPsu_Config Config;
	u16 Ecc_Stat_PerPage_flips;	/**< Ecc Correctable Error Counter for Current Page */
	u32 Ecc_Stats_total_flips;     /**< Total Ecc Errors Corrected */
	XNandPsu_DataInterface DataInterface;
	XNandPsu_TimingMode TimingMode;
	XNandPsu_SWMode Mode;		/**< Driver operating mode */
	XNandPsu_DmaMode DmaMode;	/**< MDMA mode enabled/disabled */
	XNandPsu_EccMode EccMode;	/**< ECC Mode */
	XNandPsu_EccCfg EccCfg;		/**< ECC configuration */
	XNandPsu_Geometry Geometry;	/**< Flash geometry */
	XNandPsu_Features Features;	/**< ONFI features */
	u8 PartialDataBuf[XNANDPSU_MAX_PAGE_SIZE] __attribute__ ((aligned(64)));
					/**< Partial read/write buffer */
	/* Bad block table definitions */
	XNandPsu_BbtDesc BbtDesc;	/**< Bad block table descriptor */
	XNandPsu_BbtDesc BbtMirrorDesc;	/**< Mirror BBT descriptor */
	XNandPsu_BadBlockPattern BbPattern;	/**< Bad block pattern to
						  search */
	u8 Bbt[XNANDPSU_MAX_BLOCKS >> 2];	/**< Bad block table array */
} XNandPsu;

/******************* Macro Definitions (Inline Functions) *******************/

/*****************************************************************************/
/**
 * This macro sets the bitmask in the register.
 *
 * @param	InstancePtr is a pointer to the XNandPsu instance of the
 *		controller.
 * @param	RegOffset is the register offset.
 * @param	BitMask is the bitmask.
 *
 * @note	C-style signature:
 *		void XNandPsu_SetBits(XNandPsu *InstancePtr, u32 RegOffset,
 *							u32 BitMask)
 *
 *****************************************************************************/
#define XNandPsu_SetBits(InstancePtr, RegOffset, BitMask)		\
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,		\
		(RegOffset),						\
	((u32)(XNandPsu_ReadReg((InstancePtr)->Config.BaseAddress,	\
		(RegOffset)) | (BitMask))))

/*****************************************************************************/
/**
 * This macro clears the bitmask in the register.
 *
 * @param	InstancePtr is a pointer to the XNandPsu instance of the
 *		controller.
 * @param	RegOffset is the register offset.
 * @param	BitMask is the bitmask.
 *
 * @note	C-style signature:
 *		void XNandPsu_ClrBits(XNandPsu *InstancePtr, u32 RegOffset,
 *							u32 BitMask)
 *
 *****************************************************************************/
#define XNandPsu_ClrBits(InstancePtr, RegOffset, BitMask)		\
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,		\
		(RegOffset),						\
	((u32)(XNandPsu_ReadReg((InstancePtr)->Config.BaseAddress,	\
		(RegOffset)) & ~(BitMask))))

/*****************************************************************************/
/**
 * This macro clears and updates the bitmask in the register.
 *
 * @param	InstancePtr is a pointer to the XNandPsu instance of the
 *		controller.
 * @param	RegOffset is the register offset.
 * @param	Mask is the bitmask.
 * @param	Value is the register value to write.
 *
 * @note	C-style signature:
 *		void XNandPsu_ReadModifyWrite(XNandPsu *InstancePtr,
 *					u32 RegOffset, u32 Mask, u32 Val)
 *
 *****************************************************************************/
#define XNandPsu_ReadModifyWrite(InstancePtr, RegOffset, Mask, Value)	\
	XNandPsu_WriteReg((InstancePtr)->Config.BaseAddress,		\
		(RegOffset),						\
	((u32)((u32)(XNandPsu_ReadReg((InstancePtr)->Config.BaseAddress,\
		(u32)(RegOffset)) & (u32)(~(Mask))) | (u32)(Value))))

/*****************************************************************************/
/**
 * This macro enables bitmask in Interrupt Signal Enable register.
 *
 * @param	InstancePtr is a pointer to the XNandPsu instance of the
 *		controller.
 * @param	Mask is the bitmask.
 *
 * @note	C-style signature:
 *		void XNandPsu_IntrSigEnable(XNandPsu *InstancePtr, u32 Mask)
 *
 *****************************************************************************/
#define XNandPsu_IntrSigEnable(InstancePtr, Mask)			\
		XNandPsu_SetBits((InstancePtr),				\
			XNANDPSU_INTR_SIG_EN_OFFSET,			\
			(Mask))

/*****************************************************************************/
/**
 * This macro clears bitmask in Interrupt Signal Enable register.
 *
 * @param	InstancePtr is a pointer to the XNandPsu instance of the
 *		controller.
 * @param	Mask is the bitmask.
 *
 * @note	C-style signature:
 *		void XNandPsu_IntrSigClear(XNandPsu *InstancePtr, u32 Mask)
 *
 *****************************************************************************/
#define XNandPsu_IntrSigClear(InstancePtr, Mask)			\
		XNandPsu_ClrBits((InstancePtr),				\
			XNANDPSU_INTR_SIG_EN_OFFSET,			\
			(Mask))

/*****************************************************************************/
/**
 * This macro enables bitmask in Interrupt Status Enable register.
 *
 * @param	InstancePtr is a pointer to the XNandPsu instance of the
 *		controller.
 * @param	Mask is the bitmask.
 *
 * @note	C-style signature:
 *		void XNandPsu_IntrStsEnable(XNandPsu *InstancePtr, u32 Mask)
 *
 *****************************************************************************/
#define XNandPsu_IntrStsEnable(InstancePtr, Mask)			\
		XNandPsu_SetBits((InstancePtr),				\
			XNANDPSU_INTR_STS_EN_OFFSET,			\
			(Mask))

/*****************************************************************************/
/**
 * This macro checks for the ONFI ID.
 *
 * @param	Buff is the buffer holding ONFI ID
 *
 * @note	none.
 *
 *****************************************************************************/
#define IS_ONFI(Buff)					\
	(Buff[0] == (u8)'O') && (Buff[1] == (u8)'N') &&	\
	(Buff[2] == (u8)'F') && (Buff[3] == (u8)'I')

/************************** Function Prototypes *****************************/

s32 XNandPsu_CfgInitialize(XNandPsu *InstancePtr, XNandPsu_Config *ConfigPtr,
				u32 EffectiveAddr);

s32 XNandPsu_Erase(XNandPsu *InstancePtr, u64 Offset, u64 Length);

s32 XNandPsu_Write(XNandPsu *InstancePtr, u64 Offset, u64 Length,
							u8 *SrcBuf);

s32 XNandPsu_Read(XNandPsu *InstancePtr, u64 Offset, u64 Length,
							u8 *DestBuf);

s32 XNandPsu_EraseBlock(XNandPsu *InstancePtr, u32 Target, u32 Block);

s32 XNandPsu_WriteSpareBytes(XNandPsu *InstancePtr, u32 Page, u8 *Buf);

s32 XNandPsu_ReadSpareBytes(XNandPsu *InstancePtr, u32 Page, u8 *Buf);

s32 XNandPsu_ChangeTimingMode(XNandPsu *InstancePtr,
				XNandPsu_DataInterface NewIntf,
				XNandPsu_TimingMode NewMode);

s32 XNandPsu_GetFeature(XNandPsu *InstancePtr, u32 Target, u8 Feature,
								u8 *Buf);

s32 XNandPsu_SetFeature(XNandPsu *InstancePtr, u32 Target, u8 Feature,
								u8 *Buf);

s32 XNandPsu_ScanBbt(XNandPsu *InstancePtr);

s32 XNandPsu_MarkBlockBad(XNandPsu *InstancePtr, u32 Block);

void XNandPsu_EnableDmaMode(XNandPsu *InstancePtr);

void XNandPsu_DisableDmaMode(XNandPsu *InstancePtr);

void XNandPsu_EnableEccMode(XNandPsu *InstancePtr);

void XNandPsu_DisableEccMode(XNandPsu *InstancePtr);

void XNandPsu_Prepare_Cmd(XNandPsu *InstancePtr, u8 Cmd1, u8 Cmd2, u8 EccState,
			u8 DmaMode, u8 AddrCycles);

void XNandPsu_EnableBbtOobMode(XNandPsu *InstancePtr);

void XNandPsu_DisableBbtOobMode(XNandPsu *InstancePtr);
/*
 * XNandPsu_LookupConfig in xnandpsu_sinit.c
 */
XNandPsu_Config *XNandPsu_LookupConfig(u16 DeviceID);


#ifdef __cplusplus
}
#endif

#endif /* XNANDPSU_H end of protection macro */
