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
* @file xsdps.h
* @addtogroup sdps_v2_5
* @{
* @details
*
* This file contains the implementation of XSdPs driver.
* This driver is used initialize read from and write to the SD card.
* Features such as switching bus width to 4-bit and switching to high speed,
* changing clock frequency, block size etc. are supported.
* SD 2.0 uses 1/4 bus width and speeds of 25/50KHz. Initialization, however
* is done using 1-bit bus width and 400KHz clock frequency.
* SD commands are classified as broadcast and addressed. Commands can be
* those with response only (using only command line) or
* response + data (using command and data lines).
* Only one command can be sent at a time. During a data transfer however,
* when dsta lines are in use, certain commands (which use only the command
* line) can be sent, most often to obtain status.
* This driver does not support multi card slots at present.
*
* Intialization:
* This includes initialization on the host controller side to select
* clock frequency, bus power and default transfer related parameters.
* The default voltage is 3.3V.
* On the SD card side, the initialization and identification state diagram is
* implemented. This resets the card, gives it a unique address/ID and
* identifies key card related specifications.
*
* Data transfer:
* The SD card is put in tranfer state to read from or write to it.
* The default block size is 512 bytes and if supported,
* default bus width is 4-bit and bus speed is High speed.
* The read and write functions are implemented in polled mode using ADMA2.
*
* At any point, when key parameters such as block size or
* clock/speed or bus width are modified, this driver takes care of
* maintaining the same selection on host and card.
* All error bits in host controller are monitored by the driver and in the
* event one of them is set, driver will clear the interrupt status and
* communicate failure to the upper layer.
*
* File system use:
* This driver can be used with xilffs library to read and write files to SD.
* (Please refer to procedure in diskio.c). The file system read/write example
* in polled mode can used for reference.
*
* There is no example for using SD driver without file system at present.
* However, the driver can be used without the file system. The glue layer
* in filesytem can be used as reference for the same. The block count
* passed to the read/write function in one call is limited by the ADMA2
* descriptor table and hence care will have to be taken to call read/write
* API's in a loop for large file sizes.
*
* Interrupt mode is not supported because it offers no improvement when used
* with file system.
*
* eMMC support:
* SD driver supports SD and eMMC based on the "enable MMC" parameter in SDK.
* The features of eMMC supported by the driver will depend on those supported
* by the host controller. The current driver supports read/write on eMMC card
* using 4-bit and high speed mode currently.
*
* Features not supported include - card write protect, password setting,
* lock/unlock, interrupts, SDMA mode, programmed I/O mode and
* 64-bit addressed ADMA2, erase/pre-erase commands.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date     Changes
* ----- ---    -------- -----------------------------------------------
* 1.00a hk/sg  10/17/13 Initial release
* 2.0   hk      03/07/14 Version number revised.
* 2.1   hk     04/18/14 Increase sleep for eMMC switch command.
*                       Add sleep for microblaze designs. CR# 781117.
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
* 2.5 	sg		07/09/15 Added SD 3.0 features
*       kvn     07/15/15 Modified the code according to MISRAC-2012.
* 2.6   sk     10/12/15 Added support for SD card v1.0 CR# 840601.
* 2.7   sk     11/24/15 Considered the slot type befoe checking CD/WP pins.
*       sk     12/10/15 Added support for MMC cards.
*              01/08/16 Added workaround for issue in auto tuning mode
*                       of SDR50, SDR104 and HS200.
*       sk     02/16/16 Corrected the Tuning logic.
*       sk     03/01/16 Removed Bus Width check for eMMC. CR# 938311.
* 2.8   sk     04/20/16 Added new workaround for auto tuning.
*              05/03/16 Standard Speed for SD to 19MHz in ZynqMPSoC. CR#951024
* 3.0   sk     06/09/16 Added support for mkfs to calculate sector count.
*       sk     07/16/16 Added support for UHS modes.
*       sk     07/07/16 Used usleep API for both arm and microblaze.
*       sk     07/16/16 Added Tap delays accordingly to different SD/eMMC
*                       operating modes.
*       sk     08/13/16 Removed sleep.h from xsdps.h as a temporary fix for
*                       CR#956899.
* 3.1   mi     09/07/16 Removed compilation warnings with extra compiler flags.
*       sk     10/13/16 Reduced the delay during power cycle to 1ms as per spec
*       sk     10/19/16 Used emmc_hwreset pin to reset eMMC.
*       sk     11/07/16 Enable Rst_n bit in ext_csd reg if not enabled.
*       sk     11/16/16 Issue DLL reset at 31 iteration to load new zero value.
*
* </pre>
*
******************************************************************************/


#ifndef SDPS_H_
#define SDPS_H_

#ifdef __cplusplus
extern "C" {
#endif

#include "xil_printf.h"
#include "xil_cache.h"
#include "xstatus.h"
#include "xsdps_hw.h"
#include <string.h>

/************************** Constant Definitions *****************************/

#define XSDPS_CT_ERROR	0x2U	/**< Command timeout flag */
#define MAX_TUNING_COUNT	40U		/**< Maximum Tuning count */

/**************************** Type Definitions *******************************/

typedef void (*XSdPs_ConfigTap) (u32 Bank, u32 DeviceId, u32 CardType);

/**
 * This typedef contains configuration information for the device.
 */
typedef struct {
	u16 DeviceId;			/**< Unique ID  of device */
	u32 BaseAddress;		/**< Base address of the device */
	u32 InputClockHz;		/**< Input clock frequency */
	u32 CardDetect;			/**< Card Detect */
	u32 WriteProtect;			/**< Write Protect */
	u32 BusWidth;			/**< Bus Width */
	u32 BankNumber;			/**< MIO Bank selection for SD */
	u32 HasEMIO;			/**< If SD is connected to EMIO */
} XSdPs_Config;

/* ADMA2 descriptor table */
typedef struct {
	u16 Attribute;		/**< Attributes of descriptor */
	u16 Length;		/**< Length of current dma transfer */
	u32 Address;		/**< Address of current dma transfer */
} XSdPs_Adma2Descriptor;

/**
 * The XSdPs driver instance data. The user is required to allocate a
 * variable of this type for every SD device in the system. A pointer
 * to a variable of this type is then passed to the driver API functions.
 */
typedef struct {
	XSdPs_Config Config;	/**< Configuration structure */
	u32 IsReady;		/**< Device is initialized and ready */
	u32 Host_Caps;		/**< Capabilities of host controller */
	u32 Host_CapsExt;	/**< Extended Capabilities */
	u32 HCS;		/**< High capacity support in card */
	u8  CardType;		/**< Type of card - SD/MMC/eMMC */
	u8  Card_Version;	/**< Card version */
	u8  HC_Version;		/**< Host controller version */
	u8  BusWidth;		/**< Current operating bus width */
	u32 BusSpeed;		/**< Current operating bus speed */
	u8  Switch1v8;		/**< 1.8V Switch support */
	u32 CardID[4];		/**< Card ID Register */
	u32 RelCardAddr;	/**< Relative Card Address */
	u32 CardSpecData[4];	/**< Card Specific Data Register */
	u32 SectorCount;		/**< Sector Count */
	u32 SdCardConfig;	/**< Sd Card Configuration Register */
	u32 Mode;			/**< Bus Speed Mode */
	XSdPs_ConfigTap Config_TapDelay;	/**< Configuring the tap delays */
	/**< ADMA Descriptors */
#ifdef __ICCARM__
#pragma data_alignment = 32
	XSdPs_Adma2Descriptor Adma2_DescrTbl[32];
#pragma data_alignment = 4
#else
	XSdPs_Adma2Descriptor Adma2_DescrTbl[32] __attribute__ ((aligned(32)));
#endif
} XSdPs;

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/
XSdPs_Config *XSdPs_LookupConfig(u16 DeviceId);
s32 XSdPs_CfgInitialize(XSdPs *InstancePtr, XSdPs_Config *ConfigPtr,
				u32 EffectiveAddr);
s32 XSdPs_SdCardInitialize(XSdPs *InstancePtr);
s32 XSdPs_ReadPolled(XSdPs *InstancePtr, u32 Arg, u32 BlkCnt, u8 *Buff);
s32 XSdPs_WritePolled(XSdPs *InstancePtr, u32 Arg, u32 BlkCnt, const u8 *Buff);
s32 XSdPs_SetBlkSize(XSdPs *InstancePtr, u16 BlkSize);
s32 XSdPs_Select_Card (XSdPs *InstancePtr);
s32 XSdPs_Change_ClkFreq(XSdPs *InstancePtr, u32 SelFreq);
s32 XSdPs_Change_BusWidth(XSdPs *InstancePtr);
s32 XSdPs_Change_BusSpeed(XSdPs *InstancePtr);
s32 XSdPs_Get_BusWidth(XSdPs *InstancePtr, u8 *SCR);
s32 XSdPs_Get_BusSpeed(XSdPs *InstancePtr, u8 *ReadBuff);
s32 XSdPs_Pullup(XSdPs *InstancePtr);
s32 XSdPs_MmcCardInitialize(XSdPs *InstancePtr);
s32 XSdPs_CardInitialize(XSdPs *InstancePtr);
s32 XSdPs_Get_Mmc_ExtCsd(XSdPs *InstancePtr, u8 *ReadBuff);
s32 XSdPs_Set_Mmc_ExtCsd(XSdPs *InstancePtr, u32 Arg);
#if defined (ARMR5) || defined (__aarch64__)
void XSdPs_Identify_UhsMode(XSdPs *InstancePtr, u8 *ReadBuff);
void XSdPs_hsd_sdr25_tapdelay(u32 Bank, u32 DeviceId, u32 CardType);
void XSdPs_sdr104_hs200_tapdelay(u32 Bank, u32 DeviceId, u32 CardType);
#endif

#ifdef __cplusplus
}
#endif

#endif /* SD_H_ */
/** @} */
