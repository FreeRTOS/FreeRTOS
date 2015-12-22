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
* @file xnandpsu_onfi.h
*
* This file defines all the ONFI 3.1 specific commands and values.
*
* @note		None
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date	   Changes
* ----- ----   ----------  -----------------------------------------------
* 1.0   nm     05/06/2014  First release
* </pre>
*
******************************************************************************/
#ifndef XNANDPSU_ONFI_H		/* prevent circular inclusions */
#define XNANDPSU_ONFI_H		/* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/
#include "xil_types.h"

/************************** Constant Definitions *****************************/
/*
 * Standard ONFI 3.1 Commands
 */
/*
 * ONFI 3.1 Mandatory Commands
 */
#define ONFI_CMD_RD1			0x00U	/**< Read (1st cycle) */
#define ONFI_CMD_RD2			0x30U	/**< Read (2nd cycle) */
#define ONFI_CMD_CHNG_RD_COL1		0x05U	/**< Change Read Column
						  (1st cycle) */
#define ONFI_CMD_CHNG_RD_COL2		0xE0U	/**< Change Read Column
						  (2nd cycle) */
#define ONFI_CMD_BLK_ERASE1		0x60U	/**< Block Erase (1st cycle) */
#define ONFI_CMD_BLK_ERASE2		0xD0U	/**< Block Erase (2nd cycle) */
#define ONFI_CMD_RD_STS			0x70U	/**< Read Status */
#define ONFI_CMD_PG_PROG1		0x80U	/**< Page Program(1st cycle) */
#define ONFI_CMD_PG_PROG2		0x10U	/**< Page Program(2nd cycle) */
#define ONFI_CMD_CHNG_WR_COL		0x85U	/**< Change Write Column */
#define ONFI_CMD_RD_ID			0x90U	/**< Read ID */
#define ONFI_CMD_RD_PRM_PG		0xECU	/**< Read Parameter Page */
#define ONFI_CMD_RST			0xFFU	/**< Reset */
/*
 * ONFI 3.1 Optional Commands
 */
#define ONFI_CMD_MUL_RD1		0x00U	/**< Multiplane Read
						  (1st cycle) */
#define ONFI_CMD_MUL_RD2		0x32U	/**< Multiplane Read
						  (2nd cycle) */
#define ONFI_CMD_CPBK_RD1		0x00U	/**< Copyback Read
						  (1st cycle) */
#define ONFI_CMD_CPBK_RD2		0x35U	/**< Copyback Read
						  (2nd cycle) */
#define ONFI_CMD_CHNG_RD_COL_ENHCD1	0x06U	/**< Change Read Column
						  Enhanced (1st cycle) */
#define ONFI_CMD_CHNG_RD_COL_ENHCD2	0xE0U	/**< Change Read Column
						  Enhanced (2nd cycle) */
#define ONFI_CMD_RD_CACHE_RND1		0x00U	/**< Read Cache Random
						  (1st cycle) */
#define ONFI_CMD_RD_CACHE_RND2		0x31U	/**< Read Cache Random
						  (2nd cycle) */
#define ONFI_CMD_RD_CACHE_SEQ		0x31U	/**< Read Cache Sequential */
#define ONFI_CMD_RD_CACHE_END		0x3FU	/**< Read Cache End */
#define ONFI_CMD_MUL_BLK_ERASE1		0x60U	/**< Multiplane Block Erase
						  (1st cycle) */
#define ONFI_CMD_MUL_BLK_ERASE2		0xD1U	/**< Multiplane Block Erase
						  (2nd cycle) */
#define ONFI_CMD_RD_STS_ENHCD		0x78U	/**< Read Status Enhanced */
#define ONFI_CMD_BLK_ERASE_INTRLVD2	0xD1U	/**< Block Erase Interleaved
						  (2nd cycle) */
#define ONFI_CMD_MUL_PG_PROG1		0x80U	/**< Multiplane Page Program
						  (1st cycle) */
#define ONFI_CMD_MUL_PG_PROG2		0x11U	/**< Multiplane Page Program
						  (2nd cycle) */
#define ONFI_CMD_PG_CACHE_PROG1		0x80U	/**< Page Cache Program
						  (1st cycle) */
#define ONFI_CMD_PG_CACHE_PROG2		0x15U	/**< Page Cache Program
						  (2nd cycle) */
#define ONFI_CMD_CPBK_PROG1		0x85U	/**< Copyback Program
						  (1st cycle) */
#define ONFI_CMD_CPBK_PROG2		0x10U	/**< Copyback Program
						  (2nd cycle) */
#define ONFI_CMD_MUL_CPBK_PROG1		0x85U	/**< Multiplane Copyback
						  Program (1st cycle) */
#define ONFI_CMD_MUL_CPBK_PROG2		0x10U	/**< Multiplane Copyback
						  Program (2nd cycle) */
#define ONFI_CMD_SMALL_DATA_MV1		0x85U	/**< Small Data Move
						  (1st cycle) */
#define ONFI_CMD_SMALL_DATA_MV2		0x10U	/**< Small Data Move
						  (2nd cycle) */
#define ONFI_CMD_CHNG_ROW_ADDR		0x85U	/**< Change Row Address */
#define ONFI_CMD_VOL_SEL		0xE1U	/**< Volume Select */
#define ONFI_CMD_ODT_CONF		0xE2U	/**< ODT Configure */
#define ONFI_CMD_RD_UNIQID		0xEDU	/**< Read Unique ID */
#define ONFI_CMD_GET_FEATURES		0xEEU	/**< Get Features */
#define ONFI_CMD_SET_FEATURES		0xEFU	/**< Set Features */
#define ONFI_CMD_LUN_GET_FEATURES	0xD4U	/**< LUN Get Features */
#define ONFI_CMD_LUN_SET_FEATURES	0xD5U	/**< LUN Set Features */
#define ONFI_CMD_RST_LUN		0xFAU	/**< Reset LUN */
#define ONFI_CMD_SYN_RST		0xFCU	/**< Synchronous Reset */

/*
 * ONFI Status Register bit offsets
 */
#define ONFI_STS_FAIL			0x01U	/**< FAIL */
#define ONFI_STS_FAILC			0x02U	/**< FAILC */
#define ONFI_STS_CSP			0x08U	/**< CSP */
#define ONFI_STS_VSP			0x10U	/**< VSP */
#define ONFI_STS_ARDY			0x20U	/**< ARDY */
#define ONFI_STS_RDY			0x40U	/**< RDY */
#define ONFI_STS_WP			0x80U	/**< WP_n */

/*
 * ONFI constants
 */
#define ONFI_CRC_LEN			254U	/**< ONFI CRC Buf Length */
#define ONFI_PRM_PG_LEN			256U	/**< Parameter Page Length */
#define ONFI_MND_PRM_PGS		3U	/**< Number of mandatory
						  parameter pages */
#define ONFI_SIG_LEN			4U	/**< Signature Length */
#define ONFI_CMD_INVALID		0x00U	/**< Invalid Command */

#define ONFI_READ_ID_LEN		4U	/**< ONFI ID length */
#define ONFI_READ_ID_ADDR		0x20U	/**< ONFI Read ID Address */
#define ONFI_READ_ID_ADDR_CYCLES	1U	/**< ONFI Read ID Address
						  cycles */

#define ONFI_PRM_PG_ADDR_CYCLES		1U	/**< ONFI Read Parameter page
						  address cycles */

/**
 * This enum defines the ONFI 3.1 commands.
 */
enum OnfiCommandList {
	READ=0,				/**< Read */
	MULTIPLANE_READ,		/**< Multiplane Read */
	COPYBACK_READ,			/**< Copyback Read */
	CHANGE_READ_COLUMN,		/**< Change Read Column */
	CHANGE_READ_COLUMN_ENHANCED,	/**< Change Read Column Enhanced */
	READ_CACHE_RANDOM,		/**< Read Cache Random */
	READ_CACHE_SEQUENTIAL,		/**< Read Cache Sequential */
	READ_CACHE_END,			/**< Read Cache End */
	BLOCK_ERASE,			/**< Block Erase */
	MULTIPLANE_BLOCK_ERASE,		/**< Multiplane Block Erase */
	READ_STATUS,			/**< Read Status */
	READ_STATUS_ENHANCED,		/**< Read Status Enhanced */
	PAGE_PROGRAM,			/**< Page Program */
	MULTIPLANE_PAGE_PROGRAM,	/**< Multiplane Page Program */
	PAGE_CACHE_PROGRAM,		/**< Page Cache Program */
	COPYBACK_PROGRAM,		/**< Copyback Program */
	MULTIPLANE_COPYBACK_PROGRAM,	/**< Multiplance Copyback Program */
	SMALL_DATA_MOVE,		/**< Small Data Move */
	CHANGE_WRITE_COLUMN,		/**< Change Write Column */
	CHANGE_ROW_ADDR,		/**< Change Row Address */
	READ_ID,			/**< Read ID */
	VOLUME_SELECT,			/**< Volume Select */
	ODT_CONFIGURE,			/**< ODT Configure */
	READ_PARAM_PAGE,		/**< Read Parameter Page */
	READ_UNIQUE_ID,			/**< Read Unique ID */
	GET_FEATURES,			/**< Get Features */
	SET_FEATURES,			/**< Set Features */
	LUN_GET_FEATURES,		/**< LUN Get Features */
	LUN_SET_FEATURES,		/**< LUN Set Features */
	RESET_LUN,			/**< Reset LUN */
	SYN_RESET,			/**< Synchronous Reset */
	RESET,				/**< Reset */
	MAX_CMDS			/**< Dummy Command */
};

/**************************** Type Definitions *******************************/
/*
 * Parameter page structure of ONFI 3.1 specification.
 */
typedef struct {
	/*
	 * Revision information and features block
	 */
	u8 Signature[4];		/**< Parameter page signature */
	u16 Revision;			/**< Revision Number */
	u16 Features;			/**< Features supported */
	u16 OptionalCmds;		/**< Optional commands supported */
	u8 JedecJtgPrmAdvCmd;		/**< ONFI JEDEC JTG primary advanced
					  command support */
	u8 Reserved0;			/**< Reserved (11) */
	u16 ExtParamPageLen;		/**< Extended Parameter Page Length */
	u8 NumOfParamPages;		/**< Number of Parameter Pages */
	u8 Reserved1[17];		/**< Reserved (15-31) */
	/*
	 * Manufacturer information block
	 */
	u8 DeviceManufacturer[12];	/**< Device manufacturer */
	u8 DeviceModel[20];		/**< Device model */
	u8 JedecManufacturerId;		/**< JEDEC Manufacturer ID */
	u8 DateCode[2];			/**< Date code */
	u8 Reserved2[13];		/**< Reserved (67-79) */
	/*
	 * Memory organization block
	*/
	u32 BytesPerPage;		/**< Number of data bytes per page */
	u16 SpareBytesPerPage;		/**< Number of spare bytes per page */
	u32 BytesPerPartialPage;	/**< Number of data bytes per
					  partial page */
	u16 SpareBytesPerPartialPage;	/**< Number of spare bytes per
					  partial page */
	u32 PagesPerBlock;		/**< Number of pages per block */
	u32 BlocksPerLun;		/**< Number of blocks per LUN */
	u8 NumLuns;			/**< Number of LUN's */
	u8 AddrCycles;			/**< Number of address cycles */
	u8 BitsPerCell;			/**< Number of bits per cell */
	u16 MaxBadBlocksPerLun;		/**< Bad blocks maximum per LUN */
	u16 BlockEndurance;		/**< Block endurance */
	u8 GuaranteedValidBlock;	/**< Guaranteed valid blocks at
					  beginning of target */
	u16 BlockEnduranceGVB;		/**< Block endurance for guaranteed
					  valid block */
	u8 ProgramsPerPage;		/**< Number of programs per page */
	u8 PartialProgAttr;		/**< Partial programming attributes */
	u8 EccBits;			/**< Number of bits ECC
					  correctability */
	u8 PlaneAddrBits;		/**< Number of plane address bits */
	u8 PlaneOperationAttr;		/**< Multi-plane operation
					  attributes */
	u8 EzNandSupport;		/**< EZ NAND support */
	u8 Reserved3[12];		/**< Reserved (116 - 127) */
	/*
	 * Electrical parameters block
	*/
	u8 IOPinCapacitance;		/**< I/O pin capacitance, maximum */
	u16 SDRTimingMode;		/**< SDR Timing mode support */
	u16 SDRPagecacheTimingMode;	/**< SDR Program cache timing mode */
	u16 TProg;			/**< Maximum page program time */
	u16 TBers;			/**< Maximum block erase time */
	u16 TR;				/**< Maximum page read time */
	u16 TCcs;			/**< Maximum change column setup
					  time */
	u8 NVDDRTimingMode;		/**< NVDDR timing mode support */
	u8 NVDDR2TimingMode;		/**< NVDDR2 timing mode support */
	u8 SynFeatures;			/**< NVDDR/NVDDR2 features */
	u16 ClkInputPinCap;		/**< CLK input pin capacitance */
	u16 IOPinCap;			/**< I/O pin capacitance */
	u16 InputPinCap;		/**< Input pin capacitance typical */
	u8 InputPinCapMax;		/**< Input pin capacitance maximum */
	u8 DrvStrength;			/**< Driver strength support */
	u16 TMr;			/**< Maximum multi-plane read time */
	u16 TAdl;			/**< Program page register clear
					  enhancement value */
	u16 TEr;			/**< Typical page read time for
					  EZ NAND */
	u8 NVDDR2Features;		/**< NVDDR2 Features */
	u8 NVDDR2WarmupCycles;		/**< NVDDR2 Warmup Cycles */
	u8 Reserved4[4];		/**< Reserved (160 - 163) */
	/*
	 * Vendor block
	 */
	u16 VendorRevisionNum;		/**< Vendor specific revision number */
	u8 VendorSpecific[88];		/**< Vendor specific */
	u16 Crc;			/**< Integrity CRC */
}__attribute__((packed))OnfiParamPage;

/*
 * ONFI extended parameter page structure.
 */
typedef struct {
	u16 Crc;
	u8 Sig[4];
	u8 Reserved1[10];
	u8 Section0Type;
	u8 Section0Len;
	u8 Section1Type;
	u8 Section1Len;
	u8 ResSection[12];
	u8 SectionData[256];
}__attribute__((packed))OnfiExtPrmPage;

/*
 * Driver extended parameter page information.
 */
typedef struct {
	u8 NumBitsEcc;
	u8 CodeWordSize;
	u16 MaxBadBlocks;
	u16 BlockEndurance;
	u16 Reserved;
}__attribute__((packed))OnfiExtEccBlock;

typedef struct {
	u8 Command1;			/**< Command Cycle 1 */
	u8 Command2;			/**< Command Cycle 2 */
} OnfiCmdFormat;

extern const OnfiCmdFormat OnfiCmd[MAX_CMDS];

/************************** Function Prototypes ******************************/

u32 XNandPsu_OnfiParamPageCrc(u8 *ParamBuf, u32 StartOff, u32 Length);

#ifdef __cplusplus
}
#endif

#endif /* XNANDPSU_ONFI_H end of protection macro */
