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
* @file xnandpsu_bbm.h
*
* This file implements the Bad Block Management(BBM) functionality. This is
* similar to the Bad Block Management which is a part of the MTD subsystem in
* Linux.  The factory marked bad blocks are scanned initially and a Bad Block
* Table(BBT) is created in the memory.  This table is also written to the flash
* so that upon reboot, the BBT is read back from the flash and loaded into the
* memory instead of scanning every time. The Bad Block Table(BBT) is written
* into one of the the last four blocks in the flash memory. The last four
* blocks are marked as Reserved so that user can't erase/program those blocks.
*
* There are two bad block tables, a primary table and a mirror table. The
* tables are versioned and incrementing version number is used to detect and
* recover from interrupted updates. Each table is stored in a separate block,
* beginning in the first page of that block. Only two blocks would be necessary
* in the absence of bad blocks within the last four; the range of four provides
* a little slack in case one or two of those blocks is bad. These blocks are
* marked as reserved and cannot be programmed by the user. A NAND Flash device
* with 3 or more factory bad blocks in the last 4 cannot be used. The bad block
* table signature is written into the spare data area of the pages containing
* bad block table so that upon rebooting the bad block table signature is
* searched and the bad block table is loaded into RAM. The signature is "Bbt0"
* for primary Bad Block Table and "1tbB" for Mirror Bad Block Table. The
* version offset follows the signature offset in the spare data area. The
* version number increments on every update to the bad block table and the
* version wraps at 0xff.
*
* Each block in the Bad Block Table(BBT) is represented by 2 bits.
* The two bits are encoded as follows in RAM BBT.
* 0'b00 -> Good Block
* 0'b01 -> Block is bad due to wear
* 0'b10 -> Reserved block
* 0'b11 -> Factory marked bad block
*
* While writing to the flash the two bits are encoded as follows.
* 0'b00 -> Factory marked bad block
* 0'b01 -> Reserved block
* 0'b10 -> Block is bad due to wear
* 0'b11 -> Good Block
*
* The user can check for the validity of the block using the API
* XNandPsu_IsBlockBad and take the action based on the return value. Also user
* can update the bad block table using XNandPsu_MarkBlockBad API.
*
* @note		None
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date        Changes
* ----- ----   ----------  -----------------------------------------------
* 1.0   nm     05/06/2014  First release
* 2.0   sb     01/12/2015  Added support for writing BBT signature and version
*			   in page section by enabling XNANDPSU_BBT_NO_OOB.
*			   Modified Bbt Signature and Version Offset value for
*			   Oob and No-Oob region.
* </pre>
*
******************************************************************************/
#ifndef XNANDPSU_BBM_H		/* prevent circular inclusions */
#define XNANDPSU_BBM_H		/* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/
#include "xnandpsu.h"

/************************** Constant Definitions *****************************/
/*
 * Block definitions for RAM based Bad Block Table (BBT)
 */
#define XNANDPSU_BLOCK_GOOD			0x0U	/**< Block is good */
#define XNANDPSU_BLOCK_BAD			0x1U	/**< Block is bad */
#define XNANDPSU_BLOCK_RESERVED			0x2U	/**< Reserved block */
#define XNANDPSU_BLOCK_FACTORY_BAD		0x3U	/**< Factory marked bad
							  block */
/*
 * Block definitions for FLASH based Bad Block Table (BBT)
 */
#define XNANDPSU_FLASH_BLOCK_GOOD		0x3U	/**< Block is good */
#define XNANDPSU_FLASH_BLOCK_BAD		0x2U	/**< Block is bad */
#define XNANDPSU_FLASH_BLOCK_RESERVED		0x1U	/**< Reserved block */
#define XNANDPSU_FLASH_BLOCK_FAC_BAD	0x0U	/**< Factory marked bad
							  block */

#define XNANDPSU_BBT_SCAN_2ND_PAGE		0x00000001U	/**< Scan the
								  second page
								  for bad block
								  information
								  */
#define XNANDPSU_BBT_DESC_PAGE_OFFSET		0U	/**< Page offset of Bad
							  Block Table Desc */
#define XNANDPSU_BBT_DESC_SIG_OFFSET		8U	/**< Bad Block Table
							  signature offset */
#define XNANDPSU_BBT_DESC_VER_OFFSET		12U	/**< Bad block Table
							  version offset */
#define XNANDPSU_NO_OOB_BBT_DESC_SIG_OFFSET	0U	/**< Bad Block Table
							  signature offset in
							  page memory */
#define XNANDPSU_NO_OOB_BBT_DESC_VER_OFFSET	4U	/**< Bad block Table
							  version offset in
							  page memory */
#define XNANDPSU_BBT_DESC_SIG_LEN		4U	/**< Bad block Table
							  signature length */
#define XNANDPSU_BBT_DESC_MAX_BLOCKS		64U	/**< Bad block Table
							  max blocks */

#define XNANDPSU_BBT_BLOCK_SHIFT		2U	/**< Block shift value
							  for a block in BBT */
#define XNANDPSU_BBT_ENTRY_NUM_BLOCKS		4U	/**< Num of blocks in
							  one BBT entry */
#define XNANDPSU_BB_PTRN_OFF_SML_PAGE	5U	/**< Bad block pattern
							  offset in a page */
#define XNANDPSU_BB_PTRN_LEN_SML_PAGE	1U	/**< Bad block pattern
							  length */
#define XNANDPSU_BB_PTRN_OFF_LARGE_PAGE	0U	/**< Bad block pattern
							  offset in a large
							  page */
#define XNANDPSU_BB_PTRN_LEN_LARGE_PAGE	2U	/**< Bad block pattern
							  length */
#define XNANDPSU_BB_PATTERN			0xFFU	/**< Bad block pattern
							  to search in a page
							  */
#define XNANDPSU_BLOCK_TYPE_MASK		0x03U	/**< Block type mask */
#define XNANDPSU_BLOCK_SHIFT_MASK		0x06U	/**< Block shift mask
							  for a Bad Block Table
							  entry byte */

#define XNANDPSU_ONDIE_SIG_OFFSET		0x4U
#define XNANDPSU_ONDIE_VER_OFFSET		0x14U

#define XNANDPSU_BBT_VERSION_LENGTH	1U
#define XNANDPSU_BBT_SIG_LENGTH		4U

#define XNANDPSU_BBT_BUF_LENGTH		((XNANDPSU_MAX_BLOCKS >> 		\
					 XNANDPSU_BBT_BLOCK_SHIFT) +	\
					(XNANDPSU_BBT_DESC_SIG_OFFSET +	\
					 XNANDPSU_BBT_SIG_LENGTH +	\
					 XNANDPSU_BBT_VERSION_LENGTH))
/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/****************************************************************************/
/**
*
* This macro returns the Block shift value corresponding to a Block.
*
* @param        Block is the block number.
*
* @return       Block shift value
*
* @note         None.
*
*****************************************************************************/
#define XNandPsu_BbtBlockShift(Block) \
			((u8)(((Block) * 2U) & XNANDPSU_BLOCK_SHIFT_MASK))

/************************** Variable Definitions *****************************/

/************************** Function Prototypes ******************************/

void XNandPsu_InitBbtDesc(XNandPsu *InstancePtr);

s32 XNandPsu_ScanBbt(XNandPsu *InstancePtr);

s32 XNandPsu_IsBlockBad(XNandPsu *InstancePtr, u32 Block);

s32 XNandPsu_MarkBlockBad(XNandPsu *InstancePtr, u32 Block);

#ifdef __cplusplus
}
#endif

#endif /* end of protection macro */
