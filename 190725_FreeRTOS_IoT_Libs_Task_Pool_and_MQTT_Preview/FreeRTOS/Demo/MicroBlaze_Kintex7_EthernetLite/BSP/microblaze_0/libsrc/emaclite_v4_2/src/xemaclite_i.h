/******************************************************************************
*
* Copyright (C) 2004 - 2014 Xilinx, Inc.  All rights reserved.
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
/******************************************************************************/
/**
* @file xemaclite_i.h
* @addtogroup emaclite_v4_1
* @{
*
* This header file contains internal identifiers, which are those shared
* between the files of the driver. It is intended for internal use only.
*
* NOTES:
*
* None.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.01a ecm  05/21/04 First release
* 1.11a mta  03/21/07 Updated to new coding style
* 1.13a sv   02/1/08  Added macros to Get/Set Tx/Rx status
* 3.00a ktn  10/22/09 The macros have been renamed to remove _m from the name.
*		      The macros changed in this file are
*		      XEmacLite_mGetTxActive changed to XEmacLite_GetTxActive,
*		      XEmacLite_mSetTxActive changed to XEmacLite_SetTxActive.
*
* </pre>
******************************************************************************/

#ifndef XEMACLITE_I_H		/* prevent circular inclusions */
#define XEMACLITE_I_H		/* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif


/***************************** Include Files *********************************/

#include "xemaclite.h"

/************************** Constant Definitions ****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/****************************************************************************/
/**
*
* Get the TX active location to check status. This is used to check if
* the TX buffer is currently active. There isn't any way in the hardware
* to implement this but the register is fully populated so the driver can
* set the bit in the send routine and the ISR can clear the bit when
* the handler is complete. This mimics the correct operation of the hardware
* if it was possible to do this in hardware.
*
* @param	BaseAddress is the base address of the device
*
* @return	Contents of active bit in register.
*
* @note		C-Style signature:
* 		u32 XEmacLite_GetTxActive(u32 BaseAddress)
*
*****************************************************************************/
#define XEmacLite_GetTxActive(BaseAddress)			\
		 (XEmacLite_ReadReg((BaseAddress), XEL_TSR_OFFSET))

/****************************************************************************/
/**
*
* Set the TX active location to update status. This is used to set the bit
* indicating which TX buffer is currently active. There isn't any way in the
* hardware to implement this but the register is fully populated so the driver
* can set the bit in the send routine and the ISR can clear the bit when
* the handler is complete. This mimics the correct operation of the hardware
* if it was possible to do this in hardware.
*
* @param	BaseAddress is the base address of the device
* @param	Mask is the data to be written
*
* @return	None
*
* @note		C-Style signature:
* 		void XEmacLite_SetTxActive(u32 BaseAddress, u32 Mask)
*
*****************************************************************************/
#define XEmacLite_SetTxActive(BaseAddress, Mask) 		\
	(XEmacLite_WriteReg((BaseAddress), XEL_TSR_OFFSET, (Mask)))

/************************** Variable Definitions ****************************/

extern XEmacLite_Config XEmacLite_ConfigTable[];

/************************** Function Prototypes ******************************/

void XEmacLite_AlignedWrite(void *SrcPtr, UINTPTR *DestPtr, unsigned ByteCount);
void XEmacLite_AlignedRead(UINTPTR *SrcPtr, void *DestPtr, unsigned ByteCount);

void StubHandler(void *CallBackRef);


#ifdef __cplusplus
}
#endif

#endif /* end of protection macro */
/** @} */
