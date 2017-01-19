/******************************************************************************
*
* Copyright (C) 2015 - 2016 Xilinx, Inc.  All rights reserved.
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
/**
*
* @file xipipsu_hw.h
* @addtogroup ipipsu_v1_0
* @{
*
* This file contains macro definitions for low level HW related params
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who Date     Changes
* ----- --- -------- -----------------------------------------------.
* 1.0   mjr  03/15/15 First release
* 2.1   kvn  05/05/16 Modified code for MISRA-C:2012 Compliance
*
* </pre>
*
******************************************************************************/
#ifndef XIPIPSU_HW_H_	/* prevent circular inclusions */
#define XIPIPSU_HW_H_	/* by using protection macros */

/************************** Constant Definitions *****************************/
/* Message RAM related params */
#define XIPIPSU_MSG_RAM_BASE 0xFF990000U
#define XIPIPSU_MSG_BUF_SIZE 8U	/* Size in Words */
#define XIPIPSU_MAX_BUFF_INDEX	7U

/* EIGHT pairs of TWO buffers(msg+resp) of THIRTY TWO bytes each */
#define XIPIPSU_BUFFER_OFFSET_GROUP	(8U * 2U * 32U)
#define XIPIPSU_BUFFER_OFFSET_TARGET (32U * 2U)
#define XIPIPSU_BUFFER_OFFSET_RESPONSE		(32U)

/* Max Number of IPI slots on the device */
#define XIPIPSU_MAX_TARGETS	11

/* Register Offsets for each member  of IPI Register Set */
#define XIPIPSU_TRIG_OFFSET 0x00U
#define XIPIPSU_OBS_OFFSET 0x04U
#define XIPIPSU_ISR_OFFSET 0x10U
#define XIPIPSU_IMR_OFFSET 0x14U
#define XIPIPSU_IER_OFFSET 0x18U
#define XIPIPSU_IDR_OFFSET 0x1CU

/* MASK of all valid IPI bits in above registers */
#define XIPIPSU_ALL_MASK	0x0F0F0301U

#endif /* XIPIPSU_HW_H_ */
/** @} */
