/******************************************************************************
*
* Copyright (C) 2011 - 2015 Xilinx, Inc.  All rights reserved.
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
* @file xl2cc_counter.h
*
* This header file contains APIs for configuring and controlling the event
* counters in PL310 L2 cache controller.
* PL310 has 2 event counters which can be used to count a variety of events
* like DRHIT, DRREQ, DWHIT, DWREQ, etc. This file defines configurations,
* where value configures the event counters to count a set of events.
*
* XL2cc_EventCtrInit API can be used to select a set of events and
* XL2cc_EventCtrStart configures the event counters and starts the counters.
* XL2cc_EventCtrStop diables the event counters and returns the counter values.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.00a sdm  07/11/11 First release
* 3.07a asa  08/30/12 Updated for CR 675636 to provide the L2 Base Address
*		      inside the APIs
* </pre>
*
******************************************************************************/

#ifndef L2CCCOUNTER_H /* prevent circular inclusions */
#define L2CCCOUNTER_H /* by using protection macros */

/***************************** Include Files ********************************/

#include "xpseudo_asm.h"
#include "xil_types.h"

#ifdef __cplusplus
extern "C" {
#endif /* __cplusplus */

/************************** Constant Definitions ****************************/

/*
 * The following constants define the event codes for the event counters.
 */
#define XL2CC_CO		0x1
#define XL2CC_DRHIT		0x2
#define XL2CC_DRREQ		0x3
#define XL2CC_DWHIT		0x4
#define XL2CC_DWREQ		0x5
#define XL2CC_DWTREQ		0x6
#define XL2CC_IRHIT		0x7
#define XL2CC_IRREQ		0x8
#define XL2CC_WA		0x9
#define XL2CC_IPFALLOC		0xa
#define XL2CC_EPFHIT		0xb
#define XL2CC_EPFALLOC		0xc
#define XL2CC_SRRCVD		0xd
#define XL2CC_SRCONF		0xe
#define XL2CC_EPFRCVD		0xf

/**************************** Type Definitions ******************************/

/***************** Macros (Inline Functions) Definitions ********************/

/************************** Variable Definitions ****************************/

/************************** Function Prototypes *****************************/

void XL2cc_EventCtrInit(s32 Event0, s32 Event1);
void XL2cc_EventCtrStart(void);
void XL2cc_EventCtrStop(u32 *EveCtr0, u32 *EveCtr1);

#ifdef __cplusplus
}
#endif /* __cplusplus */

#endif /* L2CCCOUNTER_H */
