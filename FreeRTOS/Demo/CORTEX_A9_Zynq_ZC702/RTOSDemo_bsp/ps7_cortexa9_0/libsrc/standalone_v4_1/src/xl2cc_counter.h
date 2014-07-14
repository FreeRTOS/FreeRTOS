/******************************************************************************
*
* (c) Copyright 2011-13  Xilinx, Inc. All rights reserved.
*
* This file contains confidential and proprietary information of Xilinx, Inc.
* and is protected under U.S. and international copyright and other
* intellectual property laws.
*
* DISCLAIMER
* This disclaimer is not a license and does not grant any rights to the
* materials distributed herewith. Except as otherwise provided in a valid
* license issued to you by Xilinx, and to the maximum extent permitted by
* applicable law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND WITH ALL
* FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES AND CONDITIONS, EXPRESS,
* IMPLIED, OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF
* MERCHANTABILITY, NON-INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE;
* and (2) Xilinx shall not be liable (whether in contract or tort, including
* negligence, or under any other theory of liability) for any loss or damage
* of any kind or nature related to, arising under or in connection with these
* materials, including for any direct, or any indirect, special, incidental,
* or consequential loss or damage (including loss of data, profits, goodwill,
* or any type of loss or damage suffered as a result of any action brought by
* a third party) even if such damage or loss was reasonably foreseeable or
* Xilinx had been advised of the possibility of the same.
*
* CRITICAL APPLICATIONS
* Xilinx products are not designed or intended to be fail-safe, or for use in
* any application requiring fail-safe performance, such as life-support or
* safety devices or systems, Class III medical devices, nuclear facilities,
* applications related to the deployment of airbags, or any other applications
* that could lead to death, personal injury, or severe property or
* environmental damage (individually and collectively, "Critical
* Applications"). Customer assumes the sole risk and liability of any use of
* Xilinx products in Critical Applications, subject only to applicable laws
* and regulations governing limitations on product liability.
*
* THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS PART OF THIS FILE
* AT ALL TIMES.
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

void XL2cc_EventCtrInit(int Event0, int Event1);
void XL2cc_EventCtrStart(void);
void XL2cc_EventCtrStop(u32 *EveCtr0, u32 *EveCtr1);

#ifdef __cplusplus
}
#endif /* __cplusplus */

#endif /* L2CCCOUNTER_H */
