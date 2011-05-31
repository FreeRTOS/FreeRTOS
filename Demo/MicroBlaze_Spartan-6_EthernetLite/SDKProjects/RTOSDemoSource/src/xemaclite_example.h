#define TESTAPP_GEN

/* $Id: xemaclite_example.h,v 1.1.2.1 2010/07/12 08:34:24 svemula Exp $
*/
/******************************************************************************
*
* (c) Copyright 2009 - 2010 Xilinx, Inc. All rights reserved.
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
* @file xemaclite_example.h
*
* Defines common data types, prototypes, and includes the proper headers
* for use with the EmacLite example code residing in this directory.
*
* This file along with xemaclite_example_util.c are utilized with the specific
* example code in the other source code files provided.
*
* These examples are designed to be compiled and utilized within the EDK
* standalone BSP development environment. The readme file contains more
* information on build requirements needed by these examples.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -------------------------------------------------------
* 2.00a ktn  04/13/09 First release
* </pre>
*
******************************************************************************/
#ifndef XEMACLITE_EXAMPLE_H
#define XEMACLITE_EXAMPLE_H

/***************************** Include Files *********************************/

#include "xparameters.h"
#include "xemaclite.h"

/************************** Constant Definitions ****************************/

#define PHY_REG0_OFFSET		0 /* Register 0 of PHY device */
#define PHY_REG1_OFFSET 	1 /* Register 1 of PHY device */

#define PHY_REG0_RESET_MASK	0x8000  /* Reset Phy device */
#define PHY_REG0_LOOPBACK_MASK	0x4000  /* Loopback Enable in Phy */
#define PHY_REG0_SPD_100_MASK	0x2000  /* Speed of 100Mbps for Phy */

#define PHY_REG1_DETECT_MASK	0x1808	/* Mask to detect PHY device */

#define EMACLITE_PHY_DELAY_SEC	4	/* Amount of time to delay waiting on
					 * PHY to reset.
					 */

/*
 * The following constants map to the XPAR parameters created in the
 * xparameters.h file. They are defined here such that a user can easily
 * change all the needed parameters in one place.
 */
#define EMAC_DEVICE_ID		XPAR_EMACLITE_0_DEVICE_ID

/***************** Macros (Inline Functions) Definitions *********************/

/**************************** Type Definitions ******************************/

/************************** Function Prototypes *****************************/

/*
 * Utility functions implemented in xemaclite_example_util.c
 */
void EmacLitePhyDelay(unsigned int Seconds);
u32 EmacLitePhyDetect(XEmacLite *InstancePtr);
int EmacLiteEnablePhyLoopBack(XEmacLite *InstancePtr, u32 PhyAddress);
int EmacLiteDisablePhyLoopBack(XEmacLite *InstancePtr, u32 PhyAddress);

/************************** Variable Definitions ****************************/
/*
 * Set up valid local MAC addresses. This loop back test uses the LocalAddress
 * both as a source and destination MAC address.
 */

XEmacLite EmacLiteInstance;	/* Instance of the EmacLite */

/*
 * Buffers used for Transmission and Reception of Packets. These are declared
 * as global so that they are not a part of the stack.
 */
u8 TxFrame[XEL_MAX_FRAME_SIZE];
u8 RxFrame[XEL_MAX_FRAME_SIZE];

volatile u32 RecvFrameLength;	/* Indicates the length of the Received packet
				 */
volatile int TransmitComplete;	/* Flag to indicate that the Transmission
				 * is complete
				 */
#endif /* XTEMAC_EXAMPLE_H */


