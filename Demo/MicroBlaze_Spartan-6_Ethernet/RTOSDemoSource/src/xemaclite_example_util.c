#define TESTAPP_GEN

/* $Id: xemaclite_example_util.c,v 1.1.2.1 2010/07/12 08:34:25 svemula Exp $ */
/******************************************************************************
*
* (c) Copyright 2009-2010 Xilinx, Inc. All rights reserved.
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
* @file xemaclite_example_util.c
*
* This file implements the utility functions for the EmacLite example code.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -------------------------------------------------------
* 2.00a  ktn 04/13/09 First release
* 2.00a  ktn 06/13/09 Changed the EmacLitePhyDetect function so that
*		      the function is not in an infinite loop in case of a
*		      faulty Phy device.
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xemaclite_example.h"
#include "stdio.h"

/************************** Variable Definitions ****************************/

/******************************************************************************/
/**
*
* This function detects the PHY address by looking for successful MII status
* register contents (PHY register 1). It looks for a PHY that supports
* auto-negotiation and 10Mbps full-duplex and half-duplex. So, this code
* won't work for PHYs that don't support those features, but it's a bit more
* general purpose than matching a specific PHY manufacturer ID.
*
* Note also that on some (older) Xilinx ML4xx boards, PHY address 0 does not
* properly respond to this query. But, since the default is 0 and assuming
* no other address responds, then it seems to work OK.
*
* @param	InstancePtr is the pointer to the instance of EmacLite driver.
*
* @return	The address of the PHY device detected (returns 0 if not
*		detected).
*
* @note
*		The bit mask (0x1808) of the MII status register
*		(PHY Register 1) used in this function are:
* 		0x1000: 10Mbps full duplex support.
* 		0x0800: 10Mbps half duplex support.
*  		0x0008: Auto-negotiation support.
*
******************************************************************************/
u32 EmacLitePhyDetect(XEmacLite *InstancePtr)
{
	u16 PhyData;
	int PhyAddr;

	/*
	 * Verify all 32 MDIO ports.
	 */
	for (PhyAddr = 31; PhyAddr >= 0; PhyAddr--) {
		XEmacLite_PhyRead(InstancePtr, PhyAddr, PHY_REG1_OFFSET,
				 &PhyData);

		if (PhyData != 0xFFFF) {
			if ((PhyData & PHY_REG1_DETECT_MASK) ==
			PHY_REG1_DETECT_MASK) {
				return PhyAddr;	/* Found a valid PHY device */
			}
		}
	}
	/*
	 * Unable to detect PHY device returning the default address of 0.
	 */
	return 0;
}

/******************************************************************************/
/**
*
* This function enables the MAC loopback on the PHY.
*
* @param	InstancePtr is the pointer to the instance of EmacLite driver.
* @param	PhyAddress is the address of the Phy device.
*
* @return
*		- XST_SUCCESS if the loop back is enabled.
*		- XST_FAILURE if the loop back was not enabled.
*
* @note		None.
*
******************************************************************************/
int EmacLiteEnablePhyLoopBack(XEmacLite *InstancePtr, u32 PhyAddress)
{
	int Status;
	u16 PhyData = 0;

	/*
	 * Set the speed and put the PHY in reset.
	 */
	PhyData |= PHY_REG0_SPD_100_MASK;
	Status = XEmacLite_PhyWrite(InstancePtr, PhyAddress, PHY_REG0_OFFSET,
			PhyData | PHY_REG0_RESET_MASK);
	if (Status != XST_SUCCESS) {
		return XST_FAILURE;
	}

	/*
	 * Give sufficient delay for Phy Reset.
	 */
	EmacLitePhyDelay(EMACLITE_PHY_DELAY_SEC);

	/*
	 * Set the PHY in loop back.
	 */
	XEmacLite_PhyWrite(InstancePtr, PhyAddress, PHY_REG0_OFFSET,
			PhyData | PHY_REG0_LOOPBACK_MASK);
	if (Status != XST_SUCCESS) {
		return XST_FAILURE;
	}

	/*
	 * Give sufficient delay for Phy Loopback Enable.
	 */
	EmacLitePhyDelay(1);

	return XST_SUCCESS;
}

/******************************************************************************/
/**
*
* This function disables the MAC loopback on the PHY.
*
* @param	InstancePtr is the pointer to the instance of EmacLite driver.
* @param	PhyAddress is the address of the Phy device.
*
* @return
*		- XST_SUCCESS if the loop back was disabled.
*		- XST_FAILURE if the loop back was not disabled.
*
* @note		None.
*
******************************************************************************/
int EmacLiteDisablePhyLoopBack(XEmacLite *InstancePtr, u32 PhyAddress)
{
	int Status;
	u16 PhyData;

	/*
	 * Disable loop back through PHY register using MDIO support.
	 */
	Status = XEmacLite_PhyRead(InstancePtr, PhyAddress, PHY_REG0_OFFSET,
					&PhyData);
	if (Status != XST_SUCCESS) {
		return XST_FAILURE;
	}

	Status = XEmacLite_PhyWrite(InstancePtr,PhyAddress, PHY_REG0_OFFSET,
					PhyData & ~(PHY_REG0_LOOPBACK_MASK));
	if (Status != XST_SUCCESS) {
		return XST_FAILURE;
	}

	return XST_SUCCESS;

}

/******************************************************************************/
/**
*
* For PPC we use a usleep call, for Microblaze we use an assembly loop that
* is roughly the same regardless of optimization level, although caches and
* memory access time can make the delay vary.  Just keep in mind that after
* resetting or updating the PHY modes, the PHY typically needs time to recover.
*
* @return   None
*
* @note     None
*
******************************************************************************/
void EmacLitePhyDelay(unsigned int Seconds)
{
#ifdef __MICROBLAZE__
	static int WarningFlag = 0;

	/* If MB caches are disabled or do not exist, this delay loop could
	 * take minutes instead of seconds (e.g., 30x longer).  Print a warning
	 * message for the user (once).  If only MB had a built-in timer!
	 */
	if (((mfmsr() & 0x20) == 0) && (!WarningFlag)) {
#ifdef STDOUT_BASEADDRESS
		xil_printf("Warning: This example will take ");
		xil_printf("minutes to complete without I-cache enabled \r\n");
#endif
		WarningFlag = 1;
	}

#define ITERS_PER_SEC   (XPAR_CPU_CORE_CLOCK_FREQ_HZ / 6)
    asm volatile ("\n"
                  "1:               \n\t"
                  "addik r7, r0, %0 \n\t"
                  "2:               \n\t"
                  "addik r7, r7, -1 \n\t"
                  "bneid  r7, 2b    \n\t"
                  "or  r0, r0, r0   \n\t"
                  "bneid %1, 1b     \n\t"
                  "addik %1, %1, -1 \n\t"
                  :: "i"(ITERS_PER_SEC), "d" (Seconds));

#else

	usleep(Seconds * 1000000);

#endif
}





