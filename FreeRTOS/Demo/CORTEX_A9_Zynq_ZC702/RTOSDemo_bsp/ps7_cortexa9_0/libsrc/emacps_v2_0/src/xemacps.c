/* $Id: xemacps.c,v 1.1.2.3 2011/05/17 12:00:33 anirudh Exp $ */
/******************************************************************************
*
* (c) Copyright 2010 Xilinx, Inc. All rights reserved.
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
* @file xemacps.c
*
* The XEmacPs driver. Functions in this file are the minimum required functions
* for this driver. See xemacps.h for a detailed description of the driver.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -------------------------------------------------------
* 1.00a wsy  01/10/10 First release
* </pre>
******************************************************************************/

/***************************** Include Files *********************************/

#include "xemacps.h"

/************************** Constant Definitions *****************************/


/**************************** Type Definitions *******************************/


/***************** Macros (Inline Functions) Definitions *********************/


/************************** Function Prototypes ******************************/

void XEmacPs_StubHandler(void);	/* Default handler routine */

/************************** Variable Definitions *****************************/


/*****************************************************************************/
/**
* Initialize a specific XEmacPs instance/driver. The initialization entails:
* - Initialize fields of the XEmacPs instance structure
* - Reset hardware and apply default options
* - Configure the DMA channels
*
* The PHY is setup independently from the device. Use the MII or whatever other
* interface may be present for setup.
*
* @param InstancePtr is a pointer to the instance to be worked on.
* @param CfgPtr is the device configuration structure containing required
*        hardware build data.
* @param EffectiveAddress is the base address of the device. If address
*        translation is not utilized, this parameter can be passed in using
*        CfgPtr->Config.BaseAddress to specify the physical base address.
*
* @return
* - XST_SUCCESS if initialization was successful
*
******************************************************************************/
int XEmacPs_CfgInitialize(XEmacPs *InstancePtr, XEmacPs_Config * CfgPtr,
			   u32 EffectiveAddress)
{
	/* Verify arguments */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(CfgPtr != NULL);

	/* Set device base address and ID */
	InstancePtr->Config.DeviceId = CfgPtr->DeviceId;
	InstancePtr->Config.BaseAddress = EffectiveAddress;

	/* Set callbacks to an initial stub routine */
	InstancePtr->SendHandler = (XEmacPs_Handler) XEmacPs_StubHandler;
	InstancePtr->RecvHandler = (XEmacPs_Handler) XEmacPs_StubHandler;
	InstancePtr->ErrorHandler = (XEmacPs_ErrHandler) XEmacPs_StubHandler;

	/* Reset the hardware and set default options */
	InstancePtr->IsReady = XIL_COMPONENT_IS_READY;
	XEmacPs_Reset(InstancePtr);

	return (XST_SUCCESS);
}


/*****************************************************************************/
/**
* Start the Ethernet controller as follows:
*   - Enable transmitter if XTE_TRANSMIT_ENABLE_OPTION is set
*   - Enable receiver if XTE_RECEIVER_ENABLE_OPTION is set
*   - Start the SG DMA send and receive channels and enable the device
*     interrupt
*
* @param InstancePtr is a pointer to the instance to be worked on.
*
* @return N/A
*
* @note
* Hardware is configured with scatter-gather DMA, the driver expects to start
* the scatter-gather channels and expects that the user has previously set up
* the buffer descriptor lists.
*
* This function makes use of internal resources that are shared between the
* Start, Stop, and Set/ClearOptions functions. So if one task might be setting
* device options while another is trying to start the device, the user is
* required to provide protection of this shared data (typically using a
* semaphore).
*
* This function must not be preempted by an interrupt that may service the
* device.
*
******************************************************************************/
void XEmacPs_Start(XEmacPs *InstancePtr)
{
	u32 Reg;

	/* Assert bad arguments and conditions */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(InstancePtr->RxBdRing.BaseBdAddr != 0);
	Xil_AssertVoid(InstancePtr->TxBdRing.BaseBdAddr != 0);

        /* If already started, then there is nothing to do */
        if (InstancePtr->IsStarted == XIL_COMPONENT_IS_STARTED) {
                return;
        }

	/* Start DMA */
	/* When starting the DMA channels, both transmit and receive sides
	 * need an initialized BD list.
	 */
	XEmacPs_WriteReg(InstancePtr->Config.BaseAddress,
			   XEMACPS_RXQBASE_OFFSET,
			   InstancePtr->RxBdRing.BaseBdAddr);

	XEmacPs_WriteReg(InstancePtr->Config.BaseAddress,
			   XEMACPS_TXQBASE_OFFSET,
			   InstancePtr->TxBdRing.BaseBdAddr);

	/* clear any existed int status */
	XEmacPs_WriteReg(InstancePtr->Config.BaseAddress, XEMACPS_ISR_OFFSET,
			   XEMACPS_IXR_ALL_MASK);

	/* Enable transmitter if not already enabled */
	if (InstancePtr->Options & XEMACPS_TRANSMITTER_ENABLE_OPTION) {
		Reg = XEmacPs_ReadReg(InstancePtr->Config.BaseAddress,
					XEMACPS_NWCTRL_OFFSET);
		if (!(Reg & XEMACPS_NWCTRL_TXEN_MASK)) {
			XEmacPs_WriteReg(InstancePtr->Config.BaseAddress,
					   XEMACPS_NWCTRL_OFFSET,
					   Reg | XEMACPS_NWCTRL_TXEN_MASK);
		}
	}

	/* Enable receiver if not already enabled */
	if (InstancePtr->Options & XEMACPS_RECEIVER_ENABLE_OPTION) {
		Reg = XEmacPs_ReadReg(InstancePtr->Config.BaseAddress,
					XEMACPS_NWCTRL_OFFSET);
		if (!(Reg & XEMACPS_NWCTRL_RXEN_MASK)) {
			XEmacPs_WriteReg(InstancePtr->Config.BaseAddress,
					   XEMACPS_NWCTRL_OFFSET,
					   Reg | XEMACPS_NWCTRL_RXEN_MASK);
		}
	}

        /* Enable TX and RX interrupts */
        XEmacPs_IntEnable(InstancePtr, (XEMACPS_IXR_TX_ERR_MASK |
		XEMACPS_IXR_RX_ERR_MASK | XEMACPS_IXR_FRAMERX_MASK |
		XEMACPS_IXR_TXCOMPL_MASK));

	/* Mark as started */
	InstancePtr->IsStarted = XIL_COMPONENT_IS_STARTED;

	return;
}


/*****************************************************************************/
/**
* Gracefully stop the Ethernet MAC as follows:
*   - Disable all interrupts from this device
*   - Stop DMA channels
*   - Disable the tansmitter and receiver
*
* Device options currently in effect are not changed.
*
* This function will disable all interrupts. Default interrupts settings that
* had been enabled will be restored when XEmacPs_Start() is called.
*
* @param InstancePtr is a pointer to the instance to be worked on.
*
* @note
* This function makes use of internal resources that are shared between the
* Start, Stop, SetOptions, and ClearOptions functions. So if one task might be
* setting device options while another is trying to start the device, the user
* is required to provide protection of this shared data (typically using a
* semaphore).
*
* Stopping the DMA channels causes this function to block until the DMA
* operation is complete.
*
******************************************************************************/
void XEmacPs_Stop(XEmacPs *InstancePtr)
{
	u32 Reg;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/* Disable all interrupts */
	XEmacPs_WriteReg(InstancePtr->Config.BaseAddress, XEMACPS_IDR_OFFSET,
			   XEMACPS_IXR_ALL_MASK);

	/* Disable the receiver & transmitter */
	Reg = XEmacPs_ReadReg(InstancePtr->Config.BaseAddress,
				XEMACPS_NWCTRL_OFFSET);
	Reg &= ~XEMACPS_NWCTRL_RXEN_MASK;
	Reg &= ~XEMACPS_NWCTRL_TXEN_MASK;
	XEmacPs_WriteReg(InstancePtr->Config.BaseAddress,
			   XEMACPS_NWCTRL_OFFSET, Reg);

	/* Mark as stopped */
	InstancePtr->IsStarted = 0;
}


/*****************************************************************************/
/**
* Perform a graceful reset of the Ethernet MAC. Resets the DMA channels, the
* transmitter, and the receiver.
*
* Steps to reset
* - Stops transmit and receive channels
* - Stops DMA
* - Configure transmit and receive buffer size to default
* - Clear transmit and receive status register and counters
* - Clear all interrupt sources
* - Clear phy (if there is any previously detected) address
* - Clear MAC addresses (1-4) as well as Type IDs and hash value
*
* All options are placed in their default state. Any frames in the
* descriptor lists will remain in the lists. The side effect of doing
* this is that after a reset and following a restart of the device, frames
* were in the list before the reset may be transmitted or received.
*
* The upper layer software is responsible for re-configuring (if necessary)
* and restarting the MAC after the reset. Note also that driver statistics
* are not cleared on reset. It is up to the upper layer software to clear the
* statistics if needed.
*
* When a reset is required, the driver notifies the upper layer software of
* this need through the ErrorHandler callback and specific status codes.
* The upper layer software is responsible for calling this Reset function
* and then re-configuring the device.
*
* @param InstancePtr is a pointer to the instance to be worked on.
*
******************************************************************************/
void XEmacPs_Reset(XEmacPs *InstancePtr)
{
	u32 Reg;
	u8 i;
	char EmacPs_zero_MAC[6] = { 0x0, 0x0, 0x0, 0x0, 0x0, 0x0 };

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/* Stop the device and reset hardware */
	XEmacPs_Stop(InstancePtr);
	InstancePtr->Options = XEMACPS_DEFAULT_OPTIONS;

	/* Setup hardware with default values */
	XEmacPs_WriteReg(InstancePtr->Config.BaseAddress,
			XEMACPS_NWCTRL_OFFSET,
			(XEMACPS_NWCTRL_STATCLR_MASK |
			XEMACPS_NWCTRL_MDEN_MASK) &
			~XEMACPS_NWCTRL_LOOPEN_MASK);

	XEmacPs_WriteReg(InstancePtr->Config.BaseAddress,
					XEMACPS_NWCFG_OFFSET,
					XEMACPS_NWCFG_100_MASK |
					XEMACPS_NWCFG_FDEN_MASK |
					XEMACPS_NWCFG_UCASTHASHEN_MASK);

	XEmacPs_WriteReg(InstancePtr->Config.BaseAddress,
			XEMACPS_DMACR_OFFSET,
			((((XEMACPS_RX_BUF_SIZE / XEMACPS_RX_BUF_UNIT) +
				((XEMACPS_RX_BUF_SIZE %
				XEMACPS_RX_BUF_UNIT) ? 1 : 0)) <<
				XEMACPS_DMACR_RXBUF_SHIFT) &
				XEMACPS_DMACR_RXBUF_MASK) |
				XEMACPS_DMACR_RXSIZE_MASK |
				XEMACPS_DMACR_TXSIZE_MASK);

	XEmacPs_WriteReg(InstancePtr->Config.BaseAddress,
			   XEMACPS_TXSR_OFFSET, 0x0);

	XEmacPs_WriteReg(InstancePtr->Config.BaseAddress,
			   XEMACPS_RXQBASE_OFFSET, 0x0);

	XEmacPs_WriteReg(InstancePtr->Config.BaseAddress,
			   XEMACPS_TXQBASE_OFFSET, 0x0);

	XEmacPs_WriteReg(InstancePtr->Config.BaseAddress,
			   XEMACPS_RXSR_OFFSET, 0x0);

	XEmacPs_WriteReg(InstancePtr->Config.BaseAddress, XEMACPS_IDR_OFFSET,
			   XEMACPS_IXR_ALL_MASK);

	Reg = XEmacPs_ReadReg(InstancePtr->Config.BaseAddress,
				XEMACPS_ISR_OFFSET);
	XEmacPs_WriteReg(InstancePtr->Config.BaseAddress, XEMACPS_ISR_OFFSET,
			   Reg);

	XEmacPs_WriteReg(InstancePtr->Config.BaseAddress,
			   XEMACPS_PHYMNTNC_OFFSET, 0x0);

	XEmacPs_ClearHash(InstancePtr);

	for (i = 1; i < 5; i++) {
		XEmacPs_SetMacAddress(InstancePtr, EmacPs_zero_MAC, i);
		XEmacPs_SetTypeIdCheck(InstancePtr, 0x0, i);
	}

	/* clear all counters */
	for (i = 0; i < (XEMACPS_LAST_OFFSET - XEMACPS_OCTTXL_OFFSET) / 4;
	     i++) {
		XEmacPs_ReadReg(InstancePtr->Config.BaseAddress,
                                   XEMACPS_OCTTXL_OFFSET + i * 4);
	}

	/* Disable the receiver */
	Reg = XEmacPs_ReadReg(InstancePtr->Config.BaseAddress,
				XEMACPS_NWCTRL_OFFSET);
	Reg &= ~XEMACPS_NWCTRL_RXEN_MASK;
	XEmacPs_WriteReg(InstancePtr->Config.BaseAddress,
			   XEMACPS_NWCTRL_OFFSET, Reg);

	/* Sync default options with hardware but leave receiver and
         * transmitter disabled. They get enabled with XEmacPs_Start() if
	 * XEMACPS_TRANSMITTER_ENABLE_OPTION and
         * XEMACPS_RECEIVER_ENABLE_OPTION are set.
	 */
	XEmacPs_SetOptions(InstancePtr, InstancePtr->Options &
			    ~(XEMACPS_TRANSMITTER_ENABLE_OPTION |
			      XEMACPS_RECEIVER_ENABLE_OPTION));

	XEmacPs_ClearOptions(InstancePtr, ~InstancePtr->Options);
}


/******************************************************************************/
/**
 * This is a stub for the asynchronous callbacks. The stub is here in case the
 * upper layer forgot to set the handler(s). On initialization, all handlers are
 * set to this callback. It is considered an error for this handler to be
 * invoked.
 *
 ******************************************************************************/
void XEmacPs_StubHandler(void)
{
	Xil_AssertVoidAlways();
}
