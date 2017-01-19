/******************************************************************************
*
* Copyright (C) 2016 Xilinx, Inc.  All rights reserved.
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
/****************************************************************************/
/**
*
* @file xusbpsu.c
* @addtogroup usbpsu_v1_0
* @{
*
* <pre>
*
* MODIFICATION HISTORY:
*
* Ver   Who    Date     Changes
* ----- -----  -------- -----------------------------------------------------
* 1.0   sg    06/16/16 First release
* 1.1   sg    10/24/16 Added new function XUsbPsu_IsSuperSpeed
*
* </pre>
*
*****************************************************************************/

/***************************** Include Files ********************************/

#include "xusbpsu.h"

/************************** Constant Definitions *****************************/


/**************************** Type Definitions *******************************/


/***************** Macros (Inline Functions) Definitions *********************/


/************************** Function Prototypes ******************************/


/************************** Variable Definitions *****************************/

/*****************************************************************************/
/**
* Waits until a bit in a register is cleared or timeout occurs
*
* @param	InstancePtr is a pointer to the XUsbPsu instance to be worked on.
* @param	Offset is register offset.
* @param	BitMask is bit mask of required bit to be checked.
* @param	Timeout is the time to wait specified in micro seconds.
*
* @return
*			- XST_SUCCESS when bit is cleared.
*			- XST_FAILURE when timed out.
*
******************************************************************************/
s32 XUsbPsu_Wait_Clear_Timeout(struct XUsbPsu *InstancePtr, u32 Offset,
								u32 BitMask, u32 Timeout)
{
	u32 RegVal;
	u32 LocalTimeout = Timeout;

	do {
		RegVal = XUsbPsu_ReadReg(InstancePtr, Offset);
		if ((RegVal & BitMask) == 0U) {
			break;
		}
		LocalTimeout--;
		if (LocalTimeout == 0U) {
			return XST_FAILURE;
		}
		XUsbSleep(1U);
	} while (1);

	return XST_SUCCESS;
}

/*****************************************************************************/
/**
* Waits until a bit in a register is set or timeout occurs
*
* @param	InstancePtr is a pointer to the XUsbPsu instance to be worked on.
* @param	Offset is register offset.
* @param	BitMask is bit mask of required bit to be checked.
* @param	Timeout is the time to wait specified in micro seconds.
*
* @return
*			- XST_SUCCESS when bit is set.
*			- XST_FAILURE when timed out.
*
******************************************************************************/
s32 XUsbPsu_Wait_Set_Timeout(struct XUsbPsu *InstancePtr, u32 Offset,
								u32 BitMask, u32 Timeout)
{
	u32 RegVal;
	u32 LocalTimeout = Timeout;

	do {
		RegVal = XUsbPsu_ReadReg(InstancePtr, Offset);
		if ((RegVal & BitMask) != 0U) {
			break;
		}
		LocalTimeout--;
		if (LocalTimeout == 0U) {
			return XST_FAILURE;
		}
		XUsbSleep(1U);
	} while (1);

	return XST_SUCCESS;
}

/*****************************************************************************/
/**
* Sets mode of Core to USB Device/Host/OTG.
*
*
* @param	InstancePtr is a pointer to the XUsbPsu instance to be worked on.
* @param	Mode is mode to set
*			- XUSBPSU_GCTL_PRTCAP_OTG
*			- XUSBPSU_GCTL_PRTCAP_HOST
*			- XUSBPSU_GCTL_PRTCAP_DEVICE
*
* @return	None
*
******************************************************************************/
void XUsbPsu_SetMode(struct XUsbPsu *InstancePtr, u32 Mode)
{
	u32 RegVal;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid((Mode <= XUSBPSU_GCTL_PRTCAP_OTG) &&
					(Mode >= XUSBPSU_GCTL_PRTCAP_HOST));

	RegVal = XUsbPsu_ReadReg(InstancePtr, XUSBPSU_GCTL);
	RegVal &= ~(XUSBPSU_GCTL_PRTCAPDIR(XUSBPSU_GCTL_PRTCAP_OTG));
	RegVal |= XUSBPSU_GCTL_PRTCAPDIR(Mode);
	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_GCTL, RegVal);
}

/*****************************************************************************/
/**
* Issues core PHY reset.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance to be worked on.
*
* @return	None
*
******************************************************************************/
void XUsbPsu_PhyReset(struct XUsbPsu *InstancePtr)
{
	u32		RegVal;

	Xil_AssertVoid(InstancePtr != NULL);

	/* Before Resetting PHY, put Core in Reset */
	RegVal = XUsbPsu_ReadReg(InstancePtr, XUSBPSU_GCTL);
	RegVal |= XUSBPSU_GCTL_CORESOFTRESET;
	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_GCTL, RegVal);

	/* Assert USB3 PHY reset */
	RegVal = XUsbPsu_ReadReg(InstancePtr, XUSBPSU_GUSB3PIPECTL(0));
	RegVal |= XUSBPSU_GUSB3PIPECTL_PHYSOFTRST;
	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_GUSB3PIPECTL(0), RegVal);

	/* Assert USB2 PHY reset */
	RegVal = XUsbPsu_ReadReg(InstancePtr, XUSBPSU_GUSB2PHYCFG(0));
	RegVal |= XUSBPSU_GUSB2PHYCFG_PHYSOFTRST;
	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_GUSB2PHYCFG(0), RegVal);

	XUsbSleep(XUSBPSU_PHY_TIMEOUT);

	/* Clear USB3 PHY reset */
	RegVal = XUsbPsu_ReadReg(InstancePtr, XUSBPSU_GUSB3PIPECTL(0));
	RegVal &= ~XUSBPSU_GUSB3PIPECTL_PHYSOFTRST;
	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_GUSB3PIPECTL(0), RegVal);

	/* Clear USB2 PHY reset */
	RegVal = XUsbPsu_ReadReg(InstancePtr, XUSBPSU_GUSB2PHYCFG(0));
	RegVal &= ~XUSBPSU_GUSB2PHYCFG_PHYSOFTRST;
	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_GUSB2PHYCFG(0), RegVal);

	XUsbSleep(XUSBPSU_PHY_TIMEOUT);

	/* Take Core out of reset state after PHYS are stable*/
	RegVal = XUsbPsu_ReadReg(InstancePtr, XUSBPSU_GCTL);
	RegVal &= ~XUSBPSU_GCTL_CORESOFTRESET;
	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_GCTL, RegVal);
}

/*****************************************************************************/
/**
* Sets up Event buffers so that events are written by Core.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance to be worked on.
*
* @return	None
*
******************************************************************************/
void XUsbPsu_EventBuffersSetup(struct XUsbPsu *InstancePtr)
{
    struct XUsbPsu_EvtBuffer *Evt;

	Xil_AssertVoid(InstancePtr != NULL);

	Evt = &InstancePtr->Evt;
	Evt->BuffAddr = (void *)InstancePtr->EventBuffer;

	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_GEVNTADRLO(0),
						(UINTPTR)InstancePtr->EventBuffer);
	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_GEVNTADRHI(0),
						((UINTPTR)(InstancePtr->EventBuffer) >> 16U) >> 16U);
	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_GEVNTSIZ(0),
					XUSBPSU_GEVNTSIZ_SIZE(sizeof(InstancePtr->EventBuffer)));
	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_GEVNTCOUNT(0), 0);
}

/*****************************************************************************/
/**
* Resets Event buffer Registers to zero so that events are not written by Core.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance to be worked on.
*
* @return	None
*
******************************************************************************/
void XUsbPsu_EventBuffersReset(struct XUsbPsu *InstancePtr)
{

	Xil_AssertVoid(InstancePtr != NULL);

	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_GEVNTADRLO(0U), 0U);
	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_GEVNTADRHI(0U), 0U);
	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_GEVNTSIZ(0U),
			(u32)XUSBPSU_GEVNTSIZ_INTMASK | XUSBPSU_GEVNTSIZ_SIZE(0U));
	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_GEVNTCOUNT(0U), 0U);
}

/*****************************************************************************/
/**
* Reads data from Hardware Params Registers of Core.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance to be worked on.
* @param	RegIndex is Register number to read
*			- XUSBPSU_GHWPARAMS0
*			- XUSBPSU_GHWPARAMS1
*			- XUSBPSU_GHWPARAMS2
*			- XUSBPSU_GHWPARAMS3
*			- XUSBPSU_GHWPARAMS4
*			- XUSBPSU_GHWPARAMS5
*			- XUSBPSU_GHWPARAMS6
*			- XUSBPSU_GHWPARAMS7
*
* @return	One of the GHWPARAMS RegValister contents.
*
******************************************************************************/
u32 XUsbPsu_ReadHwParams(struct XUsbPsu *InstancePtr, u8 RegIndex)
{
	u32 RegVal;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(RegIndex <= (u8)XUSBPSU_GHWPARAMS7);

	RegVal = XUsbPsu_ReadReg(InstancePtr, ((u32)XUSBPSU_GHWPARAMS0_OFFSET +
							((u32)RegIndex * (u32)4)));
	return RegVal;
}

/*****************************************************************************/
/**
* Initializes Core.
*
* @param  InstancePtr is a pointer to the XUsbPsu instance to be worked on.
*
* @return
*	 	- XST_SUCCESS if initialization was successful
*		- XST_FAILURE if initialization was not successful
*
******************************************************************************/
s32 XUsbPsu_CoreInit(struct XUsbPsu *InstancePtr)
{
	u32		RegVal;
	u32		Hwparams1;

	/* issue device SoftReset too */
	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_DCTL, XUSBPSU_DCTL_CSFTRST);

	if (XUsbPsu_Wait_Clear_Timeout(InstancePtr, XUSBPSU_DCTL,
			XUSBPSU_DCTL_CSFTRST, 500U) == XST_FAILURE) {
		/* timed out return failure */
		return XST_FAILURE;
	}

	XUsbPsu_PhyReset(InstancePtr);

	RegVal = XUsbPsu_ReadReg(InstancePtr, XUSBPSU_GCTL);
    RegVal &= ~XUSBPSU_GCTL_SCALEDOWN_MASK;
    RegVal &= ~XUSBPSU_GCTL_DISSCRAMBLE;
    RegVal |= XUSBPSU_GCTL_U2EXIT_LFPS;

	Hwparams1 = XUsbPsu_ReadHwParams(InstancePtr, 1U);

	switch (XUSBPSU_GHWPARAMS1_EN_PWROPT(Hwparams1)) {
		case XUSBPSU_GHWPARAMS1_EN_PWROPT_CLK:
			RegVal &= ~XUSBPSU_GCTL_DSBLCLKGTNG;
			break;

		case XUSBPSU_GHWPARAMS1_EN_PWROPT_HIB:
		/* enable hibernation here */
			break;

		default:
			/* Made for Misra-C Compliance. */
			break;
	}

	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_GCTL, RegVal);

	return XST_SUCCESS;
}

/*****************************************************************************/
/**
* Enables an interrupt in Event Enable RegValister.
*
* @param  InstancePtr is a pointer to the XUsbPsu instance to be worked on
* @param  Mask is the OR of any Interrupt Enable Masks:
*		- XUSBPSU_DEVTEN_VNDRDEVTSTRCVEDEN
*		- XUSBPSU_DEVTEN_EVNTOVERFLOWEN
*		- XUSBPSU_DEVTEN_CMDCMPLTEN
*		- XUSBPSU_DEVTEN_ERRTICERREN
*		- XUSBPSU_DEVTEN_SOFEN
*		- XUSBPSU_DEVTEN_EOPFEN
*		- XUSBPSU_DEVTEN_HIBERNATIONREQEVTEN
*		- XUSBPSU_DEVTEN_WKUPEVTEN
*		- XUSBPSU_DEVTEN_ULSTCNGEN
*		- XUSBPSU_DEVTEN_CONNECTDONEEN
*		- XUSBPSU_DEVTEN_USBRSTEN
*		- XUSBPSU_DEVTEN_DISCONNEVTEN
*
* @return  None
*
******************************************************************************/
void XUsbPsu_EnableIntr(struct XUsbPsu *InstancePtr, u32 Mask)
{
    u32	RegVal;

	Xil_AssertVoid(InstancePtr != NULL);

    RegVal = XUsbPsu_ReadReg(InstancePtr, XUSBPSU_DEVTEN);
    RegVal |= Mask;

	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_DEVTEN, RegVal);
}

/*****************************************************************************/
/**
* Disables an interrupt in Event Enable RegValister.
*
* @param  InstancePtr is a pointer to the XUsbPsu instance to be worked on.
* @param  Mask is the OR of Interrupt Enable Masks
*		- XUSBPSU_DEVTEN_VNDRDEVTSTRCVEDEN
*		- XUSBPSU_DEVTEN_EVNTOVERFLOWEN
*		- XUSBPSU_DEVTEN_CMDCMPLTEN
*		- XUSBPSU_DEVTEN_ERRTICERREN
*		- XUSBPSU_DEVTEN_SOFEN
*		- XUSBPSU_DEVTEN_EOPFEN
*		- XUSBPSU_DEVTEN_HIBERNATIONREQEVTEN
*		- XUSBPSU_DEVTEN_WKUPEVTEN
*		- XUSBPSU_DEVTEN_ULSTCNGEN
*		- XUSBPSU_DEVTEN_CONNECTDONEEN
*		- XUSBPSU_DEVTEN_USBRSTEN
*		- XUSBPSU_DEVTEN_DISCONNEVTEN
*
* @return  None
*
******************************************************************************/
void XUsbPsu_DisableIntr(struct XUsbPsu *InstancePtr, u32 Mask)
{
	u32 RegVal;

	Xil_AssertVoid(InstancePtr != NULL);

	RegVal = XUsbPsu_ReadReg(InstancePtr, XUSBPSU_DEVTEN);
	RegVal &= ~Mask;
	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_DEVTEN, RegVal);
}

/****************************************************************************/
/**
*
* This function does the following:
*	- initializes a specific XUsbPsu instance.
*	- sets up Event Buffer for Core to write events.
*	- Core Reset and PHY Reset.
*	- Sets core in Device Mode.
*	- Sets default speed as HIGH_SPEED.
*	- Sets Device Address to 0.
*	- Enables interrupts.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	ConfigPtr points to the XUsbPsu device configuration structure.
* @param	BaseAddress is the device base address in the virtual memory
*			address space. If the address translation is not used then the
*			physical address is passed.
*			Unexpected errors may occur if the address mapping is changed
*			after this function is invoked.
*
* @return	XST_SUCCESS else XST_FAILURE
*
* @note		None.
*
*****************************************************************************/
s32 XUsbPsu_CfgInitialize(struct XUsbPsu *InstancePtr,
			XUsbPsu_Config *ConfigPtr, u32 BaseAddress)
{
	int Status;
	u32 RegVal;


	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(ConfigPtr   != NULL);
	Xil_AssertNonvoid(BaseAddress != 0U)

	InstancePtr->ConfigPtr = ConfigPtr;

	Status = XUsbPsu_CoreInit(InstancePtr);
	if (Status != XST_SUCCESS) {
#ifdef XUSBPSU_DEBUG
		xil_printf("Core initialization failed\r\n");
#endif
		return XST_FAILURE;
	}

	RegVal = XUsbPsu_ReadHwParams(InstancePtr, 3U);
	InstancePtr->NumInEps = (u8)XUSBPSU_NUM_IN_EPS(RegVal);
	InstancePtr->NumOutEps = (u8)(XUSBPSU_NUM_EPS(RegVal) -
			InstancePtr->NumInEps);

	/* Map USB and Physical Endpoints */
	XUsbPsu_InitializeEps(InstancePtr);

	XUsbPsu_EventBuffersSetup(InstancePtr);

	XUsbPsu_SetMode(InstancePtr, XUSBPSU_GCTL_PRTCAP_DEVICE);

    /*
     * Setting to max speed to support SS and HS
     */
    XUsbPsu_SetSpeed(InstancePtr, XUSBPSU_DCFG_SUPERSPEED);

	(void)XUsbPsu_SetDeviceAddress(InstancePtr, 0U);

	return XST_SUCCESS;
}

/****************************************************************************/
/**
*
* Starts the controller so that Host can detect this device.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
*
* @return	XST_SUCCESS else XST_FAILURE
*
* @note		None.
*
*****************************************************************************/
s32 XUsbPsu_Start(struct XUsbPsu *InstancePtr)
{
	u32			RegVal;

	Xil_AssertNonvoid(InstancePtr != NULL);

	RegVal = XUsbPsu_ReadReg(InstancePtr, XUSBPSU_DCTL);

	RegVal |= XUSBPSU_DCTL_RUN_STOP;

	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_DCTL, RegVal);

	if (XUsbPsu_Wait_Clear_Timeout(InstancePtr, XUSBPSU_DSTS,
			XUSBPSU_DSTS_DEVCTRLHLT, 500U) == XST_FAILURE) {
		return XST_FAILURE;
	}

	return XST_SUCCESS;
}

/****************************************************************************/
/**
*
* Stops the controller so that Device disconnects from Host.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
*
* @return	XST_SUCCESS else XST_FAILURE
*
* @note		None.
*
*****************************************************************************/
s32 XUsbPsu_Stop(struct XUsbPsu *InstancePtr)
{
	u32	RegVal;

	Xil_AssertNonvoid(InstancePtr != NULL);

	RegVal = XUsbPsu_ReadReg(InstancePtr, XUSBPSU_DCTL);
	RegVal &= ~XUSBPSU_DCTL_RUN_STOP;

	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_DCTL, RegVal);

	if (XUsbPsu_Wait_Set_Timeout(InstancePtr, XUSBPSU_DSTS,
			XUSBPSU_DSTS_DEVCTRLHLT, 500U) == XST_FAILURE) {
		return XST_FAILURE;
	}

	return XST_SUCCESS;
}

/****************************************************************************/
/**
 * Enables USB2 Test Modes
 *
 * @param	InstancePtr is a pointer to the XUsbPsu instance.
 * @param	Mode is Test mode to set.
 *
 * @return	XST_SUCCESS else XST_FAILURE
 *
 * @note	None.
 *
 ****************************************************************************/
s32 XUsbPsu_SetTestMode(struct XUsbPsu *InstancePtr, u32 Mode)
{
	u32	RegVal;
	s32 Status = XST_SUCCESS;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid((Mode >= XUSBPSU_TEST_J)
			&& (Mode <= XUSBPSU_TEST_FORCE_ENABLE));

	RegVal = XUsbPsu_ReadReg(InstancePtr, XUSBPSU_DCTL);
	RegVal &= ~XUSBPSU_DCTL_TSTCTRL_MASK;

	switch (Mode) {
		case XUSBPSU_TEST_J:
		case XUSBPSU_TEST_K:
		case XUSBPSU_TEST_SE0_NAK:
		case XUSBPSU_TEST_PACKET:
		case XUSBPSU_TEST_FORCE_ENABLE:
			RegVal |= (u32)Mode << 1;
			break;

		default:
			Status = (s32)XST_FAILURE;
			break;
	}

	if (Status != (s32)XST_FAILURE) {
		XUsbPsu_WriteReg(InstancePtr, XUSBPSU_DCTL, RegVal);
		Status = XST_SUCCESS;
	}

	return Status;
}

/****************************************************************************/
/**
 * Gets current State of USB Link
 *
 * @param	InstancePtr is a pointer to the XUsbPsu instance.
 *
 * @return	Link State
 *
 * @note	None.
 *
 ****************************************************************************/
XusbPsuLinkState XUsbPsu_GetLinkState(struct XUsbPsu *InstancePtr)
{
	u32		RegVal;

	Xil_AssertNonvoid(InstancePtr != NULL);

	RegVal = XUsbPsu_ReadReg(InstancePtr, XUSBPSU_DSTS);

	return XUSBPSU_DSTS_USBLNKST(RegVal);
}

/****************************************************************************/
/**
 * Sets USB Link to a particular State
 *
 * @param	InstancePtr is a pointer to the XUsbPsu instance.
 * @param	State is State of Link to set.
 *
 * @return	XST_SUCCESS else XST_FAILURE
 *
 * @note	None.
 *
 ****************************************************************************/
s32 XUsbPsu_SetLinkState(struct XUsbPsu *InstancePtr,
		XusbPsuLinkStateChange State)
{
	u32		RegVal;

	Xil_AssertNonvoid(InstancePtr != NULL);

	 /* Wait until device controller is ready. */
	if (XUsbPsu_Wait_Clear_Timeout(InstancePtr, XUSBPSU_DSTS,
			XUSBPSU_DSTS_DCNRD, 500U) == XST_FAILURE) {
		return XST_FAILURE;
	}

	RegVal = XUsbPsu_ReadReg(InstancePtr, XUSBPSU_DCTL);
	RegVal &= ~XUSBPSU_DCTL_ULSTCHNGREQ_MASK;

	RegVal |= XUSBPSU_DCTL_ULSTCHNGREQ(State);
	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_DCTL, RegVal);

	return XST_SUCCESS;
}

/****************************************************************************/
/**
* Sets speed of the Core for connecting to Host
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	Speed is required speed
*				- XUSBPSU_DCFG_HIGHSPEED
*				- XUSBPSU_DCFG_FULLSPEED2
*				- XUSBPSU_DCFG_LOWSPEED
*				- XUSBPSU_DCFG_FULLSPEED1
*
* @return	None
*
* @note		None.
*
*****************************************************************************/
void XUsbPsu_SetSpeed(struct XUsbPsu *InstancePtr, u32 Speed)
{
	u32	RegVal;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(Speed <= (u32)XUSBPSU_DCFG_SUPERSPEED);

	RegVal = XUsbPsu_ReadReg(InstancePtr, XUSBPSU_DCFG);
	RegVal &= ~(XUSBPSU_DCFG_SPEED_MASK);
	RegVal |= Speed;
	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_DCFG, RegVal);
}

/****************************************************************************/
/**
* Sets Device Address of the Core
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	Addr is address to set.
*
* @return	XST_SUCCESS else XST_FAILURE
*
* @note	None.
*
*****************************************************************************/
s32 XUsbPsu_SetDeviceAddress(struct XUsbPsu *InstancePtr, u16 Addr)
{
	u32 RegVal;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(Addr <= 127U);

	if (InstancePtr->State == XUSBPSU_STATE_CONFIGURED) {
		return XST_FAILURE;
	}

	RegVal = XUsbPsu_ReadReg(InstancePtr, XUSBPSU_DCFG);
	RegVal &= ~(XUSBPSU_DCFG_DEVADDR_MASK);
	RegVal |= XUSBPSU_DCFG_DEVADDR(Addr);
	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_DCFG, RegVal);

	if (Addr) {
		InstancePtr->State = XUSBPSU_STATE_ADDRESS;
	}
	else {
		InstancePtr->State = XUSBPSU_STATE_DEFAULT;
	}

	return XST_SUCCESS;
}

/****************************************************************************/
/**
* Sets speed of the Core for connecting to Host
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
*
* @return	XST_SUCCESS else XST_FAILURE
*
* @note		None.
*
*****************************************************************************/
s32 XUsbPsu_IsSuperSpeed(struct XUsbPsu *InstancePtr)
{
	if (InstancePtr->Speed != XUSBPSU_SPEED_SUPER) {
		return XST_FAILURE;
	}

	return XST_SUCCESS;
}

/****************************************************************************/
/**
* Set U1 sleep timeout
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	Sleep is time in microseconds
*
* @return	XST_SUCCESS else XST_FAILURE
*
* @note	None.
*
*****************************************************************************/
s32 XUsbPsu_SetU1SleepTimeout(struct XUsbPsu *InstancePtr, u8 Sleep)
{
	u32 RegVal;

	Xil_AssertNonvoid(InstancePtr != NULL);

	RegVal = XUsbPsu_ReadReg(InstancePtr, XUSBPSU_PORTMSC_30);
	RegVal &= ~XUSBPSU_PORTMSC_30_U1_TIMEOUT_MASK;
	RegVal |= (Sleep << XUSBPSU_PORTMSC_30_U1_TIMEOUT_SHIFT);
	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_PORTMSC_30, RegVal);

	return XST_SUCCESS;
}

/****************************************************************************/
/**
* Set U2 sleep timeout
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	Sleep is time in microseconds
*
* @return	XST_SUCCESS else XST_FAILURE
*
* @note	None.
*
*****************************************************************************/
s32 XUsbPsu_SetU2SleepTimeout(struct XUsbPsu *InstancePtr, u8 Sleep)
{
	u32 RegVal;

	Xil_AssertNonvoid(InstancePtr != NULL);

	RegVal = XUsbPsu_ReadReg(InstancePtr, XUSBPSU_PORTMSC_30);
	RegVal &= ~XUSBPSU_PORTMSC_30_U2_TIMEOUT_MASK;
	RegVal |= (Sleep << XUSBPSU_PORTMSC_30_U2_TIMEOUT_SHIFT);
	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_PORTMSC_30, RegVal);

	return XST_SUCCESS;
}
/****************************************************************************/
/**
* Enable Accept U1 and U2 sleep enable
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
*
* @return	XST_SUCCESS else XST_FAILURE
*
* @note	None.
*
*****************************************************************************/
s32 XUsbPsu_AcceptU1U2Sleep(struct XUsbPsu *InstancePtr)
{
	u32 RegVal;

	Xil_AssertNonvoid(InstancePtr != NULL);

	RegVal = XUsbPsu_ReadReg(InstancePtr, XUSBPSU_DCTL);
	RegVal |= XUSBPSU_DCTL_ACCEPTU2ENA | XUSBPSU_DCTL_ACCEPTU1ENA;
	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_DCTL, RegVal);

	return XST_SUCCESS;
}

/****************************************************************************/
/**
* Enable U1 enable sleep
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
*
* @return	XST_SUCCESS else XST_FAILURE
*
* @note	None.
*
*****************************************************************************/
s32 XUsbPsu_U1SleepEnable(struct XUsbPsu *InstancePtr)
{
	u32 RegVal;

	Xil_AssertNonvoid(InstancePtr != NULL);

	RegVal = XUsbPsu_ReadReg(InstancePtr, XUSBPSU_DCTL);
	RegVal |= XUSBPSU_DCTL_INITU1ENA;
	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_DCTL, RegVal);

	return XST_SUCCESS;
}

/****************************************************************************/
/**
* Enable U2 enable sleep
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
*
* @return	XST_SUCCESS else XST_FAILURE
*
* @note	None.
*
*****************************************************************************/
s32 XUsbPsu_U2SleepEnable(struct XUsbPsu *InstancePtr)
{
	u32 RegVal;

	Xil_AssertNonvoid(InstancePtr != NULL);

	RegVal = XUsbPsu_ReadReg(InstancePtr, XUSBPSU_DCTL);
	RegVal |= XUSBPSU_DCTL_INITU2ENA;
	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_DCTL, RegVal);

	return XST_SUCCESS;
}

/****************************************************************************/
/**
* Enable U1 disable sleep
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
*
* @return	XST_SUCCESS else XST_FAILURE
*
* @note	None.
*
*****************************************************************************/
s32 XUsbPsu_U1SleepDisable(struct XUsbPsu *InstancePtr)
{
	u32 RegVal;

	Xil_AssertNonvoid(InstancePtr != NULL);

	RegVal = XUsbPsu_ReadReg(InstancePtr, XUSBPSU_DCTL);
	RegVal &= ~XUSBPSU_DCTL_INITU1ENA;
	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_DCTL, RegVal);

	return XST_SUCCESS;
}

/****************************************************************************/
/**
* Enable U2 disable sleep
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
*
* @return	XST_SUCCESS else XST_FAILURE
*
* @note	None.
*
*****************************************************************************/
s32 XUsbPsu_U2SleepDisable(struct XUsbPsu *InstancePtr)
{
	u32 RegVal;

	Xil_AssertNonvoid(InstancePtr != NULL);

	RegVal = XUsbPsu_ReadReg(InstancePtr, XUSBPSU_DCTL);
	RegVal &= ~XUSBPSU_DCTL_INITU2ENA;
	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_DCTL, RegVal);

	return XST_SUCCESS;
}
/** @} */
