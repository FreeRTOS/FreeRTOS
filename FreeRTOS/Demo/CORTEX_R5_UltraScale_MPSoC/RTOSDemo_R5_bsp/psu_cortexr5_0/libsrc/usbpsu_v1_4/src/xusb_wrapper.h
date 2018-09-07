/******************************************************************************
 *
 * Copyright (C) 2017 Xilinx, Inc.  All rights reserved.
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
 * @file xusb_wrapper.h
 *
 * This file contains declarations for USBPSU Driver wrappers.
 *
 * <pre>
 * MODIFICATION HISTORY:
 *
 * Ver   Who  	Date     Changes
 * ----- ---- 	-------- -------------------------------------------------------
 *  1.0  BK	12/01/18 First release
 *	 MYK	12/01/18 Added hibernation support for device mode
 *	 vak	22/01/18 Added Microblaze support for usbpsu driver
 *	 vak	13/03/18 Moved the setup interrupt system calls from driver to
 *			 example.
 *
 * </pre>
 *
 *****************************************************************************/

#ifndef XUSB_WRAPPER_H  /* Prevent circular inclusions */
#define XUSB_WRAPPER_H  /* by using protection macros  */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files ********************************/
#include "xusbpsu.h"

/************************** Constant Definitions ****************************/
#define USB_DEVICE_ID		XPAR_XUSBPSU_0_DEVICE_ID

#define USB_EP_DIR_IN		XUSBPSU_EP_DIR_IN
#define USB_EP_DIR_OUT		XUSBPSU_EP_DIR_OUT

#define USB_DIR_OUT				0U		/* to device */
#define USB_DIR_IN				0x80U	/* to host */

/**
 * @name Endpoint Address
 * @{
 */
#define USB_EP1_IN		0x81
#define USB_EP1_OUT		0x01
#define USB_EP2_IN		0x82
#define USB_EP2_OUT		0x02
/* @} */

/**
 * @name Endpoint Type
 * @{
 */
#define USB_EP_TYPE_CONTROL			XUSBPSU_ENDPOINT_XFER_CONTROL
#define USB_EP_TYPE_ISOCHRONOUS		XUSBPSU_ENDPOINT_XFER_ISOC
#define USB_EP_TYPE_BULK			XUSBPSU_ENDPOINT_XFER_BULK
#define USB_EP_TYPE_INTERRUPT		XUSBPSU_ENDPOINT_XFER_INT
/* @} */

#define USB_ENDPOINT_NUMBER_MASK        0x0f    /* in bEndpointAddress */
#define USB_ENDPOINT_DIR_MASK           0x80

/*
 * Device States
 */
#define		USB_STATE_ATTACHED		XUSBPSU_STATE_ATTACHED
#define		USB_STATE_POWERED		XUSBPSU_STATE_POWERED
#define		USB_STATE_DEFAULT		XUSBPSU_STATE_DEFAULT
#define		USB_STATE_ADDRESS		XUSBPSU_STATE_ADDRESS
#define		USB_STATE_CONFIGURED	XUSBPSU_STATE_CONFIGURED
#define		USB_STATE_SUSPENDED		XUSBPSU_STATE_SUSPENDED

#define XUSBPSU_REQ_REPLY_LEN	    1024	/**< Max size of reply buffer. */
#define USB_REQ_REPLY_LEN			XUSBPSU_REQ_REPLY_LEN

/*
 * Device Speeds
 */
#define	USB_SPEED_UNKNOWN		XUSBPSU_SPEED_UNKNOWN
#define	USB_SPEED_LOW			XUSBPSU_SPEED_LOW
#define	USB_SPEED_FULL			XUSBPSU_SPEED_FULL
#define	USB_SPEED_HIGH			XUSBPSU_SPEED_HIGH
#define	USB_SPEED_SUPER			XUSBPSU_SPEED_SUPER

/* Device Configuration Speed */
#define	USB_DCFG_SPEED_MASK		XUSBPSU_DCFG_SPEED_MASK
#define	USB_DCFG_SUPERSPEED		XUSBPSU_DCFG_SUPERSPEED
#define	USB_DCFG_HIGHSPEED		XUSBPSU_DCFG_HIGHSPEED
#define	USB_DCFG_FULLSPEED2		XUSBPSU_DCFG_FULLSPEED2
#define	USB_DCFG_LOWSPEED		XUSBPSU_DCFG_LOWSPEED
#define	USB_DCFG_FULLSPEED1		XUSBPSU_DCFG_FULLSPEED1

#define	USB_TEST_J				XUSBPSU_TEST_J
#define	USB_TEST_K				XUSBPSU_TEST_K
#define	USB_TEST_SE0_NAK		XUSBPSU_TEST_SE0_NAK
#define	USB_TEST_PACKET			XUSBPSU_TEST_PACKET
#define	USB_TEST_FORCE_ENABLE	XUSBPSU_TEST_FORCE_ENABLE

/* TODO: If we enable this macro, reconnection is failed with 2017.3 */
#define USB_LPM_MODE			XUSBPSU_LPM_MODE

/*
 * return Physical EP number as dwc3 mapping
 */
#define PhysicalEp(epnum, direction)	(((epnum) << 1 ) | (direction))

/**************************** Type Definitions ******************************/

/************************** Variable Definitions *****************************/
struct XUsbPsu PrivateData;

/***************** Macros (Inline Functions) Definitions *********************/
Usb_Config* LookupConfig(u16 DeviceId);
void CacheInit(void);
s32 CfgInitialize(struct Usb_DevData *InstancePtr,
			Usb_Config *ConfigPtr, u32 BaseAddress);
void Set_Ch9Handler(void *InstancePtr,
				void (*func)(struct Usb_DevData *, SetupPacket *));
void Set_RstHandler(void *InstancePtr, void (*func)(struct Usb_DevData *));
void Set_Disconnect(void *InstancePtr, void (*func)(struct Usb_DevData *));
void EpConfigure(void *UsbInstance, u8 EndpointNo, u8 dir, u32 Type);
s32 ConfigureDevice(void *UsbInstance, u8 *MemPtr, u32 memSize);
void SetEpHandler(void *InstancePtr, u8 Epnum,
			u8 Dir, void (*Handler)(void *, u32, u32));
s32 Usb_Start(void *InstancePtr);
void *Get_DrvData(void *InstancePtr);
void Set_DrvData(void *InstancePtr, void *data);
s32 IsEpStalled(void *InstancePtr, u8 Epnum, u8 Dir);
void EpClearStall(void *InstancePtr, u8 Epnum, u8 Dir);
s32 EpBufferSend(void *InstancePtr, u8 UsbEp,
			u8 *BufferPtr, u32 BufferLen);
s32 EpBufferRecv(void *InstancePtr, u8 UsbEp,
				u8 *BufferPtr, u32 Length);
void EpSetStall(void *InstancePtr, u8 Epnum, u8 Dir);
void SetBits(void *InstancePtr, u32 TestSel);
s32 SetDeviceAddress(void *InstancePtr, u16 Addr);
s32 SetU1SleepTimeout(void *InstancePtr, u8 Sleep);
s32 SetU2SleepTimeout(void *InstancePtr, u8 Sleep);
s32 AcceptU1U2Sleep(void *InstancePtr);
s32 U1SleepEnable(void *InstancePtr);
s32 U2SleepEnable(void *InstancePtr);
s32 U1SleepDisable(void *InstancePtr);
s32 U2SleepDisable(void *InstancePtr);
s32 EpEnable(void *InstancePtr, u8 UsbEpNum, u8 Dir, u16 Maxsize, u8 Type);
s32 EpDisable(void *InstancePtr, u8 UsbEpNum, u8 Dir);
void Usb_SetSpeed(void *InstancePtr, u32 Speed);
s32 IsSuperSpeed(struct Usb_DevData *InstancePtr);
void SetConfigDone(void *InstancePtr, u8 Flag);
u8 GetConfigDone(void *InstancePtr);
void Ep0StallRestart(void *InstancePtr);
void SetEpInterval(void *InstancePtr, u8 UsbEpNum, u8 Dir, u32 Interval);
void StopTransfer(void *InstancePtr, u8 EpNum, u8 Dir);
s32 StreamOn(void *InstancePtr, u8 EpNum, u8 Dir, u8 *BufferPtr);
void StreamOff(void *InstancePtr, u8 EpNum, u8 Dir);

#endif  /* End of protection macro. */
/** @} */
