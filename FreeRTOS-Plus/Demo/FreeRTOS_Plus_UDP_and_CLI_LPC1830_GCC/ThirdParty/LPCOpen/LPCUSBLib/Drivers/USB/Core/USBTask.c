/*
 * @brief Main USB service task management
 *
 * @note
 * Copyright(C) NXP Semiconductors, 2012
 * Copyright(C) Dean Camera, 2011, 2012
 * All rights reserved.
 *
 * @par
 * Software that is described herein is for illustrative purposes only
 * which provides customers with programming information regarding the
 * LPC products.  This software is supplied "AS IS" without any warranties of
 * any kind, and NXP Semiconductors and its licensor disclaim any and
 * all warranties, express or implied, including all implied warranties of
 * merchantability, fitness for a particular purpose and non-infringement of
 * intellectual property rights.  NXP Semiconductors assumes no responsibility
 * or liability for the use of the software, conveys no license or rights under any
 * patent, copyright, mask work right, or any other intellectual property rights in
 * or to any products. NXP Semiconductors reserves the right to make changes
 * in the software without notification. NXP Semiconductors also makes no
 * representation or warranty that such application will be suitable for the
 * specified use without further testing or modification.
 *
 * @par
 * Permission to use, copy, modify, and distribute this software and its
 * documentation is hereby granted, under NXP Semiconductors' and its
 * licensor's relevant copyrights in the software, without fee, provided that it
 * is used in conjunction with NXP Semiconductors microcontrollers.  This
 * copyright, permission, and disclaimer notice must appear in all copies of
 * this code.
 */


#define  __INCLUDE_FROM_USBTASK_C
#define  __INCLUDE_FROM_USB_DRIVER
#include "USBTask.h"

volatile bool        USB_IsInitialized;

/* This structure must be 4 bytes aligned */
PRAGMA_ALIGN_4
USB_Request_Header_t USB_ControlRequest ATTR_ALIGNED(4) __BSS(USBRAM_SECTION);

#if defined(USB_CAN_BE_HOST) && !defined(HOST_STATE_AS_GPIOR)
volatile uint8_t     USB_HostState[MAX_USB_CORE];
#endif

#if defined(USB_CAN_BE_DEVICE) && !defined(DEVICE_STATE_AS_GPIOR)
volatile uint8_t     USB_DeviceState[MAX_USB_CORE];
#endif

void USB_USBTask(uint8_t corenum, uint8_t mode)
{
	#if defined(USB_HOST_ONLY)
 		USB_HostTask(corenum);
	#elif defined(USB_DEVICE_ONLY)
 		USB_DeviceTask(corenum);
	#else
			if (mode == USB_MODE_Device)
				USB_DeviceTask(corenum);
			else if (mode == USB_MODE_Host)
				USB_HostTask(corenum);
	#endif
}

#if defined(USB_CAN_BE_DEVICE)
static void USB_DeviceTask(uint8_t corenum)
{
	if (USB_DeviceState[corenum] != DEVICE_STATE_Unattached)
	{
		uint8_t PrevEndpoint = Endpoint_GetCurrentEndpoint(corenum);

		Endpoint_SelectEndpoint(corenum, ENDPOINT_CONTROLEP);

		if (Endpoint_IsSETUPReceived(corenum))
		  USB_Device_ProcessControlRequest(corenum);

		Endpoint_SelectEndpoint(corenum, PrevEndpoint);
	}
}
#endif

#if defined(USB_CAN_BE_HOST)
static void USB_HostTask(uint8_t corenum)
{

	uint8_t PrevPipe;

	PrevPipe = Pipe_GetCurrentPipe(corenum);
	Pipe_SelectPipe(corenum,PIPE_CONTROLPIPE);
	USB_Host_ProcessNextHostState(corenum);
	Pipe_SelectPipe(corenum,PrevPipe);
}
#endif

