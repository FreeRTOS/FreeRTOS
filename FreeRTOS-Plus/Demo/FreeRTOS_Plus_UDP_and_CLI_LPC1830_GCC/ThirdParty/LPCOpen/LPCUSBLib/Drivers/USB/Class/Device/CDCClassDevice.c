/*
 * @brief Device mode driver for the library USB CDC Class driver
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


#define  __INCLUDE_FROM_USB_DRIVER
#include "../../Core/USBMode.h"

#if defined(USB_CAN_BE_DEVICE)

#define  __INCLUDE_FROM_CDC_DRIVER
#define  __INCLUDE_FROM_CDC_DEVICE_C
#include "CDCClassDevice.h"

void CDC_Device_ProcessControlRequest(USB_ClassInfo_CDC_Device_t* const CDCInterfaceInfo)
{
	if (!(Endpoint_IsSETUPReceived(CDCInterfaceInfo->Config.PortNumber)))
	  return;

	if (USB_ControlRequest.wIndex != CDCInterfaceInfo->Config.ControlInterfaceNumber)
	  return;

	switch (USB_ControlRequest.bRequest)
	{
		case CDC_REQ_GetLineEncoding:
			if (USB_ControlRequest.bmRequestType == (REQDIR_DEVICETOHOST | REQTYPE_CLASS | REQREC_INTERFACE))
			{
				Endpoint_ClearSETUP(CDCInterfaceInfo->Config.PortNumber);

				while (!(Endpoint_IsINReady(CDCInterfaceInfo->Config.PortNumber)));

				Endpoint_Write_32_LE(CDCInterfaceInfo->Config.PortNumber, CDCInterfaceInfo->State.LineEncoding.BaudRateBPS);
				Endpoint_Write_8(CDCInterfaceInfo->Config.PortNumber, CDCInterfaceInfo->State.LineEncoding.CharFormat);
				Endpoint_Write_8(CDCInterfaceInfo->Config.PortNumber, CDCInterfaceInfo->State.LineEncoding.ParityType);
				Endpoint_Write_8(CDCInterfaceInfo->Config.PortNumber, CDCInterfaceInfo->State.LineEncoding.DataBits);

				Endpoint_ClearIN(CDCInterfaceInfo->Config.PortNumber);
				Endpoint_ClearStatusStage(CDCInterfaceInfo->Config.PortNumber);
			}

			break;
		case CDC_REQ_SetLineEncoding:
			if (USB_ControlRequest.bmRequestType == (REQDIR_HOSTTODEVICE | REQTYPE_CLASS | REQREC_INTERFACE))
			{
				Endpoint_ClearSETUP(CDCInterfaceInfo->Config.PortNumber);

				while (!(Endpoint_IsOUTReceived(CDCInterfaceInfo->Config.PortNumber)));

				CDCInterfaceInfo->State.LineEncoding.BaudRateBPS = Endpoint_Read_32_LE(CDCInterfaceInfo->Config.PortNumber);
				CDCInterfaceInfo->State.LineEncoding.CharFormat  = Endpoint_Read_8(CDCInterfaceInfo->Config.PortNumber);
				CDCInterfaceInfo->State.LineEncoding.ParityType  = Endpoint_Read_8(CDCInterfaceInfo->Config.PortNumber);
				CDCInterfaceInfo->State.LineEncoding.DataBits    = Endpoint_Read_8(CDCInterfaceInfo->Config.PortNumber);

				Endpoint_ClearOUT(CDCInterfaceInfo->Config.PortNumber);
				Endpoint_ClearStatusStage(CDCInterfaceInfo->Config.PortNumber);

				EVENT_CDC_Device_LineEncodingChanged(CDCInterfaceInfo);
			}

			break;
		case CDC_REQ_SetControlLineState:
			if (USB_ControlRequest.bmRequestType == (REQDIR_HOSTTODEVICE | REQTYPE_CLASS | REQREC_INTERFACE))
			{
				Endpoint_ClearSETUP(CDCInterfaceInfo->Config.PortNumber);
				Endpoint_ClearStatusStage(CDCInterfaceInfo->Config.PortNumber);

				CDCInterfaceInfo->State.ControlLineStates.HostToDevice = USB_ControlRequest.wValue;

				EVENT_CDC_Device_ControLineStateChanged(CDCInterfaceInfo);
			}

			break;
		case CDC_REQ_SendBreak:
			if (USB_ControlRequest.bmRequestType == (REQDIR_HOSTTODEVICE | REQTYPE_CLASS | REQREC_INTERFACE))
			{
				Endpoint_ClearSETUP(CDCInterfaceInfo->Config.PortNumber);
				Endpoint_ClearStatusStage(CDCInterfaceInfo->Config.PortNumber);

				EVENT_CDC_Device_BreakSent(CDCInterfaceInfo, (uint8_t)USB_ControlRequest.wValue);
			}

			break;
	}
}

bool CDC_Device_ConfigureEndpoints(USB_ClassInfo_CDC_Device_t* const CDCInterfaceInfo)
{
	memset(&CDCInterfaceInfo->State, 0x00, sizeof(CDCInterfaceInfo->State));

	for (uint8_t EndpointNum = 1; EndpointNum < ENDPOINT_TOTAL_ENDPOINTS(CDCInterfaceInfo->Config.PortNumber); EndpointNum++)
	{
		uint16_t Size;
		uint8_t  Type;
		uint8_t  Direction;
		bool     DoubleBanked;

		if (EndpointNum == CDCInterfaceInfo->Config.DataINEndpointNumber)
		{
			Size         = CDCInterfaceInfo->Config.DataINEndpointSize;
			Direction    = ENDPOINT_DIR_IN;
			Type         = EP_TYPE_BULK;
			DoubleBanked = CDCInterfaceInfo->Config.DataINEndpointDoubleBank;
		}
		else if (EndpointNum == CDCInterfaceInfo->Config.DataOUTEndpointNumber)
		{
			Size         = CDCInterfaceInfo->Config.DataOUTEndpointSize;
			Direction    = ENDPOINT_DIR_OUT;
			Type         = EP_TYPE_BULK;
			DoubleBanked = CDCInterfaceInfo->Config.DataOUTEndpointDoubleBank;
		}
		else if (EndpointNum == CDCInterfaceInfo->Config.NotificationEndpointNumber)
		{
			Size         = CDCInterfaceInfo->Config.NotificationEndpointSize;
			Direction    = ENDPOINT_DIR_IN;
			Type         = EP_TYPE_INTERRUPT;
			DoubleBanked = CDCInterfaceInfo->Config.NotificationEndpointDoubleBank;
		}
		else
		{
			continue;
		}

		if (!(Endpoint_ConfigureEndpoint(CDCInterfaceInfo->Config.PortNumber, EndpointNum, Type, Direction, Size,
		                                 DoubleBanked ? ENDPOINT_BANK_DOUBLE : ENDPOINT_BANK_SINGLE)))
		{
			return false;
		}
	}

	return true;
}

void CDC_Device_USBTask(USB_ClassInfo_CDC_Device_t* const CDCInterfaceInfo)
{
	if ((USB_DeviceState[CDCInterfaceInfo->Config.PortNumber] != DEVICE_STATE_Configured) || !(CDCInterfaceInfo->State.LineEncoding.BaudRateBPS))
	  return;

	#if !defined(NO_CLASS_DRIVER_AUTOFLUSH)
	CDC_Device_Flush(CDCInterfaceInfo);
	#endif
}

uint8_t CDC_Device_SendString(USB_ClassInfo_CDC_Device_t* const CDCInterfaceInfo,
                              const char* const String)
{
	if ((USB_DeviceState[CDCInterfaceInfo->Config.PortNumber] != DEVICE_STATE_Configured) || !(CDCInterfaceInfo->State.LineEncoding.BaudRateBPS))
	  return ENDPOINT_RWSTREAM_DeviceDisconnected;

	Endpoint_SelectEndpoint(CDCInterfaceInfo->Config.PortNumber, CDCInterfaceInfo->Config.DataINEndpointNumber);
	Endpoint_Write_Stream_LE(CDCInterfaceInfo->Config.PortNumber, String, strlen(String), NULL);
	Endpoint_ClearIN(CDCInterfaceInfo->Config.PortNumber);
	return ENDPOINT_RWSTREAM_NoError;
}

uint8_t CDC_Device_SendData(USB_ClassInfo_CDC_Device_t* const CDCInterfaceInfo,
                            const char* const Buffer,
                            const uint16_t Length)
{
	if ((USB_DeviceState[CDCInterfaceInfo->Config.PortNumber] != DEVICE_STATE_Configured) || !(CDCInterfaceInfo->State.LineEncoding.BaudRateBPS))
	  return ENDPOINT_RWSTREAM_DeviceDisconnected;

	Endpoint_SelectEndpoint(CDCInterfaceInfo->Config.PortNumber, CDCInterfaceInfo->Config.DataINEndpointNumber);
	Endpoint_Write_Stream_LE(CDCInterfaceInfo->Config.PortNumber, Buffer, Length, NULL);
	Endpoint_ClearIN(CDCInterfaceInfo->Config.PortNumber);
	return ENDPOINT_RWSTREAM_NoError;
}

uint8_t CDC_Device_SendByte(USB_ClassInfo_CDC_Device_t* const CDCInterfaceInfo,
                            const uint8_t Data)
{
	if ((USB_DeviceState[CDCInterfaceInfo->Config.PortNumber] != DEVICE_STATE_Configured) || !(CDCInterfaceInfo->State.LineEncoding.BaudRateBPS))
	  return ENDPOINT_RWSTREAM_DeviceDisconnected;

	Endpoint_SelectEndpoint(CDCInterfaceInfo->Config.PortNumber, CDCInterfaceInfo->Config.DataINEndpointNumber);

	if (!(Endpoint_IsReadWriteAllowed(CDCInterfaceInfo->Config.PortNumber)))
	{
		Endpoint_ClearIN(CDCInterfaceInfo->Config.PortNumber);

		uint8_t ErrorCode;

		if ((ErrorCode = Endpoint_WaitUntilReady()) != ENDPOINT_READYWAIT_NoError)
		  return ErrorCode;
	}

	Endpoint_Write_8(CDCInterfaceInfo->Config.PortNumber, Data);
	return ENDPOINT_READYWAIT_NoError;
}

uint8_t CDC_Device_Flush(USB_ClassInfo_CDC_Device_t* const CDCInterfaceInfo)
{
	if ((USB_DeviceState[CDCInterfaceInfo->Config.PortNumber] != DEVICE_STATE_Configured) || !(CDCInterfaceInfo->State.LineEncoding.BaudRateBPS))
	  return ENDPOINT_RWSTREAM_DeviceDisconnected;

	uint8_t ErrorCode;

	Endpoint_SelectEndpoint(CDCInterfaceInfo->Config.PortNumber, CDCInterfaceInfo->Config.DataINEndpointNumber);

	if (!(Endpoint_BytesInEndpoint(CDCInterfaceInfo->Config.PortNumber)))
	  return ENDPOINT_READYWAIT_NoError;

	bool BankFull = !(Endpoint_IsReadWriteAllowed(CDCInterfaceInfo->Config.PortNumber));

	Endpoint_ClearIN(CDCInterfaceInfo->Config.PortNumber);

	if (BankFull)
	{
		if ((ErrorCode = Endpoint_WaitUntilReady()) != ENDPOINT_READYWAIT_NoError)
		  return ErrorCode;

		Endpoint_ClearIN(CDCInterfaceInfo->Config.PortNumber);
	}

	return ENDPOINT_READYWAIT_NoError;
}

uint16_t CDC_Device_BytesReceived(USB_ClassInfo_CDC_Device_t* const CDCInterfaceInfo)
{
	if ((USB_DeviceState[CDCInterfaceInfo->Config.PortNumber] != DEVICE_STATE_Configured) || !(CDCInterfaceInfo->State.LineEncoding.BaudRateBPS))
	  return 0;

	Endpoint_SelectEndpoint(CDCInterfaceInfo->Config.PortNumber, CDCInterfaceInfo->Config.DataOUTEndpointNumber);

	if (Endpoint_IsOUTReceived(CDCInterfaceInfo->Config.PortNumber))
	{
		if (!(Endpoint_BytesInEndpoint(CDCInterfaceInfo->Config.PortNumber)))
		{
			Endpoint_ClearOUT(CDCInterfaceInfo->Config.PortNumber);
			return 0;
		}
		else
		{
			return Endpoint_BytesInEndpoint(CDCInterfaceInfo->Config.PortNumber);
		}
	}
	else
	{
		return 0;
	}
}

int16_t CDC_Device_ReceiveByte(USB_ClassInfo_CDC_Device_t* const CDCInterfaceInfo)
{
	if ((USB_DeviceState[CDCInterfaceInfo->Config.PortNumber] != DEVICE_STATE_Configured) || !(CDCInterfaceInfo->State.LineEncoding.BaudRateBPS))
	  return -1;

	int16_t ReceivedByte = -1;

	Endpoint_SelectEndpoint(CDCInterfaceInfo->Config.PortNumber, CDCInterfaceInfo->Config.DataOUTEndpointNumber);

	if (Endpoint_IsOUTReceived(CDCInterfaceInfo->Config.PortNumber))
	{
		if (Endpoint_BytesInEndpoint(CDCInterfaceInfo->Config.PortNumber)){
		  ReceivedByte = Endpoint_Read_8(CDCInterfaceInfo->Config.PortNumber);
		//Endpoint_ClearOUT();
		}

		if (!(Endpoint_BytesInEndpoint(CDCInterfaceInfo->Config.PortNumber)))
		  Endpoint_ClearOUT(CDCInterfaceInfo->Config.PortNumber);
	}

	return ReceivedByte;
}

void CDC_Device_SendControlLineStateChange(USB_ClassInfo_CDC_Device_t* const CDCInterfaceInfo)
{
	if ((USB_DeviceState[CDCInterfaceInfo->Config.PortNumber] != DEVICE_STATE_Configured) || !(CDCInterfaceInfo->State.LineEncoding.BaudRateBPS))
	  return;

	Endpoint_SelectEndpoint(CDCInterfaceInfo->Config.PortNumber, CDCInterfaceInfo->Config.NotificationEndpointNumber);

	USB_Request_Header_t Notification = (USB_Request_Header_t)
		{
			.bmRequestType = (REQDIR_DEVICETOHOST | REQTYPE_CLASS | REQREC_INTERFACE),
			.bRequest      = CDC_NOTIF_SerialState,
			.wValue        = CPU_TO_LE16(0),
			.wIndex        = CPU_TO_LE16(0),
			.wLength       = CPU_TO_LE16(sizeof(CDCInterfaceInfo->State.ControlLineStates.DeviceToHost)),
		};

	Endpoint_Write_Stream_LE(CDCInterfaceInfo->Config.PortNumber, &Notification, sizeof(USB_Request_Header_t), NULL);
	Endpoint_Write_Stream_LE(CDCInterfaceInfo->Config.PortNumber, &CDCInterfaceInfo->State.ControlLineStates.DeviceToHost,
	                         sizeof(CDCInterfaceInfo->State.ControlLineStates.DeviceToHost),
	                         NULL);
	Endpoint_ClearIN(CDCInterfaceInfo->Config.PortNumber);
}

#if (defined(FDEV_SETUP_STREAM) && (!defined(__IAR_SYSTEMS_ICC__) || (_DLIB_FILE_DESCRIPTOR == 1)))
void CDC_Device_CreateStream(USB_ClassInfo_CDC_Device_t* const CDCInterfaceInfo,
                             FILE* const Stream)
{
	*Stream = (FILE)FDEV_SETUP_STREAM(CDC_Device_putchar, CDC_Device_getchar, _FDEV_SETUP_RW);
	fdev_set_udata(Stream, CDCInterfaceInfo);
}

void CDC_Device_CreateBlockingStream(USB_ClassInfo_CDC_Device_t* const CDCInterfaceInfo,
                                     FILE* const Stream)
{
	*Stream = (FILE)FDEV_SETUP_STREAM(CDC_Device_putchar, CDC_Device_getchar_Blocking, _FDEV_SETUP_RW);
	fdev_set_udata(Stream, CDCInterfaceInfo);
}

static int CDC_Device_putchar(char c,
                              FILE* Stream)
{
	return CDC_Device_SendByte((USB_ClassInfo_CDC_Device_t*)fdev_get_udata(Stream), c) ? _FDEV_ERR : 0;
}

static int CDC_Device_getchar(FILE* Stream)
{
	int16_t ReceivedByte = CDC_Device_ReceiveByte((USB_ClassInfo_CDC_Device_t*)fdev_get_udata(Stream));

	if (ReceivedByte < 0)
	  return _FDEV_EOF;

	return ReceivedByte;
}

static int CDC_Device_getchar_Blocking(FILE* Stream)
{
	int16_t ReceivedByte;

	while ((ReceivedByte = CDC_Device_ReceiveByte((USB_ClassInfo_CDC_Device_t*)fdev_get_udata(Stream))) < 0)
	{
		if (USB_DeviceState[corenum] == DEVICE_STATE_Unattached)
		  return _FDEV_EOF;

		CDC_Device_USBTask((USB_ClassInfo_CDC_Device_t*)fdev_get_udata(Stream));
		USB_USBTask();
	}

	return ReceivedByte;
}
#endif

void CDC_Device_Event_Stub(USB_ClassInfo_CDC_Device_t* const CDCInterfaceInfo)
{

}

void CDC_Device_Event_Stub2(USB_ClassInfo_CDC_Device_t* const CDCInterfaceInfo, const uint8_t Duration)
{
}
#endif

