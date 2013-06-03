/*
 * @brief USB Configuration Descriptor definitions
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
#include "ConfigDescriptor.h"

#if defined(USB_CAN_BE_HOST)
uint8_t USB_Host_GetDeviceConfigDescriptor(const uint8_t corenum,
										   const uint8_t ConfigNumber,
                                           uint16_t* const ConfigSizePtr,
                                           void* const BufferPtr,
                                           const uint16_t BufferSize)
{
	uint8_t ErrorCode;
	uint8_t ConfigHeader[sizeof(USB_Descriptor_Configuration_Header_t)];
	USB_Descriptor_Configuration_Header_t *pCfgHeader = (USB_Descriptor_Configuration_Header_t*)ConfigHeader;

	USB_ControlRequest = (USB_Request_Header_t)
		{
			.bmRequestType = (REQDIR_DEVICETOHOST | REQTYPE_STANDARD | REQREC_DEVICE),
			.bRequest      = REQ_GetDescriptor,
			.wValue        = ((DTYPE_Configuration << 8) | (ConfigNumber - 1)),
			.wIndex        = 0,
			.wLength       = sizeof(USB_Descriptor_Configuration_Header_t),
		};

	Pipe_SelectPipe(corenum,PIPE_CONTROLPIPE);

	if ((ErrorCode = USB_Host_SendControlRequest(corenum,ConfigHeader)) != HOST_SENDCONTROL_Successful)
	  return ErrorCode;

	*ConfigSizePtr = le16_to_cpu(pCfgHeader->TotalConfigurationSize);

	if (*ConfigSizePtr > BufferSize)
	  return HOST_GETCONFIG_BuffOverflow;

	USB_ControlRequest.wLength = *ConfigSizePtr;

	if ((ErrorCode = USB_Host_SendControlRequest(corenum,BufferPtr)) != HOST_SENDCONTROL_Successful)
	  return ErrorCode;

	if (DESCRIPTOR_TYPE(BufferPtr) != DTYPE_Configuration)
	  return HOST_GETCONFIG_InvalidData;

	return HOST_GETCONFIG_Successful;
}
#endif

void USB_GetNextDescriptorOfType(uint16_t* const BytesRem,
                                 void** const CurrConfigLoc,
                                 const uint8_t Type)
{
	while (*BytesRem)
	{
		USB_GetNextDescriptor(BytesRem, CurrConfigLoc);

		if (DESCRIPTOR_TYPE(*CurrConfigLoc) == Type)
		  return;
	}
}

void USB_GetNextDescriptorOfTypeBefore(uint16_t* const BytesRem,
                                       void** const CurrConfigLoc,
                                       const uint8_t Type,
                                       const uint8_t BeforeType)
{
	while (*BytesRem)
	{
		USB_GetNextDescriptor(BytesRem, CurrConfigLoc);

		if (DESCRIPTOR_TYPE(*CurrConfigLoc) == Type)
		{
			return;
		}
		else if (DESCRIPTOR_TYPE(*CurrConfigLoc) == BeforeType)
		{
			*BytesRem = 0;
			return;
		}
	}
}

void USB_GetNextDescriptorOfTypeAfter(uint16_t* const BytesRem,
                                      void** const CurrConfigLoc,
                                      const uint8_t Type,
                                      const uint8_t AfterType)
{
	USB_GetNextDescriptorOfType(BytesRem, CurrConfigLoc, AfterType);

	if (*BytesRem)
	  USB_GetNextDescriptorOfType(BytesRem, CurrConfigLoc, Type);
}

uint8_t USB_GetNextDescriptorComp(uint16_t* const BytesRem,
                                  void** const CurrConfigLoc,
                                  ConfigComparatorPtr_t const ComparatorRoutine)
{
	uint8_t ErrorCode;

	while (*BytesRem)
	{
		uint8_t* PrevDescLoc  = *CurrConfigLoc;
		uint16_t PrevBytesRem = *BytesRem;

		USB_GetNextDescriptor(BytesRem, CurrConfigLoc);

		if ((ErrorCode = ComparatorRoutine(*CurrConfigLoc)) != DESCRIPTOR_SEARCH_NotFound)
		{
			if (ErrorCode == DESCRIPTOR_SEARCH_Fail)
			{
				*CurrConfigLoc = PrevDescLoc;
				*BytesRem      = PrevBytesRem;
			}

			return ErrorCode;
		}
	}

	return DESCRIPTOR_SEARCH_COMP_EndOfDescriptor;
}

