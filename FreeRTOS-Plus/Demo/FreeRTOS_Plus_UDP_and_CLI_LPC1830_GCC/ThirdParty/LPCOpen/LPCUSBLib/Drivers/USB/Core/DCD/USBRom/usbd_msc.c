/*
 * @brief USB ROM based MSC Class driver functions
 *
 * @note
 * Copyright(C) NXP Semiconductors, 2012
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
#include "../../USBMode.h"

#if defined(USB_CAN_BE_DEVICE)
#include "../../Device.h"
#include "../../Endpoint.h"

#if defined(USB_DEVICE_ROM_DRIVER)

/* FIXME Abstract & make this size configurable */
//#define ROMDRIVER_MSC_MEM_SIZE	0x1000
//uint8_t usb_RomDriver_MSC_buffer[ROMDRIVER_MSC_MEM_SIZE] ATTR_ALIGNED(4) __BSS(USBRAM_SECTION);

void UsbdMsc_Init(void)
{
	USBD_MSC_INIT_PARAM_T msc_param =
	{
			/* mass storage paramas */
			.InquiryStr = (uint8_t*) CALLBACK_UsbdMsc_Register_InquiryData(),

			.BlockCount = CALLBACK_UsbdMsc_Register_BlockCount(),
			.BlockSize = CALLBACK_UsbdMsc_Register_BlockSize(),
			.MemorySize = CALLBACK_UsbdMsc_Register_MemorySize(),

			.intf_desc = (uint8_t*) CALLBACK_UsbdMsc_Register_InterfaceDescriptor(),

			/* user defined functions */
			.MSC_Write = (void(*)(uint32_t,uint8_t**,uint32_t))CALLBACK_UsbdMsc_Register_MSCWrite(),
			.MSC_Read = (void(*)(uint32_t,uint8_t**,uint32_t))CALLBACK_UsbdMsc_Register_MSCRead(),
			.MSC_Verify = (ErrorCode_t(*)(uint32_t,uint8_t*,uint32_t))CALLBACK_UsbdMsc_Register_MSCVerify(),
			.MSC_GetWriteBuf = (void(*)(uint32_t,uint8_t**,uint32_t))CALLBACK_UsbdMsc_Register_MSCGetWriteBuf(),

			.mem_base = (uint32_t) usb_RomDriver_MSC_buffer,
			.mem_size = ROMDRIVER_MSC_MEM_SIZE
	};
	USBD_API->msc->init(UsbHandle, &msc_param);
}

#endif /* USB_DEVICE_ROM_DRIVER */

#endif /* USB_CAN_BE_DEVICE */
