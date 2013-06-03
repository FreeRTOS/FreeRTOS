/*
 * @brief USB ROM based core driver functions
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
USBD_HANDLE_T UsbHandle;
/* FIXME Abstract & make this size configurable */
//#define ROMDRIVER_MEM_SIZE	0x1000
//uint8_t usb_RomDriver_buffer[ROMDRIVER_MEM_SIZE] ATTR_ALIGNED(2048) __BSS(USBRAM_SECTION);

ErrorCode_t UsbdRom_Event_Stub (USBD_HANDLE_T hUsb);
PRAGMA_WEAK(USB_Interface_Event,UsbdRom_Event_Stub)
ErrorCode_t USB_Interface_Event (USBD_HANDLE_T hUsb) ATTR_WEAK ATTR_ALIAS(UsbdRom_Event_Stub);
PRAGMA_WEAK(USB_Configure_Event,USB_Configure_Event_Stub)
ErrorCode_t USB_Configure_Event (USBD_HANDLE_T hUsb) ATTR_WEAK ATTR_ALIAS(USB_Configure_Event_Stub);
ErrorCode_t USB_Configure_Event_Stub (USBD_HANDLE_T hUsb)
{
	USB_CORE_CTRL_T* pCtrl = (USB_CORE_CTRL_T*)hUsb;
	uint8_t epnum = CALLBACK_UsbdRom_Register_ConfigureEndpoint();

	if((pCtrl->config_value)&&(epnum!=0))
	{
		USBD_API->hw->WriteEP(hUsb, (epnum + 0x80), usb_RomDriver_buffer, 1);//TODO: what is this for?
	}
	return LPC_OK;
}
void UsbdRom_Init(uint8_t corenum)
{
	ErrorCode_t ret;

	USBD_API_INIT_PARAM_T usb_param =
	{
			.usb_reg_base = ROMDRIVER_USB0_BASE,
			.max_num_ep = ENDPOINT_TOTAL_ENDPOINTS(corenum),
			.mem_base = (uint32_t) usb_RomDriver_buffer,
			.mem_size = ROMDRIVER_MEM_SIZE,
			.USB_Configure_Event = USB_Configure_Event
	};
	USB_CORE_DESCS_T DeviceDes = {NULL};

	if(corenum)
		usb_param.usb_reg_base = ROMDRIVER_USB1_BASE;

	/* add custom Interface Event */
	if(USB_Interface_Event != UsbdRom_Event_Stub)
	{
		usb_param.USB_Interface_Event = USB_Interface_Event;
	}
	DeviceDes.device_desc = (uint8_t*)CALLBACK_UsbdRom_Register_DeviceDescriptor();
	DeviceDes.high_speed_desc = (uint8_t*)CALLBACK_UsbdRom_Register_ConfigurationDescriptor();
	DeviceDes.full_speed_desc = (uint8_t*)CALLBACK_UsbdRom_Register_ConfigurationDescriptor();
	DeviceDes.string_desc = (uint8_t*)CALLBACK_UsbdRom_Register_StringDescriptor();
	DeviceDes.device_qualifier = (uint8_t*)CALLBACK_UsbdRom_Register_DeviceQualifierDescriptor();

	ret = USBD_API->hw->Init(&UsbHandle, &DeviceDes, &usb_param);

	// trap failed initialization
	while(ret != LPC_OK);
}

void UsbdRom_IrqHandler(void)
{
	USBD_API->hw->ISR(UsbHandle);
}

ErrorCode_t UsbdRom_Event_Stub (USBD_HANDLE_T hUsb)
{
	return LPC_OK;
}
#endif /* USB_DEVICE_ROM_DRIVER */

#endif /* USB_CAN_BE_DEVICE */
