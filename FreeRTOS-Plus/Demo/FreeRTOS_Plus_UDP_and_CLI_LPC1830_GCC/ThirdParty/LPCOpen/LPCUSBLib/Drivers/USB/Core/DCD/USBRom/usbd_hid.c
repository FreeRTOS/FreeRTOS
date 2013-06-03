/*
 * @brief USB ROM based HID Class driver functions
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
//#define ROMDRIVER_HID_MEM_SIZE	0x800
//uint8_t usb_RomDriver_HID_buffer[ROMDRIVER_HID_MEM_SIZE] ATTR_ALIGNED(4) __BSS(USBRAM_SECTION);
uint8_t *reportinbuffer;
uint32_t reportinsize;

ErrorCode_t GetReport( USBD_HANDLE_T hHid, USB_SETUP_PACKET* pSetup, uint8_t** pBuffer, uint16_t* plength);
ErrorCode_t GetReport( USBD_HANDLE_T hHid, USB_SETUP_PACKET* pSetup, uint8_t** pBuffer, uint16_t* plength)
{
	uint8_t report[reportinsize];

	if(reportinbuffer == NULL)
		return (LPC_OK);
	memset(report, 0,reportinsize);
	/* ReportID = SetupPacket.wValue.WB.L; */
	switch (pSetup->wValue.WB.H) {
	case HID_REPORT_INPUT:
		if(CALLBACK_UsbdHid_IsReportChanged())
		{
			*pBuffer = reportinbuffer;
			CALLBACK_UsbdHid_SetReportChange(false);
		}
		else
		{
			*pBuffer = report;
		}
		*plength = (uint16_t)reportinsize;
	  break;
	case HID_REPORT_OUTPUT:
	  return (ERR_USBD_STALL);          /* Not Supported */
	case HID_REPORT_FEATURE:
	  return (ERR_USBD_STALL);          /* Not Supported */
	}
	return (LPC_OK);
}
ErrorCode_t SetReport( USBD_HANDLE_T hHid, USB_SETUP_PACKET* pSetup, uint8_t** pBuffer, uint16_t length);
ErrorCode_t SetReport( USBD_HANDLE_T hHid, USB_SETUP_PACKET* pSetup, uint8_t** pBuffer, uint16_t length)
{
  /* we will reuse standard EP0Buf */
  if (length == 0)
    return LPC_OK;
  /* ReportID = SetupPacket.wValue.WB.L; */
  switch (pSetup->wValue.WB.H) {
    case HID_REPORT_INPUT:
      return (ERR_USBD_STALL);          /* Not Supported */
    case HID_REPORT_OUTPUT:
    	CALLBACK_UsbdHid_SetReport(pBuffer,(uint32_t)length);
      break;
    case HID_REPORT_FEATURE:
      return (ERR_USBD_STALL);          /* Not Supported */
  }
  return (LPC_OK);
}
ErrorCode_t EpInHdlr (USBD_HANDLE_T hUsb, void* data, uint32_t event);
ErrorCode_t EpInHdlr (USBD_HANDLE_T hUsb, void* data, uint32_t event)
{
	USB_HID_CTRL_T* pHidCtrl = (USB_HID_CTRL_T*)data;
	uint8_t report[reportinsize];

	if(reportinbuffer == NULL)
		return (LPC_OK);
	memset(report, 0,reportinsize);
	switch (event) {
	case USB_EVT_IN:
		if(CALLBACK_UsbdHid_IsReportChanged())
		{
			USBD_API->hw->WriteEP(hUsb, pHidCtrl->epin_adr, reportinbuffer, reportinsize);
			CALLBACK_UsbdHid_SetReportChange(false);
		}
		else
		{
			USBD_API->hw->WriteEP(hUsb, pHidCtrl->epin_adr, reportinbuffer, reportinsize);
		}
		break;
	}
	return LPC_OK;
}
void UsbdHid_Init(void)
{
	  USBD_HID_INIT_PARAM_T hid_param;
	  USB_HID_REPORT_T reports_data;

	  memset((void*)&hid_param, 0, sizeof(USBD_HID_INIT_PARAM_T));
	  /* Init reports_data */
	  reports_data.len = (uint16_t)CALLBACK_UsbdHid_Register_ReportDescriptor(&reports_data.desc);
	  reports_data.idle_time = 0;
	  /* Init reports buffer */
	  reportinsize = CALLBACK_UsbdHid_Register_ReportInBuffer(&reportinbuffer);

	  /* HID paramas */
	  hid_param.mem_base = (uint32_t)usb_RomDriver_HID_buffer;
	  hid_param.mem_size = (uint32_t)ROMDRIVER_HID_MEM_SIZE;
	  hid_param.max_reports = 1;		//TODO let user configures this number
	  hid_param.intf_desc = (uint8_t*)CALLBACK_UsbdHid_Register_InterfaceDescriptor();
	  hid_param.report_data  = &reports_data;
	  /* user defined functions */
	  hid_param.HID_GetReport = GetReport;
	  hid_param.HID_SetReport = SetReport;
	  hid_param.HID_EpIn_Hdlr = EpInHdlr;

	  USBD_API->hid->init(UsbHandle, &hid_param);
}

#endif /* USB_DEVICE_ROM_DRIVER */

#endif /* USB_CAN_BE_DEVICE */
