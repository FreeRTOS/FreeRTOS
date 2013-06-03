/*
 * @brief Boot ROM drivers/library USB Communication Device Class Definitions
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

/** Internal definition */
/* FIXME Abstract & make this size configurable */
//#define ROMDRIVER_CDC_MEM_SIZE	0x800
#define ROMDRIVER_CDC_DATA_BUFFER_SIZE	640
#define CDC_EP_SIZE						(CALLBACK_UsbdCdc_Register_DataOutEndpointSize())
#if (USB_FORCED_FULLSPEED)
	#define CDC_MAX_BULK_EP_SIZE			64
#else
	#define CDC_MAX_BULK_EP_SIZE			512
#endif

/** Circle Buffer Type */
typedef struct {
	uint8_t data[ROMDRIVER_CDC_DATA_BUFFER_SIZE];
	volatile uint32_t rd_index;
	volatile uint32_t wr_index;
	volatile uint32_t count;
} CDC_CIRCLE_BUFFER_T;

//uint8_t usb_RomDriver_CDC_buffer[ROMDRIVER_CDC_MEM_SIZE] ATTR_ALIGNED(4) __BSS(USBRAM_SECTION);
CDC_LINE_CODING* UsbdCdcLineCoding;
USBD_HANDLE_T UsbdCdcHdlr;				//what is this for?

/** Endpoint IN buffer, used for DMA operation */
//uint8_t UsbdCdc_EPIN_buffer[CDC_MAX_BULK_EP_SIZE] ATTR_ALIGNED(4) __BSS(USBRAM_SECTION);
volatile uint32_t UsbdCdc_EPIN_buffer_count = 0;
/** Endpoint OUT buffer, used for DMA operation */
//uint8_t UsbdCdc_EPOUT_buffer[CDC_MAX_BULK_EP_SIZE] ATTR_ALIGNED(4) __BSS(USBRAM_SECTION);
volatile uint32_t UsbdCdc_EPOUT_buffer_index = 0;
volatile uint32_t UsbdCdc_EPOUT_buffer_count = 0;

CDC_CIRCLE_BUFFER_T UsbdCdc_OUT_buffer, UsbdCdc_IN_buffer;

ErrorCode_t UsbdCdc_Bulk_OUT_Hdlr(USBD_HANDLE_T hUsb, void* data, uint32_t event);
ErrorCode_t UsbdCdc_Bulk_IN_Hdlr(USBD_HANDLE_T hUsb, void* data, uint32_t event);

void UsbdCdc_OUT_Buffer_Reset(void)
{
	UsbdCdc_OUT_buffer.rd_index = 0;
	UsbdCdc_OUT_buffer.wr_index = 0;
	UsbdCdc_OUT_buffer.count = 0;
}

void UsbdCdc_IN_Buffer_Reset(void)
{
	UsbdCdc_IN_buffer.rd_index = 0;
	UsbdCdc_IN_buffer.wr_index = 0;
	UsbdCdc_IN_buffer.count = 0;
}

PRAGMA_WEAK(EVENT_UsbdCdc_SetLineCode,EVENT_UsbdCdc_SetLineCode_Stub)
void EVENT_UsbdCdc_SetLineCode(CDC_LINE_CODING* line_coding) ATTR_WEAK ATTR_ALIAS(EVENT_UsbdCdc_SetLineCode_Stub);

/** Set Line Coding Handler */
ErrorCode_t CALLBACK_UsbdCdc_SetLineCode(USBD_HANDLE_T hCDC, CDC_LINE_CODING* line_coding)
{
	memcpy(UsbdCdcLineCoding, line_coding, sizeof(CDC_LINE_CODING));
	EVENT_UsbdCdc_SetLineCode(line_coding);
	return LPC_OK;
}

/** Initialize USBD CDC driver */
void UsbdCdc_Init(void)
{
	USBD_CDC_INIT_PARAM_T cdc_param;
	uint32_t ep_indx;
	memset((void*)&cdc_param, 0, sizeof(USBD_CDC_INIT_PARAM_T));
	UsbdCdcLineCoding = (CDC_LINE_CODING*)CALLBACK_UsbdCdc_Register_LineCoding();

	/* CDC paramas */
	cdc_param.mem_base = (uint32_t)usb_RomDriver_CDC_buffer;
	cdc_param.mem_size = (uint32_t)ROMDRIVER_CDC_MEM_SIZE;
	cdc_param.cif_intf_desc = (uint8_t*)CALLBACK_UsbdCdc_Register_ControlInterfaceDescriptor();
	cdc_param.dif_intf_desc = (uint8_t*)CALLBACK_UsbdCdc_Register_DataInterfaceDescriptor();
	/* user defined functions */
	cdc_param.SetLineCode = CALLBACK_UsbdCdc_SetLineCode;

	/* register Bulk IN endpoint interrupt handler */
	ep_indx = (((CALLBACK_UsbdCdc_Register_DataInEndpointNumber() & 0x0F) << 1) + 1);
	USBD_API->core->RegisterEpHandler (UsbHandle, ep_indx, UsbdCdc_Bulk_IN_Hdlr, NULL);
	
	/* register Bulk OUT endpoint interrupt handler */
	ep_indx = ((CALLBACK_UsbdCdc_Register_DataOutEndpointNumber() & 0x0F) << 1);
	USBD_API->core->RegisterEpHandler (UsbHandle, ep_indx, UsbdCdc_Bulk_OUT_Hdlr, NULL);

	UsbdCdc_OUT_Buffer_Reset();
	UsbdCdc_IN_Buffer_Reset();
	USBD_API->cdc->init(UsbHandle, &cdc_param, &UsbdCdcHdlr);
}


/** This is blocking send function */
void UsbdCdc_SendData(uint8_t* buffer, uint32_t cnt)
{
	uint32_t buffer_index = 0;
	//uint8_t EpAdd = USB_ENDPOINT_IN(CALLBACK_UsbdCdc_Register_DataInEndpointNumber());
	while(cnt)
	{
		if(UsbdCdc_IN_buffer.count <= ROMDRIVER_CDC_DATA_BUFFER_SIZE)
		{
			UsbdCdc_IN_buffer.data[UsbdCdc_IN_buffer.wr_index] = buffer[buffer_index++];
			UsbdCdc_IN_buffer.wr_index++;
			UsbdCdc_IN_buffer.wr_index &= (ROMDRIVER_CDC_DATA_BUFFER_SIZE -1);
			UsbdCdc_IN_buffer.count++;
			cnt--;
		}
	}
}

/** Receive data to user buffer */
uint32_t UsbdCdc_RecvData(uint8_t* buffer, uint32_t len)
{
	uint32_t avail_len, i;
	if(UsbdCdc_OUT_buffer.count > len)
	{
		avail_len = len;
	}else
	{
		avail_len = UsbdCdc_OUT_buffer.count;
	}
	for(i=0; i<avail_len;i++)
	{
		buffer[i] = UsbdCdc_OUT_buffer.data[UsbdCdc_OUT_buffer.rd_index];
		UsbdCdc_OUT_buffer.rd_index++;
		UsbdCdc_OUT_buffer.rd_index &= (ROMDRIVER_CDC_DATA_BUFFER_SIZE - 1);
		UsbdCdc_OUT_buffer.count--;
	}
	return avail_len;
}

/** sync EP buffer(DMA) and CDC driver IO buffer */
void UsbdCdc_IO_Buffer_Sync_Task(void)
{
	uint32_t avail_count, i;

	/* Sync OUT EP task */
	avail_count = ROMDRIVER_CDC_DATA_BUFFER_SIZE - UsbdCdc_OUT_buffer.count;
	if(avail_count > UsbdCdc_EPOUT_buffer_count)
	{
		avail_count = UsbdCdc_EPOUT_buffer_count;
	}
	for(i=0; i<avail_count; i++)
	{
                uint8_t t = UsbdCdc_EPOUT_buffer[UsbdCdc_EPOUT_buffer_index];
		UsbdCdc_OUT_buffer.data[UsbdCdc_OUT_buffer.wr_index] = t;
		UsbdCdc_EPOUT_buffer_index++;

		UsbdCdc_OUT_buffer.count++;
		UsbdCdc_OUT_buffer.wr_index++;
		UsbdCdc_OUT_buffer.wr_index &= (ROMDRIVER_CDC_DATA_BUFFER_SIZE - 1);
		/* Sync 2 buffers must be implemented when all other tasks completed */
		UsbdCdc_EPOUT_buffer_count--;
	}

	/* Sync IN EP task */
	if(UsbdCdc_EPIN_buffer_count == 0){
		if(UsbdCdc_IN_buffer.count > CDC_EP_SIZE)
		{
			avail_count = CDC_EP_SIZE;
		}else
		{
			avail_count = UsbdCdc_IN_buffer.count;
		}
	
		for(i=0; i<avail_count; i++)
		{
			UsbdCdc_EPIN_buffer[i] = UsbdCdc_IN_buffer.data[UsbdCdc_IN_buffer.rd_index];
			UsbdCdc_IN_buffer.rd_index++;
			UsbdCdc_IN_buffer.rd_index &= (ROMDRIVER_CDC_DATA_BUFFER_SIZE - 1);
			UsbdCdc_IN_buffer.count --;
		}
		/* Sync 2 buffers must be implemented when all other tasks completed */
		UsbdCdc_EPIN_buffer_count = avail_count;
	}
}

ErrorCode_t UsbdCdc_Bulk_OUT_Hdlr(USBD_HANDLE_T hUsb, void* data, uint32_t event)
{
	uint8_t EpAdd = USB_ENDPOINT_OUT(CALLBACK_UsbdCdc_Register_DataOutEndpointNumber());
	if (event == USB_EVT_OUT)
	{
		UsbdCdc_EPOUT_buffer_count = USBD_API->hw->ReadEP(UsbHandle, EpAdd, UsbdCdc_EPOUT_buffer);
	}
	else if(event == USB_EVT_OUT_NAK)
	{
		if(UsbdCdc_EPOUT_buffer_count == 0)
		{
			/* Reset EP OUT buffer */
			UsbdCdc_EPOUT_buffer_index = 0;
			/* Send DMA request */
			USBD_API->hw->ReadReqEP(UsbHandle, EpAdd, UsbdCdc_EPOUT_buffer, CDC_EP_SIZE);
		}
	}
	return LPC_OK;
}

ErrorCode_t UsbdCdc_Bulk_IN_Hdlr(USBD_HANDLE_T hUsb, void* data, uint32_t event)
{
	uint8_t EpAdd = USB_ENDPOINT_IN(CALLBACK_UsbdCdc_Register_DataInEndpointNumber());
	
	if (event == USB_EVT_IN)
	{
		USBD_API->hw->WriteEP(UsbHandle, EpAdd, UsbdCdc_EPIN_buffer,UsbdCdc_EPIN_buffer_count);
		/* Clear EP buffer */
		UsbdCdc_EPIN_buffer_count = 0;
	}
	return LPC_OK;
}

void UsbdCdc_EVENT_Stub(void* param)
{

}
void EVENT_UsbdCdc_SetLineCode_Stub(CDC_LINE_CODING* line_coding)
{

}
#endif /* USB_DEVICE_ROM_DRIVER */

#endif /* USB_CAN_BE_DEVICE */
