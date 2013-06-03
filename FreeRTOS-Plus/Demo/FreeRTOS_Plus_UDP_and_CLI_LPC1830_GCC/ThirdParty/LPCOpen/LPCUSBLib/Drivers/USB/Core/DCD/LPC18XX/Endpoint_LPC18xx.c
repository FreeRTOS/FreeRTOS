/*
 * @brief USB Endpoint definitions for the LPC18xx microcontrollers
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

#if (defined(__LPC18XX__) || defined(__LPC43XX__)) && defined(USB_CAN_BE_DEVICE)
#include "../../Endpoint.h"
#include <string.h>

#if defined(USB_DEVICE_ROM_DRIVER)
PRAGMA_ALIGN_2048
uint8_t usb_RomDriver_buffer[ROMDRIVER_MEM_SIZE] ATTR_ALIGNED(2048) __BSS(USBRAM_SECTION);
PRAGMA_ALIGN_4
uint8_t usb_RomDriver_MSC_buffer[ROMDRIVER_MSC_MEM_SIZE] ATTR_ALIGNED(4) __BSS(USBRAM_SECTION);
PRAGMA_ALIGN_4
uint8_t usb_RomDriver_CDC_buffer[ROMDRIVER_CDC_MEM_SIZE] ATTR_ALIGNED(4) __BSS(USBRAM_SECTION);
/** Endpoint IN buffer, used for DMA operation */
PRAGMA_ALIGN_4
uint8_t UsbdCdc_EPIN_buffer[CDC_MAX_BULK_EP_SIZE] ATTR_ALIGNED(4) __BSS(USBRAM_SECTION);
/** Endpoint OUT buffer, used for DMA operation */
PRAGMA_ALIGN_4
uint8_t UsbdCdc_EPOUT_buffer[CDC_MAX_BULK_EP_SIZE] ATTR_ALIGNED(4) __BSS(USBRAM_SECTION);
PRAGMA_ALIGN_4
uint8_t usb_RomDriver_HID_buffer[ROMDRIVER_HID_MEM_SIZE] ATTR_ALIGNED(4) __BSS(USBRAM_SECTION);

#endif

#define STREAM_TDs      16

PRAGMA_ALIGN_2048
volatile DeviceQueueHead dQueueHead0[USED_PHYSICAL_ENDPOINTS0] ATTR_ALIGNED(2048) __BSS(USBRAM_SECTION);
PRAGMA_ALIGN_2048
volatile DeviceQueueHead dQueueHead1[USED_PHYSICAL_ENDPOINTS1] ATTR_ALIGNED(2048) __BSS(USBRAM_SECTION);
PRAGMA_ALIGN_32
DeviceTransferDescriptor dTransferDescriptor0[USED_PHYSICAL_ENDPOINTS0] ATTR_ALIGNED(32) __BSS(USBRAM_SECTION);
PRAGMA_ALIGN_32
DeviceTransferDescriptor dTransferDescriptor1[USED_PHYSICAL_ENDPOINTS1] ATTR_ALIGNED(32) __BSS(USBRAM_SECTION);
PRAGMA_ALIGN_32
DeviceTransferDescriptor dStreamTD0[STREAM_TDs] ATTR_ALIGNED(32) __BSS(USBRAM_SECTION);
PRAGMA_ALIGN_32
DeviceTransferDescriptor dStreamTD1[STREAM_TDs] ATTR_ALIGNED(32) __BSS(USBRAM_SECTION);
PRAGMA_ALIGN_4
uint8_t iso_buffer[512] ATTR_ALIGNED(4);
volatile DeviceQueueHead * const dQueueHead[LPC18_43_MAX_USB_CORE] = {dQueueHead0, dQueueHead1};
DeviceTransferDescriptor * const dTransferDescriptor[LPC18_43_MAX_USB_CORE] = {dTransferDescriptor0, dTransferDescriptor1};
DeviceTransferDescriptor * const dStreamTD_Tbl[LPC18_43_MAX_USB_CORE] = {dStreamTD0, dStreamTD1};

typedef struct {
	uint32_t stream_buffer_address,
			stream_dummy_buffer_address,
			stream_remain_packets,
			stream_dummy_packets,
			stream_packet_size,
			stream_total_packets;
} STREAM_VAR_t;

static STREAM_VAR_t Stream_Variable[LPC18_43_MAX_USB_CORE];

PRAGMA_WEAK(CALLBACK_HAL_GetISOBufferAddress, Dummy_EPGetISOAddress)
uint32_t CALLBACK_HAL_GetISOBufferAddress(const uint32_t EPNum, uint32_t *last_packet_size) ATTR_WEAK ATTR_ALIAS(
	Dummy_EPGetISOAddress);

/* Device transfer completed event
 * Event is required for using the device stack with any RTOS
 */
PRAGMA_WEAK(EVENT_USB_Device_TransferComplete,Dummy_EVENT_USB_Device_TransferComplete)
void EVENT_USB_Device_TransferComplete(int logicalEP, int xfer_in) ATTR_WEAK ATTR_ALIAS(Dummy_EVENT_USB_Device_TransferComplete);

void DcdInsertTD(uint32_t head, uint32_t newtd);

void DcdPrepareTD(DeviceTransferDescriptor *pDTD, uint8_t *pData, uint32_t length, uint8_t IOC);

void HAL_Reset(uint8_t corenum)
{
	uint32_t i;
	IP_USBHS_001_T * USB_Reg;
	USB_Reg = USB_REG(corenum);

	/* disable all EPs */
	USB_Reg->ENDPTCTRL[0] &= ~(ENDPTCTRL_RxEnable | ENDPTCTRL_TxEnable);
	USB_Reg->ENDPTCTRL[1] &= ~(ENDPTCTRL_RxEnable | ENDPTCTRL_TxEnable);
	USB_Reg->ENDPTCTRL[2] &= ~(ENDPTCTRL_RxEnable | ENDPTCTRL_TxEnable);
	USB_Reg->ENDPTCTRL[3] &= ~(ENDPTCTRL_RxEnable | ENDPTCTRL_TxEnable);
	if (corenum == 0) {
		USB_Reg->ENDPTCTRL[4] &= ~(ENDPTCTRL_RxEnable | ENDPTCTRL_TxEnable);
		USB_Reg->ENDPTCTRL[5] &= ~(ENDPTCTRL_RxEnable | ENDPTCTRL_TxEnable);
	}

	/* Clear all pending interrupts */
	USB_Reg->ENDPTNAK     = 0xFFFFFFFF;
	USB_Reg->ENDPTNAKEN       = 0;
	USB_Reg->USBSTS_D     = 0xFFFFFFFF;
	USB_Reg->ENDPTSETUPSTAT   = USB_Reg->ENDPTSETUPSTAT;
	USB_Reg->ENDPTCOMPLETE    = USB_Reg->ENDPTCOMPLETE;
	while (USB_Reg->ENDPTPRIME) ;				/* Wait until all bits are 0 */
	USB_Reg->ENDPTFLUSH = 0xFFFFFFFF;
	while (USB_Reg->ENDPTFLUSH) ;	/* Wait until all bits are 0 */

	/* Set the interrupt Threshold control interval to 0 */
	USB_Reg->USBCMD_D &= ~0x00FF0000;

	/* Configure the Endpoint List Address */
	/* make sure it in on 64 byte boundary !!! */
	/* init list address */
	USB_Reg->ENDPOINTLISTADDR = (uint32_t) dQueueHead[corenum];

	/* Enable interrupts: USB interrupt, error, port change, reset, suspend, NAK interrupt */
	USB_Reg->USBINTR_D =  USBINTR_D_UsbIntEnable | USBINTR_D_UsbErrorIntEnable |
									 USBINTR_D_PortChangeIntEnable | USBINTR_D_UsbResetEnable |
									 USBINTR_D_SuspendEnable | USBINTR_D_NAKEnable | USBINTR_D_SofReceivedEnable;

	USB_Device_SetDeviceAddress(corenum, 0);

	endpointselected[corenum] = 0;
	for (i = 0; i < ENDPOINT_TOTAL_ENDPOINTS(corenum); i++)
		endpointhandle(corenum)[i] = 0;

	usb_data_buffer_size[corenum] = 0;
	usb_data_buffer_index[corenum] = 0;

	usb_data_buffer_OUT_size[corenum] = 0;
	usb_data_buffer_OUT_index[corenum] = 0;

	// usb_data_buffer_IN_size = 0;
	usb_data_buffer_IN_index[corenum] = 0;
	Stream_Variable[corenum].stream_total_packets = 0;
}

bool Endpoint_ConfigureEndpoint(uint8_t corenum, const uint8_t Number, const uint8_t Type,
								const uint8_t Direction, const uint16_t Size, const uint8_t Banks)
{
	uint8_t * ISO_Address;
	volatile DeviceQueueHead * pdQueueHead;
	uint32_t PhyEP = 2 * Number + (Direction == ENDPOINT_DIR_OUT ? 0 : 1);
	__IO uint32_t * pEndPointCtrl = &ENDPTCTRL_REG(corenum, Number);
	uint32_t EndPtCtrl = *pEndPointCtrl;
	
	pdQueueHead = &(dQueueHead[corenum][PhyEP]);
	memset((void *) pdQueueHead, 0, sizeof(DeviceQueueHead) );
	
	pdQueueHead->MaxPacketSize = Size & 0x3ff;
	pdQueueHead->IntOnSetup = 1;
	pdQueueHead->ZeroLengthTermination = 1;
	pdQueueHead->overlay.NextTD = LINK_TERMINATE;

	if (Direction == ENDPOINT_DIR_OUT) {
		EndPtCtrl &= ~0x0000FFFF;
		EndPtCtrl |= ((Type << 2) & ENDPTCTRL_RxType) | ENDPTCTRL_RxEnable | ENDPTCTRL_RxToggleReset;
		if (Type == EP_TYPE_ISOCHRONOUS) {
			uint32_t size = 0;
			*pEndPointCtrl = (Type << 2);					// TODO dummy to let DcdDataTransfer() knows iso transfer
			ISO_Address = (uint8_t *) CALLBACK_HAL_GetISOBufferAddress(Number, &size);
			DcdDataTransfer(corenum, PhyEP, ISO_Address, USB_DATA_BUFFER_TEM_LENGTH);
		}
		else {
			USB_REG(corenum)->ENDPTNAKEN |=  (1 << EP_Physical2BitPosition(PhyEP));
		}
	}
	else {	/* ENDPOINT_DIR_IN */
		EndPtCtrl &= ~0xFFFF0000;
		EndPtCtrl |= ((Type << 18) & ENDPTCTRL_TxType) | ENDPTCTRL_TxEnable | ENDPTCTRL_TxToggleReset;
		if (Type == EP_TYPE_ISOCHRONOUS) {
			uint32_t size = 0;
			*pEndPointCtrl = (Type << 18);					// TODO dummy to let DcdDataTransfer() knows iso transfer
			ISO_Address = (uint8_t *) CALLBACK_HAL_GetISOBufferAddress(Number, &size);
			DcdDataTransfer(corenum, PhyEP, ISO_Address, size);
		}
	}
	*pEndPointCtrl = EndPtCtrl;

	endpointhandle(corenum)[Number] = (Number == ENDPOINT_CONTROLEP) ? ENDPOINT_CONTROLEP : PhyEP;
	return true;
}

void Endpoint_Streaming(uint8_t corenum, uint8_t *buffer, uint16_t packetsize,
						uint16_t totalpackets, uint16_t dummypackets)
{
	uint8_t PhyEP = endpointhandle(corenum)[endpointselected[corenum]];
	uint16_t i;
	volatile DeviceQueueHead * pdQueueHead;
#if 0
	for (i = 0; i < totalpackets; i++) {
		DcdDataTransfer(corenum, PhyEP, (uint8_t *) (buffer + i * packetsize), packetsize);
		while (!(
				   (dQueueHead[PhyEP].overlay.NextTD & LINK_TERMINATE)
				   && (dQueueHead[PhyEP].overlay.Active == 0)
				   )
			   ) ;
	}
	for (i = 0; i < dummypackets; i++) {
		DcdDataTransfer(corenum, PhyEP, buffer, packetsize);
		while (!(
				   (dQueueHead[PhyEP].overlay.NextTD & LINK_TERMINATE)
				   && (dQueueHead[PhyEP].overlay.Active == 0)
				   )
			   ) ;
	}
#else
	STREAM_VAR_t * current_stream = &Stream_Variable[corenum];
	DeviceTransferDescriptor *dStreamTD = dStreamTD_Tbl[corenum];
	uint16_t cnt = 0;
	dummypackets = dummypackets;
	while ( USB_REG(corenum)->ENDPTSTAT & _BIT(EP_Physical2BitPosition(PhyEP) ) ) {	/* Endpoint is already primed */
	}

	for (i = 0; i < totalpackets; i++) {
		uint8_t ioc;
		if (i == STREAM_TDs) {
			break;
		}
		if ((i == totalpackets - 1) || (i == STREAM_TDs - 1)) {
			ioc = 1;
		}
		else {
			ioc = 0;
		}

		DcdPrepareTD(&dStreamTD[i], (uint8_t *) (buffer + i * packetsize), packetsize, ioc);
		if (i > 0) {
			DcdInsertTD((uint32_t) dStreamTD, (uint32_t) &dStreamTD[i]);
		}
		cnt++;
	}

	if (STREAM_TDs < totalpackets) {
		current_stream->stream_remain_packets = totalpackets - STREAM_TDs;
		current_stream->stream_buffer_address = (uint32_t) buffer + STREAM_TDs * packetsize;
		current_stream->stream_packet_size = packetsize;
	}
	else {
		current_stream->stream_remain_packets = current_stream->stream_buffer_address = current_stream->stream_packet_size = 0;
	}
	current_stream->stream_total_packets = totalpackets;
	pdQueueHead = &(dQueueHead[corenum][PhyEP]);
	pdQueueHead->overlay.Halted = 0;	/* this should be in USBInt */
	pdQueueHead->overlay.Active = 0;	/* this should be in USBInt */
	pdQueueHead->overlay.NextTD = (uint32_t) dStreamTD;
	pdQueueHead->TransferCount = totalpackets * packetsize;
	pdQueueHead->IsOutReceived = 0;

	USB_REG(corenum)->ENDPTPRIME |= _BIT(EP_Physical2BitPosition(PhyEP) );
#endif
}

void DcdInsertTD(uint32_t head, uint32_t newtd)
{
	DeviceTransferDescriptor *pTD = (DeviceTransferDescriptor *) head;
	while (!(pTD->NextTD & LINK_TERMINATE)) pTD = (DeviceTransferDescriptor *) pTD->NextTD;
	pTD->NextTD = newtd;
}

void DcdPrepareTD(DeviceTransferDescriptor *pDTD, uint8_t *pData, uint32_t length, uint8_t IOC)
{
	/* Zero out the device transfer descriptors */
	memset((void *) pDTD, 0, sizeof(DeviceTransferDescriptor));

	pDTD->NextTD = LINK_TERMINATE;
	pDTD->TotalBytes = length;
	pDTD->IntOnComplete = IOC;
	pDTD->Active = 1;
	pDTD->BufferPage[0] = (uint32_t) pData;
	pDTD->BufferPage[1] = ((uint32_t) pData + 0x1000) & 0xfffff000;
	//	pDTD->BufferPage[2] = ((uint32_t) pData + 0x2000) & 0xfffff000;
	//	pDTD->BufferPage[3] = ((uint32_t) pData + 0x3000) & 0xfffff000;
	//	pDTD->BufferPage[4] = ((uint32_t) pData + 0x4000) & 0xfffff000;
}

void DcdDataTransfer(uint8_t corenum, uint8_t PhyEP, uint8_t *pData, uint32_t length)
{
	DeviceTransferDescriptor * pDTD = (DeviceTransferDescriptor *) &dTransferDescriptor[corenum][PhyEP];
	volatile DeviceQueueHead * pdQueueHead = &(dQueueHead[corenum][PhyEP]);
	while ( USB_REG(corenum)->ENDPTSTAT & _BIT(EP_Physical2BitPosition(PhyEP) ) ) {	/* Endpoint is already primed */
	}

	/* Zero out the device transfer descriptors */
	memset((void *) pDTD, 0, sizeof(DeviceTransferDescriptor));

	if (((ENDPTCTRL_REG(corenum, PhyEP / 2) >> 2) & EP_TYPE_MASK) == EP_TYPE_ISOCHRONOUS) {	// iso out endpoint
		uint32_t mult = (USB_DATA_BUFFER_TEM_LENGTH + 1024) / 1024;
		pDTD->NextTD = LINK_TERMINATE;
		pdQueueHead->Mult = mult;
	}
	else if (((ENDPTCTRL_REG(corenum, PhyEP / 2) >> 18) & EP_TYPE_MASK) == EP_TYPE_ISOCHRONOUS) {// iso in endpoint
		uint32_t mult = (USB_DATA_BUFFER_TEM_LENGTH + 1024) / 1024;
		pDTD->NextTD = LINK_TERMINATE;
		pdQueueHead->Mult = mult;
	}
	else {																		// other endpoint types
		pDTD->NextTD = LINK_TERMINATE;	/* The next DTD pointer is INVALID */
	}
	pDTD->TotalBytes = length;
	pDTD->IntOnComplete = 1;
	pDTD->Active = 1;

	pDTD->BufferPage[0] = (uint32_t) pData;
	pDTD->BufferPage[1] = ((uint32_t) pData + 0x1000) & 0xfffff000;
	pDTD->BufferPage[2] = ((uint32_t) pData + 0x2000) & 0xfffff000;
	pDTD->BufferPage[3] = ((uint32_t) pData + 0x3000) & 0xfffff000;
	pDTD->BufferPage[4] = ((uint32_t) pData + 0x4000) & 0xfffff000;

	pdQueueHead->overlay.Halted = 0;	/* this should be in USBInt */
	pdQueueHead->overlay.Active = 0;	/* this should be in USBInt */
	pdQueueHead->overlay.NextTD = (uint32_t) &dTransferDescriptor[corenum][PhyEP];
	pdQueueHead->TransferCount = length;

	/* prime the endpoint for transmit */
	USB_REG(corenum)->ENDPTPRIME |= _BIT(EP_Physical2BitPosition(PhyEP) );
}

void TransferCompleteISR(uint8_t corenum)
{
	uint8_t * ISO_Address;
 	IP_USBHS_001_T *	USB_Reg = USB_REG(corenum);
	STREAM_VAR_t * current_stream = &Stream_Variable[corenum];
	uint32_t ENDPTCOMPLETE = USB_Reg->ENDPTCOMPLETE;
	USB_Reg->ENDPTCOMPLETE = ENDPTCOMPLETE;
	if (ENDPTCOMPLETE) {
		uint8_t n;
		for (n = 0; n < USED_PHYSICAL_ENDPOINTS(corenum) / 2; n++) {	/* LOGICAL */
			if ( ENDPTCOMPLETE & _BIT(n) ) {/* OUT */
				if (((ENDPTCTRL_REG(corenum, n) >> 2) & EP_TYPE_MASK) == EP_TYPE_ISOCHRONOUS) {	// iso out endpoint
					uint32_t size = dQueueHead[corenum][2 * n].TransferCount;
                                        size -= dQueueHead[corenum][2 * n].overlay.TotalBytes;
					// copy to share buffer
					ISO_Address = (uint8_t *) CALLBACK_HAL_GetISOBufferAddress(n, &size);
					DcdDataTransfer(corenum, 2 * n, ISO_Address, USB_DATA_BUFFER_TEM_LENGTH);
				}
				else {
					
					uint32_t tem = dQueueHead[corenum][2 * n].overlay.TotalBytes;
					dQueueHead[corenum][2 * n].TransferCount -= tem;

					if (current_stream->stream_total_packets > 0) {
						if (current_stream->stream_remain_packets > 0) {
							uint32_t cnt = dQueueHead[corenum][2 * n].TransferCount;
							Endpoint_Streaming(corenum,(uint8_t *) current_stream->stream_buffer_address,
									current_stream->stream_packet_size,
									current_stream->stream_remain_packets,
											   0);
							dQueueHead[corenum][2 * n].TransferCount = cnt;
						}
						else {
							current_stream->stream_total_packets = 0;
							dQueueHead[corenum][2 * n].IsOutReceived = 1;
						}
					}
					else {
						//stream_total_packets = 0;
						dQueueHead[corenum][2 * n].IsOutReceived = 1;
					}
					if (n == 0) {
						usb_data_buffer_size[corenum] = dQueueHead[corenum][2 * n].TransferCount;
					}
					else {
						usb_data_buffer_OUT_size[corenum] = dQueueHead[corenum][2 * n].TransferCount;
					}
				}
				EVENT_USB_Device_TransferComplete(n, 0);
			}
			if ( ENDPTCOMPLETE & _BIT( (n + 16) ) ) {	/* IN */
				if (((ENDPTCTRL_REG(corenum, n) >> 18) & EP_TYPE_MASK) == EP_TYPE_ISOCHRONOUS) {	// iso in endpoint
					uint32_t size;
					ISO_Address = (uint8_t *) CALLBACK_HAL_GetISOBufferAddress(n, &size);
					DcdDataTransfer(corenum, 2 * n + 1, ISO_Address, size);
				}
				else {
					if (current_stream->stream_remain_packets > 0) {
						uint32_t cnt = dQueueHead[corenum][2 * n].TransferCount;
						Endpoint_Streaming(corenum, (uint8_t *) current_stream->stream_buffer_address,
								current_stream->stream_packet_size,
								current_stream->stream_remain_packets,
										   0);
						dQueueHead[corenum][2 * n].TransferCount = cnt;
					}
					else {
						current_stream->stream_total_packets = 0;
					}
				}
				EVENT_USB_Device_TransferComplete(n, 1);
			}
		}
	}
}

void Endpoint_GetSetupPackage(uint8_t corenum, uint8_t *pData)
{
	USB_Request_Header_t * ctrlrq = (USB_Request_Header_t *) pData;
	volatile DeviceQueueHead* pdQueueHead = &(dQueueHead[corenum][0]);
	memcpy(pData, (void *) pdQueueHead->SetupPackage, 8);
	/* Below fix is to prevent Endpoint_Read_Control_Stream_LE()
	 * from getting wrong data*/

	if (
		(ctrlrq->wLength != 0)
		) {
		pdQueueHead->IsOutReceived = 0;
	}
}

void DcdIrqHandler(uint8_t corenum)
{
	uint32_t USBSTS_D;
	IP_USBHS_001_T *	USB_Reg = USB_REG(corenum);
	uint32_t t = USB_Reg->USBINTR_D;

	USBSTS_D = USB_Reg->USBSTS_D & t;	/* Device Interrupt Status */
	if (USBSTS_D == 0) {/* avoid to clear disabled interrupt source */
		return;
	}

	USB_Reg->USBSTS_D = USBSTS_D;	/* Acknowledge Interrupt */

	/* Process Interrupt Sources */
	if (USBSTS_D & USBSTS_D_UsbInt) {
		if (USB_Reg->ENDPTSETUPSTAT) {
			//			memcpy(SetupPackage, dQueueHead[0].SetupPackage, 8);
			/* Will be cleared by Endpoint_ClearSETUP */
		}

		if (USB_Reg->ENDPTCOMPLETE) {
			TransferCompleteISR(corenum);
		}
	}

	if (USBSTS_D & USBSTS_D_NAK) {					/* NAK */
		uint32_t ENDPTNAK = USB_Reg->ENDPTNAK;
                uint32_t en = USB_Reg->ENDPTNAKEN;
                ENDPTNAK &= en;
		USB_Reg->ENDPTNAK = ENDPTNAK;

		if (ENDPTNAK) {	/* handle NAK interrupts */
			uint8_t LogicalEP;
			for (LogicalEP = 0; LogicalEP < USED_PHYSICAL_ENDPOINTS(corenum) / 2; LogicalEP++)
				if (ENDPTNAK & _BIT(LogicalEP)) {	/* Only OUT Endpoint is NAK enable */
					uint8_t PhyEP = 2 * LogicalEP;
					if ( !(USB_Reg->ENDPTSTAT & _BIT(LogicalEP)) ) {/* Is In ready */
						/* Check read OUT flag */
						if (!dQueueHead[corenum][PhyEP].IsOutReceived) {

							if (PhyEP == 0) {
								usb_data_buffer_size[corenum] = 0;
								USB_Reg->ENDPTNAKEN &= ~(1 << 0);
								DcdDataTransfer(corenum, PhyEP, usb_data_buffer[corenum], 512);
							}
							else {
								if (Stream_Variable[corenum].stream_total_packets == 0) {
									usb_data_buffer_OUT_size[corenum] = 0;
									/* Clear NAK */
									USB_Reg->ENDPTNAKEN &= ~(1 << LogicalEP);
									DcdDataTransfer(corenum, PhyEP, usb_data_buffer_OUT[corenum], 512	/*512*/);
								}
							}
						}
					}
				}
		}
	}

	if (USBSTS_D & USBSTS_D_SofReceived) {					/* Start of Frame Interrupt */
		EVENT_USB_Device_StartOfFrame();
	}

	if (USBSTS_D & USBSTS_D_ResetReceived) {					/* Reset */
		HAL_Reset(corenum);
		USB_DeviceState[corenum] = DEVICE_STATE_Default;
		Endpoint_ConfigureEndpoint(corenum,
									 ENDPOINT_CONTROLEP,
								   EP_TYPE_CONTROL,
								   ENDPOINT_DIR_OUT,
								   USB_Device_ControlEndpointSize,
								   0);
		Endpoint_ConfigureEndpoint(corenum, 
									 ENDPOINT_CONTROLEP,
								   EP_TYPE_CONTROL,
								   ENDPOINT_DIR_IN,
								   USB_Device_ControlEndpointSize,
								   0);
	}

	if (USBSTS_D & USBSTS_D_SuspendInt) {					/* Suspend */

	}

	if (USBSTS_D & USBSTS_D_PortChangeDetect) {					/* Resume */

	}

	if (USBSTS_D & USBSTS_D_UsbErrorInt) {					/* Error Interrupt */
		// while(1){}
	}
}

uint32_t Dummy_EPGetISOAddress(uint32_t EPNum, uint32_t *last_packet_size)
{
	return (uint32_t) iso_buffer;
}

/*********************************************************************//**
 * @brief		Dummy USB device transfer complete event
 * @param[in]   logicalEP Logical endpoint number
 * @param[in]	xfer_in If this argument is 0 then xfer type is out, else in
 * @note		This event is required for running the stack with RTOS
 *      		and so it should never be removed!
 * @return	 	None
 **********************************************************************/
void Dummy_EVENT_USB_Device_TransferComplete(int logicalEP, int xfer_in)
{
	/**
	 * This is a dummy function
	 * If xfer_in zero then the endpoint it OUT
	 * else ep is IN.
	 **/
}
// #endif

#endif /*__LPC18XX__*/
