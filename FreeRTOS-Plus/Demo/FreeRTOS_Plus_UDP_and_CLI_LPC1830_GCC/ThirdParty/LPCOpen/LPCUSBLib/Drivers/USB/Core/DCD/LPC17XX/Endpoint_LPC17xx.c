/*
 * @brief USB Endpoint definitions for the LPC17xx microcontrollers
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

#if (defined(__LPC175X_6X__) || defined(__LPC177X_8X__) || defined(__LPC407X_8X__)) && defined(USB_CAN_BE_DEVICE)
#include "../../Endpoint.h"

#define IsOutEndpoint(PhysicalEP)       (!((PhysicalEP) & 1) )

volatile bool SETUPReceived;
volatile bool isOutReceived;
volatile bool isInReady;

PRAGMA_ALIGN_128
uint32_t UDCA[32] __BSS(USBRAM_SECTION) ATTR_ALIGNED(128);
DMADescriptor dmaDescriptor[USED_PHYSICAL_ENDPOINTS] __BSS(USBRAM_SECTION);
static uint8_t SetupPackage[8] __BSS(USBRAM_SECTION);
uint32_t DataInRemainCount, DataInRemainOffset;
bool IsConfigured, shortpacket;
uint8_t *ISO_Address;
PRAGMA_ALIGN_4
uint8_t iso_buffer[512] ATTR_ALIGNED(4) __BSS(USBRAM_SECTION);
PRAGMA_WEAK(CALLBACK_HAL_GetISOBufferAddress, Dummy_EPGetISOAddress)
uint32_t CALLBACK_HAL_GetISOBufferAddress(const uint32_t EPNum, uint32_t *last_packet_size) ATTR_WEAK ATTR_ALIAS(
	Dummy_EPGetISOAddress);

uint32_t BufferAddressIso[32] __BSS(USBRAM_SECTION);
uint32_t SizeAudioTransfer;

void SIE_WriteCommand(uint32_t cmd) {

	USB_REG(0)->DevIntClr = CCEMTY_INT;
	USB_REG(0)->CmdCode = cmd;
	while ((USB_REG(0)->DevIntSt & CCEMTY_INT) == 0) ;
}

void SIE_WriteCommandData(uint32_t cmd, uint32_t val) {

	USB_REG(0)->DevIntClr = CCEMTY_INT;
	USB_REG(0)->CmdCode = cmd;
	while ((USB_REG(0)->DevIntSt & CCEMTY_INT) == 0) ;
	USB_REG(0)->DevIntClr = CCEMTY_INT;
	USB_REG(0)->CmdCode = val;
	while ((USB_REG(0)->DevIntSt & CCEMTY_INT) == 0) ;
}

uint32_t SIE_ReadCommandData(uint32_t cmd) {

	USB_REG(0)->DevIntClr = CCEMTY_INT | CDFULL_INT;
	USB_REG(0)->CmdCode = cmd;
	while ((USB_REG(0)->DevIntSt & CDFULL_INT) == 0) ;
	return USB_REG(0)->CmdData;
}

void HAL_Reset(uint8_t corenum)
{
	uint32_t n;

	USB_REG(corenum)->EpInd = 0;
	USB_REG(corenum)->MaxPSize = USB_Device_ControlEndpointSize;
	USB_REG(corenum)->EpInd = 1;
	USB_REG(corenum)->MaxPSize = USB_Device_ControlEndpointSize;
	while ((USB_REG(corenum)->DevIntSt & EP_RLZED_INT) == 0) ;

	/* Slave Register */
	USB_REG(corenum)->EpIntEn     = 0;
	USB_REG(corenum)->DevIntEn    = (DEV_STAT_INT | EP_SLOW_INT | ERR_INT);

	USB_REG(corenum)->EpIntClr    = 0xFFFFFFFF;
	USB_REG(corenum)->DevIntClr   = 0xFFFFFFFF;
	USB_REG(corenum)->EpIntPri    = 0;

	/* DMA registers */
	USB_REG(corenum)->EpDMADis    = 0xFFFFFFFF;
	USB_REG(corenum)->DMARClr     = 0xFFFFFFFF;
	USB_REG(corenum)->EoTIntClr   = 0xFFFFFFFF;
	USB_REG(corenum)->NDDRIntClr  = 0xFFFFFFFF;
	USB_REG(corenum)->SysErrIntClr = 0xFFFFFFFF;

	USB_REG(corenum)->DMAIntEn  = (EOT_INT | NDD_REQ_INT | SYS_ERR_INT );
	USB_REG(corenum)->UDCAH   = (uint32_t) UDCA;
	for (n = 0; n < USED_PHYSICAL_ENDPOINTS; n++)
		UDCA[n] = 0;
	IsConfigured = false;
	isOutReceived = false;
	isInReady = true;
	usb_data_buffer_size[corenum] = 0;
	usb_data_buffer_index[corenum] = 0;

	usb_data_buffer_OUT_size[corenum] = 0;
	usb_data_buffer_OUT_index[corenum] = 0;
	// uint32_t usb_data_buffer_IN_size = 0;
	usb_data_buffer_IN_index[corenum] = 0;
	// SIE_WriteCommandData(CMD_SET_MODE, DAT_WR_BYTE(0) );
	//	SIE_WriteCommandData(CMD_SET_MODE, DAT_WR_BYTE(INAK_IO | INAK_BO) ); /* Disable INAK_IO, INAK_BO */
}

void Endpoint_StallTransaction(uint8_t corenum)
{
	if (endpointselected[corenum] == ENDPOINT_CONTROLEP) {
		SIE_WriteCommandData(CMD_SET_EP_STAT(endpointhandle(corenum)[endpointselected[corenum]]), DAT_WR_BYTE(EP_STAT_CND_ST) );
	}
	else {
		SIE_WriteCommandData(CMD_SET_EP_STAT(endpointhandle(corenum)[endpointselected[corenum]]), DAT_WR_BYTE(EP_STAT_ST) );
	}
}

bool Endpoint_ConfigureEndpoint(uint8_t corenum, const uint8_t Number, const uint8_t Type,
								const uint8_t Direction, const uint16_t Size, const uint8_t Banks)
{
	uint32_t PhyEP = 2 * Number + (Direction == ENDPOINT_DIR_OUT ? 0 : 1);

	if ((!IsConfigured) && (PhyEP > 1)) {
		IsConfigured = true;
		SIE_WriteCommandData(CMD_CFG_DEV, DAT_WR_BYTE(CONF_DVICE));
	}

	USB_REG(corenum)->ReEp |= (1 << PhyEP);		/* Realize endpoint */

	USB_REG(corenum)->EpInd = PhyEP;				/* Endpoint Index */
	USB_REG(corenum)->MaxPSize = Size & 0x3ff;	/* Max Packet Size */

	while ((USB_REG(corenum)->DevIntSt & EP_RLZED_INT) == 0) ;	/* TODO shouldd we wait for this */
	USB_REG(corenum)->DevIntClr = EP_RLZED_INT;

	if (Number == ENDPOINT_CONTROLEP) {	/* Control endpoints have to uses slave mode */
		USB_REG(corenum)->EpIntEn |= _BIT(PhyEP);
		DataInRemainCount = 0;
		DataInRemainOffset = 0;
	}
	else {	/* all other endpoints use DMA mode */
		memset(&dmaDescriptor[PhyEP], 0, sizeof(DMADescriptor));
		dmaDescriptor[PhyEP].Isochronous = (Type == EP_TYPE_ISOCHRONOUS ? 1 : 0 );
		dmaDescriptor[PhyEP].MaxPacketSize = Size;
		dmaDescriptor[PhyEP].Retired = 1;	/* inactive DD */

		USB_REG(corenum)->EpDMAEn = _BIT(PhyEP);
	}

	SIE_WriteCommandData(CMD_SET_EP_STAT(PhyEP), DAT_WR_BYTE(0));	/*enable endpoint*/
	SIE_WriteCommandData(CMD_SET_EP_STAT(PhyEP), DAT_WR_BYTE(0));	/* Reset Endpoint */

	endpointhandle(corenum)[Number] = (Number == ENDPOINT_CONTROLEP) ? ENDPOINT_CONTROLEP : PhyEP;
	return true;
}

void ReadControlEndpoint(uint8_t *pData)
{
	uint32_t cnt, n;

	USB_REG(0)->Ctrl = CTRL_RD_EN;

	do {
		cnt = USB_REG(0)->RxPLen;
	} while ((cnt & PKT_RDY) == 0);
	cnt &= PKT_LNGTH_MASK;

	for (n = 0; n < (cnt + 3) / 4; n++) {
		*((uint32_t *) pData) = USB_REG(0)->RxData;
		pData += 4;
	}
	USB_REG(0)->Ctrl = 0;

	if ((cnt > 0) && (SETUPReceived == false)) {
		isOutReceived = true;
	}
	usb_data_buffer_size[0] = cnt;

	//	SIE_WriteCommamd(CMD_SEL_EP(ENDPOINT_CONTROLEP));
	//	SIE_WriteCommamd(CMD_CLR_BUF);
}

void WriteControlEndpoint(uint8_t *pData, uint32_t cnt)
{
	uint32_t n;
	uint32_t count;

	isInReady = false;
	if (cnt >= USB_Device_ControlEndpointSize) {
		if (cnt == USB_Device_ControlEndpointSize) {
			shortpacket = true;
		}
		count = USB_Device_ControlEndpointSize;
		DataInRemainCount = cnt - USB_Device_ControlEndpointSize;
		DataInRemainOffset += count;
	}
	else {
		count = cnt;
		DataInRemainCount = 0;
		DataInRemainOffset = 0;
	}
	USB_REG(0)->Ctrl = CTRL_WR_EN;
	USB_REG(0)->TxPLen = count;

	for (n = 0; n < (count + 3) / 4; n++) {
		USB_REG(0)->TxData = *((uint32_t *) pData);
		pData += 4;
	}

	USB_REG(0)->Ctrl = 0;

	SIE_WriteCommand(CMD_SEL_EP(ENDPOINT_CONTROLEP + 1));
	SIE_WriteCommand(CMD_VALID_BUF);
}

void HAL17XX_SetDeviceAddress(uint8_t Address)
{
	SIE_WriteCommandData(CMD_SET_ADDR, DAT_WR_BYTE(DEV_EN | Address));	/* Don't wait for next */
	SIE_WriteCommandData(CMD_SET_ADDR, DAT_WR_BYTE(DEV_EN | Address));	/*  Setup Status Phase */
}

void HAL17XX_USBConnect(uint32_t con)
{
	SIE_WriteCommandData(CMD_SET_DEV_STAT, DAT_WR_BYTE(con ? DEV_CON : 0));
}

void Endpoint_GetSetupPackage(uint8_t corenum, uint8_t *pData)
{
	memcpy(pData, SetupPackage, 8);
}

void SlaveEndpointISR()
{
	uint32_t PhyEP;
	for (PhyEP = 0; PhyEP < 2; PhyEP++)		  /* Check Control Endpoints */
		if (USB_REG(0)->EpIntSt & _BIT(PhyEP)) {
			USB_REG(0)->EpIntClr = _BIT(PhyEP);	/*-- Clear Interrupt Endpoint --*/

			if (PhyEP == ENDPOINT_CONTROLEP) {			/* Control OUT Endpoint */
				uint32_t SIEEndpointStatus;

				while ((USB_REG(0)->DevIntSt & CDFULL_INT) == 0) ;
				SIEEndpointStatus = USB_REG(0)->CmdData;

				if (SIEEndpointStatus & EP_SEL_STP) {	/* Setup Packet */
					SETUPReceived = true;
					ReadControlEndpoint(SetupPackage);
				}
				else {
					ReadControlEndpoint(usb_data_buffer[0]);
				}
			}
			else {								/* IN Endpoint */
				isInReady = true;
				if (DataInRemainCount) {
					WriteControlEndpoint((uint8_t *) (usb_data_buffer[0] + DataInRemainOffset), DataInRemainCount);
				}
				else {
					if (shortpacket) {
						shortpacket = false;
						WriteControlEndpoint((uint8_t *) (usb_data_buffer[0] + DataInRemainOffset), DataInRemainCount);
						DataInRemainOffset = 0;
					}
				}
			}
		}
}

void Endpoint_Streaming(uint8_t corenum, uint8_t *buffer, uint16_t packetsize,
						uint16_t totalpackets, uint16_t dummypackets)
{
	uint8_t PhyEP = endpointhandle(corenum)[endpointselected[corenum]];
	uint16_t i;
	dummypackets = dummypackets;
	if (PhyEP & 1) {
		for (i = 0; i < totalpackets; i++) {
				while (!Endpoint_IsReadWriteAllowed(corenum)) ;
				Endpoint_Write_Stream_LE(corenum, (void *) (buffer + i * packetsize), packetsize, NULL);
				Endpoint_ClearIN(corenum);
			}
		}
	else {
		for (i = 0; i < totalpackets; i++) {
			DcdDataTransfer(PhyEP, usb_data_buffer_OUT[corenum], packetsize);
			Endpoint_ClearOUT(corenum);
			while (!Endpoint_IsReadWriteAllowed(corenum)) ;
			Endpoint_Read_Stream_LE(corenum, (void *) (buffer + i * packetsize), packetsize, NULL);
		}
	}
}

void DcdDataTransfer(uint8_t PhyEP, uint8_t *pData, uint32_t cnt)
{
	dmaDescriptor[PhyEP].BufferStartAddr = pData;
	if (dmaDescriptor[PhyEP].Isochronous == 1) {// iso endpoint
		if (PhyEP & 1) {// IN DIRECTION
			uint8_t BufferCount;
			for (BufferCount = 0; BufferCount < cnt / 0xFF; BufferCount++)
				BufferAddressIso[BufferCount] = 0xFF;
			BufferAddressIso[BufferCount] = (cnt % 0xFF);
			if (cnt % 0xFF != 0) {
				dmaDescriptor[PhyEP].BufferLength = cnt / 0xFF + 1;
			}
			else {
				dmaDescriptor[PhyEP].BufferLength = cnt / 0xFF;
			}
		}
		else {	// OUT DIRECTION
			dmaDescriptor[PhyEP].BufferLength = 1;
		}
		dmaDescriptor[PhyEP].IsoBufferAddr = (uint32_t) BufferAddressIso;
		dmaDescriptor[PhyEP].Isochronous = 1;
		dmaDescriptor[PhyEP].MaxPacketSize = 0;
	}
	else {
		dmaDescriptor[PhyEP].BufferLength = cnt;
	}
	dmaDescriptor[PhyEP].Retired = 0;
	dmaDescriptor[PhyEP].Status = 0;
	dmaDescriptor[PhyEP].IsoPacketValid = 0;
	dmaDescriptor[PhyEP].LSByteExtracted = 0;
	dmaDescriptor[PhyEP].MSByteExtracted = 0;
	dmaDescriptor[PhyEP].PresentCount = 0;

	UDCA[PhyEP] = (uint32_t) &dmaDescriptor[PhyEP];
	USB_REG(0)->EpDMAEn = _BIT(PhyEP);
}

void DMAEndTransferISR()
{
	uint32_t PhyEP;
	uint32_t EoTIntSt = USB_REG(0)->EoTIntSt;

	for (PhyEP = 2; PhyEP < USED_PHYSICAL_ENDPOINTS; PhyEP++)			   /* Check All Endpoints */
		if ( EoTIntSt & _BIT(PhyEP) ) {
			if ( IsOutEndpoint(PhyEP) ) {				/* OUT Endpoint */
                                uint32_t tem = usb_data_buffer_OUT_index[0];    //just to clear warning
				if (dmaDescriptor[PhyEP].Isochronous == 1) {// iso endpoint
					SizeAudioTransfer = (BufferAddressIso[0]) & 0xFFFF;
					ISO_Address = (uint8_t *) CALLBACK_HAL_GetISOBufferAddress(PhyEP / 2, &SizeAudioTransfer);
					DcdDataTransfer(PhyEP, ISO_Address, 512);
				}
				usb_data_buffer_OUT_size[0] += dmaDescriptor[PhyEP].PresentCount;
				if ((usb_data_buffer_OUT_size[0] + tem + dmaDescriptor[PhyEP].MaxPacketSize) > 512) {
					USB_REG(0)->DMAIntEn &= ~(1 << 1);
				}
			}
			else {								/* IN Endpoint */
				/* Should be left blank */
			}
		}
	USB_REG(0)->EoTIntClr = EoTIntSt;
}

void DMANewTransferRequestISR()
{
	uint32_t PhyEP;
	uint32_t NDDRIntSt = USB_REG(0)->NDDRIntSt;

	for (PhyEP = 2; PhyEP < USED_PHYSICAL_ENDPOINTS; PhyEP++)			   /* Check All Endpoints */
		if ( NDDRIntSt & _BIT(PhyEP) ) {
			if ( IsOutEndpoint(PhyEP) ) {					/* OUT Endpoint */
				if (dmaDescriptor[PhyEP].Isochronous == 1) {// iso endpoint
					DcdDataTransfer(PhyEP, ISO_Address, 512);
				}
				else {
					uint16_t MaxPS = dmaDescriptor[PhyEP].MaxPacketSize;
					if (usb_data_buffer_OUT_size[0] == 0) {
						usb_data_buffer_OUT_index[0] = 0;
						DcdDataTransfer(PhyEP, usb_data_buffer_OUT[0], MaxPS);

					}
					else {
							uint32_t tem = usb_data_buffer_OUT_index[0];      //just to clear warning
							DcdDataTransfer(PhyEP, &usb_data_buffer_OUT[0][usb_data_buffer_OUT_size[0] + tem], MaxPS);
					}
				}
			}
			else {								/* IN Endpoint */
				if (dmaDescriptor[PhyEP].Isochronous == 1) {
					ISO_Address = (uint8_t *) CALLBACK_HAL_GetISOBufferAddress(PhyEP / 2, &SizeAudioTransfer);
					if (SizeAudioTransfer > 0) {
						DcdDataTransfer(PhyEP, ISO_Address, SizeAudioTransfer);
					}
					else {
						DcdDataTransfer(PhyEP, ISO_Address, 512);
					}
				}
			}
		}
	USB_REG(0)->NDDRIntClr = NDDRIntSt;
}

// void DMASysErrISR()
// {
//  uint32_t PhyEP;
//  uint32_t SysErrIntSt = LPC_USB->USBSysErrIntSt;
//  for (PhyEP = 2; PhyEP < USED_PHYSICAL_ENDPOINTS; PhyEP++)              /* Check All Endpoints */
//  {
//      if ( SysErrIntSt & _BIT(PhyEP) )
//      {
//          if ( IsOutEndpoint(PhyEP) )         /* OUT Endpoint */
//          {
//          }
//          else			                    /* IN Endpoint */
//          {
//          }
//      }
//  }
//  LPC_USB->USBSysErrIntClr = SysErrIntSt;
// }

void DcdIrqHandler(uint8_t DeviceID)
{
	uint32_t DevIntSt, DMAIntSt;

	DevIntSt = USB_REG(DeviceID)->DevIntEn;						/* Device Interrupt Status */
        DevIntSt &= USB_REG(DeviceID)->DevIntEn;
        
	USB_REG(DeviceID)->DevIntClr = DevIntSt;

	/* Device Status Interrupt (Reset, Connect change, Suspend/Resume) */
	if (DevIntSt & DEV_STAT_INT) {
		uint32_t SIEDeviceStatus;
		SIE_WriteCommand(CMD_GET_DEV_STAT);
		SIEDeviceStatus = SIE_ReadCommandData(DAT_GET_DEV_STAT);		/* Device Status */
		if (SIEDeviceStatus & DEV_RST) {					/* Reset */
			HAL_Reset(DeviceID);
			USB_DeviceState[DeviceID] = DEVICE_STATE_Default;
			Endpoint_ConfigureEndpoint(DeviceID, ENDPOINT_CONTROLEP, 0, ENDPOINT_DIR_OUT, USB_Device_ControlEndpointSize, 0);
			Endpoint_ConfigureEndpoint(DeviceID, ENDPOINT_CONTROLEP, 0, ENDPOINT_DIR_IN, USB_Device_ControlEndpointSize, 0);
		}
		if (SIEDeviceStatus & DEV_CON_CH) {					/* Connect change */
		}
		if (SIEDeviceStatus & DEV_SUS_CH) {					/* Suspend/Resume */
			if (SIEDeviceStatus & DEV_SUS) {				/* Suspend */
			}
			else {								/* Resume */
			}
		}
	}

	if (DevIntSt & FRAME_INT) {}

	if (DevIntSt & ERR_INT) {
		volatile uint32_t SIEErrorStatus;
		SIE_WriteCommand(CMD_RD_ERR_STAT);
		SIEErrorStatus = SIE_ReadCommandData(DAT_RD_ERR_STAT);
	}

	/* SLAVE mode : Endpoint's Slow Interrupt */
	if ( (DevIntSt & EP_SLOW_INT) || (DevIntSt & EP_FAST_INT) ) {
		SlaveEndpointISR();
	}

	/* DMA mode */
	DMAIntSt = LPC_USB->DMAIntSt;
        DMAIntSt &= USB_REG(DeviceID)->DMAIntEn;

	if (DMAIntSt & EOT_INT) {			/* End of Transfer Interrupt */
		DMAEndTransferISR();
	}

	if (DMAIntSt & NDD_REQ_INT) {			/* New DD Request Interrupt */
		DMANewTransferRequestISR();

	}

	if (DMAIntSt & SYS_ERR_INT) {			/* System Error Interrupt */
		// DMASysErrISR();
		USB_REG(DeviceID)->SysErrIntClr = USB_REG(DeviceID)->SysErrIntSt;
	}
}

uint32_t Dummy_EPGetISOAddress(uint32_t EPNum, uint32_t *last_packet_size)
{
	return (uint32_t) iso_buffer;
}

#endif /*__LPC17XX__ || __LPC40XX__*/
