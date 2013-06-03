/*
 * @brief Audio device class ROM based application's specific functions supporting audio class layer
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

#if defined(USB_DEVICE_ROM_DRIVER) && !(defined(__LPC11U2X_3X__)||defined(__LPC13UXX__))
#include "../../../Class/AudioClass.h"
#include "usbd_adcuser.h"

/** Internal definition */
#define AUDIO_MAX_SAMPLE_FREQ 48000

/* Volume definitions */
#define VOLUME_MIN          0x0000
#define VOLUME_MAX          0x003F
#define VOLUME_RES          0x0001

uint32_t ISO_packet_size = 0;

/* Device Transfer Descriptor used in Custom ROM mode */
DeviceTransferDescriptor Rom_dTD ATTR_ALIGNED(32);
/* external Audio Sample Frequency variable */
extern uint32_t CurrentAudioSampleFrequency;
/* Current Volume */
uint32_t curr_vol;
static uint8_t ISOEndpointNumber;
static uint8_t StreamInterfaceNumber;
static uint8_t ControlInterfaceNumber;
static uint8_t USBPort;

extern uint32_t sample_buffer_size;

extern uint32_t CALLBACK_HAL_GetISOBufferAddress(const uint32_t EPNum, uint32_t* last_packet_size);
extern void Audio_Reset_Data_Buffer(void);
extern void Audio_Init (uint32_t samplefreq);

/* inline functions */
static INLINE DeviceQueueHead* Usbd_GetEpQH(USB_CORE_CTRL_T* pCtrl, uint8_t ep)
{
    DeviceQueueHead* ep_QH = (DeviceQueueHead*)(*((uint32_t*)pCtrl->hw_data));
    uint32_t ep_idx = (ep & 0x0F) << 1;

    if(ep & 0x80)
       ep_idx++;

    return &ep_QH[ep_idx];
}

/** Get Transfer packet size */
static INLINE uint32_t Usbd_GetTransferSize(USB_CORE_CTRL_T *pCtrl, uint8_t ep)
{
	DeviceQueueHead *ep_QH = Usbd_GetEpQH(pCtrl, ep);
	return ep_QH->TransferCount - ep_QH->overlay.TotalBytes;
}

static void UsbdDcdDataTransfer(uint8_t EPNum, uint8_t *pData, uint32_t length)
{
	uint8_t PhyEP = (EPNum<<1) | (EPNum>>7); /* Rotate left without carry */
	DeviceQueueHead* ep_QH = Usbd_GetEpQH((USB_CORE_CTRL_T*) UsbHandle, EPNum);
	DeviceTransferDescriptor*  pDTD = (DeviceTransferDescriptor*) &Rom_dTD;
	IP_USBHS_001_T * USB_Reg;
	USB_Reg = USB_REG(USBPort);

	while ( USB_Reg->ENDPTSTAT & _BIT( EP_Physical2BitPosition(PhyEP) ) )	/* Endpoint is already primed */
	{
	}

	/* Zero out the device transfer descriptors */
	memset((void*)pDTD, 0, sizeof(DeviceTransferDescriptor));

	if(((ENDPTCTRL_REG(USBPort, PhyEP/2)>>2)&EP_TYPE_MASK)==EP_TYPE_ISOCHRONOUS)	// iso out endpoint
	{
		uint32_t mult = (USB_DATA_BUFFER_TEM_LENGTH + 1024) / 1024;
		pDTD->NextTD = LINK_TERMINATE ;
		ep_QH->Mult = mult;
	}
	else if(((ENDPTCTRL_REG(USBPort, PhyEP/2)>>18)&EP_TYPE_MASK)==EP_TYPE_ISOCHRONOUS)// iso in endpoint
	{
		uint32_t mult = (USB_DATA_BUFFER_TEM_LENGTH + 1024) / 1024;
		pDTD->NextTD = LINK_TERMINATE;
		ep_QH->Mult = mult;
	}
	else {																		// other endpoint types
		pDTD->NextTD = LINK_TERMINATE;	/* The next DTD pointer is INVALID */
	}
	
	pDTD->TotalBytes = length;
	pDTD->IntOnComplete = 1;
	pDTD->Active = 1;
	pDTD->MultiplierOverride = 1;

	pDTD->BufferPage[0] = (uint32_t) pData;
	pDTD->BufferPage[1] = ((uint32_t) pData + 0x1000) & 0xfffff000;
	pDTD->BufferPage[2] = ((uint32_t) pData + 0x2000) & 0xfffff000;
	pDTD->BufferPage[3] = ((uint32_t) pData + 0x3000) & 0xfffff000;
	pDTD->BufferPage[4] = ((uint32_t) pData + 0x4000) & 0xfffff000;

	ep_QH->Mult = 1;
	ep_QH->MaxPacketSize = 512;
	ep_QH->overlay.NextTD = (uint32_t) pDTD;
	ep_QH->TransferCount = length;

	/* prime the endpoint for transmit */
	USB_Reg->ENDPTPRIME |= _BIT( EP_Physical2BitPosition(PhyEP) ) ;
}

/** Initialize USBD ADC driver */
void UsbdAdc_Init(USB_ClassInfo_Audio_Device_t* AudioInterface)
{
	uint32_t ep_indx;
	USBD_API->hw->ForceFullSpeed(UsbHandle,1);

	/* register ep0 handler */
	USBD_API->core->RegisterClassHandler(UsbHandle, UsbdAdc_ep0_hdlr, NULL);
	
	StreamInterfaceNumber = AudioInterface->Config.StreamingInterfaceNumber;
	ControlInterfaceNumber = AudioInterface->Config.ControlInterfaceNumber;
	USBPort = AudioInterface->Config.PortNumber;
	/* register ISO OUT endpoint interrupt handler */
	if(AudioInterface->Config.DataOUTEndpointNumber)
	{
		ISOEndpointNumber = AudioInterface->Config.DataOUTEndpointNumber;
		ep_indx = ((ISOEndpointNumber & 0x0F) << 1);
		USBD_API->core->RegisterEpHandler (UsbHandle, ep_indx, UsbdAdc_ISO_Hdlr, NULL);
	}
	else if(AudioInterface->Config.DataINEndpointNumber)
	{
		ISOEndpointNumber = AudioInterface->Config.DataINEndpointNumber;
		ep_indx = ((ISOEndpointNumber & 0x0F) << 1) + 1;
		USBD_API->core->RegisterEpHandler (UsbHandle, ep_indx, UsbdAdc_ISO_Hdlr, NULL);
	}

}

/**----------------------------------------------------------------------------
  ADC_IF_GetRequest: Audio Device Class Interface Get Request Callback
    Called automatically on ADC Interface Get Request
 *----------------------------------------------------------------------------*/
ErrorCode_t ADC_IF_GetRequest (USB_CORE_CTRL_T* pCtrl)
{

    /*
      Interface = SetupPacket.wIndex.WB.L;
      EntityID  = SetupPacket.wIndex.WB.H;
      Request   = SetupPacket.bRequest;
      Value     = SetupPacket.wValue.W;
      ...
    */
    ErrorCode_t ret = ERR_USBD_INVALID_REQ;

    if (pCtrl->SetupPacket.wIndex.W == 0x0200) {
        /* Feature Unit: Interface = 0, ID = 2 */
        if (pCtrl->SetupPacket.wValue.WB.L == 0) {
            /* Master Channel */
            switch (pCtrl->SetupPacket.wValue.WB.H) {
            case AUDIO_MUTE_CONTROL:
                if (pCtrl->SetupPacket.bRequest == AUDIO_REQUEST_GET_CUR) {
                	/*TODO: Get MUTE */
                    //pCtrl->EP0Buf[0] = (ADC_PLAY_MUTE)?1:0;
                    ret = LPC_OK;
                }
                break;
            case AUDIO_VOLUME_CONTROL:
                switch (pCtrl->SetupPacket.bRequest) {
                case AUDIO_REQUEST_GET_CUR:
                    *((uint16_t *)pCtrl->EP0Buf) = curr_vol;
                    ret = LPC_OK;
                    break;
                case AUDIO_REQUEST_GET_MIN:
                    *((uint16_t *)pCtrl->EP0Buf) = VOLUME_MIN;
                    ret = LPC_OK;
                    break;
                case AUDIO_REQUEST_GET_MAX:
                    *((uint16_t *)pCtrl->EP0Buf) = VOLUME_MAX;
                    ret = LPC_OK;
                    break;
                case AUDIO_REQUEST_GET_RES:
                    *((uint16_t *)pCtrl->EP0Buf) = VOLUME_RES;
                    ret = LPC_OK;
                    break;
                }
                break;
            }
        }
    }
    
    return (ret);  /* Not Supported */
}


/**----------------------------------------------------------------------------
  ADC_IF_SetRequest: Audio Device Class Interface Set Request Callback
    Called automatically on ADC Interface Set Request
 *----------------------------------------------------------------------------*/
ErrorCode_t ADC_IF_SetRequest (USB_CORE_CTRL_T* pCtrl)
{

/*
  Interface = SetupPacket.wIndex.WB.L;
  EntityID  = SetupPacket.wIndex.WB.H;
  Request   = SetupPacket.bRequest;
  Value     = SetupPacket.wValue.W;
  ...
*/
    ErrorCode_t ret = ERR_USBD_INVALID_REQ;
    if (pCtrl->SetupPacket.wIndex.W == 0x0200) {
        /* Feature Unit: Interface = 0, ID = 2 */
        if ((pCtrl->SetupPacket.wValue.WB.L == 0) &&
            (pCtrl->SetupPacket.bRequest == AUDIO_REQUEST_SET_CUR)) {
            /* Master Channel */
            switch (pCtrl->SetupPacket.wValue.WB.H) {
            case AUDIO_MUTE_CONTROL:
                if (pCtrl->EP0Buf[0])
                {    /*TODO: set MUTE here */
                }else
                {   /*TODO: disable MUTE here */
                }
                ret = (LPC_OK);
                break;
            case AUDIO_VOLUME_CONTROL:
                /*TODO: Set volume here */
		curr_vol = *((uint16_t *)pCtrl->EP0Buf);
                ret =  (LPC_OK);
                break;
            }
        }
    }

    return ret;  /* Not Supported */
}


/**----------------------------------------------------------------------------
  ADC_EP_GetRequest: Audio Device Class EndPoint Get Request Callback
    Called automatically on ADC EndPoint Get Request
 *----------------------------------------------------------------------------*/
ErrorCode_t ADC_EP_GetRequest (USB_CORE_CTRL_T* pCtrl)
{
    /*
      EndPoint = SetupPacket.wIndex.WB.L;
      Request  = SetupPacket.bRequest;
      Value    = SetupPacket.wValue.W;
      ...
    */
    ErrorCode_t ret = ERR_USBD_INVALID_REQ;
    
    if((pCtrl->SetupPacket.wIndex.W & 0x7F) == ISOEndpointNumber) {
        /* Feature Unit: Interface = 0, ID = 2 */
        if (pCtrl->SetupPacket.wValue.WB.L == 0) {
            /* Master Channel */
            if ((pCtrl->SetupPacket.wValue.WB.H == AUDIO_CONTROL_SAMPLING_FREQ) &&
                (pCtrl->SetupPacket.bRequest == AUDIO_REQUEST_GET_CUR) ) {
                pCtrl->EP0Buf[0] = (uint8_t)(CurrentAudioSampleFrequency & 0xFF);
                pCtrl->EP0Buf[1] = (uint8_t)((CurrentAudioSampleFrequency >> 8) & 0xFF);
                pCtrl->EP0Buf[2] = (uint8_t)((CurrentAudioSampleFrequency >> 16) & 0xFF);
                ret = (LPC_OK);
            }
        }
    }
    return ret;  /* Not Supported */
}


/**----------------------------------------------------------------------------
  ADC_EP_SetRequest: Audio Device Class EndPoint Set Request Callback
    Called automatically on ADC EndPoint Set Request
 *----------------------------------------------------------------------------*/
ErrorCode_t ADC_EP_SetRequest (USB_CORE_CTRL_T* pCtrl) 
{

    /*
      EndPoint = SetupPacket.wIndex.WB.L;
      Request  = SetupPacket.bRequest;
      Value    = SetupPacket.wValue.W;
      ...
    */
    uint32_t rate;
    ErrorCode_t ret = ERR_USBD_INVALID_REQ;
    
    if((pCtrl->SetupPacket.wIndex.W & 0x7F) == ISOEndpointNumber) {
        /* Feature Unit: Interface = 0, ID = 2 */
        if (pCtrl->SetupPacket.wValue.WB.L == 0) {
            /* Master Channel */
            if (pCtrl->SetupPacket.wValue.WB.H == AUDIO_CONTROL_SAMPLING_FREQ) {
                rate = pCtrl->EP0Buf[0] | (pCtrl->EP0Buf[1] << 8) | (pCtrl->EP0Buf[2] << 16);
                if (pCtrl->SetupPacket.bRequest == AUDIO_REQUEST_SET_CUR) {
                	CurrentAudioSampleFrequency = rate;
                	if(CurrentAudioSampleFrequency <= AUDIO_MAX_SAMPLE_FREQ)
                	{
				Audio_Init(CurrentAudioSampleFrequency);
                      ret = LPC_OK;
                    }
                }
            }
        }
    }
    return (ret);  /* Not Supported */
}

/**----------------------------------------------------------------------------
  Override standard Interface Event
 *----------------------------------------------------------------------------*/
ErrorCode_t USB_Interface_Event (USBD_HANDLE_T hUsb)
{
    USB_CORE_CTRL_T* pCtrl = (USB_CORE_CTRL_T*)hUsb;
    uint16_t wIndex = pCtrl->SetupPacket.wIndex.W;
    uint16_t wValue = pCtrl->SetupPacket.wValue.W;
    
    /* write code to enable/disable audo playback when interface 
    ALT setting is changed */
    if (wIndex == StreamInterfaceNumber) {
    	if((wValue == 0x0001)){
    		UsbdAdc_start_xfr();
    	}else
    	{
    		UsbdAdc_stop_xfr();
    	}

    }

    return LPC_OK;
}
/** disable configure event in usbd_rom.c */
ErrorCode_t USB_Configure_Event (USBD_HANDLE_T hUsb)
{
	return LPC_OK;
}

#if defined(__ICCARM__)
/* Temp fix for IAR */
uint32_t TransferDelayidx=0;
volatile uint8_t Event_store[128];
#endif

/**----------------------------------------------------------------------------
  Audio Class handler
 *----------------------------------------------------------------------------*/
ErrorCode_t UsbdAdc_ep0_hdlr(USBD_HANDLE_T hUsb, void* data, uint32_t event)
{
    USB_CORE_CTRL_T* pCtrl = (USB_CORE_CTRL_T*)hUsb;
    ErrorCode_t ret = ERR_USBD_UNHANDLED;
    
    #if defined(__ICCARM__)
    /* Temp fix for IAR */ 
    Event_store[TransferDelayidx] = event;
    #endif
    
    if (pCtrl->SetupPacket.bmRequestType.BM.Type == REQUEST_CLASS) {
        switch (event) {
        case USB_EVT_SETUP:
            if ((pCtrl->SetupPacket.bmRequestType.BM.Recipient == REQUEST_TO_INTERFACE) &&
            ((pCtrl->SetupPacket.wIndex.WB.L == ControlInterfaceNumber)  ||       /* IF number correct? */
            (pCtrl->SetupPacket.wIndex.WB.L == StreamInterfaceNumber)) ) {
                switch (pCtrl->SetupPacket.bRequest) {
                case AUDIO_REQUEST_GET_CUR:
                case AUDIO_REQUEST_GET_MIN:
                case AUDIO_REQUEST_GET_MAX:
                case AUDIO_REQUEST_GET_RES:
                    
                    ret = ADC_IF_GetRequest(pCtrl);
                    if (ret == LPC_OK) {
                        pCtrl->EP0Data.pData = pCtrl->EP0Buf;                     /* point to data to be sent */
                        USBD_API->core->DataInStage(pCtrl);                       /* send requested data */
                    }
                    break;
                case AUDIO_REQUEST_SET_CUR:
                    //                case AUDIO_REQUEST_SET_MIN:
                    //                case AUDIO_REQUEST_SET_MAX:
                    //                case AUDIO_REQUEST_SET_RES:
                    pCtrl->EP0Data.pData = pCtrl->EP0Buf;                              /* data to be received */ 
					
                    ret = LPC_OK;
                    break;
                }
            }
          else if (pCtrl->SetupPacket.bmRequestType.BM.Recipient == REQUEST_TO_ENDPOINT) {
                switch (pCtrl->SetupPacket.bRequest) {
                case AUDIO_REQUEST_GET_CUR:
                case AUDIO_REQUEST_GET_MIN:
                case AUDIO_REQUEST_GET_MAX:
                case AUDIO_REQUEST_GET_RES:
                    ret = ADC_EP_GetRequest(pCtrl);
                    if (ret == LPC_OK) {
                        pCtrl->EP0Data.pData = pCtrl->EP0Buf;                              /* point to data to be sent */
                        USBD_API->core->DataInStage(pCtrl);                                   /* send requested data */
                    }
                    break;
                case AUDIO_REQUEST_SET_CUR:
                    //              case AUDIO_REQUEST_SET_MIN:
                    //              case AUDIO_REQUEST_SET_MAX:
                    //              case AUDIO_REQUEST_SET_RES:
                    pCtrl->EP0Data.pData = pCtrl->EP0Buf;                                /* data to be received */ 
                    ret = LPC_OK;
                    break;
                }
            } 
            break;
        case USB_EVT_OUT:
            if ((pCtrl->SetupPacket.bmRequestType.BM.Recipient == REQUEST_TO_INTERFACE) &&
            ((pCtrl->SetupPacket.wIndex.WB.L == ControlInterfaceNumber)  ||       /* IF number correct? */
            (pCtrl->SetupPacket.wIndex.WB.L == StreamInterfaceNumber)) ) {
                switch (pCtrl->SetupPacket.bRequest) {
                case AUDIO_REQUEST_SET_CUR:
                    //                      case AUDIO_REQUEST_SET_MIN:
                    //                      case AUDIO_REQUEST_SET_MAX:
                    //                      case AUDIO_REQUEST_SET_RES:
                    ret = ADC_IF_SetRequest(pCtrl);
                    if (ret == LPC_OK) {
                        USBD_API->core->StatusInStage(pCtrl);                         /* send Acknowledge */
                    }
                    break;
                }
            } else if (pCtrl->SetupPacket.bmRequestType.BM.Recipient == REQUEST_TO_ENDPOINT) {
                switch (pCtrl->SetupPacket.bRequest) {
                case AUDIO_REQUEST_SET_CUR:
                    //                    case AUDIO_REQUEST_SET_MIN:
                    //                    case AUDIO_REQUEST_SET_MAX:
                    //                    case AUDIO_REQUEST_SET_RES:
                    ret = ADC_EP_SetRequest(pCtrl);
                    if (ret == LPC_OK) {
                        USBD_API->core->StatusInStage(pCtrl);                           /* send Acknowledge */
                    }
                    break;
                }
            }
            break;
        
        default:
            break;
        }
    }  
    return ret;
}

/**----------------------------------------------------------------------------
  Audio Start Transfer Callback
 *----------------------------------------------------------------------------*/
void UsbdAdc_start_xfr(void)
{
	ISO_packet_size = 0;
	uint32_t ISO_buffer_address;
	/* reset audio buffer */
	Audio_Reset_Data_Buffer();
	ISO_buffer_address = CALLBACK_HAL_GetISOBufferAddress(USB_ENDPOINT_IN(ISOEndpointNumber), &ISO_packet_size);
	if(ISO_buffer_address != 0)
		UsbdDcdDataTransfer(USB_ENDPOINT_IN(ISOEndpointNumber), (uint8_t*)ISO_buffer_address, ISO_packet_size);

	ISO_buffer_address = CALLBACK_HAL_GetISOBufferAddress(ISOEndpointNumber, &ISO_packet_size);
	if(ISO_buffer_address != 0)
		UsbdDcdDataTransfer(ISOEndpointNumber, (uint8_t*)ISO_buffer_address, 512);
}

/**----------------------------------------------------------------------------
  Audio Stop Transfer Callback
 *----------------------------------------------------------------------------*/
void UsbdAdc_stop_xfr(void)
{
	ISO_packet_size = 0;
	/* reset audio buffer */
	Audio_Reset_Data_Buffer();
	USBD_API->hw->ResetEP(UsbHandle, ISOEndpointNumber);
	USBD_API->hw->ResetEP(UsbHandle, USB_ENDPOINT_IN(ISOEndpointNumber));
}


/**----------------------------------------------------------------------------
  Audio ISO handler
 *----------------------------------------------------------------------------*/
ErrorCode_t UsbdAdc_ISO_Hdlr (USBD_HANDLE_T hUsb, void* data, uint32_t event)
{
	uint32_t ISO_buffer_address;

	if (event == USB_EVT_OUT) {
		ISO_packet_size = Usbd_GetTransferSize((USB_CORE_CTRL_T *) hUsb, ISOEndpointNumber);
		if (ISO_packet_size != 0) {
			ISO_packet_size = ISO_packet_size;
		}
		/* Send DMA request */
		ISO_buffer_address = CALLBACK_HAL_GetISOBufferAddress(ISOEndpointNumber, &ISO_packet_size);
		UsbdDcdDataTransfer(ISOEndpointNumber, (uint8_t *) ISO_buffer_address, 512);
	}

	if (event == USB_EVT_IN)
	{
		/* Send DMA request */
		ISO_buffer_address = CALLBACK_HAL_GetISOBufferAddress(USB_ENDPOINT_IN(ISOEndpointNumber), &ISO_packet_size);
		UsbdDcdDataTransfer(USB_ENDPOINT_IN(ISOEndpointNumber), (uint8_t*)ISO_buffer_address, ISO_packet_size);
	}

    return LPC_OK;
}

#endif
#endif
