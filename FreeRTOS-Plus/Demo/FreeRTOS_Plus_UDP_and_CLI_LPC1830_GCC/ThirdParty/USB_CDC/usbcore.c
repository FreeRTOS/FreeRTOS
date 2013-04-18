/*----------------------------------------------------------------------------
 *      U S B  -  K e r n e l
 *----------------------------------------------------------------------------
 * Name:    usbcore.c
 * Purpose: USB Core Module
 * Version: V1.20
 *----------------------------------------------------------------------------
 *      This software is supplied "AS IS" without any warranties, express,
 *      implied or statutory, including but not limited to the implied
 *      warranties of fitness for purpose, satisfactory quality and
 *      noninfringement. Keil extends you a royalty-free right to reproduce
 *      and distribute executable files created using this software for use
 *      on NXP Semiconductors LPC family microcontroller devices only. Nothing 
 *      else gives you the right to use this software.
 *
 * Copyright (c) 2009 Keil - An ARM Company. All rights reserved.
 *----------------------------------------------------------------------------
 * History:
 *          V1.20 Added vendor specific requests
 *                Changed string descriptor handling
 *                Reworked Endpoint0
 *          V1.00 Initial Version
 *----------------------------------------------------------------------------*/
#include "lpc18xx.H"
#include "lpc_types.h"

#include "usb.h"
#include "usbcfg.h"
#include "usbhw.h"
#include "usbcore.h"
#include "usbdesc.h"
#include "usbuser.h"

#if (USB_CLASS)

#if (USB_AUDIO)
#include "audio.h"
#include "adcuser.h"
#endif

#if (USB_HID)
#include "hid.h"
#include "hiduser.h"
#endif

#if (USB_MSC)
#include "msc.h"
#include "mscuser.h"
extern MSC_CSW CSW;
#endif

#if (USB_CDC)
#include "cdc.h"
#include "cdcuser.h"
#endif

#endif

#if (USB_VENDOR)
#include "vendor.h"
#endif

#ifdef __CC_ARM
#pragma diag_suppress 111,177,1441
#endif

#if defined   (  __GNUC__  )
#define __packed __attribute__((__packed__))
#endif

uint16_t  USB_DeviceStatus;
uint8_t  USB_DeviceAddress;
uint8_t  USB_Configuration;
uint32_t USB_EndPointMask;
uint32_t USB_EndPointHalt;
uint32_t USB_EndPointStall;                         /* EP must stay stalled */
uint8_t  USB_NumInterfaces;
uint8_t  USB_AltSetting[USB_IF_NUM];

USB_EP_DATA EP0Data;

#pragma pack(4)
uint8_t  EP0Buf[USB_MAX_PACKET0];
USB_SETUP_PACKET SetupPacket;

extern volatile uint32_t DevStatusFS2HS;

/*
 *  Reset USB Core
 *    Parameters:      None
 *    Return Value:    None
 */

void USB_ResetCore (void) {

  USB_DeviceStatus  = USB_POWER;
  USB_DeviceAddress = 0;
  USB_Configuration = 0;
  USB_EndPointMask  = 0x00010001;
  USB_EndPointHalt  = 0x00000000;
  USB_EndPointStall = 0x00000000;
}


/*
 *  USB Request - Setup Stage
 *    Parameters:      None (global SetupPacket)
 *    Return Value:    None
 */

void USB_SetupStage (void) {
  USB_ReadSetupPkt(0x00, (uint32_t *)&SetupPacket);
}


/*
 *  USB Request - Data In Stage
 *    Parameters:      None (global EP0Data)
 *    Return Value:    None
 */

void USB_DataInStage (void) {
  uint32_t cnt;

  if (EP0Data.Count > USB_MAX_PACKET0) {
    cnt = USB_MAX_PACKET0;
  } else {
    cnt = EP0Data.Count;
  }
  cnt = USB_WriteEP(0x80, EP0Data.pData, cnt);
  EP0Data.pData += cnt;
  EP0Data.Count -= cnt;
}


/*
 *  USB Request - Data Out Stage
 *    Parameters:      None (global EP0Data)
 *    Return Value:    None
 */

void USB_DataOutStage (void) {
  uint32_t cnt;

  cnt = USB_ReadEP(0x00, EP0Data.pData);
  EP0Data.pData += cnt;
  EP0Data.Count -= cnt;
}


/*
 *  USB Request - Status In Stage
 *    Parameters:      None
 *    Return Value:    None
 */

void USB_StatusInStage (void) {
  USB_WriteEP(0x80, NULL, 0);
}


/*
 *  USB Request - Status Out Stage
 *    Parameters:      None
 *    Return Value:    None
 */

void USB_StatusOutStage (void) {
  USB_ReadEP(0x00, EP0Buf);
}


/*
 *  Get Status USB Request
 *    Parameters:      None (global SetupPacket)
 *    Return Value:    TRUE - Success, FALSE - Error
 */

INLINE uint32_t USB_ReqGetStatus (void) {
  uint32_t n, m;

  switch (SetupPacket.bmRequestType.BM.Recipient) {
    case REQUEST_TO_DEVICE:
      EP0Data.pData = (uint8_t *)&USB_DeviceStatus;
      break;
    case REQUEST_TO_INTERFACE:
      if ((USB_Configuration != 0) && (SetupPacket.wIndex.WB.L < USB_NumInterfaces)) {
        *((__packed uint16_t *)EP0Buf) = 0;
        EP0Data.pData = EP0Buf;
      } else {
        return (FALSE);
      }
      break;
    case REQUEST_TO_ENDPOINT:
      n = SetupPacket.wIndex.WB.L & 0x8F;
      m = (n & 0x80) ? ((1 << 16) << (n & 0x0F)) : (1 << n);
      if (((USB_Configuration != 0) || ((n & 0x0F) == 0)) && (USB_EndPointMask & m)) {
        *((__packed uint16_t *)EP0Buf) = (USB_EndPointHalt & m) ? 1 : 0;
        EP0Data.pData = EP0Buf;
      } else {
        return (FALSE);
      }
      break;
    default:
      return (FALSE);
  }
  return (TRUE);
}


/*
 *  Set/Clear Feature USB Request
 *    Parameters:      sc:    0 - Clear, 1 - Set
 *                            (global SetupPacket)
 *    Return Value:    TRUE - Success, FALSE - Error
 */

INLINE uint32_t USB_ReqSetClrFeature (uint32_t sc) {
  uint32_t n, m;

  switch (SetupPacket.bmRequestType.BM.Recipient) {
    case REQUEST_TO_DEVICE:
      if (SetupPacket.wValue.W == USB_FEATURE_REMOTE_WAKEUP) {
        if (sc) {
          USB_WakeUpCfg(TRUE);
          USB_DeviceStatus |=  USB_GETSTATUS_REMOTE_WAKEUP;
        } else {
          USB_WakeUpCfg(FALSE);
          USB_DeviceStatus &= ~USB_GETSTATUS_REMOTE_WAKEUP;
        }
      } else if (SetupPacket.wValue.W == USB_FEATURE_TEST_MODE) {
          return USB_SetTestMode(SetupPacket.wIndex.WB.H);
      } else {
        return (FALSE);
      }
      break;
    case REQUEST_TO_INTERFACE:
      return (FALSE);
    case REQUEST_TO_ENDPOINT:
      n = SetupPacket.wIndex.WB.L & 0x8F;
      m = (n & 0x80) ? ((1 << 16) << (n & 0x0F)) : (1 << n);
      if ((USB_Configuration != 0) && ((n & 0x0F) != 0) && (USB_EndPointMask & m)) {
        if (SetupPacket.wValue.W == USB_FEATURE_ENDPOINT_STALL) {
          if (sc) {
            USB_SetStallEP(n);
            USB_EndPointHalt |=  m;
          } else {
            if ((USB_EndPointStall & m) != 0) {
              return (TRUE);
            }
            USB_ClrStallEP(n);
#if (USB_MSC)
            if ((n == MSC_EP_IN) && ((USB_EndPointHalt & m) != 0)) {
              /* Compliance Test: rewrite CSW after unstall */
              if (CSW.dSignature == MSC_CSW_Signature) {
                USB_WriteEP(MSC_EP_IN, (uint8_t *)&CSW, sizeof(CSW));
              }
            }
#endif
            USB_EndPointHalt &= ~m;
          }
        } else {
          return (FALSE);
        }
      } else {
        return (FALSE);
      }
      break;
    default:
      return (FALSE);
  }
  return (TRUE);
}


/*
 *  Set Address USB Request
 *    Parameters:      None (global SetupPacket)
 *    Return Value:    TRUE - Success, FALSE - Error
 */

INLINE uint32_t USB_ReqSetAddress (void) {

  switch (SetupPacket.bmRequestType.BM.Recipient) {
    case REQUEST_TO_DEVICE:
      USB_DeviceAddress = 0x80 | SetupPacket.wValue.WB.L;
      break;
    default:
      return (FALSE);
  }
  return (TRUE);
}


/*
 *  Get Descriptor USB Request
 *    Parameters:      None (global SetupPacket)
 *    Return Value:    TRUE - Success, FALSE - Error
 */

INLINE uint32_t USB_ReqGetDescriptor (void) {
  uint8_t  *pD;
  uint32_t len, n;

  switch (SetupPacket.bmRequestType.BM.Recipient) {
    case REQUEST_TO_DEVICE:
      switch (SetupPacket.wValue.WB.H) {
        case USB_DEVICE_DESCRIPTOR_TYPE:
          EP0Data.pData = (uint8_t *)USB_DeviceDescriptor;
          len = USB_DEVICE_DESC_SIZE;
          break;
        case USB_CONFIGURATION_DESCRIPTOR_TYPE:
          if ( DevStatusFS2HS == FALSE ) { 
            pD = (uint8_t *)USB_FSConfigDescriptor;
          } else {
            pD = (uint8_t *)USB_HSConfigDescriptor;
		      }
          for (n = 0; n != SetupPacket.wValue.WB.L; n++) {
            if (((USB_CONFIGURATION_DESCRIPTOR *)pD)->bLength != 0) {
              pD += ((USB_CONFIGURATION_DESCRIPTOR *)pD)->wTotalLength;
            }
          }
          if (((USB_CONFIGURATION_DESCRIPTOR *)pD)->bLength == 0) {
            return (FALSE);
          }
          EP0Data.pData = pD;
          len = ((USB_CONFIGURATION_DESCRIPTOR *)pD)->wTotalLength;
          break;
        case USB_STRING_DESCRIPTOR_TYPE:
          pD = (uint8_t *)USB_StringDescriptor;
          for (n = 0; n != SetupPacket.wValue.WB.L; n++) {
            if (((USB_STRING_DESCRIPTOR *)pD)->bLength != 0) {
              pD += ((USB_STRING_DESCRIPTOR *)pD)->bLength;
            }
          }
          if (((USB_STRING_DESCRIPTOR *)pD)->bLength == 0) {
            return (FALSE);
          }
          EP0Data.pData = pD;
          len = ((USB_STRING_DESCRIPTOR *)pD)->bLength;
          break;
        case USB_DEVICE_QUALIFIER_DESCRIPTOR_TYPE:
          /* USB Chapter 9. page 9.6.2 */
          if ( DevStatusFS2HS == FALSE ) {
	          return (FALSE);
          }
          else
          {
      	     EP0Data.pData = (uint8_t *)USB_DeviceQualifier;
	           len = USB_DEVICE_QUALI_SIZE;
          }
          break;
        case USB_OTHER_SPEED_CONFIG_DESCRIPTOR_TYPE:
		      if ( DevStatusFS2HS == TRUE ) { 
                pD = (uint8_t *)USB_FSOtherSpeedConfiguration;
              } else {
                pD = (uint8_t *)USB_HSOtherSpeedConfiguration;
		      }
          
          for (n = 0; n != SetupPacket.wValue.WB.L; n++) {
            if (((USB_OTHER_SPEED_CONFIGURATION *)pD)->bLength != 0) {
              pD += ((USB_OTHER_SPEED_CONFIGURATION *)pD)->wTotalLength;
            }
          }
          if (((USB_OTHER_SPEED_CONFIGURATION *)pD)->bLength == 0) {
            return (FALSE);
          }
          EP0Data.pData = pD;
          len = ((USB_OTHER_SPEED_CONFIGURATION *)pD)->wTotalLength;
          break;
        default:
          return (FALSE);
      }
      break;
    case REQUEST_TO_INTERFACE:
      switch (SetupPacket.wValue.WB.H) {
#if USB_HID
        case HID_HID_DESCRIPTOR_TYPE:
          if (SetupPacket.wIndex.WB.L != USB_HID_IF_NUM) {
            return (FALSE);    /* Only Single HID Interface is supported */
          }
		  if ( DevStatusFS2HS == FALSE ) { 
            EP0Data.pData = (uint8_t *)USB_FSConfigDescriptor + HID_DESC_OFFSET;
          } else {
		    EP0Data.pData = (uint8_t *)USB_HSConfigDescriptor + HID_DESC_OFFSET;
		  }
          len = HID_DESC_SIZE;
          break;
        case HID_REPORT_DESCRIPTOR_TYPE:
          if (SetupPacket.wIndex.WB.L != USB_HID_IF_NUM) {
            return (FALSE);    /* Only Single HID Interface is supported */
          }
          EP0Data.pData = (uint8_t *)HID_ReportDescriptor;
          len = HID_ReportDescSize;
          break;
        case HID_PHYSICAL_DESCRIPTOR_TYPE:
          return (FALSE);      /* HID Physical Descriptor is not supported */
#endif
        default:
          return (FALSE);
      }
      break;
    default:
      return (FALSE);
  }

  if (EP0Data.Count > len) {
    EP0Data.Count = len;
  }

  return (TRUE);
}


/*
 *  Get Configuration USB Request
 *    Parameters:      None (global SetupPacket)
 *    Return Value:    TRUE - Success, FALSE - Error
 */

INLINE uint32_t USB_ReqGetConfiguration (void) {

  switch (SetupPacket.bmRequestType.BM.Recipient) {
    case REQUEST_TO_DEVICE:
      EP0Data.pData = &USB_Configuration;
      break;
    default:
      return (FALSE);
  }
  return (TRUE);
}


/*
 *  Set Configuration USB Request
 *    Parameters:      None (global SetupPacket)
 *    Return Value:    TRUE - Success, FALSE - Error
 */

INLINE uint32_t USB_ReqSetConfiguration (void) {
  USB_COMMON_DESCRIPTOR *pD;
  uint32_t alt = 0;
  uint32_t n, m;
  uint32_t new_addr;
  switch (SetupPacket.bmRequestType.BM.Recipient) {
    case REQUEST_TO_DEVICE:

      if (SetupPacket.wValue.WB.L) {
        if ( DevStatusFS2HS == FALSE ) { 
          pD = (USB_COMMON_DESCRIPTOR *)USB_FSConfigDescriptor;
	    } else {
	      pD = (USB_COMMON_DESCRIPTOR *)USB_HSConfigDescriptor;
	    }
        while (pD->bLength) {
          switch (pD->bDescriptorType) {
            case USB_CONFIGURATION_DESCRIPTOR_TYPE:
              if (((USB_CONFIGURATION_DESCRIPTOR *)pD)->bConfigurationValue == SetupPacket.wValue.WB.L) {
                USB_Configuration = SetupPacket.wValue.WB.L;
                USB_NumInterfaces = ((USB_CONFIGURATION_DESCRIPTOR *)pD)->bNumInterfaces;
                for (n = 0; n < USB_IF_NUM; n++) {
                  USB_AltSetting[n] = 0;
                }
              for (n = 1; n < USB_EP_NUM; n++) {
                  if (USB_EndPointMask & (1 << n)) {
                    USB_DisableEP(n);
                  }
                  if (USB_EndPointMask & ((1 << 16) << n)) {
                    USB_DisableEP(n | 0x80);
                  }
                }
                USB_EndPointMask = 0x00010001;
                USB_EndPointHalt = 0x00000000;
                USB_EndPointStall= 0x00000000;
                USB_Configure(TRUE);
                if (((USB_CONFIGURATION_DESCRIPTOR *)pD)->bmAttributes & USB_CONFIG_POWERED_MASK) {
                  USB_DeviceStatus |=  USB_GETSTATUS_SELF_POWERED;
                } else {
                  USB_DeviceStatus &= ~USB_GETSTATUS_SELF_POWERED;
                }
              } else {
              new_addr = (uint32_t)pD + ((USB_CONFIGURATION_DESCRIPTOR *)pD)->wTotalLength;
              pD = (USB_COMMON_DESCRIPTOR*)new_addr;
                continue;
              }
              break;
            case USB_INTERFACE_DESCRIPTOR_TYPE:
              alt = ((USB_INTERFACE_DESCRIPTOR *)pD)->bAlternateSetting;
              break;
            case USB_ENDPOINT_DESCRIPTOR_TYPE:
              if (alt == 0) {
                n = ((USB_ENDPOINT_DESCRIPTOR *)pD)->bEndpointAddress & 0x8F;
                m = (n & 0x80) ? ((1 << 16) << (n & 0x0F)) : (1 << n);
                USB_EndPointMask |= m;
                USB_ConfigEP((USB_ENDPOINT_DESCRIPTOR *)pD);
                USB_EnableEP(n);
                USB_ResetEP(n);
              }
              break;
          }
        new_addr = (uint32_t)pD + pD->bLength;
        pD = (USB_COMMON_DESCRIPTOR*)new_addr;
        }
      }
      else {
        USB_Configuration = 0;
      for (n = 1; n < USB_EP_NUM; n++) {
          if (USB_EndPointMask & (1 << n)) {
            USB_DisableEP(n);
          }
          if (USB_EndPointMask & ((1 << 16) << n)) {
            USB_DisableEP(n | 0x80);
          }
        }
        USB_EndPointMask  = 0x00010001;
        USB_EndPointHalt  = 0x00000000;
        USB_EndPointStall = 0x00000000;
        USB_Configure(FALSE);
      }

      if (USB_Configuration != SetupPacket.wValue.WB.L) {
        return (FALSE);
      }
      break;
    default:
      return (FALSE);
  }
  return (TRUE);
}


/*
 *  Get Interface USB Request
 *    Parameters:      None (global SetupPacket)
 *    Return Value:    TRUE - Success, FALSE - Error
 */

INLINE uint32_t USB_ReqGetInterface (void) {

  switch (SetupPacket.bmRequestType.BM.Recipient) {
    case REQUEST_TO_INTERFACE:
      if ((USB_Configuration != 0) && (SetupPacket.wIndex.WB.L < USB_NumInterfaces)) {
        EP0Data.pData = USB_AltSetting + SetupPacket.wIndex.WB.L;
      } else {
        return (FALSE);
      }
      break;
    default:
      return (FALSE);
  }
  return (TRUE);
}


/*
 *  Set Interface USB Request
 *    Parameters:      None (global SetupPacket)
 *    Return Value:    TRUE - Success, FALSE - Error
 */

INLINE uint32_t USB_ReqSetInterface (void) {
  USB_COMMON_DESCRIPTOR *pD;
  uint32_t ifn = 0, alt = 0, old = 0, msk = 0;
  uint32_t n, m;
  uint32_t set, new_addr;

  switch (SetupPacket.bmRequestType.BM.Recipient) {
    case REQUEST_TO_INTERFACE:
      if (USB_Configuration == 0) return (FALSE);
      set = FALSE;
      if ( DevStatusFS2HS == FALSE ) { 
        pD  = (USB_COMMON_DESCRIPTOR *)USB_FSConfigDescriptor;
      } else {
        pD  = (USB_COMMON_DESCRIPTOR *)USB_HSConfigDescriptor;
      }
      while (pD->bLength) {
        switch (pD->bDescriptorType) {
          case USB_CONFIGURATION_DESCRIPTOR_TYPE:
            if (((USB_CONFIGURATION_DESCRIPTOR *)pD)->bConfigurationValue != USB_Configuration) {
              new_addr = (uint32_t)pD + ((USB_CONFIGURATION_DESCRIPTOR *)pD)->wTotalLength;
              pD = (USB_COMMON_DESCRIPTOR*)new_addr;
              continue;
            }
            break;
          case USB_INTERFACE_DESCRIPTOR_TYPE:
            ifn = ((USB_INTERFACE_DESCRIPTOR *)pD)->bInterfaceNumber;
            alt = ((USB_INTERFACE_DESCRIPTOR *)pD)->bAlternateSetting;
            msk = 0;
            if ((ifn == SetupPacket.wIndex.WB.L) && (alt == SetupPacket.wValue.WB.L)) {
              set = TRUE;
              old = USB_AltSetting[ifn];
              USB_AltSetting[ifn] = (uint8_t)alt;
            }
            break;
          case USB_ENDPOINT_DESCRIPTOR_TYPE:
            if (ifn == SetupPacket.wIndex.WB.L) {
              n = ((USB_ENDPOINT_DESCRIPTOR *)pD)->bEndpointAddress & 0x8F;
              m = (n & 0x80) ? ((1 << 16) << (n & 0x0F)) : (1 << n);
              if (alt == SetupPacket.wValue.WB.L) {
                USB_EndPointMask |=  m;
                USB_EndPointHalt &= ~m;
                USB_ConfigEP((USB_ENDPOINT_DESCRIPTOR *)pD);
                USB_EnableEP(n);
                USB_ResetEP(n);
                msk |= m;
              }
              else if ((alt == old) && ((msk & m) == 0)) {
                USB_EndPointMask &= ~m;
                USB_EndPointHalt &= ~m;
                USB_DisableEP(n);
              }
            }
           break;
        }
        new_addr = (uint32_t)pD + pD->bLength;
        pD = (USB_COMMON_DESCRIPTOR*)new_addr;
      }
      break;
    default:
      return (FALSE);
  }

  return (set);
}


/*
 *  USB Endpoint 0 Event Callback
 *    Parameters:      event
 *    Return Value:    none
 */
 
void USB_EndPoint0 (uint32_t event) {

  switch (event) {
    case USB_EVT_SETUP:
      USB_SetupStage();
      USB_DirCtrlEP(SetupPacket.bmRequestType.BM.Dir);
      EP0Data.Count = SetupPacket.wLength;     /* Number of bytes to transfer */
      switch (SetupPacket.bmRequestType.BM.Type) {

        case REQUEST_STANDARD:
          switch (SetupPacket.bRequest) {
            case USB_REQUEST_GET_STATUS:
              if (!USB_ReqGetStatus()) {
                goto stall_i;
              }
              USB_DataInStage();
              break;

            case USB_REQUEST_CLEAR_FEATURE:
              if (!USB_ReqSetClrFeature(0)) {
                goto stall_i;
              }
              USB_StatusInStage();
#if USB_FEATURE_EVENT
              USB_Feature_Event();
#endif
              break;

            case USB_REQUEST_SET_FEATURE:
              if (!USB_ReqSetClrFeature(1)) {
                goto stall_i;
              }
              USB_StatusInStage();
#if USB_FEATURE_EVENT
              USB_Feature_Event();
#endif
              break;

            case USB_REQUEST_SET_ADDRESS:
              if (!USB_ReqSetAddress()) {
                goto stall_i;
              }
              USB_StatusInStage();
              break;

            case USB_REQUEST_GET_DESCRIPTOR:
              if (!USB_ReqGetDescriptor()) {
                goto stall_i;
              }
              USB_DataInStage();
              break;

            case USB_REQUEST_SET_DESCRIPTOR:
/*stall_o:*/  USB_SetStallEP(0x00);            /* not supported */
              EP0Data.Count = 0;
              break;

            case USB_REQUEST_GET_CONFIGURATION:
              if (!USB_ReqGetConfiguration()) {
                goto stall_i;
              }
              USB_DataInStage();
              break;

            case USB_REQUEST_SET_CONFIGURATION:
              if (!USB_ReqSetConfiguration()) {
                goto stall_i;
              }
              USB_StatusInStage();
#if USB_CONFIGURE_EVENT
              USB_Configure_Event();
#endif
              break;

            case USB_REQUEST_GET_INTERFACE:
              if (!USB_ReqGetInterface()) {
                goto stall_i;
              }
              USB_DataInStage();
              break;

            case USB_REQUEST_SET_INTERFACE:
              if (!USB_ReqSetInterface()) {
                goto stall_i;
              }
              USB_StatusInStage();
#if USB_INTERFACE_EVENT
              USB_Interface_Event();
#endif
              break;

            default:
              goto stall_i;
          }
          break;  /* end case REQUEST_STANDARD */

#if USB_CLASS
        case REQUEST_CLASS:
          switch (SetupPacket.bmRequestType.BM.Recipient) {

            case REQUEST_TO_DEVICE:
              goto stall_i;                                              /* not supported */

            case REQUEST_TO_INTERFACE:
#if USB_HID
              if (SetupPacket.wIndex.WB.L == USB_HID_IF_NUM) {           /* IF number correct? */
                switch (SetupPacket.bRequest) {
                  case HID_REQUEST_GET_REPORT:
                    if (HID_GetReport()) {
                      EP0Data.pData = EP0Buf;                            /* point to data to be sent */
                      USB_DataInStage();                                 /* send requested data */
                      goto setup_class_ok;
                    }
                    break;
                  case HID_REQUEST_SET_REPORT:
                    EP0Data.pData = EP0Buf;                              /* data to be received */ 
                    goto setup_class_ok;
                  case HID_REQUEST_GET_IDLE:
                    if (HID_GetIdle()) {
                      EP0Data.pData = EP0Buf;                            /* point to data to be sent */
                      USB_DataInStage();                                 /* send requested data */
                      goto setup_class_ok;
                    }
                    break;
                  case HID_REQUEST_SET_IDLE:
                    if (HID_SetIdle()) {
                      USB_StatusInStage();                               /* send Acknowledge */
                      goto setup_class_ok;
                    }
                    break;
                  case HID_REQUEST_GET_PROTOCOL:
                    if (HID_GetProtocol()) {
                      EP0Data.pData = EP0Buf;                            /* point to data to be sent */
                      USB_DataInStage();                                 /* send requested data */
                      goto setup_class_ok;
                    }
                    break;
                  case HID_REQUEST_SET_PROTOCOL:
                    if (HID_SetProtocol()) {
                      USB_StatusInStage();                               /* send Acknowledge */
                      goto setup_class_ok;
                    }
                    break;
                }
              }
#endif  /* USB_HID */
#if USB_MSC
              if (SetupPacket.wIndex.WB.L == USB_MSC_IF_NUM) {           /* IF number correct? */
                switch (SetupPacket.bRequest) {
                  case MSC_REQUEST_RESET:
                    if ((SetupPacket.wValue.W == 0) &&	                 /* RESET with invalid parameters -> STALL */
                        (SetupPacket.wLength  == 0)) {
                      if (MSC_Reset()) {
                        USB_StatusInStage();
                        goto setup_class_ok;
                      }
                    }
                    break;
                  case MSC_REQUEST_GET_MAX_LUN:
                    if ((SetupPacket.wValue.W == 0) &&	                 /* GET_MAX_LUN with invalid parameters -> STALL */
                        (SetupPacket.wLength  == 1)) { 
                      if (MSC_GetMaxLUN()) {
                        EP0Data.pData = EP0Buf;
                        USB_DataInStage();
                        goto setup_class_ok;
                      }
                    }
                    break;
                }
              }
#endif  /* USB_MSC */
#if USB_AUDIO
              if ((SetupPacket.wIndex.WB.L == USB_ADC_CIF_NUM)  ||       /* IF number correct? */
                  (SetupPacket.wIndex.WB.L == USB_ADC_SIF1_NUM) ||
                  (SetupPacket.wIndex.WB.L == USB_ADC_SIF2_NUM)) {
                switch (SetupPacket.bRequest) {
                  case AUDIO_REQUEST_GET_CUR:
                  case AUDIO_REQUEST_GET_MIN:
                  case AUDIO_REQUEST_GET_MAX:
                  case AUDIO_REQUEST_GET_RES:
                    if (ADC_IF_GetRequest()) {
                      EP0Data.pData = EP0Buf;                            /* point to data to be sent */
                      USB_DataInStage();                                 /* send requested data */
                      goto setup_class_ok;
                    }
                    break;
                  case AUDIO_REQUEST_SET_CUR:
//                case AUDIO_REQUEST_SET_MIN:
//                case AUDIO_REQUEST_SET_MAX:
//                case AUDIO_REQUEST_SET_RES:
                    EP0Data.pData = EP0Buf;                              /* data to be received */ 
                    goto setup_class_ok;
                }
              }
#endif  /* USB_AUDIO */
#if USB_CDC
              if ((SetupPacket.wIndex.WB.L == USB_CDC_CIF_NUM)  ||       /* IF number correct? */
                  (SetupPacket.wIndex.WB.L == USB_CDC_DIF_NUM)) {
                switch (SetupPacket.bRequest) {
                  case CDC_SEND_ENCAPSULATED_COMMAND:
                    EP0Data.pData = EP0Buf;                              /* data to be received, see USB_EVT_OUT */
                    goto setup_class_ok;
                  case CDC_GET_ENCAPSULATED_RESPONSE:
                    if (CDC_GetEncapsulatedResponse()) {
                      EP0Data.pData = EP0Buf;                            /* point to data to be sent */
                      USB_DataInStage();                                 /* send requested data */
                      goto setup_class_ok;
                    }
                    break;
                  case CDC_SET_COMM_FEATURE:
                    EP0Data.pData = EP0Buf;                              /* data to be received, see USB_EVT_OUT */
                    goto setup_class_ok;
                  case CDC_GET_COMM_FEATURE:
                    if (CDC_GetCommFeature(SetupPacket.wValue.W)) {
                      EP0Data.pData = EP0Buf;                            /* point to data to be sent */
                      USB_DataInStage();                                 /* send requested data */
                      goto setup_class_ok;
                    }
                    break;
                  case CDC_CLEAR_COMM_FEATURE:
                    if (CDC_ClearCommFeature(SetupPacket.wValue.W)) {
                      USB_StatusInStage();                               /* send Acknowledge */
                      goto setup_class_ok;
                    }
                    break;
                  case CDC_SET_LINE_CODING:
                    EP0Data.pData = EP0Buf;                              /* data to be received, see USB_EVT_OUT */
                    goto setup_class_ok;
                  case CDC_GET_LINE_CODING:
                    if (CDC_GetLineCoding()) {
                      EP0Data.pData = EP0Buf;                            /* point to data to be sent */
                      USB_DataInStage();                                 /* send requested data */
                      goto setup_class_ok;
                    }
                    break;
                  case CDC_SET_CONTROL_LINE_STATE:
                    if (CDC_SetControlLineState(SetupPacket.wValue.W)) {
                      USB_StatusInStage();                               /* send Acknowledge */
                      goto setup_class_ok;
                    }
                    break;
                  case CDC_SEND_BREAK:
                    if (CDC_SendBreak(SetupPacket.wValue.W)) {
                      USB_StatusInStage();                               /* send Acknowledge */
                      goto setup_class_ok;
                    }
                    break;
                }
              }
#endif  /* USB_CDC */
              goto stall_i;                                              /* not supported */
              /* end case REQUEST_TO_INTERFACE */

            case REQUEST_TO_ENDPOINT:
#if USB_AUDIO
              switch (SetupPacket.bRequest) {
                case AUDIO_REQUEST_GET_CUR:
                case AUDIO_REQUEST_GET_MIN:
                case AUDIO_REQUEST_GET_MAX:
                case AUDIO_REQUEST_GET_RES:
                  if (ADC_EP_GetRequest()) {
                    EP0Data.pData = EP0Buf;                              /* point to data to be sent */
                    USB_DataInStage();                                   /* send requested data */
                    goto setup_class_ok;
                  }
                  break;
                case AUDIO_REQUEST_SET_CUR:
//              case AUDIO_REQUEST_SET_MIN:
//              case AUDIO_REQUEST_SET_MAX:
//              case AUDIO_REQUEST_SET_RES:
                  EP0Data.pData = EP0Buf;                                /* data to be received */ 
                  goto setup_class_ok;
              }
#endif  /* USB_AUDIO */
              goto stall_i;
              /* end case REQUEST_TO_ENDPOINT */

            default:
              goto stall_i;
          }
setup_class_ok:                                                          /* request finished successfully */
          break;  /* end case REQUEST_CLASS */
#endif  /* USB_CLASS */

#if USB_VENDOR
        case REQUEST_VENDOR:
          switch (SetupPacket.bmRequestType.BM.Recipient) {

            case REQUEST_TO_DEVICE:
              if (!USB_ReqVendorDev(TRUE)) {
                goto stall_i;                                            /* not supported */               
              }
              break;

            case REQUEST_TO_INTERFACE:
              if (!USB_ReqVendorIF(TRUE)) {
                goto stall_i;                                            /* not supported */               
              }
              break;

            case REQUEST_TO_ENDPOINT:
              if (!USB_ReqVendorEP(TRUE)) {
                goto stall_i;                                            /* not supported */               
              }
              break;

            default:
              goto stall_i;
          }

          if (SetupPacket.wLength) {
            if (SetupPacket.bmRequestType.BM.Dir == REQUEST_DEVICE_TO_HOST) {
              USB_DataInStage();
            }
          } else {
            USB_StatusInStage();
          }

          break;  /* end case REQUEST_VENDOR */ 
#endif  /* USB_VENDOR */

        default:
stall_i:  USB_SetStallEP(0x80);
          EP0Data.Count = 0;
          break;
      }
      break;  /* end case USB_EVT_SETUP */

    case USB_EVT_OUT_NAK:
      if (SetupPacket.bmRequestType.BM.Dir == 0)
      {
        USB_ReadReqEP(0x00, EP0Data.pData, EP0Data.Count);
      }
      else
      {
        /* might be zero length pkt */
        USB_ReadReqEP(0x00, EP0Data.pData, 0);
      }
      break;
    case USB_EVT_OUT:
      if (SetupPacket.bmRequestType.BM.Dir == REQUEST_HOST_TO_DEVICE) {
        if (EP0Data.Count) {                                             /* still data to receive ? */
          USB_DataOutStage();                                            /* receive data */
          if (EP0Data.Count == 0) {                                      /* data complete ? */
            switch (SetupPacket.bmRequestType.BM.Type) {

              case REQUEST_STANDARD:
                goto stall_i;                                            /* not supported */

#if (USB_CLASS) 
              case REQUEST_CLASS:
                switch (SetupPacket.bmRequestType.BM.Recipient) {
                  case REQUEST_TO_DEVICE:
                    goto stall_i;                                        /* not supported */

                  case REQUEST_TO_INTERFACE:
#if USB_HID
                    if (SetupPacket.wIndex.WB.L == USB_HID_IF_NUM) {     /* IF number correct? */
                      switch (SetupPacket.bRequest) {
                        case HID_REQUEST_SET_REPORT:
                          if (HID_SetReport()) {
                            USB_StatusInStage();                         /* send Acknowledge */
                            goto out_class_ok;
                          }
                          break;
                      }
                    }
#endif  /* USB_HID */  
#if USB_AUDIO
                    if ((SetupPacket.wIndex.WB.L == USB_ADC_CIF_NUM)  || /* IF number correct? */
                        (SetupPacket.wIndex.WB.L == USB_ADC_SIF1_NUM) ||
                        (SetupPacket.wIndex.WB.L == USB_ADC_SIF2_NUM)) {
                      switch (SetupPacket.bRequest) {
                        case AUDIO_REQUEST_SET_CUR:
//                      case AUDIO_REQUEST_SET_MIN:
//                      case AUDIO_REQUEST_SET_MAX:
//                      case AUDIO_REQUEST_SET_RES:
                          if (ADC_IF_SetRequest()) {
                            USB_StatusInStage();                         /* send Acknowledge */
                            goto out_class_ok;
                          }
                          break;
                      }
                    }
#endif  /* USB_AUDIO */
#if USB_CDC
                    if ((SetupPacket.wIndex.WB.L == USB_CDC_CIF_NUM)  || /* IF number correct? */
                        (SetupPacket.wIndex.WB.L == USB_CDC_DIF_NUM)) {
                      switch (SetupPacket.bRequest) {
                        case CDC_SEND_ENCAPSULATED_COMMAND:
                          if (CDC_SendEncapsulatedCommand()) {
                            USB_StatusInStage();                         /* send Acknowledge */
                            goto out_class_ok;
                          }
                          break;
                        case CDC_SET_COMM_FEATURE:
                          if (CDC_SetCommFeature(SetupPacket.wValue.W)) {
                            USB_StatusInStage();                         /* send Acknowledge */
                            goto out_class_ok;
                          }
                          break;
                        case CDC_SET_LINE_CODING:
                          if (CDC_SetLineCoding()) {
                            USB_StatusInStage();                         /* send Acknowledge */
                            goto out_class_ok;
                          }
                          break;
                      }
                    } 
#endif  /* USB_CDC */
                    goto stall_i;
                    /* end case REQUEST_TO_INTERFACE */

                  case REQUEST_TO_ENDPOINT:
#if USB_AUDIO
                    switch (SetupPacket.bRequest) {
                      case AUDIO_REQUEST_SET_CUR:
//                    case AUDIO_REQUEST_SET_MIN:
//                    case AUDIO_REQUEST_SET_MAX:
//                    case AUDIO_REQUEST_SET_RES:
                        if (ADC_EP_SetRequest()) {
                          USB_StatusInStage();                           /* send Acknowledge */
                          goto out_class_ok;
                        }
                        break;
                    }
#endif  /* USB_AUDIO */
                    goto stall_i;
                    /* end case REQUEST_TO_ENDPOINT */

                  default:
                    goto stall_i;
                }
out_class_ok:                                                            /* request finished successfully */
                break; /* end case REQUEST_CLASS */
#endif  /* USB_CLASS */

#if USB_VENDOR
              case REQUEST_VENDOR:
                switch (SetupPacket.bmRequestType.BM.Recipient) {
      
                  case REQUEST_TO_DEVICE:
                    if (!USB_ReqVendorDev(FALSE)) {
                      goto stall_i;                                      /* not supported */               
                    }
                    break;
      
                  case REQUEST_TO_INTERFACE:
                    if (!USB_ReqVendorIF(FALSE)) {
                      goto stall_i;                                      /* not supported */               
                    }
                    break;
      
                  case REQUEST_TO_ENDPOINT:
                    if (!USB_ReqVendorEP(FALSE)) {
                      goto stall_i;                                      /* not supported */               
                    }
                    break;
      
                  default:
                    goto stall_i;
                }
      
                USB_StatusInStage();
      
                break;  /* end case REQUEST_VENDOR */ 
#endif  /* USB_VENDOR */

              default:
                goto stall_i;
            }
          }
        }
      } else {
        USB_StatusOutStage();                                            /* receive Acknowledge */
      }
      break;  /* end case USB_EVT_OUT */

    case USB_EVT_IN :
      if (SetupPacket.bmRequestType.BM.Dir == REQUEST_DEVICE_TO_HOST) {
        USB_DataInStage();                                               /* send data */
      } else {
        if (USB_DeviceAddress & 0x80) {
          USB_DeviceAddress &= 0x7F;
          USB_SetAddress(USB_DeviceAddress);
        }
      }
      break;  /* end case USB_EVT_IN */

    case USB_EVT_OUT_STALL:
      USB_ClrStallEP(0x00);
      break;

    case USB_EVT_IN_STALL:
      USB_ClrStallEP(0x80);
      break;

  }
}
