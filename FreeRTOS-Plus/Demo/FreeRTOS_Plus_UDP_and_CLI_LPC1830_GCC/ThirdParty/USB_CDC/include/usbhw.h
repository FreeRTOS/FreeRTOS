/*----------------------------------------------------------------------------
 *      U S B  -  K e r n e l
 *----------------------------------------------------------------------------
 * Name:    usbhw.h
 * Purpose: USB Hardware Layer Definitions
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
 *          V1.20 Added USB_ClearEPBuf 
 *          V1.00 Initial Version
 *----------------------------------------------------------------------------*/

#ifndef __USBHW_H__
#define __USBHW_H__
#include "usb.h"
/* dTD Transfer Description */
typedef volatile struct
{
  volatile uint32_t next_dTD;
  volatile uint32_t total_bytes ;
  volatile uint32_t buffer0;
  volatile uint32_t buffer1;
  volatile uint32_t buffer2;
  volatile uint32_t buffer3;
  volatile uint32_t buffer4;
  volatile uint32_t reserved;
}  DTD_T;

/* dQH  Queue Head */
typedef volatile struct
{
  volatile uint32_t cap;
  volatile uint32_t curr_dTD;
  volatile uint32_t next_dTD;
  volatile uint32_t total_bytes;
  volatile uint32_t buffer0;
  volatile uint32_t buffer1;
  volatile uint32_t buffer2;
  volatile uint32_t buffer3;
  volatile uint32_t buffer4;
  volatile uint32_t reserved;
  volatile uint32_t setup[2];
  volatile uint32_t gap[4];
}  DQH_T;

/* bit defines for USBCMD register */
#define USBCMD_RS	    (1<<0)
#define USBCMD_RST	    (1<<1)
#define USBCMD_ATDTW 	(1<<12)
#define USBCMD_SUTW	    (1<<13)

/* bit defines for USBSTS register */
#define USBSTS_UI	    (1<<0)
#define USBSTS_UEI	    (1<<1)
#define USBSTS_PCI	    (1<<2)
#define USBSTS_URI	    (1<<6)
#define USBSTS_SRI	    (1<<7)
#define USBSTS_SLI	    (1<<8)
#define USBSTS_NAKI	    (1<<16)

/* bit defines for DEVICEADDR register */
#define USBDEV_ADDR_AD	(1<<24)
#define USBDEV_ADDR(n)	(((n) & 0x7F)<<25)

/* bit defines for PRTSC1 register */
#define USBPRTS_CCS     (1<<0)
#define USBPRTS_PE      (1<<2)
#define USBPRTS_FPR     (1<<6)
#define USBPRTS_SUSP    (1<<7)
#define USBPRTS_PR      (1<<8)
#define USBPRTS_HSP     (1<<9)
#define USBPRTS_PLPSCD  (1<<23)
#define USBPRTS_PFSC    (1<<24)

/* bit defines for USBMODE register */
#define USBMODE_CM_IDLE	(0x0<<0)
#define USBMODE_CM_DEV	(0x2<<0)
#define USBMODE_CM_HOST	(0x3<<0)
#define USBMODE_SLOM    (1<<3)
#define USBMODE_SDIS    (1<<4)

/* bit defines for EP registers*/
#define USB_EP_BITPOS(n) (((n) & 0x80)? (0x10 | ((n) & 0x7)) : ((n) & 0x7))

/* bit defines EPcontrol registers*/
#define EPCTRL_RXS	      (1<<0)
#define EPCTRL_RX_TYPE(n) (((n) & 0x3)<<2)
#define EPCTRL_RX_CTL	  (0<<2)
#define EPCTRL_RX_ISO	  (1<<2)
#define EPCTRL_RX_BLK	  (2<<2)
#define EPCTRL_RXI	      (1<<5)
#define EPCTRL_RXR	      (1<<6)
#define EPCTRL_RXE	      (1<<7)
#define EPCTRL_TXS	      (1<<16)
#define EPCTRL_TX_TYPE(n) (((n) & 0x3)<<18)
#define EPCTRL_TX_CTL	  (0<<18)
#define EPCTRL_TX_ISO	  (1<<18)
#define EPCTRL_TX_BLK	  (2<<18)
#define EPCTRL_TX_INT	  (3<<18)
#define EPCTRL_TXI	      (1<<21)
#define EPCTRL_TXR	      (1<<22)
#define EPCTRL_TXE	      (1<<23)

/* dQH field and bit defines */
/* Temp fixed on max, should be taken out of table */
#define QH_MAX_CTRL_PAYLOAD       0x03ff
#define QH_MAX_PKT_LEN_POS            16
#define QH_MAXP(n)                (((n) & 0x3FF)<<16)
#define QH_IOS                    (1<<15)
#define QH_ZLT                    (1<<29)

/* dTD field and bit defines */
#define TD_NEXT_TERMINATE         (1<<0)
#define TD_IOC                    (1<<15)

/* Total physical enpoints*/
#define EP_NUM_MAX	8


/* USB Hardware Functions */
extern void  USB_Init       (LPC_USBDRV_INIT_T* cbs);
extern void  USB_Connect    (uint32_t  con);
extern void  USB_Reset      (void);
extern void  USB_Suspend    (void);
extern void  USB_Resume     (void);
extern void  USB_WakeUp     (void);
extern void  USB_WakeUpCfg  (uint32_t  cfg);
extern void  USB_SetAddress (uint32_t adr);
extern void  USB_Configure  (uint32_t  cfg);
extern void  USB_ConfigEP   (USB_ENDPOINT_DESCRIPTOR *pEPD);
extern void  USB_DirCtrlEP  (uint32_t dir);
extern void  USB_EnableEP   (uint32_t EPNum);
extern void  USB_DisableEP  (uint32_t EPNum);
extern void  USB_ResetEP    (uint32_t EPNum);
extern void  USB_SetStallEP (uint32_t EPNum);
extern void  USB_ClrStallEP (uint32_t EPNum);
extern void  USB_ClearEPBuf  (uint32_t  EPNum);
extern uint32_t USB_SetTestMode(uint8_t mode);
extern uint32_t USB_ReadEP     (uint32_t EPNum, uint8_t *pData);
extern uint32_t USB_ReadReqEP(uint32_t EPNum, uint8_t *pData, uint32_t len);
extern uint32_t USB_ReadSetupPkt(uint32_t, uint32_t *);
extern uint32_t USB_WriteEP    (uint32_t EPNum, uint8_t *pData, uint32_t cnt);
extern uint32_t USB_GetFrame   (void);
//extern void  USB_ISR(void) __irq;

#endif  /* __USBHW_H__ */
