/**********************************************************************
* $Id$		usbhw.c					2011-06-02
*//**
* @file		usbhw.c
* @brief	 USB Hardware Layer Module for NXP's lpc43xx MCU
* @version	1.0
* @date		02. June. 2011
* @author	NXP MCU SW Application Team
*
* Copyright(C) 2011, NXP Semiconductor
* All rights reserved.
*
***********************************************************************
* Software that is described herein is for illustrative purposes only
* which provides customers with programming information regarding the
* products. This software is supplied "AS IS" without any warranties.
* NXP Semiconductors assumes no responsibility or liability for the
* use of the software, conveys no license or title under any patent,
* copyright, or mask work right to the product. NXP Semiconductors
* reserves the right to make changes in the software without
* notification. NXP Semiconductors also make no representation or
* warranty that such application will be suitable for the specified
* use without further testing or modification.
**********************************************************************/
#include <string.h>
#include "lpc18xx.H"                        /* lpc43xx definitions */
#include "lpc_types.h"
#include "usb.h"
#include "usbhw.h"
#include "usbcfg.h"
#include "usbcore.h"
#include "lpc18xx_scu.h"
#include "lpc18xx_cgu.h"
#include "FreeRTOS.h"
#ifdef __CC_ARM
#pragma diag_suppress 1441
#endif

#ifdef __ICCARM__
#pragma data_alignment=2048
DQH_T ep_QH[EP_NUM_MAX];
#pragma data_alignment=32
DTD_T ep_TD[EP_NUM_MAX];
#pragma data_alignment=4
#elif defined   (  __GNUC__  )
#define __align(x) __attribute__((aligned(x)))
DQH_T ep_QH[EP_NUM_MAX] __attribute__((aligned(2048)));
DTD_T ep_TD[EP_NUM_MAX] __attribute__((aligned(32)));
#else
DQH_T __align(2048) ep_QH[EP_NUM_MAX];
DTD_T __align(32) ep_TD[EP_NUM_MAX];
#endif


static uint32_t ep_read_len[4];
volatile uint32_t DevStatusFS2HS = FALSE;
LPC_USBDRV_INIT_T g_drv;

/*
 *  Get Endpoint Physical Address
 *    Parameters:      EPNum: Endpoint Number
 *                       EPNum.0..3: Address
 *                       EPNum.7:    Dir
 *    Return Value:    Endpoint Physical Address
 */

uint32_t EPAdr (uint32_t EPNum) {
  uint32_t val;

  val = (EPNum & 0x0F) << 1;
  if (EPNum & 0x80) {
    val += 1;
  }
  return (val);
}

/*
 *  USB Initialize Function
 *   Called by the User to initialize USB
 *    Return Value:    None
 */

void USB_Init (LPC_USBDRV_INIT_T* cbs)
{
  memcpy(&g_drv, cbs, sizeof(LPC_USBDRV_INIT_T));
  /*maxp for EP0 should be atleast 8 */
  if( g_drv.ep0_maxp == 0)
    g_drv.ep0_maxp = 64;

#ifdef USE_USB0
	scu_pinmux(0x8,1,MD_PLN_FAST,FUNC1);    //  0: motocon pcap0_1          1: usb0 usb0_ind1           2:  nc                      3: gpio4 gpio4_1
	scu_pinmux(0x8,2,MD_PLN_FAST,FUNC1);    //  0: motocon pcap0_0          1: usb0 usb0_ind0           2:  nc                      3: gpio4 gpio4_2
#endif
#ifdef USE_USB0
	CGU_SetPLL0();
	CGU_EnableEntity(CGU_CLKSRC_PLL0, ENABLE);
	CGU_EntityConnect(CGU_CLKSRC_PLL0, CGU_BASE_USB0);
#else
	CGU_SetPLL1(5);
	CGU_EnableEntity(CGU_CLKSRC_PLL1, ENABLE);
	CGU_EntityConnect(CGU_CLKSRC_PLL1, CGU_BASE_USB1);
	/* enable USB phy */
    LPC_CREG->CREG0 &= ~(1 << 5);
    /* enable USB1_DP and USB1_DN on chip FS phy */
    LPC_SCU->SFSUSB = 0x12;
    /* enable USB1_VBUS */
    scu_pinmux(0x2, 5, MD_PLN | MD_EZI | MD_ZI, FUNC2);

#endif
	/* Turn on the phy */
#ifdef USE_USB0
	LPC_CREG->CREG0 &= ~(1<<5);
#endif
	/* reset the controller */
	LPC_USB->USBCMD_D = USBCMD_RST;
	/* wait for reset to complete */
	while (LPC_USB->USBCMD_D & USBCMD_RST);

	/* Program the controller to be the USB device controller */
	LPC_USB->USBMODE_D =   USBMODE_CM_DEV
	                  | USBMODE_SDIS
	                  | USBMODE_SLOM ;

	/* set OTG transcever in proper state, device is present
	on the port(CCS=1), port enable/disable status change(PES=1). */
#ifdef USE_USB0	
	LPC_USB->OTGSC = (1<<3) | (1<<0) /*| (1<<16)| (1<<24)| (1<<25)| (1<<26)| (1<<27)| (1<<28)| (1<<29)| (1<<30)*/;
#else
	/* force full speed */
	LPC_USB->PORTSC1_D |= (1<<24);
#endif

#ifdef USE_USB0
	NVIC_EnableIRQ(USB0_IRQn); //  enable USB0 interrrupts
	NVIC_SetPriority(USB0_IRQn, configMIN_LIBRARY_INTERRUPT_PRIORITY );
#else
  	NVIC_EnableIRQ(USB1_IRQn); //  enable USB1 interrrupts
  	NVIC_SetPriority(USB0_IRQn, configMIN_LIBRARY_INTERRUPT_PRIORITY );
#endif

	USB_Reset();
	USB_SetAddress(0);
	return;
}

/*
 *  USB Connect Function
 *   Called by the User to Connect/Disconnect USB
 *    Parameters:      con:   Connect/Disconnect
 *    Return Value:    None
 */
void USB_Connect (uint32_t con) {
  if (con)
    LPC_USB->USBCMD_D |= USBCMD_RS;
  else
    LPC_USB->USBCMD_D &= ~USBCMD_RS;
}


/*
 *  USB Reset Function
 *   Called automatically on USB Reset
 *    Return Value:    None
 */

void USB_Reset (void)
{
  uint32_t i;

  DevStatusFS2HS = FALSE;
  /* disable all EPs */
  LPC_USB->ENDPTCTRL0 &= ~(EPCTRL_RXE | EPCTRL_TXE);
  LPC_USB->ENDPTCTRL2 &= ~(EPCTRL_RXE | EPCTRL_TXE);
  LPC_USB->ENDPTCTRL3 &= ~(EPCTRL_RXE | EPCTRL_TXE);

  /* Clear all pending interrupts */
  LPC_USB->ENDPTNAK   = 0xFFFFFFFF;
  LPC_USB->ENDPTNAKEN = 0;
  LPC_USB->USBSTS_D     = 0xFFFFFFFF;
  LPC_USB->ENDPTSETUPSTAT = LPC_USB->ENDPTSETUPSTAT;
  LPC_USB->ENDPTCOMPLETE  = LPC_USB->ENDPTCOMPLETE;
  while (LPC_USB->ENDPTPRIME)                  /* Wait until all bits are 0 */
  {
  }
  LPC_USB->ENDPTFLUSH = 0xFFFFFFFF;
  while (LPC_USB->ENDPTFLUSH); /* Wait until all bits are 0 */


  /* Set the interrupt Threshold control interval to 0 */
  LPC_USB->USBCMD_D &= ~0x00FF0000;

  /* Zero out the Endpoint queue heads */
  memset((void*)ep_QH, 0, EP_NUM_MAX * sizeof(DQH_T));
  /* Zero out the device transfer descriptors */
  memset((void*)ep_TD, 0, EP_NUM_MAX * sizeof(DTD_T));
  memset((void*)ep_read_len, 0, sizeof(ep_read_len));
  /* Configure the Endpoint List Address */
  /* make sure it in on 64 byte boundary !!! */
  /* init list address */
  LPC_USB->ENDPOINTLISTADDR = (uint32_t)ep_QH;
  /* Initialize device queue heads for non ISO endpoint only */
  for (i = 0; i < EP_NUM_MAX; i++)
  {
    ep_QH[i].next_dTD = (uint32_t)&ep_TD[i];
  }
  /* Enable interrupts */
  LPC_USB->USBINTR_D =  USBSTS_UI
                     | USBSTS_UEI
                     | USBSTS_PCI
                     | USBSTS_URI
                     | USBSTS_SLI
                     | USBSTS_NAKI;
//  LPC_USB->usbintr |= (0x1<<7);		/* Test SOF */
  /* enable ep0 IN and ep0 OUT */
  ep_QH[0].cap  = QH_MAXP(g_drv.ep0_maxp)
                  | QH_IOS
                  | QH_ZLT;
  ep_QH[1].cap  = QH_MAXP(g_drv.ep0_maxp)
                  | QH_IOS
                  | QH_ZLT;
  /* enable EP0 */
  LPC_USB->ENDPTCTRL0 = EPCTRL_RXE | EPCTRL_RXR | EPCTRL_TXE | EPCTRL_TXR;
  return;

}


/*
 *  USB Suspend Function
 *   Called automatically on USB Suspend
 *    Return Value:    None
 */

void USB_Suspend (void) {
  /* Performed by Hardware */
}


/*
 *  USB Resume Function
 *   Called automatically on USB Resume
 *    Return Value:    None
 */

void USB_Resume (void) {
  /* Performed by Hardware */
}


/*
 *  USB Remote Wakeup Function
 *   Called automatically on USB Remote Wakeup
 *    Return Value:    None
 */

void USB_WakeUp (void) {

  //if (USB_DeviceStatus & USB_GETSTATUS_REMOTE_WAKEUP)
  {
    /* Set FPR bit in PORTSCX reg p63 */
    LPC_USB->PORTSC1_D |= USBPRTS_FPR ;
  }
}


/*
 *  USB Remote Wakeup Configuration Function
 *    Parameters:      cfg:   Enable/Disable
 *    Return Value:    None
 */

void USB_WakeUpCfg (uint32_t cfg) {
  ( void ) cfg;
  /* Not needed */
}


/*
 *  USB Set Address Function
 *    Parameters:      adr:   USB Address
 *    Return Value:    None
 */

void USB_SetAddress (uint32_t adr) {
  LPC_USB->DEVICEADDR = USBDEV_ADDR(adr);
  LPC_USB->DEVICEADDR |= USBDEV_ADDR_AD;
}

/*
*  USB set test mode Function
*    Parameters:      mode:   test mode
*    Return Value:    TRUE if supported else FALSE
*/

uint32_t USB_SetTestMode(uint8_t mode)
{
  uint32_t portsc;

  if ((mode > 0) && (mode < 8))
  {
    portsc = LPC_USB->PORTSC1_D & ~(0xF << 16);

    LPC_USB->PORTSC1_D = portsc | (mode << 16);
    return TRUE;
  }
  return (FALSE);
}

/*
 *  USB Configure Function
 *    Parameters:      cfg:   Configure/Deconfigure
 *    Return Value:    None
 */

void USB_Configure (uint32_t cfg) {
	( void ) cfg;
}


/*
 *  Configure USB Endpoint according to Descriptor
 *    Parameters:      pEPD:  Pointer to Endpoint Descriptor
 *    Return Value:    None
 */

void USB_ConfigEP (USB_ENDPOINT_DESCRIPTOR *pEPD) {
  uint32_t num, lep;
  uint32_t ep_cfg;
  uint8_t  bmAttributes;

  lep = pEPD->bEndpointAddress & 0x7F;
  num = EPAdr(pEPD->bEndpointAddress);

  ep_cfg = ((uint32_t*)&(LPC_USB->ENDPTCTRL0))[lep];
  /* mask the attributes we are not-intersetd in */
  bmAttributes = pEPD->bmAttributes & USB_ENDPOINT_TYPE_MASK;
  /* set EP type */
  if (bmAttributes != USB_ENDPOINT_TYPE_ISOCHRONOUS)
  {
    /* init EP capabilities */
    ep_QH[num].cap  = QH_MAXP(pEPD->wMaxPacketSize)
                      | QH_IOS | QH_ZLT ;
    /* The next DTD pointer is INVALID */
    ep_TD[num].next_dTD = 0x01 ;
  }
  else
  {
    /* init EP capabilities */
    ep_QH[num].cap  = QH_MAXP(0x400) | QH_ZLT;
  }
  /* setup EP control register */
  if (pEPD->bEndpointAddress & 0x80)
  {
    ep_cfg &= ~0xFFFF0000;
    ep_cfg |= EPCTRL_TX_TYPE(bmAttributes)
              | EPCTRL_TXR;
  }
  else
  {
    ep_cfg &= ~0xFFFF;
    ep_cfg |= EPCTRL_RX_TYPE(bmAttributes)
              | EPCTRL_RXR;
  }
  ((uint32_t*)&(LPC_USB->ENDPTCTRL0))[lep] = ep_cfg;
  return;
}

/*
 *  Set Direction for USB Control Endpoint
 *    Parameters:      dir:   Out (dir == 0), In (dir <> 0)
 *    Return Value:    None
 */

void USB_DirCtrlEP (uint32_t dir) {
  /* Not needed */
  ( void ) dir;
}


/*
 *  Enable USB Endpoint
 *    Parameters:      EPNum: Endpoint Number
 *                       EPNum.0..3: Address
 *                       EPNum.7:    Dir
 *    Return Value:    None
 */

void USB_EnableEP (uint32_t EPNum) {
  uint32_t lep, bitpos;

  lep = EPNum & 0x0F;

  if (EPNum & 0x80)
  {
    ((uint32_t*)&(LPC_USB->ENDPTCTRL0))[lep] |= EPCTRL_TXE;
  }
  else
  {
    ((uint32_t*)&(LPC_USB->ENDPTCTRL0))[lep] |= EPCTRL_RXE;
    /* enable NAK interrupt */
    bitpos = USB_EP_BITPOS(EPNum);
    LPC_USB->ENDPTNAKEN |= (1<<bitpos);
  }
}

/*
 *  Disable USB Endpoint
 *    Parameters:      EPNum: Endpoint Number
 *                       EPNum.0..3: Address
 *                       EPNum.7:    Dir
 *    Return Value:    None
 */

void USB_DisableEP (uint32_t EPNum) {
  uint32_t lep, bitpos;

  lep = EPNum & 0x0F;
  if (EPNum & 0x80)
  {
    ((uint32_t*)&(LPC_USB->ENDPTCTRL0))[lep] &= ~EPCTRL_TXE;
  }
  else
  {
    /* disable NAK interrupt */
    bitpos = USB_EP_BITPOS(EPNum);
    LPC_USB->ENDPTNAKEN &= ~(1<<bitpos);
    ((uint32_t*)&(LPC_USB->ENDPTCTRL0))[lep] &= ~EPCTRL_RXE;
  }
}

/*
 *  Reset USB Endpoint
 *    Parameters:      EPNum: Endpoint Number
 *                       EPNum.0..3: Address
 *                       EPNum.7:    Dir
 *    Return Value:    None
 */

void USB_ResetEP (uint32_t EPNum) {
  uint32_t bit_pos = USB_EP_BITPOS(EPNum);
  uint32_t lep = EPNum & 0x0F;

  /* flush EP buffers */
  LPC_USB->ENDPTFLUSH = (1<<bit_pos);
  while (LPC_USB->ENDPTFLUSH & (1<<bit_pos));
  /* reset data toggles */
  if (EPNum & 0x80)
  {
    ((uint32_t*)&(LPC_USB->ENDPTCTRL0))[lep] |= EPCTRL_TXR;
  }
  else
  {
    ((uint32_t*)&(LPC_USB->ENDPTCTRL0))[lep] |= EPCTRL_RXR;
  }
}

/*
 *  Set Stall for USB Endpoint
 *    Parameters:      EPNum: Endpoint Number
 *                       EPNum.0..3: Address
 *                       EPNum.7:    Dir
 *    Return Value:    None
 */

void USB_SetStallEP (uint32_t EPNum) {
  uint32_t lep;

  lep = EPNum & 0x0F;
  if (EPNum & 0x80)
  {
    ((uint32_t*)&(LPC_USB->ENDPTCTRL0))[lep] |= EPCTRL_TXS;
  }
  else
  {
    ((uint32_t*)&(LPC_USB->ENDPTCTRL0))[lep] |= EPCTRL_RXS;
  }
}

/*
 *  Clear Stall for USB Endpoint
 *    Parameters:      EPNum: Endpoint Number
 *                       EPNum.0..3: Address
 *                       EPNum.7:    Dir
 *    Return Value:    None
 */

void USB_ClrStallEP (uint32_t EPNum) {
  uint32_t lep;

  lep = EPNum & 0x0F;
  if (EPNum & 0x80)
  {
    ((uint32_t*)&(LPC_USB->ENDPTCTRL0))[lep] &= ~EPCTRL_TXS;
    /* reset data toggle */
    ((uint32_t*)&(LPC_USB->ENDPTCTRL0))[lep] |= EPCTRL_TXR;
  }
  else
  {
    ((uint32_t*)&(LPC_USB->ENDPTCTRL0))[lep] &= ~EPCTRL_RXS;
    /* reset data toggle */
    ((uint32_t*)&(LPC_USB->ENDPTCTRL0))[lep] |= EPCTRL_RXR;
  }
}

/*
 *  Process DTD
 *    Parameters:      EPNum: Endpoint Number
 *                       EPNum.0..3: Address
 *                       EPNum.7:    Dir
 *                     Buffer pointer
 *                     Transfer buffer size
 *    Return Value:    None
 */
void USB_ProgDTD(uint32_t Edpt, uint32_t ptrBuff, uint32_t TsfSize)
{
  DTD_T*  pDTD;

  pDTD = (DTD_T*)&ep_TD[ Edpt ];

  /* Zero out the device transfer descriptors */
  memset((void*)pDTD, 0, sizeof(DTD_T));
  /* The next DTD pointer is INVALID */
  pDTD->next_dTD = 0x01 ;

  /* Length */
  pDTD->total_bytes = ((TsfSize & 0x7fff) << 16);
  pDTD->total_bytes |= TD_IOC ;
  pDTD->total_bytes |= 0x80 ;

  pDTD->buffer0 = ptrBuff;
  pDTD->buffer1 = (ptrBuff + 0x1000) & 0xfffff000;
  pDTD->buffer2 = (ptrBuff + 0x2000) & 0xfffff000;
  pDTD->buffer3 = (ptrBuff + 0x3000) & 0xfffff000;
  pDTD->buffer4 = (ptrBuff + 0x4000) & 0xfffff000;

  ep_QH[Edpt].next_dTD = (uint32_t)(&ep_TD[ Edpt ]);
  ep_QH[Edpt].total_bytes &= (~0xC0) ;
}

/*
*  Read USB Endpoint Data
*    Parameters:      EPNum: Endpoint Number
*                       EPNum.0..3: Address
*                       EPNum.7:    Dir
*                     pData: Pointer to Data Buffer
*    Return Value:    Number of bytes read
*/
uint32_t USB_ReadSetupPkt(uint32_t EPNum, uint32_t *pData)
{
  uint32_t setup_int, cnt = 0;
  uint32_t num = EPAdr(EPNum);

  setup_int = LPC_USB->ENDPTSETUPSTAT ;
  /* Clear the setup interrupt */
  LPC_USB->ENDPTSETUPSTAT = setup_int;

  /* ********************************** */
  /*  Check if we have received a setup */
  /* ********************************** */
  if (setup_int & (1<<0))                    /* Check only for bit 0 */
    /* No setup are admitted on other endpoints than 0 */
  {
    do
    {
      /* Setup in a setup - must considere only the second setup */
      /*- Set the tripwire */
      LPC_USB->USBCMD_D |= USBCMD_SUTW ;

      /* Transfer Set-up data to the gtmudsCore_Request buffer */
      pData[0] = ep_QH[num].setup[0];
      pData[1] = ep_QH[num].setup[1];
      cnt = 8;

    }
    while (!(LPC_USB->USBCMD_D & USBCMD_SUTW)) ;

    /* setup in a setup - Clear the tripwire */
    LPC_USB->USBCMD_D &= (~USBCMD_SUTW);
  }
  while ((setup_int = LPC_USB->ENDPTSETUPSTAT) != 0)
  {
    /* Clear the setup interrupt */
    LPC_USB->ENDPTSETUPSTAT = setup_int;
  }
  return cnt;
}

/*
*  Enque read request
*    Parameters:      EPNum: Endpoint Number
*                       EPNum.0..3: Address
*                       EPNum.7:    Dir
*                     pData: Pointer to Data Buffer
*    Return Value:    Number of bytes read
*/

uint32_t USB_ReadReqEP(uint32_t EPNum, uint8_t *pData, uint32_t len)
{
  uint32_t num = EPAdr(EPNum);
  uint32_t n = USB_EP_BITPOS(EPNum);

  USB_ProgDTD(num, (uint32_t)pData, len);
  ep_read_len[EPNum & 0x0F] = len;
  /* prime the endpoint for read */
  LPC_USB->ENDPTPRIME |= (1<<n);
  return len;
}
/*
*  Read USB Endpoint Data
*    Parameters:      EPNum: Endpoint Number
*                       EPNum.0..3: Address
*                       EPNum.7:    Dir
*                     pData: Pointer to Data Buffer
*    Return Value:    Number of bytes read
*/

uint32_t USB_ReadEP(uint32_t EPNum, uint8_t *pData)
{
  uint32_t cnt, n;
  DTD_T*  pDTD ;

  ( void ) pData;

  n = EPAdr(EPNum);
  pDTD = (DTD_T*)&ep_TD[n];

  /* return the total bytes read */
  cnt  = (pDTD->total_bytes >> 16) & 0x7FFF;
  cnt = ep_read_len[EPNum & 0x0F] - cnt;
  return (cnt);
}

/*
*  Write USB Endpoint Data
*    Parameters:      EPNum: Endpoint Number
*                       EPNum.0..3: Address
*                       EPNum.7:    Dir
*                     pData: Pointer to Data Buffer
*                     cnt:   Number of bytes to write
*    Return Value:    Number of bytes written
*/
uint32_t USB_WriteEP(uint32_t EPNum, uint8_t *pData, uint32_t cnt)
{
  uint32_t x = 0, n = USB_EP_BITPOS(EPNum);

  USB_ProgDTD(EPAdr(EPNum), (uint32_t)pData, cnt);
  /* prime the endpoint for transmit */
  LPC_USB->ENDPTPRIME |= (1<<n);
   /* check if priming succeeded */
  while ((LPC_USB->ENDPTPRIME & (1<<n))&&(++x<0xffff));/*_RB_ Fix for hang here. */
  return (cnt);
}

/*
 *  USB Interrupt Service Routine
 */
#ifdef USE_USB0
void USB0_IRQHandler (void)
#else
void USB1_IRQHandler (void)
#endif
{
  uint32_t disr, val, n;

  disr = LPC_USB->USBSTS_D;                      /* Device Interrupt Status */
  LPC_USB->USBSTS_D = disr;

//  printf("USB interrupt: 0x%08x\n",disr);

//	LPC_UART1->THR = 'U';
//	LPC_UART1->THR = 'S';
//	LPC_UART1->THR = 'B';
//	LPC_UART1->THR = '\n';


  /* Device Status Interrupt (Reset, Connect change, Suspend/Resume) */
  if (disr & USBSTS_URI)                      /* Reset */
  {
//												  	LPC_UART1->THR = 'R';
//												  	LPC_UART1->THR = '\n';
    USB_Reset();
    if (g_drv.USB_Reset_Event)
      g_drv.USB_Reset_Event();
    return;
	//goto isr_end;
  }

  if (disr & USBSTS_SLI)                   /* Suspend */
  {
//												  LPC_UART1->THR = 'U';
//												  	LPC_UART1->THR = '\n';
    if (g_drv.USB_Suspend_Event)
      g_drv.USB_Suspend_Event();
  }

  if (disr & USBSTS_PCI)                  /* Resume */
  {
//												  	LPC_UART1->THR = 'P';
//												  	LPC_UART1->THR = '\n';
    /* check if device isoperating in HS mode or full speed */
    if (LPC_USB->PORTSC1_D & (1<<9))
      DevStatusFS2HS = TRUE;

    if (g_drv.USB_Resume_Event)
      g_drv.USB_Resume_Event();
  }

  /* handle setup status interrupts */
  val = LPC_USB->ENDPTSETUPSTAT;
  /* Only EP0 will have setup packets so call EP0 handler */
  if (val)
  {
//												    LPC_UART1->THR = 'S';
//												  	LPC_UART1->THR = '\n';
    /* Clear the endpoint complete CTRL OUT & IN when */
    /* a Setup is received */
    LPC_USB->ENDPTCOMPLETE = 0x00010001;
    /* enable NAK inetrrupts */
    LPC_USB->ENDPTNAKEN |= 0x00010001;
    if (g_drv.USB_P_EP[0]){
//														LPC_UART1->THR = 's';
//												  		LPC_UART1->THR = '\n';
        g_drv.USB_P_EP[0](USB_EVT_SETUP);
	}
  }

  /* handle completion interrupts */
  val = LPC_USB->ENDPTCOMPLETE;
  if (val)
  {
//														LPC_UART1->THR = 'C';
//													  	LPC_UART1->THR = '\n';

    LPC_USB->ENDPTNAK = val;
    for (n = 0; n < EP_NUM_MAX / 2; n++)
    {
      if (val & (1<<n))
      {
        if (g_drv.USB_P_EP[n])
          g_drv.USB_P_EP[n](USB_EVT_OUT);

        LPC_USB->ENDPTCOMPLETE = (1<<n);
      }
      if (val & (1<<(n + 16)))
      {
        ep_TD [(n << 1) + 1 ].total_bytes &= 0xC0;
        if (g_drv.USB_P_EP[n])
          g_drv.USB_P_EP[n](USB_EVT_IN);
        LPC_USB->ENDPTCOMPLETE = (1<<(n + 16));
      }
    }
  }

  if (disr & USBSTS_NAKI)
  {
//												  	LPC_UART1->THR = 'N';
//												  	LPC_UART1->THR = '\n';
    val = LPC_USB->ENDPTNAK;
    val &= LPC_USB->ENDPTNAKEN;
    /* handle NAK interrupts */
    if (val)
    {
      for (n = 0; n < EP_NUM_MAX / 2; n++)
      {
        if (val & (1<<n))
        {
          if (g_drv.USB_P_EP[n])
            g_drv.USB_P_EP[n](USB_EVT_OUT_NAK);
        }
        if (val & (1<<(n + 16)))
        {
          if (g_drv.USB_P_EP[n])
            g_drv.USB_P_EP[n](USB_EVT_IN_NAK);
        }
      }
      LPC_USB->ENDPTNAK = val;
    }
  }

  /* Start of Frame Interrupt */
  if (disr & USBSTS_SRI)
  {
//												  	LPC_UART1->THR = 'F';
//												  	LPC_UART1->THR = '\n';
    if (g_drv.USB_SOF_Event)
      g_drv.USB_SOF_Event();
  }

  /* Error Interrupt */
  if (disr & USBSTS_UEI)
  {
//													  LPC_UART1->THR = 'E';
//													  	LPC_UART1->THR = '\n';
    if (g_drv.USB_Error_Event)
      g_drv.USB_Error_Event(disr);
  }

//    LPC_UART1->THR = 'r';
//  	LPC_UART1->THR = '\n';
//isr_end:
//  LPC_VIC->VectAddr = 0;                   /* Acknowledge Interrupt */
  return;
}
