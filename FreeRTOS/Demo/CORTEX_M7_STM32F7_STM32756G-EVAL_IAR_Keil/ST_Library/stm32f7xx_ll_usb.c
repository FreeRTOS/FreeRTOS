/**
  ******************************************************************************
  * @file    stm32f7xx_ll_usb.c
  * @author  MCD Application Team
  * @version V1.0.0
  * @date    12-May-2015
  * @brief   USB Low Layer HAL module driver.
  *    
  *          This file provides firmware functions to manage the following 
  *          functionalities of the USB Peripheral Controller:
  *           + Initialization/de-initialization functions
  *           + I/O operation functions
  *           + Peripheral Control functions 
  *           + Peripheral State functions
  *         
  @verbatim
  ==============================================================================
                    ##### How to use this driver #####
  ==============================================================================
    [..]
      (#) Fill parameters of Init structure in USB_OTG_CfgTypeDef structure.
  
      (#) Call USB_CoreInit() API to initialize the USB Core peripheral.

      (#) The upper HAL HCD/PCD driver will call the right routines for its internal processes.

  @endverbatim
  ******************************************************************************
  * @attention
  *
  * <h2><center>&copy; COPYRIGHT(c) 2015 STMicroelectronics</center></h2>
  *
  * Redistribution and use in source and binary forms, with or without modification,
  * are permitted provided that the following conditions are met:
  *   1. Redistributions of source code must retain the above copyright notice,
  *      this list of conditions and the following disclaimer.
  *   2. Redistributions in binary form must reproduce the above copyright notice,
  *      this list of conditions and the following disclaimer in the documentation
  *      and/or other materials provided with the distribution.
  *   3. Neither the name of STMicroelectronics nor the names of its contributors
  *      may be used to endorse or promote products derived from this software
  *      without specific prior written permission.
  *
  * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
  * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
  * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
  * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
  * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
  * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
  * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
  * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
  * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
  * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
  *
  ******************************************************************************
  */ 

/* Includes ------------------------------------------------------------------*/
#include "stm32f7xx_hal.h"

/** @addtogroup STM32F7xx_LL_USB_DRIVER
  * @{
  */

#if defined (HAL_PCD_MODULE_ENABLED) || defined (HAL_HCD_MODULE_ENABLED)

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
/* Private functions ---------------------------------------------------------*/
static HAL_StatusTypeDef USB_CoreReset(USB_OTG_GlobalTypeDef *USBx);

/** @defgroup PCD_Private_Functions
  * @{
  */

/** @defgroup LL_USB_Group1 Initialization/de-initialization functions 
 *  @brief    Initialization and Configuration functions 
 *
@verbatim    
 ===============================================================================
              ##### Initialization/de-initialization functions #####
 ===============================================================================
    [..]  This section provides functions allowing to:
 
@endverbatim
  * @{
  */

/**
  * @brief  Initializes the USB Core
  * @param  USBx: USB Instance
  * @param  cfg : pointer to a USB_OTG_CfgTypeDef structure that contains
  *         the configuration information for the specified USBx peripheral.
  * @retval HAL status
  */
HAL_StatusTypeDef USB_CoreInit(USB_OTG_GlobalTypeDef *USBx, USB_OTG_CfgTypeDef cfg)
{
  if (cfg.phy_itface == USB_OTG_ULPI_PHY)
  {
    
    USBx->GCCFG &= ~(USB_OTG_GCCFG_PWRDWN);

    /* Init The ULPI Interface */
    USBx->GUSBCFG &= ~(USB_OTG_GUSBCFG_TSDPS | USB_OTG_GUSBCFG_ULPIFSLS | USB_OTG_GUSBCFG_PHYSEL);
   
    /* Select vbus source */
    USBx->GUSBCFG &= ~(USB_OTG_GUSBCFG_ULPIEVBUSD | USB_OTG_GUSBCFG_ULPIEVBUSI);
    if(cfg.use_external_vbus == 1)
    {
      USBx->GUSBCFG |= USB_OTG_GUSBCFG_ULPIEVBUSD;
    }
    /* Reset after a PHY select  */
    USB_CoreReset(USBx); 
  }
  else /* FS interface (embedded Phy) */
  {
    
    /* Select FS Embedded PHY */
    USBx->GUSBCFG |= USB_OTG_GUSBCFG_PHYSEL;
    
    /* Reset after a PHY select and set Host mode */
    USB_CoreReset(USBx);
    
    /* Deactivate the power down*/
    USBx->GCCFG = USB_OTG_GCCFG_PWRDWN;
  }
 
  if(cfg.dma_enable == ENABLE)
  {
    USBx->GAHBCFG |= (USB_OTG_GAHBCFG_HBSTLEN_1 | USB_OTG_GAHBCFG_HBSTLEN_2);
    USBx->GAHBCFG |= USB_OTG_GAHBCFG_DMAEN;
  }  

  return HAL_OK;
}

/**
  * @brief  USB_EnableGlobalInt
  *         Enables the controller's Global Int in the AHB Config reg
  * @param  USBx : Selected device
  * @retval HAL status
  */
HAL_StatusTypeDef USB_EnableGlobalInt(USB_OTG_GlobalTypeDef *USBx)
{
  USBx->GAHBCFG |= USB_OTG_GAHBCFG_GINT;
  return HAL_OK;
}


/**
  * @brief  USB_DisableGlobalInt
  *         Disable the controller's Global Int in the AHB Config reg
  * @param  USBx : Selected device
  * @retval HAL status
*/
HAL_StatusTypeDef USB_DisableGlobalInt(USB_OTG_GlobalTypeDef *USBx)
{
  USBx->GAHBCFG &= ~USB_OTG_GAHBCFG_GINT;
  return HAL_OK;
}
   
/**
  * @brief  USB_SetCurrentMode : Set functional mode
  * @param  USBx : Selected device
  * @param  mode :  current core mode
  *          This parameter can be one of the these values:
  *            @arg USB_OTG_DEVICE_MODE: Peripheral mode
  *            @arg USB_OTG_HOST_MODE: Host mode
  *            @arg USB_OTG_DRD_MODE: Dual Role Device mode  
  * @retval HAL status
  */
HAL_StatusTypeDef USB_SetCurrentMode(USB_OTG_GlobalTypeDef *USBx , USB_OTG_ModeTypeDef mode)
{
  USBx->GUSBCFG &= ~(USB_OTG_GUSBCFG_FHMOD | USB_OTG_GUSBCFG_FDMOD); 
  
  if ( mode == USB_OTG_HOST_MODE)
  {
    USBx->GUSBCFG |= USB_OTG_GUSBCFG_FHMOD; 
  }
  else if ( mode == USB_OTG_DEVICE_MODE)
  {
    USBx->GUSBCFG |= USB_OTG_GUSBCFG_FDMOD; 
  }
  HAL_Delay(50);
  
  return HAL_OK;
}

/**
  * @brief  USB_DevInit : Initializes the USB_OTG controller registers 
  *         for device mode
  * @param  USBx : Selected device
  * @param  cfg  : pointer to a USB_OTG_CfgTypeDef structure that contains
  *         the configuration information for the specified USBx peripheral.
  * @retval HAL status
  */
HAL_StatusTypeDef USB_DevInit (USB_OTG_GlobalTypeDef *USBx, USB_OTG_CfgTypeDef cfg)
{
  uint32_t i = 0;

  /*Activate VBUS Sensing B */
  USBx->GCCFG |= USB_OTG_GCCFG_VBDEN;
  
  if (cfg.vbus_sensing_enable == 0)
  {
    /*Desactivate VBUS Sensing B */
    USBx->GCCFG &= ~ USB_OTG_GCCFG_VBDEN;
    
    /* B-peripheral session valid override enable*/ 
    USBx->GOTGCTL |= USB_OTG_GOTGCTL_BVALOEN;
    USBx->GOTGCTL |= USB_OTG_GOTGCTL_BVALOVAL;
  }
   
  /* Restart the Phy Clock */
  USBx_PCGCCTL = 0;

  /* Device mode configuration */
  USBx_DEVICE->DCFG |= DCFG_FRAME_INTERVAL_80;
  
  if(cfg.phy_itface  == USB_OTG_ULPI_PHY)
  {
    if(cfg.speed == USB_OTG_SPEED_HIGH)
    {      
      /* Set High speed phy */
      USB_SetDevSpeed (USBx , USB_OTG_SPEED_HIGH);
    }
    else 
    {
      /* set High speed phy in Full speed mode */
      USB_SetDevSpeed (USBx , USB_OTG_SPEED_HIGH_IN_FULL);
    }
  }
  else
  {
    /* Set Full speed phy */
    USB_SetDevSpeed (USBx , USB_OTG_SPEED_FULL);
  }

  /* Flush the FIFOs */
  USB_FlushTxFifo(USBx , 0x10); /* all Tx FIFOs */
  USB_FlushRxFifo(USBx);

  
  /* Clear all pending Device Interrupts */
  USBx_DEVICE->DIEPMSK = 0;
  USBx_DEVICE->DOEPMSK = 0;
  USBx_DEVICE->DAINT = 0xFFFFFFFF;
  USBx_DEVICE->DAINTMSK = 0;
  
  for (i = 0; i < cfg.dev_endpoints; i++)
  {
    if ((USBx_INEP(i)->DIEPCTL & USB_OTG_DIEPCTL_EPENA) == USB_OTG_DIEPCTL_EPENA)
    {
      USBx_INEP(i)->DIEPCTL = (USB_OTG_DIEPCTL_EPDIS | USB_OTG_DIEPCTL_SNAK);
    }
    else
    {
      USBx_INEP(i)->DIEPCTL = 0;
    }
    
    USBx_INEP(i)->DIEPTSIZ = 0;
    USBx_INEP(i)->DIEPINT  = 0xFF;
  }
  
  for (i = 0; i < cfg.dev_endpoints; i++)
  {
    if ((USBx_OUTEP(i)->DOEPCTL & USB_OTG_DOEPCTL_EPENA) == USB_OTG_DOEPCTL_EPENA)
    {
      USBx_OUTEP(i)->DOEPCTL = (USB_OTG_DOEPCTL_EPDIS | USB_OTG_DOEPCTL_SNAK);
    }
    else
    {
      USBx_OUTEP(i)->DOEPCTL = 0;
    }
    
    USBx_OUTEP(i)->DOEPTSIZ = 0;
    USBx_OUTEP(i)->DOEPINT  = 0xFF;
  }
  
  USBx_DEVICE->DIEPMSK &= ~(USB_OTG_DIEPMSK_TXFURM);
  
  if (cfg.dma_enable == 1)
  {
    /*Set threshold parameters */
    USBx_DEVICE->DTHRCTL = (USB_OTG_DTHRCTL_TXTHRLEN_6 | USB_OTG_DTHRCTL_RXTHRLEN_6);
    USBx_DEVICE->DTHRCTL |= (USB_OTG_DTHRCTL_RXTHREN | USB_OTG_DTHRCTL_ISOTHREN | USB_OTG_DTHRCTL_NONISOTHREN);
    
    i= USBx_DEVICE->DTHRCTL;
  }
  
  /* Disable all interrupts. */
  USBx->GINTMSK = 0;
  
  /* Clear any pending interrupts */
  USBx->GINTSTS = 0xBFFFFFFF;

  /* Enable the common interrupts */
  if (cfg.dma_enable == DISABLE)
  {
    USBx->GINTMSK |= USB_OTG_GINTMSK_RXFLVLM; 
  }
  
  /* Enable interrupts matching to the Device mode ONLY */
  USBx->GINTMSK |= (USB_OTG_GINTMSK_USBSUSPM | USB_OTG_GINTMSK_USBRST |\
                    USB_OTG_GINTMSK_ENUMDNEM | USB_OTG_GINTMSK_IEPINT |\
                    USB_OTG_GINTMSK_OEPINT   | USB_OTG_GINTMSK_IISOIXFRM|\
                    USB_OTG_GINTMSK_PXFRM_IISOOXFRM | USB_OTG_GINTMSK_WUIM);
  
  if(cfg.Sof_enable)
  {
    USBx->GINTMSK |= USB_OTG_GINTMSK_SOFM;
  }

  if (cfg.vbus_sensing_enable == ENABLE)
  {
    USBx->GINTMSK |= (USB_OTG_GINTMSK_SRQIM | USB_OTG_GINTMSK_OTGINT); 
  }
  
  return HAL_OK;
}


/**
  * @brief  USB_OTG_FlushTxFifo : Flush a Tx FIFO
  * @param  USBx : Selected device
  * @param  num : FIFO number
  *         This parameter can be a value from 1 to 15
            15 means Flush all Tx FIFOs
  * @retval HAL status
  */
HAL_StatusTypeDef USB_FlushTxFifo (USB_OTG_GlobalTypeDef *USBx, uint32_t num )
{
  uint32_t count = 0;
 
  USBx->GRSTCTL = ( USB_OTG_GRSTCTL_TXFFLSH |(uint32_t)( num << 5 )); 
 
  do
  {
    if (++count > 200000)
    {
      return HAL_TIMEOUT;
    }
  }
  while ((USBx->GRSTCTL & USB_OTG_GRSTCTL_TXFFLSH) == USB_OTG_GRSTCTL_TXFFLSH);
  
  return HAL_OK;
}


/**
  * @brief  USB_FlushRxFifo : Flush Rx FIFO
  * @param  USBx : Selected device
  * @retval HAL status
  */
HAL_StatusTypeDef USB_FlushRxFifo(USB_OTG_GlobalTypeDef *USBx)
{
  uint32_t count = 0;
  
  USBx->GRSTCTL = USB_OTG_GRSTCTL_RXFFLSH;
  
  do
  {
    if (++count > 200000)
    {
      return HAL_TIMEOUT;
    }
  }
  while ((USBx->GRSTCTL & USB_OTG_GRSTCTL_RXFFLSH) == USB_OTG_GRSTCTL_RXFFLSH);
  
  return HAL_OK;
}

/**
  * @brief  USB_SetDevSpeed :Initializes the DevSpd field of DCFG register 
  *         depending the PHY type and the enumeration speed of the device.
  * @param  USBx : Selected device
  * @param  speed : device speed
  *          This parameter can be one of the these values:
  *            @arg USB_OTG_SPEED_HIGH: High speed mode
  *            @arg USB_OTG_SPEED_HIGH_IN_FULL: High speed core in Full Speed mode
  *            @arg USB_OTG_SPEED_FULL: Full speed mode
  *            @arg USB_OTG_SPEED_LOW: Low speed mode
  * @retval  Hal status
  */
HAL_StatusTypeDef USB_SetDevSpeed(USB_OTG_GlobalTypeDef *USBx , uint8_t speed)
{
  USBx_DEVICE->DCFG |= speed;
  return HAL_OK;
}

/**
  * @brief  USB_GetDevSpeed :Return the  Dev Speed 
  * @param  USBx : Selected device
  * @retval speed : device speed
  *          This parameter can be one of the these values:
  *            @arg USB_OTG_SPEED_HIGH: High speed mode
  *            @arg USB_OTG_SPEED_FULL: Full speed mode
  *            @arg USB_OTG_SPEED_LOW: Low speed mode
  */
uint8_t USB_GetDevSpeed(USB_OTG_GlobalTypeDef *USBx)
{
  uint8_t speed = 0;
  
  if((USBx_DEVICE->DSTS & USB_OTG_DSTS_ENUMSPD) == DSTS_ENUMSPD_HS_PHY_30MHZ_OR_60MHZ)
  {
    speed = USB_OTG_SPEED_HIGH;
  }
  else if (((USBx_DEVICE->DSTS & USB_OTG_DSTS_ENUMSPD) == DSTS_ENUMSPD_FS_PHY_30MHZ_OR_60MHZ)||
           ((USBx_DEVICE->DSTS & USB_OTG_DSTS_ENUMSPD) == DSTS_ENUMSPD_FS_PHY_48MHZ))
  {
    speed = USB_OTG_SPEED_FULL;
  }
  else if((USBx_DEVICE->DSTS & USB_OTG_DSTS_ENUMSPD) == DSTS_ENUMSPD_LS_PHY_6MHZ)
  {
    speed = USB_OTG_SPEED_LOW;
  }
  
  return speed;
}

/**
  * @brief  Activate and configure an endpoint
  * @param  USBx : Selected device
  * @param  ep: pointer to endpoint structure
  * @retval HAL status
  */
HAL_StatusTypeDef USB_ActivateEndpoint(USB_OTG_GlobalTypeDef *USBx, USB_OTG_EPTypeDef *ep)
{
  if (ep->is_in == 1)
  {
   USBx_DEVICE->DAINTMSK |= USB_OTG_DAINTMSK_IEPM & ((1 << (ep->num)));
   
    if (((USBx_INEP(ep->num)->DIEPCTL) & USB_OTG_DIEPCTL_USBAEP) == 0)
    {
      USBx_INEP(ep->num)->DIEPCTL |= ((ep->maxpacket & USB_OTG_DIEPCTL_MPSIZ ) | (ep->type << 18 ) |\
        ((ep->num) << 22 ) | (USB_OTG_DIEPCTL_SD0PID_SEVNFRM) | (USB_OTG_DIEPCTL_USBAEP)); 
    } 

  }
  else
  {
     USBx_DEVICE->DAINTMSK |= USB_OTG_DAINTMSK_OEPM & ((1 << (ep->num)) << 16);
     
    if (((USBx_OUTEP(ep->num)->DOEPCTL) & USB_OTG_DOEPCTL_USBAEP) == 0)
    {
      USBx_OUTEP(ep->num)->DOEPCTL |= ((ep->maxpacket & USB_OTG_DOEPCTL_MPSIZ ) | (ep->type << 18 ) |\
       (USB_OTG_DIEPCTL_SD0PID_SEVNFRM)| (USB_OTG_DOEPCTL_USBAEP));
    } 
  }
  return HAL_OK;
}
/**
  * @brief  Activate and configure a dedicated endpoint
  * @param  USBx : Selected device
  * @param  ep: pointer to endpoint structure
  * @retval HAL status
  */
HAL_StatusTypeDef USB_ActivateDedicatedEndpoint(USB_OTG_GlobalTypeDef *USBx, USB_OTG_EPTypeDef *ep)
{
  static __IO uint32_t debug = 0;
  
  /* Read DEPCTLn register */
  if (ep->is_in == 1)
  {
    if (((USBx_INEP(ep->num)->DIEPCTL) & USB_OTG_DIEPCTL_USBAEP) == 0)
    {
      USBx_INEP(ep->num)->DIEPCTL |= ((ep->maxpacket & USB_OTG_DIEPCTL_MPSIZ ) | (ep->type << 18 ) |\
        ((ep->num) << 22 ) | (USB_OTG_DIEPCTL_SD0PID_SEVNFRM) | (USB_OTG_DIEPCTL_USBAEP)); 
    } 
    
    
    debug  |= ((ep->maxpacket & USB_OTG_DIEPCTL_MPSIZ ) | (ep->type << 18 ) |\
        ((ep->num) << 22 ) | (USB_OTG_DIEPCTL_SD0PID_SEVNFRM) | (USB_OTG_DIEPCTL_USBAEP)); 
    
   USBx_DEVICE->DEACHMSK |= USB_OTG_DAINTMSK_IEPM & ((1 << (ep->num)));
  }
  else
  {
    if (((USBx_OUTEP(ep->num)->DOEPCTL) & USB_OTG_DOEPCTL_USBAEP) == 0)
    {
      USBx_OUTEP(ep->num)->DOEPCTL |= ((ep->maxpacket & USB_OTG_DOEPCTL_MPSIZ ) | (ep->type << 18 ) |\
        ((ep->num) << 22 ) | (USB_OTG_DOEPCTL_USBAEP));
      
      debug = (uint32_t)(((uint32_t )USBx) + USB_OTG_OUT_ENDPOINT_BASE + (0)*USB_OTG_EP_REG_SIZE);
      debug = (uint32_t )&USBx_OUTEP(ep->num)->DOEPCTL;
      debug |= ((ep->maxpacket & USB_OTG_DOEPCTL_MPSIZ ) | (ep->type << 18 ) |\
        ((ep->num) << 22 ) | (USB_OTG_DOEPCTL_USBAEP)); 
    } 
    
     USBx_DEVICE->DEACHMSK |= USB_OTG_DAINTMSK_OEPM & ((1 << (ep->num)) << 16);
  }

  return HAL_OK;
}
/**
  * @brief  De-activate and de-initialize an endpoint
  * @param  USBx : Selected device
  * @param  ep: pointer to endpoint structure
  * @retval HAL status
  */
HAL_StatusTypeDef USB_DeactivateEndpoint(USB_OTG_GlobalTypeDef *USBx, USB_OTG_EPTypeDef *ep)
{
  /* Read DEPCTLn register */
  if (ep->is_in == 1)
  {
   USBx_DEVICE->DEACHMSK &= ~(USB_OTG_DAINTMSK_IEPM & ((1 << (ep->num))));
   USBx_DEVICE->DAINTMSK &= ~(USB_OTG_DAINTMSK_IEPM & ((1 << (ep->num))));   
   USBx_INEP(ep->num)->DIEPCTL &= ~ USB_OTG_DIEPCTL_USBAEP;   
  }
  else
  {

     USBx_DEVICE->DEACHMSK &= ~(USB_OTG_DAINTMSK_OEPM & ((1 << (ep->num)) << 16));
     USBx_DEVICE->DAINTMSK &= ~(USB_OTG_DAINTMSK_OEPM & ((1 << (ep->num)) << 16));     
     USBx_OUTEP(ep->num)->DOEPCTL &= ~USB_OTG_DOEPCTL_USBAEP;      
  }
  return HAL_OK;
}

/**
  * @brief  De-activate and de-initialize a dedicated endpoint
  * @param  USBx : Selected device
  * @param  ep: pointer to endpoint structure
  * @retval HAL status
  */
HAL_StatusTypeDef USB_DeactivateDedicatedEndpoint(USB_OTG_GlobalTypeDef *USBx, USB_OTG_EPTypeDef *ep)
{
  /* Read DEPCTLn register */
  if (ep->is_in == 1)
  {
   USBx_INEP(ep->num)->DIEPCTL &= ~ USB_OTG_DIEPCTL_USBAEP;
   USBx_DEVICE->DAINTMSK &= ~(USB_OTG_DAINTMSK_IEPM & ((1 << (ep->num))));
  }
  else
  {
     USBx_OUTEP(ep->num)->DOEPCTL &= ~USB_OTG_DOEPCTL_USBAEP; 
     USBx_DEVICE->DAINTMSK &= ~(USB_OTG_DAINTMSK_OEPM & ((1 << (ep->num)) << 16));
  }
  return HAL_OK;
}

/**
  * @brief  USB_EPStartXfer : setup and starts a transfer over an EP
  * @param  USBx : Selected device
  * @param  ep: pointer to endpoint structure
  * @param  dma: USB dma enabled or disabled 
  *          This parameter can be one of the these values:
  *           0 : DMA feature not used 
  *           1 : DMA feature used  
  * @retval HAL status
  */
HAL_StatusTypeDef USB_EPStartXfer(USB_OTG_GlobalTypeDef *USBx , USB_OTG_EPTypeDef *ep, uint8_t dma)
{
  uint16_t pktcnt = 0;
  
  /* IN endpoint */
  if (ep->is_in == 1)
  {
    /* Zero Length Packet? */
    if (ep->xfer_len == 0)
    {
      USBx_INEP(ep->num)->DIEPTSIZ &= ~(USB_OTG_DIEPTSIZ_PKTCNT); 
      USBx_INEP(ep->num)->DIEPTSIZ |= (USB_OTG_DIEPTSIZ_PKTCNT & (1 << 19)) ;
      USBx_INEP(ep->num)->DIEPTSIZ &= ~(USB_OTG_DIEPTSIZ_XFRSIZ); 
    }
    else
    {
      /* Program the transfer size and packet count
      * as follows: xfersize = N * maxpacket +
      * short_packet pktcnt = N + (short_packet
      * exist ? 1 : 0)
      */
      USBx_INEP(ep->num)->DIEPTSIZ &= ~(USB_OTG_DIEPTSIZ_XFRSIZ);
      USBx_INEP(ep->num)->DIEPTSIZ &= ~(USB_OTG_DIEPTSIZ_PKTCNT); 
      USBx_INEP(ep->num)->DIEPTSIZ |= (USB_OTG_DIEPTSIZ_PKTCNT & (((ep->xfer_len + ep->maxpacket -1)/ ep->maxpacket) << 19)) ;
      USBx_INEP(ep->num)->DIEPTSIZ |= (USB_OTG_DIEPTSIZ_XFRSIZ & ep->xfer_len); 
      
      if (ep->type == EP_TYPE_ISOC)
      {
        USBx_INEP(ep->num)->DIEPTSIZ &= ~(USB_OTG_DIEPTSIZ_MULCNT); 
        USBx_INEP(ep->num)->DIEPTSIZ |= (USB_OTG_DIEPTSIZ_MULCNT & (1 << 29)); 
      }       
    }

    if (dma == 1)
    {
      USBx_INEP(ep->num)->DIEPDMA = (uint32_t)(ep->dma_addr);
    }
    else
    {
      if (ep->type != EP_TYPE_ISOC)
      {
        /* Enable the Tx FIFO Empty Interrupt for this EP */
        if (ep->xfer_len > 0)
        {
          USBx_DEVICE->DIEPEMPMSK |= 1 << ep->num;
        }
      }
    }

    if (ep->type == EP_TYPE_ISOC)
    {
      if ((USBx_DEVICE->DSTS & ( 1 << 8 )) == 0)
      {
        USBx_INEP(ep->num)->DIEPCTL |= USB_OTG_DIEPCTL_SODDFRM;
      }
      else
      {
        USBx_INEP(ep->num)->DIEPCTL |= USB_OTG_DIEPCTL_SD0PID_SEVNFRM;
      }
    } 
    
    /* EP enable, IN data in FIFO */
    USBx_INEP(ep->num)->DIEPCTL |= (USB_OTG_DIEPCTL_CNAK | USB_OTG_DIEPCTL_EPENA);
    
    if (ep->type == EP_TYPE_ISOC)
    {
      USB_WritePacket(USBx, ep->xfer_buff, ep->num, ep->xfer_len, dma);   
    }    
  }
  else /* OUT endpoint */
  {
    /* Program the transfer size and packet count as follows:
    * pktcnt = N
    * xfersize = N * maxpacket
    */  
    USBx_OUTEP(ep->num)->DOEPTSIZ &= ~(USB_OTG_DOEPTSIZ_XFRSIZ); 
    USBx_OUTEP(ep->num)->DOEPTSIZ &= ~(USB_OTG_DOEPTSIZ_PKTCNT); 
      
    if (ep->xfer_len == 0)
    {
      USBx_OUTEP(ep->num)->DOEPTSIZ |= (USB_OTG_DOEPTSIZ_XFRSIZ & ep->maxpacket);
      USBx_OUTEP(ep->num)->DOEPTSIZ |= (USB_OTG_DOEPTSIZ_PKTCNT & (1 << 19)) ;      
    }
    else
    {
      pktcnt = (ep->xfer_len + ep->maxpacket -1)/ ep->maxpacket; 
      USBx_OUTEP(ep->num)->DOEPTSIZ |= (USB_OTG_DOEPTSIZ_PKTCNT & (pktcnt << 19));
      USBx_OUTEP(ep->num)->DOEPTSIZ |= (USB_OTG_DOEPTSIZ_XFRSIZ & (ep->maxpacket * pktcnt)); 
    }

    if (dma == 1)
    {
      USBx_OUTEP(ep->num)->DOEPDMA = (uint32_t)ep->xfer_buff;
    }
    
    if (ep->type == EP_TYPE_ISOC)
    {
      if ((USBx_DEVICE->DSTS & ( 1 << 8 )) == 0)
      {
        USBx_OUTEP(ep->num)->DOEPCTL |= USB_OTG_DOEPCTL_SODDFRM;
      }
      else
      {
        USBx_OUTEP(ep->num)->DOEPCTL |= USB_OTG_DOEPCTL_SD0PID_SEVNFRM;
      }
    }
    /* EP enable */
    USBx_OUTEP(ep->num)->DOEPCTL |= (USB_OTG_DOEPCTL_CNAK | USB_OTG_DOEPCTL_EPENA);
  }
  return HAL_OK;
}

/**
  * @brief  USB_EP0StartXfer : setup and starts a transfer over the EP  0
  * @param  USBx : Selected device
  * @param  ep: pointer to endpoint structure
  * @param  dma: USB dma enabled or disabled 
  *          This parameter can be one of the these values:
  *           0 : DMA feature not used 
  *           1 : DMA feature used  
  * @retval HAL status
  */
HAL_StatusTypeDef USB_EP0StartXfer(USB_OTG_GlobalTypeDef *USBx , USB_OTG_EPTypeDef *ep, uint8_t dma)
{
  /* IN endpoint */
  if (ep->is_in == 1)
  {
    /* Zero Length Packet? */
    if (ep->xfer_len == 0)
    {
      USBx_INEP(ep->num)->DIEPTSIZ &= ~(USB_OTG_DIEPTSIZ_PKTCNT); 
      USBx_INEP(ep->num)->DIEPTSIZ |= (USB_OTG_DIEPTSIZ_PKTCNT & (1 << 19)) ;
      USBx_INEP(ep->num)->DIEPTSIZ &= ~(USB_OTG_DIEPTSIZ_XFRSIZ); 
    }
    else
    {
      /* Program the transfer size and packet count
      * as follows: xfersize = N * maxpacket +
      * short_packet pktcnt = N + (short_packet
      * exist ? 1 : 0)
      */
      USBx_INEP(ep->num)->DIEPTSIZ &= ~(USB_OTG_DIEPTSIZ_XFRSIZ);
      USBx_INEP(ep->num)->DIEPTSIZ &= ~(USB_OTG_DIEPTSIZ_PKTCNT); 
      
      if(ep->xfer_len > ep->maxpacket)
      {
        ep->xfer_len = ep->maxpacket;
      }
      USBx_INEP(ep->num)->DIEPTSIZ |= (USB_OTG_DIEPTSIZ_PKTCNT & (1 << 19)) ;
      USBx_INEP(ep->num)->DIEPTSIZ |= (USB_OTG_DIEPTSIZ_XFRSIZ & ep->xfer_len); 
    
    }
    
    if (dma == 1)
    {
      USBx_INEP(ep->num)->DIEPDMA = (uint32_t)(ep->dma_addr);
    }
    else
    {
      /* Enable the Tx FIFO Empty Interrupt for this EP */
      if (ep->xfer_len > 0)
      {
        USBx_DEVICE->DIEPEMPMSK |= 1 << (ep->num);
      }
    }
    
    /* EP enable, IN data in FIFO */
    USBx_INEP(ep->num)->DIEPCTL |= (USB_OTG_DIEPCTL_CNAK | USB_OTG_DIEPCTL_EPENA);   
  }
  else /* OUT endpoint */
  {
    /* Program the transfer size and packet count as follows:
    * pktcnt = N
    * xfersize = N * maxpacket
    */
    USBx_OUTEP(ep->num)->DOEPTSIZ &= ~(USB_OTG_DOEPTSIZ_XFRSIZ); 
    USBx_OUTEP(ep->num)->DOEPTSIZ &= ~(USB_OTG_DOEPTSIZ_PKTCNT); 
      
    if (ep->xfer_len > 0)
    {
      ep->xfer_len = ep->maxpacket;
    }
    
    USBx_OUTEP(ep->num)->DOEPTSIZ |= (USB_OTG_DOEPTSIZ_PKTCNT & (1 << 19));
    USBx_OUTEP(ep->num)->DOEPTSIZ |= (USB_OTG_DOEPTSIZ_XFRSIZ & (ep->maxpacket)); 
    

    if (dma == 1)
    {
      USBx_OUTEP(ep->num)->DOEPDMA = (uint32_t)(ep->xfer_buff);
    }
    
    /* EP enable */
    USBx_OUTEP(ep->num)->DOEPCTL |= (USB_OTG_DOEPCTL_CNAK | USB_OTG_DOEPCTL_EPENA);    
  }
  return HAL_OK;
}

/**
  * @brief  USB_WritePacket : Writes a packet into the Tx FIFO associated 
  *         with the EP/channel
  * @param  USBx : Selected device           
  * @param  src :  pointer to source buffer
  * @param  ch_ep_num : endpoint or host channel number
  * @param  len : Number of bytes to write
  * @param  dma: USB dma enabled or disabled 
  *          This parameter can be one of the these values:
  *           0 : DMA feature not used 
  *           1 : DMA feature used  
  * @retval HAL status
  */
HAL_StatusTypeDef USB_WritePacket(USB_OTG_GlobalTypeDef *USBx, uint8_t *src, uint8_t ch_ep_num, uint16_t len, uint8_t dma)
{
  uint32_t count32b= 0 , i= 0;
  
  if (dma == 0)
  {
    count32b =  (len + 3) / 4;
    for (i = 0; i < count32b; i++, src += 4)
    {
      USBx_DFIFO(ch_ep_num) = *((__packed uint32_t *)src);
    }
  }
  return HAL_OK;
}

/**
  * @brief  USB_ReadPacket : read a packet from the Tx FIFO associated 
  *         with the EP/channel
  * @param  USBx : Selected device  
  * @param  src : source pointer
  * @param  ch_ep_num : endpoint or host channel number
  * @param  len : Number of bytes to read
  * @param  dma: USB dma enabled or disabled 
  *          This parameter can be one of the these values:
  *           0 : DMA feature not used 
  *           1 : DMA feature used  
  * @retval pointer to destination buffer
  */
void *USB_ReadPacket(USB_OTG_GlobalTypeDef *USBx, uint8_t *dest, uint16_t len)
{
  uint32_t i=0;
  uint32_t count32b = (len + 3) / 4;
  
  for ( i = 0; i < count32b; i++, dest += 4 )
  {
    *(__packed uint32_t *)dest = USBx_DFIFO(0);
    
  }
  return ((void *)dest);
}

/**
  * @brief  USB_EPSetStall : set a stall condition over an EP
  * @param  USBx : Selected device
  * @param  ep: pointer to endpoint structure   
  * @retval HAL status
  */
HAL_StatusTypeDef USB_EPSetStall(USB_OTG_GlobalTypeDef *USBx , USB_OTG_EPTypeDef *ep)
{
  if (ep->is_in == 1)
  {
    if (((USBx_INEP(ep->num)->DIEPCTL) & USB_OTG_DIEPCTL_EPENA) == 0)
    {
      USBx_INEP(ep->num)->DIEPCTL &= ~(USB_OTG_DIEPCTL_EPDIS); 
    } 
    USBx_INEP(ep->num)->DIEPCTL |= USB_OTG_DIEPCTL_STALL;
  }
  else
  {
    if (((USBx_OUTEP(ep->num)->DOEPCTL) & USB_OTG_DOEPCTL_EPENA) == 0)
    {
      USBx_OUTEP(ep->num)->DOEPCTL &= ~(USB_OTG_DOEPCTL_EPDIS); 
    } 
    USBx_OUTEP(ep->num)->DOEPCTL |= USB_OTG_DOEPCTL_STALL;
  }
  return HAL_OK;
}


/**
  * @brief  USB_EPClearStall : Clear a stall condition over an EP
  * @param  USBx : Selected device
  * @param  ep: pointer to endpoint structure   
  * @retval HAL status
  */
HAL_StatusTypeDef USB_EPClearStall(USB_OTG_GlobalTypeDef *USBx, USB_OTG_EPTypeDef *ep)
{
  if (ep->is_in == 1)
  {
    USBx_INEP(ep->num)->DIEPCTL &= ~USB_OTG_DIEPCTL_STALL;
    if (ep->type == EP_TYPE_INTR || ep->type == EP_TYPE_BULK)
    {
       USBx_INEP(ep->num)->DIEPCTL |= USB_OTG_DIEPCTL_SD0PID_SEVNFRM; /* DATA0 */
    }    
  }
  else
  {
    USBx_OUTEP(ep->num)->DOEPCTL &= ~USB_OTG_DOEPCTL_STALL;
    if (ep->type == EP_TYPE_INTR || ep->type == EP_TYPE_BULK)
    {
      USBx_OUTEP(ep->num)->DOEPCTL |= USB_OTG_DOEPCTL_SD0PID_SEVNFRM; /* DATA0 */
    }    
  }
  return HAL_OK;
}

/**
  * @brief  USB_StopDevice : Stop the usb device mode
  * @param  USBx : Selected device
  * @retval HAL status
  */
HAL_StatusTypeDef USB_StopDevice(USB_OTG_GlobalTypeDef *USBx)
{
  uint32_t i;
  
  /* Clear Pending interrupt */
  for (i = 0; i < 15 ; i++)
  {
    USBx_INEP(i)->DIEPINT  = 0xFF;
    USBx_OUTEP(i)->DOEPINT  = 0xFF;
  }
  USBx_DEVICE->DAINT = 0xFFFFFFFF;
  
  /* Clear interrupt masks */
  USBx_DEVICE->DIEPMSK  = 0;
  USBx_DEVICE->DOEPMSK  = 0;
  USBx_DEVICE->DAINTMSK = 0;
  
  /* Flush the FIFO */
  USB_FlushRxFifo(USBx);
  USB_FlushTxFifo(USBx ,  0x10 );  
  
  return HAL_OK;
}

/**
  * @brief  USB_SetDevAddress : Stop the usb device mode
  * @param  USBx : Selected device
  * @param  address : new device address to be assigned
  *          This parameter can be a value from 0 to 255
  * @retval HAL status
  */
HAL_StatusTypeDef  USB_SetDevAddress (USB_OTG_GlobalTypeDef *USBx, uint8_t address)
{
  USBx_DEVICE->DCFG &= ~ (USB_OTG_DCFG_DAD);
  USBx_DEVICE->DCFG |= (address << 4) & USB_OTG_DCFG_DAD ;
  
  return HAL_OK;  
}

/**
  * @brief  USB_DevConnect : Connect the USB device by enabling the pull-up/pull-down
  * @param  USBx : Selected device
  * @retval HAL status
  */
HAL_StatusTypeDef  USB_DevConnect (USB_OTG_GlobalTypeDef *USBx)
{
  USBx_DEVICE->DCTL &= ~USB_OTG_DCTL_SDIS ;
  HAL_Delay(3);
  
  return HAL_OK;  
}

/**
  * @brief  USB_DevDisconnect : Disconnect the USB device by disabling the pull-up/pull-down
  * @param  USBx : Selected device
  * @retval HAL status
  */
HAL_StatusTypeDef  USB_DevDisconnect (USB_OTG_GlobalTypeDef *USBx)
{
  USBx_DEVICE->DCTL |= USB_OTG_DCTL_SDIS ;
  HAL_Delay(3);
  
  return HAL_OK;  
}

/**
  * @brief  USB_ReadInterrupts: return the global USB interrupt status
  * @param  USBx : Selected device
  * @retval HAL status
  */
uint32_t  USB_ReadInterrupts (USB_OTG_GlobalTypeDef *USBx)
{
  uint32_t v = 0;
  
  v = USBx->GINTSTS;
  v &= USBx->GINTMSK;
  return v;  
}

/**
  * @brief  USB_ReadDevAllOutEpInterrupt: return the USB device OUT endpoints interrupt status
  * @param  USBx : Selected device
  * @retval HAL status
  */
uint32_t USB_ReadDevAllOutEpInterrupt (USB_OTG_GlobalTypeDef *USBx)
{
  uint32_t v;
  v  = USBx_DEVICE->DAINT;
  v &= USBx_DEVICE->DAINTMSK;
  return ((v & 0xffff0000) >> 16);
}

/**
  * @brief  USB_ReadDevAllInEpInterrupt: return the USB device IN endpoints interrupt status
  * @param  USBx : Selected device
  * @retval HAL status
  */
uint32_t USB_ReadDevAllInEpInterrupt (USB_OTG_GlobalTypeDef *USBx)
{
  uint32_t v;
  v  = USBx_DEVICE->DAINT;
  v &= USBx_DEVICE->DAINTMSK;
  return ((v & 0xFFFF));
}

/**
  * @brief  Returns Device OUT EP Interrupt register
  * @param  USBx : Selected device
  * @param  epnum : endpoint number
  *          This parameter can be a value from 0 to 15
  * @retval Device OUT EP Interrupt register
  */
uint32_t USB_ReadDevOutEPInterrupt (USB_OTG_GlobalTypeDef *USBx , uint8_t epnum)
{
  uint32_t v;
  v  = USBx_OUTEP(epnum)->DOEPINT;
  v &= USBx_DEVICE->DOEPMSK;
  return v;
}

/**
  * @brief  Returns Device IN EP Interrupt register
  * @param  USBx : Selected device
  * @param  epnum : endpoint number
  *          This parameter can be a value from 0 to 15
  * @retval Device IN EP Interrupt register
  */
uint32_t USB_ReadDevInEPInterrupt (USB_OTG_GlobalTypeDef *USBx , uint8_t epnum)
{
  uint32_t v, msk, emp;
  
  msk = USBx_DEVICE->DIEPMSK;
  emp = USBx_DEVICE->DIEPEMPMSK;
  msk |= ((emp >> epnum) & 0x1) << 7;
  v = USBx_INEP(epnum)->DIEPINT & msk;
  return v;
}

/**
  * @brief  USB_ClearInterrupts: clear a USB interrupt
  * @param  USBx : Selected device
  * @param  interrupt : interrupt flag
  * @retval None
  */
void  USB_ClearInterrupts (USB_OTG_GlobalTypeDef *USBx, uint32_t interrupt)
{
  USBx->GINTSTS |= interrupt; 
}

/**
  * @brief  Returns USB core mode
  * @param  USBx : Selected device
  * @retval return core mode : Host or Device
  *          This parameter can be one of the these values:
  *           0 : Host 
  *           1 : Device
  */
uint32_t USB_GetMode(USB_OTG_GlobalTypeDef *USBx)
{
  return ((USBx->GINTSTS ) & 0x1);
}


/**
  * @brief  Activate EP0 for Setup transactions
  * @param  USBx : Selected device
  * @retval HAL status
  */
HAL_StatusTypeDef  USB_ActivateSetup (USB_OTG_GlobalTypeDef *USBx)
{
  /* Set the MPS of the IN EP based on the enumeration speed */
  USBx_INEP(0)->DIEPCTL &= ~USB_OTG_DIEPCTL_MPSIZ;
  
  if((USBx_DEVICE->DSTS & USB_OTG_DSTS_ENUMSPD) == DSTS_ENUMSPD_LS_PHY_6MHZ)
  {
    USBx_INEP(0)->DIEPCTL |= 3;
  }
  USBx_DEVICE->DCTL |= USB_OTG_DCTL_CGINAK;

  return HAL_OK;
}


/**
  * @brief  Prepare the EP0 to start the first control setup
  * @param  USBx : Selected device
  * @param  dma: USB dma enabled or disabled 
  *          This parameter can be one of the these values:
  *           0 : DMA feature not used 
  *           1 : DMA feature used  
  * @param  psetup : pointer to setup packet
  * @retval HAL status
  */
HAL_StatusTypeDef USB_EP0_OutStart(USB_OTG_GlobalTypeDef *USBx, uint8_t dma, uint8_t *psetup)
{
  USBx_OUTEP(0)->DOEPTSIZ = 0;
  USBx_OUTEP(0)->DOEPTSIZ |= (USB_OTG_DOEPTSIZ_PKTCNT & (1 << 19)) ;
  USBx_OUTEP(0)->DOEPTSIZ |= (3 * 8);
  USBx_OUTEP(0)->DOEPTSIZ |=  USB_OTG_DOEPTSIZ_STUPCNT;  
  
  if (dma == 1)
  {
    USBx_OUTEP(0)->DOEPDMA = (uint32_t)psetup;
    /* EP enable */
    USBx_OUTEP(0)->DOEPCTL = 0x80008000;
  }
  
  return HAL_OK;  
}


/**
  * @brief  Reset the USB Core (needed after USB clock settings change)
  * @param  USBx : Selected device
  * @retval HAL status
  */
static HAL_StatusTypeDef USB_CoreReset(USB_OTG_GlobalTypeDef *USBx)
{
  uint32_t count = 0;

  /* Wait for AHB master IDLE state. */
  do
  {
    if (++count > 200000)
    {
      return HAL_TIMEOUT;
    }
  }
  while ((USBx->GRSTCTL & USB_OTG_GRSTCTL_AHBIDL) == 0);
  
  /* Core Soft Reset */
  count = 0;
  USBx->GRSTCTL |= USB_OTG_GRSTCTL_CSRST;

  do
  {
    if (++count > 200000)
    {
      return HAL_TIMEOUT;
    }
  }
  while ((USBx->GRSTCTL & USB_OTG_GRSTCTL_CSRST) == USB_OTG_GRSTCTL_CSRST);
  
  return HAL_OK;
}


/**
  * @brief  USB_HostInit : Initializes the USB OTG controller registers 
  *         for Host mode 
  * @param  USBx : Selected device
  * @param  cfg  : pointer to a USB_OTG_CfgTypeDef structure that contains
  *         the configuration information for the specified USBx peripheral.
  * @retval HAL status
  */
HAL_StatusTypeDef USB_HostInit (USB_OTG_GlobalTypeDef *USBx, USB_OTG_CfgTypeDef cfg)
{
  uint32_t i;
  
  /* Restart the Phy Clock */
  USBx_PCGCCTL = 0;
  
  /*Activate VBUS Sensing B */
  USBx->GCCFG |= USB_OTG_GCCFG_VBDEN;
  
  /* Disable the FS/LS support mode only */
  if((cfg.speed == USB_OTG_SPEED_FULL)&&
     (USBx != USB_OTG_FS))
  {
    USBx_HOST->HCFG |= USB_OTG_HCFG_FSLSS; 
  }
  else
  {
    USBx_HOST->HCFG &= ~(USB_OTG_HCFG_FSLSS);  
  }

  /* Make sure the FIFOs are flushed. */
  USB_FlushTxFifo(USBx, 0x10 ); /* all Tx FIFOs */
  USB_FlushRxFifo(USBx);

  /* Clear all pending HC Interrupts */
  for (i = 0; i < cfg.Host_channels; i++)
  {
    USBx_HC(i)->HCINT = 0xFFFFFFFF;
    USBx_HC(i)->HCINTMSK = 0;
  }
  
  /* Enable VBUS driving */
  USB_DriveVbus(USBx, 1);
  
  HAL_Delay(200);
  
  /* Disable all interrupts. */
  USBx->GINTMSK = 0;
  
  /* Clear any pending interrupts */
  USBx->GINTSTS = 0xFFFFFFFF;

  
  if(USBx == USB_OTG_FS)
  {
    /* set Rx FIFO size */
    USBx->GRXFSIZ  = (uint32_t )0x80; 
    USBx->DIEPTXF0_HNPTXFSIZ = (uint32_t )(((0x60 << 16)& USB_OTG_NPTXFD) | 0x80);
    USBx->HPTXFSIZ = (uint32_t )(((0x40 << 16)& USB_OTG_HPTXFSIZ_PTXFD) | 0xE0);

  }

  else
  {
    /* set Rx FIFO size */
    USBx->GRXFSIZ  = (uint32_t )0x200; 
    USBx->DIEPTXF0_HNPTXFSIZ = (uint32_t )(((0x100 << 16)& USB_OTG_NPTXFD) | 0x200);
    USBx->HPTXFSIZ = (uint32_t )(((0xE0 << 16)& USB_OTG_HPTXFSIZ_PTXFD) | 0x300);
  }
  
  /* Enable the common interrupts */
  if (cfg.dma_enable == DISABLE)
  {
    USBx->GINTMSK |= USB_OTG_GINTMSK_RXFLVLM; 
  }
  
  /* Enable interrupts matching to the Host mode ONLY */
  USBx->GINTMSK |= (USB_OTG_GINTMSK_PRTIM            | USB_OTG_GINTMSK_HCIM |\
                    USB_OTG_GINTMSK_SOFM             |USB_OTG_GINTSTS_DISCINT|\
                    USB_OTG_GINTMSK_PXFRM_IISOOXFRM  | USB_OTG_GINTMSK_WUIM);

  return HAL_OK;
}

/**
  * @brief  USB_InitFSLSPClkSel : Initializes the FSLSPClkSel field of the 
  *         HCFG register on the PHY type and set the right frame interval
  * @param  USBx : Selected device
  * @param  freq : clock frequency
  *          This parameter can be one of the these values:
  *           HCFG_48_MHZ : Full Speed 48 MHz Clock 
  *           HCFG_6_MHZ : Low Speed 6 MHz Clock 
  * @retval HAL status
  */
HAL_StatusTypeDef USB_InitFSLSPClkSel(USB_OTG_GlobalTypeDef *USBx , uint8_t freq)
{
  USBx_HOST->HCFG &= ~(USB_OTG_HCFG_FSLSPCS);
  USBx_HOST->HCFG |= (freq & USB_OTG_HCFG_FSLSPCS);
  
  if (freq ==  HCFG_48_MHZ)
  {
    USBx_HOST->HFIR = (uint32_t)48000;
  }
  else if (freq ==  HCFG_6_MHZ)
  {
    USBx_HOST->HFIR = (uint32_t)6000;
  } 
  return HAL_OK;  
}

/**
* @brief  USB_OTG_ResetPort : Reset Host Port
  * @param  USBx : Selected device
  * @retval HAL status
  * @note : (1)The application must wait at least 10 ms
  *   before clearing the reset bit.
  */
HAL_StatusTypeDef USB_ResetPort(USB_OTG_GlobalTypeDef *USBx)
{
  __IO uint32_t hprt0;
  
  hprt0 = USBx_HPRT0;
  
  hprt0 &= ~(USB_OTG_HPRT_PENA    | USB_OTG_HPRT_PCDET |\
    USB_OTG_HPRT_PENCHNG | USB_OTG_HPRT_POCCHNG );
  
  USBx_HPRT0 = (USB_OTG_HPRT_PRST | hprt0);  
  HAL_Delay (10);                                /* See Note #1 */
  USBx_HPRT0 = ((~USB_OTG_HPRT_PRST) & hprt0); 
  return HAL_OK;
}

/**
  * @brief  USB_DriveVbus : activate or de-activate vbus
  * @param  state : VBUS state
  *          This parameter can be one of the these values:
  *           0 : VBUS Active 
  *           1 : VBUS Inactive
  * @retval HAL status
*/
HAL_StatusTypeDef USB_DriveVbus (USB_OTG_GlobalTypeDef *USBx, uint8_t state)
{
  __IO uint32_t hprt0;

  hprt0 = USBx_HPRT0;
  hprt0 &= ~(USB_OTG_HPRT_PENA    | USB_OTG_HPRT_PCDET |\
                         USB_OTG_HPRT_PENCHNG | USB_OTG_HPRT_POCCHNG );
  
  if (((hprt0 & USB_OTG_HPRT_PPWR) == 0 ) && (state == 1 ))
  {
    USBx_HPRT0 = (USB_OTG_HPRT_PPWR | hprt0); 
  }
  if (((hprt0 & USB_OTG_HPRT_PPWR) == USB_OTG_HPRT_PPWR) && (state == 0 ))
  {
    USBx_HPRT0 = ((~USB_OTG_HPRT_PPWR) & hprt0); 
  }
  return HAL_OK; 
}

/**
  * @brief  Return Host Core speed
  * @param  USBx : Selected device
  * @retval speed : Host speed
  *          This parameter can be one of the these values:
  *            @arg USB_OTG_SPEED_HIGH: High speed mode
  *            @arg USB_OTG_SPEED_FULL: Full speed mode
  *            @arg USB_OTG_SPEED_LOW: Low speed mode
  */
uint32_t USB_GetHostSpeed (USB_OTG_GlobalTypeDef *USBx)
{
  __IO uint32_t hprt0;
  
  hprt0 = USBx_HPRT0;
  return ((hprt0 & USB_OTG_HPRT_PSPD) >> 17);
}

/**
  * @brief  Return Host Current Frame number
  * @param  USBx : Selected device
  * @retval current frame number
*/
uint32_t USB_GetCurrentFrame (USB_OTG_GlobalTypeDef *USBx)
{
  return (USBx_HOST->HFNUM & USB_OTG_HFNUM_FRNUM);
}

/**
  * @brief  Initialize a host channel
  * @param  USBx : Selected device
  * @param  ch_num : Channel number
  *         This parameter can be a value from 1 to 15
  * @param  epnum : Endpoint number
  *          This parameter can be a value from 1 to 15
  * @param  dev_address : Current device address
  *          This parameter can be a value from 0 to 255
  * @param  speed : Current device speed
  *          This parameter can be one of the these values:
  *            @arg USB_OTG_SPEED_HIGH: High speed mode
  *            @arg USB_OTG_SPEED_FULL: Full speed mode
  *            @arg USB_OTG_SPEED_LOW: Low speed mode
  * @param  ep_type : Endpoint Type
  *          This parameter can be one of the these values:
  *            @arg EP_TYPE_CTRL: Control type
  *            @arg EP_TYPE_ISOC: Isochronous type
  *            @arg EP_TYPE_BULK: Bulk type
  *            @arg EP_TYPE_INTR: Interrupt type
  * @param  mps : Max Packet Size
  *          This parameter can be a value from 0 to32K
  * @retval HAL state
  */
HAL_StatusTypeDef USB_HC_Init(USB_OTG_GlobalTypeDef *USBx,  
                              uint8_t ch_num,
                              uint8_t epnum,
                              uint8_t dev_address,
                              uint8_t speed,
                              uint8_t ep_type,
                              uint16_t mps)
{
    
  /* Clear old interrupt conditions for this host channel. */
  USBx_HC(ch_num)->HCINT = 0xFFFFFFFF;
  
  /* Enable channel interrupts required for this transfer. */
  switch (ep_type) 
  {
  case EP_TYPE_CTRL:
  case EP_TYPE_BULK:
    
    USBx_HC(ch_num)->HCINTMSK = USB_OTG_HCINTMSK_XFRCM  |\
                                USB_OTG_HCINTMSK_STALLM |\
                                USB_OTG_HCINTMSK_TXERRM |\
                                USB_OTG_HCINTMSK_DTERRM |\
                                USB_OTG_HCINTMSK_AHBERR |\
                                USB_OTG_HCINTMSK_NAKM ;
 
    if (epnum & 0x80) 
    {
      USBx_HC(ch_num)->HCINTMSK |= USB_OTG_HCINTMSK_BBERRM;
    } 
    else 
    {
      if(USBx != USB_OTG_FS)
      {
        USBx_HC(ch_num)->HCINTMSK |= (USB_OTG_HCINTMSK_NYET | USB_OTG_HCINTMSK_ACKM);
      }
    }
    break;
  case EP_TYPE_INTR:
    
    USBx_HC(ch_num)->HCINTMSK = USB_OTG_HCINTMSK_XFRCM  |\
                                USB_OTG_HCINTMSK_STALLM |\
                                USB_OTG_HCINTMSK_TXERRM |\
                                USB_OTG_HCINTMSK_DTERRM |\
                                USB_OTG_HCINTMSK_NAKM   |\
                                USB_OTG_HCINTMSK_AHBERR |\
                                USB_OTG_HCINTMSK_FRMORM ;    
    
    if (epnum & 0x80) 
    {
      USBx_HC(ch_num)->HCINTMSK |= USB_OTG_HCINTMSK_BBERRM;
    }
    
    break;
  case EP_TYPE_ISOC:
    
    USBx_HC(ch_num)->HCINTMSK = USB_OTG_HCINTMSK_XFRCM  |\
                                USB_OTG_HCINTMSK_ACKM   |\
                                USB_OTG_HCINTMSK_AHBERR |\
                                USB_OTG_HCINTMSK_FRMORM ;   
    
    if (epnum & 0x80) 
    {
      USBx_HC(ch_num)->HCINTMSK |= (USB_OTG_HCINTMSK_TXERRM | USB_OTG_HCINTMSK_BBERRM);      
    }
    break;
  }
  
  /* Enable the top level host channel interrupt. */
  USBx_HOST->HAINTMSK |= (1 << ch_num);
  
  /* Make sure host channel interrupts are enabled. */
  USBx->GINTMSK |= USB_OTG_GINTMSK_HCIM;
  
  /* Program the HCCHAR register */
  USBx_HC(ch_num)->HCCHAR = (((dev_address << 22) & USB_OTG_HCCHAR_DAD)  |\
                             (((epnum & 0x7F)<< 11) & USB_OTG_HCCHAR_EPNUM)|\
                             ((((epnum & 0x80) == 0x80)<< 15) & USB_OTG_HCCHAR_EPDIR)|\
                             (((speed == HPRT0_PRTSPD_LOW_SPEED)<< 17) & USB_OTG_HCCHAR_LSDEV)|\
                             ((ep_type << 18) & USB_OTG_HCCHAR_EPTYP)|\
                             (mps & USB_OTG_HCCHAR_MPSIZ));
    
  if (ep_type == EP_TYPE_INTR)
  {
    USBx_HC(ch_num)->HCCHAR |= USB_OTG_HCCHAR_ODDFRM ;
  }

  return HAL_OK; 
}

/**
  * @brief  Start a transfer over a host channel
  * @param  USBx : Selected device
  * @param  hc : pointer to host channel structure
  * @param  dma: USB dma enabled or disabled 
  *          This parameter can be one of the these values:
  *           0 : DMA feature not used 
  *           1 : DMA feature used  
  * @retval HAL state
  */
#if defined   (__CC_ARM) /*!< ARM Compiler */
#pragma O0
#elif defined (__GNUC__) /*!< GNU Compiler */
#pragma GCC optimize ("O0")
#endif /* __CC_ARM */
HAL_StatusTypeDef USB_HC_StartXfer(USB_OTG_GlobalTypeDef *USBx, USB_OTG_HCTypeDef *hc, uint8_t dma)
{
  uint8_t  is_oddframe = 0; 
  uint16_t len_words = 0;   
  uint16_t num_packets = 0;
  uint16_t max_hc_pkt_count = 256;
  
  if((USBx != USB_OTG_FS) && (hc->speed == USB_OTG_SPEED_HIGH))
  {
    if((dma == 0) && (hc->do_ping == 1))
    {
      USB_DoPing(USBx, hc->ch_num);
      return HAL_OK;
    }
    else if(dma == 1)
    {
      USBx_HC(hc->ch_num)->HCINTMSK &= ~(USB_OTG_HCINTMSK_NYET | USB_OTG_HCINTMSK_ACKM);
      hc->do_ping = 0;
    }
  }
  
  /* Compute the expected number of packets associated to the transfer */
  if (hc->xfer_len > 0)
  {
    num_packets = (hc->xfer_len + hc->max_packet - 1) / hc->max_packet;
    
    if (num_packets > max_hc_pkt_count)
    {
      num_packets = max_hc_pkt_count;
      hc->xfer_len = num_packets * hc->max_packet;
    }
  }
  else
  {
    num_packets = 1;
  }
  if (hc->ep_is_in)
  {
    hc->xfer_len = num_packets * hc->max_packet;
  }
  
  
  
  /* Initialize the HCTSIZn register */
  USBx_HC(hc->ch_num)->HCTSIZ = (((hc->xfer_len) & USB_OTG_HCTSIZ_XFRSIZ)) |\
    ((num_packets << 19) & USB_OTG_HCTSIZ_PKTCNT) |\
      (((hc->data_pid) << 29) & USB_OTG_HCTSIZ_DPID);
  
  if (dma)
  {
    /* xfer_buff MUST be 32-bits aligned */
    USBx_HC(hc->ch_num)->HCDMA = (uint32_t)hc->xfer_buff;
  }
  
  is_oddframe = (USBx_HOST->HFNUM & 0x01) ? 0 : 1;
  USBx_HC(hc->ch_num)->HCCHAR &= ~USB_OTG_HCCHAR_ODDFRM;
  USBx_HC(hc->ch_num)->HCCHAR |= (is_oddframe << 29);
  
  /* Set host channel enable */
  USBx_HC(hc->ch_num)->HCCHAR &= ~USB_OTG_HCCHAR_CHDIS;
  USBx_HC(hc->ch_num)->HCCHAR |= USB_OTG_HCCHAR_CHENA;
  
  if (dma == 0) /* Slave mode */
  {  
    if((hc->ep_is_in == 0) && (hc->xfer_len > 0))
    {
      switch(hc->ep_type) 
      {
        /* Non periodic transfer */
      case EP_TYPE_CTRL:
      case EP_TYPE_BULK:
        
        len_words = (hc->xfer_len + 3) / 4;
        
        /* check if there is enough space in FIFO space */
        if(len_words > (USBx->HNPTXSTS & 0xFFFF))
        {
          /* need to process data in nptxfempty interrupt */
          USBx->GINTMSK |= USB_OTG_GINTMSK_NPTXFEM;
        }
        break;
        /* Periodic transfer */
      case EP_TYPE_INTR:
      case EP_TYPE_ISOC:
        len_words = (hc->xfer_len + 3) / 4;
        /* check if there is enough space in FIFO space */
        if(len_words > (USBx_HOST->HPTXSTS & 0xFFFF)) /* split the transfer */
        {
          /* need to process data in ptxfempty interrupt */
          USBx->GINTMSK |= USB_OTG_GINTMSK_PTXFEM;          
        }
        break;
        
      default:
        break;
      }
      
      /* Write packet into the Tx FIFO. */
      USB_WritePacket(USBx, hc->xfer_buff, hc->ch_num, hc->xfer_len, 0);
    }
  }
  
  return HAL_OK;
}

/**
  * @brief Read all host channel interrupts status
  * @param  USBx : Selected device
  * @retval HAL state
  */
uint32_t USB_HC_ReadInterrupt (USB_OTG_GlobalTypeDef *USBx)
{
  return ((USBx_HOST->HAINT) & 0xFFFF);
}

/**
  * @brief  Halt a host channel
  * @param  USBx : Selected device
  * @param  hc_num : Host Channel number
  *         This parameter can be a value from 1 to 15
  * @retval HAL state
  */
HAL_StatusTypeDef USB_HC_Halt(USB_OTG_GlobalTypeDef *USBx , uint8_t hc_num)
{
  uint32_t count = 0;
  
  /* Check for space in the request queue to issue the halt. */
  if (((USBx_HC(hc_num)->HCCHAR) & (HCCHAR_CTRL << 18)) || ((USBx_HC(hc_num)->HCCHAR) & (HCCHAR_BULK << 18)))
  {
    USBx_HC(hc_num)->HCCHAR |= USB_OTG_HCCHAR_CHDIS;
    
    if ((USBx->HNPTXSTS & 0xFFFF) == 0)
    {
      USBx_HC(hc_num)->HCCHAR &= ~USB_OTG_HCCHAR_CHENA;
      USBx_HC(hc_num)->HCCHAR |= USB_OTG_HCCHAR_CHENA;  
      USBx_HC(hc_num)->HCCHAR &= ~USB_OTG_HCCHAR_EPDIR;
      do 
      {
        if (++count > 1000) 
        {
          break;
        }
      } 
      while ((USBx_HC(hc_num)->HCCHAR & USB_OTG_HCCHAR_CHENA) == USB_OTG_HCCHAR_CHENA);     
    }
    else
    {
      USBx_HC(hc_num)->HCCHAR |= USB_OTG_HCCHAR_CHENA; 
    }
  }
  else
  {
    USBx_HC(hc_num)->HCCHAR |= USB_OTG_HCCHAR_CHDIS;
    
    if ((USBx_HOST->HPTXSTS & 0xFFFF) == 0)
    {
      USBx_HC(hc_num)->HCCHAR &= ~USB_OTG_HCCHAR_CHENA;
      USBx_HC(hc_num)->HCCHAR |= USB_OTG_HCCHAR_CHENA;  
      USBx_HC(hc_num)->HCCHAR &= ~USB_OTG_HCCHAR_EPDIR;
      do 
      {
        if (++count > 1000) 
        {
          break;
        }
      } 
      while ((USBx_HC(hc_num)->HCCHAR & USB_OTG_HCCHAR_CHENA) == USB_OTG_HCCHAR_CHENA);     
    }
    else
    {
       USBx_HC(hc_num)->HCCHAR |= USB_OTG_HCCHAR_CHENA; 
    }
  }
  
  return HAL_OK;
}

/**
  * @brief  Initiate Do Ping protocol
  * @param  USBx : Selected device
  * @param  hc_num : Host Channel number
  *         This parameter can be a value from 1 to 15
  * @retval HAL state
  */
HAL_StatusTypeDef USB_DoPing(USB_OTG_GlobalTypeDef *USBx , uint8_t ch_num)
{
  uint8_t  num_packets = 1;

  USBx_HC(ch_num)->HCTSIZ = ((num_packets << 19) & USB_OTG_HCTSIZ_PKTCNT) |\
                                USB_OTG_HCTSIZ_DOPING;
  
  /* Set host channel enable */
  USBx_HC(ch_num)->HCCHAR &= ~USB_OTG_HCCHAR_CHDIS;
  USBx_HC(ch_num)->HCCHAR |= USB_OTG_HCCHAR_CHENA;
  
  return HAL_OK;  
}

/**
  * @brief  Stop Host Core
  * @param  USBx : Selected device
  * @retval HAL state
  */
HAL_StatusTypeDef USB_StopHost(USB_OTG_GlobalTypeDef *USBx)
{
  uint8_t i;
  uint32_t count = 0;
  uint32_t value;
  
  USB_DisableGlobalInt(USBx);
  
    /* Flush FIFO */
  USB_FlushTxFifo(USBx, 0x10);
  USB_FlushRxFifo(USBx);
  
  /* Flush out any leftover queued requests. */
  for (i = 0; i <= 15; i++)
  {   

    value = USBx_HC(i)->HCCHAR ;
    value |=  USB_OTG_HCCHAR_CHDIS;
    value &= ~USB_OTG_HCCHAR_CHENA;  
    value &= ~USB_OTG_HCCHAR_EPDIR;
    USBx_HC(i)->HCCHAR = value;
  }
  
  /* Halt all channels to put them into a known state. */  
  for (i = 0; i <= 15; i++)
  {   

    value = USBx_HC(i)->HCCHAR ;
    
    value |= USB_OTG_HCCHAR_CHDIS;
    value |= USB_OTG_HCCHAR_CHENA;  
    value &= ~USB_OTG_HCCHAR_EPDIR;
    
    USBx_HC(i)->HCCHAR = value;
    do 
    {
      if (++count > 1000) 
      {
        break;
      }
    } 
    while ((USBx_HC(i)->HCCHAR & USB_OTG_HCCHAR_CHENA) == USB_OTG_HCCHAR_CHENA);
  }

  /* Clear any pending Host interrupts */
  USBx_HOST->HAINT = 0xFFFFFFFF;
  USBx->GINTSTS = 0xFFFFFFFF;
  USB_EnableGlobalInt(USBx);
  return HAL_OK;  
}
/**
  * @}
  */

#endif /* defined (HAL_PCD_MODULE_ENABLED) || defined (HAL_HCD_MODULE_ENABLED) */

/**
  * @}
  */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
