/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2010, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/** \file */

#ifndef USBHS_H
#define USBHS_H
/** addtogroup usbd_hal
 *@{
 */

#define  USB_DEVICE_HS_SUPPORT

//! Control endpoint size
#define  USB_DEVICE_EP_CTRL_SIZE       64

/** Indicates chip has an UDP High Speed. */
#define CHIP_USB_UDP

/** Indicates chip has an internal pull-up. */
#define CHIP_USB_PULLUP_INTERNAL

/** Number of USB endpoints */
#define CHIP_USB_NUMENDPOINTS   10

/** Endpoints max packet size */
#define CHIP_USB_ENDPOINTS_MAXPACKETSIZE(ep) \
   ((ep == 0) ? 64 : 1024)

/** Endpoints Number of Bank */
#define CHIP_USB_ENDPOINTS_BANKS(ep)            ((ep==0)?1:((ep<=2)?3:2))
     
     
#define CHIP_USB_ENDPOINTS_HBW(ep)               ((((ep)>=1) &&((ep)<=2))?true:false)

/** Endpoints DMA support */
#define CHIP_USB_ENDPOINTS_DMA(ep)              ((((ep)>=1)&&((ep)<=7))?true:false)
    
/** Max size of the FMA FIFO */
#define DMA_MAX_FIFO_SIZE     (65536/1)
/** fifo space size in DW */
#define EPT_VIRTUAL_SIZE      16384     
         
     
     //! @name USBHS Host IP properties
//!
//! @{
//! Get maximal number of endpoints
#define uhd_get_pipe_max_nbr()                (9)
#define USBHS_EPT_NUM                        (uhd_get_pipe_max_nbr()+1)
  //! Get maximal number of banks of endpoints
#define uhd_get_pipe_bank_max_nbr(ep)         ((ep == 0) ? 1 : (( ep <= 2) ? 3 : 2))
  //! Get maximal size of endpoint (3X, 1024/64)
#define uhd_get_pipe_size_max(ep)             (((ep) == 0) ? 64 : 1024)
  //! Get DMA support of endpoints
#define Is_uhd_pipe_dma_supported(ep)         ((((ep) >= 1) && ((ep) <= 6)) ? true : false)
  //! Get High Band Width support of endpoints
#define Is_uhd_pipe_high_bw_supported(ep)     (((ep) >= 2) ? true : false)
//! @}

typedef enum
{
  HOST_MODE= 0,
  DEVICE_MODE=1
}USB_Mode_t;

//! Maximum transfer size on USB DMA
#define UHD_PIPE_MAX_TRANS 0x8000

/**
=================================  
		USBHS_CTRL 
=================================
**/

/**
 * \brief Freeze or unfreeze USB clock
 * \param pUsbhs   Pointer to an USBHS instance.
 * \param Enable Enable or disable
 */
__STATIC_INLINE void USBHS_FreezeClock(Usbhs *pUsbhs)
{
	pUsbhs->USBHS_CTRL |= USBHS_CTRL_FRZCLK;
}

/**
 * \brief Freeze or unfreeze USB clock
 * \param pUsbhs   Pointer to an USBHS instance.
 * \param Enable Enable or disable
 */
__STATIC_INLINE void USBHS_UnFreezeClock(Usbhs *pUsbhs)
{
  pUsbhs->USBHS_CTRL &= ~((uint32_t)USBHS_CTRL_FRZCLK);
}
/**
 * \brief Freeze or unfreeze USB clock
 * \param pUsbhs   Pointer to an USBHS instance.
 * \param Enable Enable or disable
 */
__STATIC_INLINE void USBHS_VBusHWC(Usbhs *pUsbhs, uint8_t Enable)
{
      
    if(!Enable) {
        pUsbhs->USBHS_CTRL |= (1<<8);
    } else {
        pUsbhs->USBHS_CTRL &= ~((uint32_t)(1<<8));
    }
}

/**
 * \brief Enables or disables USB 
 * \param pUsbhs   Pointer to an USBHS instance.
 * \param Enable Enable or disable
 */

__STATIC_INLINE void USBHS_UsbEnable(Usbhs *pUsbhs, uint8_t Enable)
{
	if(Enable) {
		pUsbhs->USBHS_CTRL |= USBHS_CTRL_USBE;
	} else {
		pUsbhs->USBHS_CTRL &= ~((uint32_t)USBHS_CTRL_USBE);
	}
}


/**
 * \brief Device or Host Mode
 * \param pUsbhs   Pointer to an USBHS instance.
 * \param Mode   Device or Host Mode
 */

__STATIC_INLINE void USBHS_UsbMode(Usbhs *pUsbhs, USB_Mode_t Mode)
{
	if(Mode) {
		pUsbhs->USBHS_CTRL |= USBHS_CTRL_UIMOD_DEVICE;
	} else {
		pUsbhs->USBHS_CTRL &= ~((uint32_t)USBHS_CTRL_UIMOD_DEVICE);
	}
}

/********************* USBHS_SR  *****************/

/**
 * \brief Check if clock is usable or not
 * \param pUsbhs   Pointer to an USBHS instance.
 * \return 1 if USB clock is usable
 */

__STATIC_INLINE uint8_t USBHS_ISUsableClock(Usbhs *pUsbhs)
{ 
	return (( pUsbhs->USBHS_SR & USBHS_SR_CLKUSABLE) >> 14);
}


/**
 * \brief Raise interrupt for endpoint.
 * \param pUsbhs   Pointer to an USBHS instance.
 * \return USB status
 */

__STATIC_INLINE uint32_t USBHS_ReadStatus(Usbhs *pUsbhs)
{   
	return (pUsbhs->USBHS_SR);   
}

/**
 * \brief Enable or disable USB address
 * \param pUsbhs   Pointer to an USBHS instance.
 * \return USB speed status
 */

__STATIC_INLINE uint32_t USBHS_GetUsbSpeed(Usbhs *pUsbhs)
{
	return ( (pUsbhs->USBHS_SR & USBHS_SR_SPEED_Msk) );
}


/**
 * \brief Enable or disable USB address
 * \param pUsbhs   Pointer to an USBHS instance.
 * \return USB speed status
 */

__STATIC_INLINE bool USBHS_IsUsbFullSpeed(Usbhs *pUsbhs)
{
  return ( (pUsbhs->USBHS_SR & USBHS_SR_SPEED_Msk) == USBHS_SR_SPEED_FULL_SPEED) ? true:false;
}


/**
 * \brief Enable or disable USB address
 * \param pUsbhs   Pointer to an USBHS instance.
 * \return USB speed status
 */

__STATIC_INLINE bool USBHS_IsUsbHighSpeed(Usbhs *pUsbhs)
{
    return ( (pUsbhs->USBHS_SR & USBHS_SR_SPEED_Msk) == USBHS_SR_SPEED_HIGH_SPEED) ? true:false;
}

/**
 * \brief Enable or disable USB address
 * \param pUsbhs   Pointer to an USBHS instance.
 * \return USB speed status
 */

__STATIC_INLINE bool USBHS_IsUsbLowSpeed(Usbhs *pUsbhs)
{
    return ( (pUsbhs->USBHS_SR & USBHS_SR_SPEED_Msk) == USBHS_SR_SPEED_LOW_SPEED) ? true:false;
}
/********************* USBHS_SCR  *****************/

/**
 * \brief Raise interrupt for endpoint.
 * \param pUsbhs   Pointer to an USBHS instance.
 * \param AckType Interrupt Acknowledge type
 */

__STATIC_INLINE void USBHS_Ack(Usbhs *pUsbhs, uint32_t AckType)
{
	pUsbhs->USBHS_SCR |= AckType;
}

/********************* USBHS_SFR  *****************/

/**
 * \brief Raise interrupt for endpoint.
 * \param pUsbhs   Pointer to an USBHS instance.
 * \param SetStatus Set USB status
 */

__STATIC_INLINE void USBHS_Set(Usbhs *pUsbhs, uint32_t SetStatus)
{
	pUsbhs->USBHS_SFR |= SetStatus;
}


 /*--------------------------------------------------------
 * =========== USB Device functions ======================
 *---------------------------------------------------------*/

/**
 * \brief Enable or disable USB address
 * \param pUsbhs   Pointer to an USBHS instance.
 * \param SetStatus Set USB status
 */

__STATIC_INLINE void USBHS_EnableAddress(Usbhs *pUsbhs, uint8_t Enable)
{
	if(Enable) {
		pUsbhs->USBHS_DEVCTRL |= USBHS_DEVCTRL_ADDEN;
	} else {
		pUsbhs->USBHS_DEVCTRL &= ~((uint32_t)USBHS_DEVCTRL_ADDEN);
	}
}

/**
 * \brief Configure USB address and enable or disable it
 * \param pUsbhs   Pointer to an USBHS instance.
 * \param Addr   USB device status
 */

__STATIC_INLINE void USBHS_SetAddress(Usbhs *pUsbhs, uint8_t Addr)
{
	pUsbhs->USBHS_DEVCTRL |= USBHS_DEVCTRL_UADD(Addr);
	pUsbhs->USBHS_DEVCTRL |= USBHS_DEVCTRL_ADDEN;
}

/**
 * \brief Get USB address
 * \param pUsbhs   Pointer to an USBHS instance.
 */

__STATIC_INLINE uint8_t USBHS_GetAddress(Usbhs *pUsbhs)
{
	return ( pUsbhs->USBHS_DEVCTRL & USBHS_DEVCTRL_UADD_Msk);
}

/**
 * \brief Attach or detach USB.
 * \param pUsbhs   Pointer to an USBHS instance.
 * \param Enable Attachs or detach USB device
 */

__STATIC_INLINE void USBHS_DetachUsb(Usbhs *pUsbhs, uint8_t Enable)
{
	if(Enable) {
		pUsbhs->USBHS_DEVCTRL |= USBHS_DEVCTRL_DETACH;
	} else {
		pUsbhs->USBHS_DEVCTRL &= ~((uint32_t)USBHS_DEVCTRL_DETACH);
	}
  
}

/**
 * \brief Force Low Speed mode
 * \param pUsbhs   Pointer to an USBHS instance.
 * \param Enable Enables the Full speed
 */

__STATIC_INLINE void USBHS_ForceLowSpeed(Usbhs *pUsbhs, uint8_t Enable)
{
	if(Enable) {
		pUsbhs->USBHS_DEVCTRL |= USBHS_DEVCTRL_LS;
	} else {
		pUsbhs->USBHS_DEVCTRL &= ~((uint32_t)USBHS_DEVCTRL_LS);
	}
}

/**
 * \brief Disable/Enables High Speed mode
 * \param pUsbhs   Pointer to an USBHS instance.
 * \param Enable Enables/disable option
 */

__STATIC_INLINE void USBHS_EnableHighSpeed(Usbhs *pUsbhs, uint8_t Enable)
{
	uint32_t cfg = pUsbhs->USBHS_DEVCTRL;
	cfg &= ~((uint32_t)USBHS_DEVCTRL_SPDCONF_Msk);
	if(Enable) {
		pUsbhs->USBHS_DEVCTRL |= cfg;
	} else {
		pUsbhs->USBHS_DEVCTRL |= (cfg | USBHS_DEVCTRL_SPDCONF_FORCED_FS);
	}
  
}

/**
 * \brief Set Remote WakeUp mode
 * \param pUsbhs   Pointer to an USBHS instance.
 */

__STATIC_INLINE void USBHS_SetRemoteWakeUp(Usbhs *pUsbhs)
{
	pUsbhs->USBHS_DEVCTRL |= USBHS_DEVCTRL_RMWKUP;
}

/**
 * \brief Disable/Enables Test mode
 * \param pUsbhs   Pointer to an USBHS instance.
 * \param mode Enables/disable option
 */

__STATIC_INLINE void USBHS_EnableTestMode(Usbhs *pUsbhs, uint32_t mode)
{
	pUsbhs->USBHS_DEVCTRL |= mode;
}


/**
 * \brief Disable/Enables HS Test mode
 * \param pUsbhs   Pointer to an USBHS instance.
 */

__STATIC_INLINE void USBHS_EnableHSTestMode(Usbhs *pUsbhs)
{
	pUsbhs->USBHS_DEVCTRL |= USBHS_DEVCTRL_SPDCONF_HIGH_SPEED;
}

/**
 * \brief Read status for an interrupt
 * \param pUsbhs   Pointer to an USBHS instance.
 * \param IntType Interrupt type
 */

__STATIC_INLINE uint32_t USBHS_ReadIntStatus(Usbhs *pUsbhs, uint32_t IntType)
{   
	return (pUsbhs->USBHS_DEVISR & IntType);    
}

/**
 * \brief Read status for an Endpoint
 * \param pUsbhs   Pointer to an USBHS instance.
 * \param EpNum  Endpoint
 */

__STATIC_INLINE uint32_t USBHS_ReadEpIntStatus(Usbhs *pUsbhs, uint8_t EpNum)
{   
	return (pUsbhs->USBHS_DEVISR & ( USBHS_DEVISR_PEP_0 << EpNum) );    
}

/**
 * \brief Read status for a DMA Endpoint
 * \param pUsbhs   Pointer to an USBHS instance.
 * \param DmaNum  DMA Endpoint
 */
__STATIC_INLINE uint32_t USBHS_ReadDmaIntStatus(Usbhs *pUsbhs, uint8_t DmaNum)
{   
	return (pUsbhs->USBHS_DEVISR & ( USBHS_DEVISR_DMA_1 << DmaNum) );
}

/**
 * \brief Acknowledge interrupt for endpoint.
 * \param pUsbhs   Pointer to an USBHS instance.
 * \param IntType Interrupt Type
 */

__STATIC_INLINE void USBHS_AckInt(Usbhs *pUsbhs, uint32_t IntType)
{   
	pUsbhs->USBHS_DEVICR |=  IntType;
}

/**
 * \brief Raise interrupt for endpoint.
 * \param pUsbhs   Pointer to an USBHS instance.
 * \param IntType Interrupt Type
 */


__STATIC_INLINE void USBHS_RaiseInt(Usbhs *pUsbhs, uint32_t IntType)
{   
	pUsbhs->USBHS_DEVIFR |=  IntType;
}

/**
 * \brief Raise DMA interrupt for endpoint.
 * \param pUsbhs   Pointer to an USBHS instance.
 * \param IntType Interrupt Type
 */
__STATIC_INLINE void USBHS_RaiseDmaInt(Usbhs *pUsbhs, uint8_t Dma)
{   
	assert(Dma< USBHSDEVDMA_NUMBER);
	pUsbhs->USBHS_DEVIFR |=  ( USBHS_DEVIFR_DMA_1 << Dma );
}

/**
 * \brief check for interrupt of endpoint.
 * \param pUsbhs   Pointer to an USBHS instance.
 * \param IntType Interrupt Type
 */

__STATIC_INLINE uint32_t USBHS_IsIntEnable(Usbhs *pUsbhs, uint32_t IntType)
{
	return (pUsbhs->USBHS_DEVIMR &  IntType);
}

/**
 * \brief Check if endpoint's interrupt is enabled for a given endpoint number
 * \param pUsbhs   Pointer to an USBHS instance.
 * \param EpNum Endpoint number
 */

__STATIC_INLINE uint32_t USBHS_IsIntEnableEP(Usbhs *pUsbhs, uint8_t EpNum)
{
	return (pUsbhs->USBHS_DEVIMR &  (USBHS_DEVIMR_PEP_0 << EpNum ));
}


/**
 * \brief Check if endpoint's DMA interrupt is enabled for a given endpoint 
 * DMA number
 * \param pUsbhs   Pointer to an USBHS instance.
 * \param DmaNum Endpoint's DMA number
 */

__STATIC_INLINE uint32_t USBHS_IsDmaIntEnable(Usbhs *pUsbhs, uint8_t DmaNum)
{
	return (pUsbhs->USBHS_DEVIMR &  (USBHS_DEVIMR_DMA_1 << DmaNum));
}


/**
 * \brief Enables Interrupt
 * \param pUsbhs   Pointer to an USBHS instance.
 * \param IntType Interrupt Type
 */
__STATIC_INLINE void USBHS_EnableInt(Usbhs *pUsbhs, uint32_t IntType)
{   
	pUsbhs->USBHS_DEVIER |=  IntType;
}

/**
 * \brief Enables interrupt for a given endpoint.
 * \param pUsbhs   Pointer to an USBHS instance.
 * \param DmaNum Endpoint's DMA number
 */
__STATIC_INLINE void USBHS_EnableIntEP(Usbhs *pUsbhs, uint8_t EpNum)
{   
	pUsbhs->USBHS_DEVIER |=  (USBHS_DEVIER_PEP_0 << EpNum);
}

/**
 * \brief Enables DMA interrupt for a given endpoint.
 * \param pUsbhs   Pointer to an USBHS instance.
 * \param DmaEp  Endpoint's DMA interrupt number
 */

__STATIC_INLINE void USBHS_EnableDMAIntEP(Usbhs *pUsbhs, uint32_t DmaEp)
{   
	assert(DmaEp< USBHSDEVDMA_NUMBER);
	pUsbhs->USBHS_DEVIER |=  (USBHS_DEVIER_DMA_1 << DmaEp);
}
  
 /**
 * \brief Disables interrupt for endpoint.
 * \param pUsbhs   Pointer to an USBHS instance.
 * \param IntType Int type
 */  

__STATIC_INLINE void USBHS_DisableInt(Usbhs *pUsbhs, uint32_t IntType)
{   
	pUsbhs->USBHS_DEVIDR |=  IntType;
}

 /**
 * \brief Disables interrupt for endpoint.
 * \param pUsbhs  Pointer to an USBHS instance.
 * \param Ep    Endpoint number
 */ 

__STATIC_INLINE void USBHS_DisableIntEP(Usbhs *pUsbhs, uint8_t Ep)
{   
	pUsbhs->USBHS_DEVIDR |=  (USBHS_DEVIDR_PEP_0 << Ep);    
}

 /**
 * \brief Disables DMA interrupt for endpoint.
 * \param pUsbhs  Pointer to an USBHS instance.
 * \param DmaEp Endpoint's DMA number
 */
__STATIC_INLINE void USBHS_DisableDMAIntEP(Usbhs *pUsbhs, uint8_t DmaEp)
{   
	assert(DmaEp< USBHSDEVDMA_NUMBER);
	pUsbhs->USBHS_DEVIDR |=  (USBHS_DEVIDR_DMA_1 << DmaEp);
}


 /**
 * \brief Enables or disables endpoint.
 * \param pUsbhs  Pointer to an USBHS instance.
 * \param Enable Enable/disable endpoint
 */

__STATIC_INLINE void USBHS_EnableEP(Usbhs *pUsbhs, uint8_t Ep, uint8_t Enable)
{
	if(Enable) {
		pUsbhs->USBHS_DEVEPT |= (USBHS_DEVEPT_EPEN0 << Ep);
	} else {
		pUsbhs->USBHS_DEVEPT &= ~(uint32_t)(USBHS_DEVEPT_EPEN0 << Ep);
	}
	
}


 /**
 * \brief Rests Endpoint
 * \param pUsbhs  Pointer to an USBHS instance.
 * \param Ep    Endpoint Number
 */

__STATIC_INLINE void USBHS_ResetEP(Usbhs *pUsbhs, uint8_t Ep)
{
	pUsbhs->USBHS_DEVEPT |=  (USBHS_DEVEPT_EPRST0 << Ep);
   //pUsbhs->USBHS_DEVEPT &=  ~(uint32_t)(USBHS_DEVEPT_EPRST0 << Ep);
}

 /**
 * \brief Checks if Endpoint is enable
 * \param pUsbhs  Pointer to an USBHS instance.
 * \param Ep    Endpoint Number
 */

__STATIC_INLINE uint32_t USBHS_IsEPEnabled(Usbhs *pUsbhs, uint8_t Ep)
{
	return (pUsbhs->USBHS_DEVEPT & (USBHS_DEVEPT_EPEN0 << Ep) );
}

 /**
 * \brief Get MicrFrame number
 * \param pUsbhs  Pointer to an USBHS instance.
 * \retruns Micro frame number
 */
__STATIC_INLINE uint8_t USBHS_GetMicroFrameNum(Usbhs *pUsbhs)
{
	return (pUsbhs->USBHS_DEVFNUM & USBHS_DEVFNUM_MFNUM_Msk);    
}


 /**
 * \brief Get Frame number
 * \param pUsbhs  Pointer to an USBHS instance.
 * \retruns frame number
 */
__STATIC_INLINE uint8_t USBHS_GetFrameNum(Usbhs *pUsbhs)
{
	return ( (pUsbhs->USBHS_DEVFNUM & USBHS_DEVFNUM_FNUM_Msk) 
			>> USBHS_DEVFNUM_FNUM_Pos); 
}

 /**
 * \brief Get Frame number CRC error
 * \param pUsbhs  Pointer to an USBHS instance.
 * \retruns Frame number error status
 */
__STATIC_INLINE uint8_t USBHS_GetFrameNumCrcErr(Usbhs *pUsbhs)
{
	return ( (pUsbhs->USBHS_DEVFNUM & USBHS_DEVFNUM_FNCERR) >> 15);
}

 /*-----------------------------------------
 * =========== USB Device's Endpoint functions ========
 *------------------------------------------*/

/**
 * Set Endpoints configuration
 * Bank size, type and direction
 */
__STATIC_INLINE void USBHS_ConfigureEPs(Usbhs *pUsbhs, const uint8_t Ep,
		const uint8_t Type, const uint8_t Dir, 
		const uint8_t Size, const uint8_t Bank)
{  
	
	pUsbhs->USBHS_DEVEPTCFG[Ep] |= 
		((Size << USBHS_DEVEPTCFG_EPSIZE_Pos) & USBHS_DEVEPTCFG_EPSIZE_Msk);
	pUsbhs->USBHS_DEVEPTCFG[Ep] |= 
		((Dir << 8 ) & USBHS_DEVEPTCFG_EPDIR);
	pUsbhs->USBHS_DEVEPTCFG[Ep] |= 
		(( (Type) << USBHS_DEVEPTCFG_EPTYPE_Pos) & USBHS_DEVEPTCFG_EPTYPE_Msk);
	pUsbhs->USBHS_DEVEPTCFG[Ep] |= 
		(( (Bank) << USBHS_DEVEPTCFG_EPBK_Pos) & USBHS_DEVEPTCFG_EPBK_Msk);
}


/**
 * Enable or disable Auto switch of banks
 */
__STATIC_INLINE void USBHS_AutoSwitchBankEnable(Usbhs *pUsbhs, uint8_t Ep, uint8_t Enable)
{
	if(Enable) {
		pUsbhs->USBHS_DEVEPTCFG[Ep] |=USBHS_DEVEPTCFG_AUTOSW;
	} else {
		pUsbhs->USBHS_DEVEPTCFG[Ep] &= ~((uint32_t)USBHS_DEVEPTCFG_AUTOSW);
	}
}


/**
 * Allocate Endpoint memory
 */
__STATIC_INLINE void USBHS_AllocateMemory(Usbhs *pUsbhs, uint8_t Ep)
{
	pUsbhs->USBHS_DEVEPTCFG[Ep] |=USBHS_DEVEPTCFG_ALLOC;
}


/**
 * Free allocated Endpoint memory
 */
__STATIC_INLINE void USBHS_FreeMemory(Usbhs *pUsbhs, uint8_t Ep)
{
	pUsbhs->USBHS_DEVEPTCFG[Ep] &= ~((uint32_t)USBHS_DEVEPTCFG_ALLOC);
}


/**
 * Get Endpoint configuration
 */
__STATIC_INLINE uint32_t USBHS_GetConfigureEPs(Usbhs *pUsbhs, uint8_t Ep,
												uint32_t IntType)
{  
	return ((pUsbhs->USBHS_DEVEPTCFG[Ep] ) & IntType);
}

/**
 * Get Endpoint Type
 */
__STATIC_INLINE uint8_t USBHS_GetEpType(Usbhs *pUsbhs, uint8_t Ep)
{  
	return ((pUsbhs->USBHS_DEVEPTCFG[Ep] & USBHS_DEVEPTCFG_EPTYPE_Msk) 
			>> USBHS_DEVEPTCFG_EPTYPE_Pos);
}

/**
 * Get Endpoint Size
 */
__STATIC_INLINE uint32_t USBHS_GetEpSize(Usbhs *pUsbhs, uint8_t Ep)
{  
	return ( 8 << ( (pUsbhs->USBHS_DEVEPTCFG[Ep] & USBHS_DEVEPTCFG_EPSIZE_Msk)
			>> USBHS_DEVEPTCFG_EPSIZE_Pos) );
}


/**
 * Sets ISO endpoint's Number of Transfer for High Speed
 */
__STATIC_INLINE void USBHS_SetIsoTrans(Usbhs *pUsbhs, uint8_t Ep, 
		uint8_t nbTrans)
{  
	pUsbhs->USBHS_DEVEPTCFG[Ep] |= USBHS_DEVEPTCFG_NBTRANS(nbTrans) ;
}

/**
 * Check for interrupt types enabled for a given endpoint
 */
__STATIC_INLINE uint32_t USBHS_IsEpIntEnable(Usbhs *pUsbhs, uint8_t Ep,
		uint32_t EpIntType)
{  
	return (pUsbhs->USBHS_DEVEPTIMR[Ep] & EpIntType);
}


/**
 * Enables an interrupt type for a given endpoint
 */
__STATIC_INLINE void USBHS_EnableEPIntType(Usbhs *pUsbhs, uint8_t Ep, 
		uint32_t EpInt)
{
	pUsbhs->USBHS_DEVEPTIER[Ep] |=  EpInt;
}

/**
 * Enables an interrupt type for a given endpoint
 */
__STATIC_INLINE uint32_t USBHS_IsBankKilled(Usbhs *pUsbhs, uint8_t Ep)
{   
	return (pUsbhs->USBHS_DEVEPTIMR[Ep] & USBHS_DEVEPTIMR_KILLBK);
}

/**
 * Enables an interrupt type for a given endpoint
 */
__STATIC_INLINE void USBHS_KillBank(Usbhs *pUsbhs, uint8_t Ep)
{
	pUsbhs->USBHS_DEVEPTIER[Ep] =  USBHS_DEVEPTIER_KILLBKS;
}
/**
 * Disables an interrupt type for a given endpoint
 */
__STATIC_INLINE void USBHS_DisableEPIntType(Usbhs *pUsbhs, uint8_t Ep, 
		uint32_t EpInt)
{
	pUsbhs->USBHS_DEVEPTIDR[Ep] |=  EpInt;
}

/**
 * Clears register/acknowledge for a given endpoint
 */
__STATIC_INLINE void USBHS_AckEpInterrupt(Usbhs *pUsbhs, uint8_t Ep, uint32_t EpInt)
{
	pUsbhs->USBHS_DEVEPTICR[Ep] |=  EpInt;
}

/**
 * Sets/Raise register for a given endpoint
 */
__STATIC_INLINE void USBHS_RaiseEPInt(Usbhs *pUsbhs, uint8_t Ep, uint32_t EpInt)
{   
	pUsbhs->USBHS_DEVEPTIFR[Ep] |=  EpInt;    
}

/**
 * Gets interrupt status for a given EP
 */
__STATIC_INLINE uint32_t USBHS_ReadEPStatus(Usbhs *pUsbhs, uint8_t Ep, 
		uint32_t EpInt)
{
	return (pUsbhs->USBHS_DEVEPTISR[Ep] & EpInt);
}

/**
 * Check if given endpoint's bank is free
 */
__STATIC_INLINE uint8_t USBHS_IsBankFree(Usbhs *pUsbhs, uint8_t Ep)
{
	if( (pUsbhs->USBHS_DEVEPTISR[Ep] & USBHS_DEVEPTISR_NBUSYBK_Msk)) {
		return false;
	} else {
		return true;
	}
}

/**
 * Read endpoint's bank number in use
 */
__STATIC_INLINE uint8_t USBHS_NumOfBanksInUse(Usbhs *pUsbhs, uint8_t Ep)
{
	return ( (pUsbhs->USBHS_DEVEPTISR[Ep] & USBHS_DEVEPTISR_NBUSYBK_Msk) 
		>> USBHS_DEVEPTISR_NBUSYBK_Pos);
}


/**
 * Read endpoint's bank number in use
 */
__STATIC_INLINE uint16_t USBHS_ByteCount(Usbhs *pUsbhs, uint8_t Ep)
{
	return (uint16_t)( (pUsbhs->USBHS_DEVEPTISR[Ep] & USBHS_DEVEPTISR_BYCT_Msk)
		>> USBHS_DEVEPTISR_BYCT_Pos);
}

 /*--------------------------------------------------------
 * =========== USB Device's Ep's DMA functions =========
 *---------------------------------------------------------*/

 /**
 * \brief Sets DMA next descriptor address
 * \param pUsbDma  USBHS device DMA instance
 * \param Desc NDA address
 */ 
__STATIC_INLINE void USBHS_SetDmaNDA(UsbhsDevdma *pUsbDma, uint32_t Desc)
{
	pUsbDma->USBHS_DEVDMANXTDSC = Desc;
}

 /**
 * \brief Gets DMA next descriptor address
 * \param pUsbDma  USBHS device DMA instance
 * \return Next DMA descriptor
 */ 
__STATIC_INLINE uint32_t USBHS_GetDmaNDA(UsbhsDevdma *pUsbDma)
{
	return (pUsbDma->USBHS_DEVDMANXTDSC);
}

 /**
 * \brief Sets USBHS's DMA Buffer addresse
 * \param pUsbDma  USBHS device DMA instance
 * \param Addr  DMA's buffer Addrs
 */ 
__STATIC_INLINE void USBHS_SetDmaBuffAdd(UsbhsDevdma *pUsbDma, uint32_t Addr)
{
	pUsbDma->USBHS_DEVDMAADDRESS = Addr;
}


 /**
 * \brief Gets USBHS's DMA Buffer addresse
 * \param pUsbDma  USBHS device DMA instance
 * \return DMA addrs
 */ 
__STATIC_INLINE uint32_t USBHS_GetDmaBuffAdd(UsbhsDevdma *pUsbDma)
{
	return (pUsbDma->USBHS_DEVDMAADDRESS);
}

 /**
 * \brief Setup the USBHS DMA
 * \param pUsbDma  USBHS device DMA instance
 * \param Cfg  DMA's configuration
 */ 
__STATIC_INLINE void USBHS_ConfigureDma(UsbhsDevdma *pUsbDma, uint32_t Cfg)
{
	pUsbDma->USBHS_DEVDMACONTROL |= Cfg;
}

 /**
 * \brief Get DMA configuration
 * \param pUsbDma  USBHS device DMA instance
 * \return DMA control setup
 */ 
__STATIC_INLINE uint32_t USBHS_GetDmaConfiguration(UsbhsDevdma *pUsbDma)
{
	return (pUsbDma->USBHS_DEVDMACONTROL);
}


 /**
 * \brief Set DMA status
 * \param pUsbDma  USBHS device DMA instance
 * \Status Set DMA status
 */ 
__STATIC_INLINE void USBHS_SetDmaStatus(UsbhsDevdma *pUsbDma, uint32_t Status)
{
	pUsbDma->USBHS_DEVDMASTATUS = Status;
}


 /**
 * \brief Get Dma Status
 * \param pUsbDma  USBHS device DMA instance
 * \return Dma status
 */ 
__STATIC_INLINE uint32_t USBHS_GetDmaStatus(UsbhsDevdma *pUsbDma)
{
	return (pUsbDma->USBHS_DEVDMASTATUS);
}


 /**
 * \brief Get DMA buffer's count
 * \param pUsbDma  USBHS device DMA instance
 * \return Buffer count
 */ 
__STATIC_INLINE uint16_t USBHS_GetDmaBuffCount(UsbhsDevdma *pUsbDma)
{
	return ( (pUsbDma->USBHS_DEVDMASTATUS & USBHS_DEVDMASTATUS_BUFF_COUNT_Msk)
		>> USBHS_DEVDMASTATUS_BUFF_COUNT_Pos);
}


 /*--------------------------------------------------------
 * =========== USB Host Functions  ========================
 *---------------------------------------------------------*/

/** Number of USB endpoints */
#define CHIP_USB_NUMPIPE            10
/** Number of USB endpoints */
#define CHIP_USB_DMA_NUMPIPE        7

/** Endpoints max paxcket size */
#define CHIP_USB_PIPE_MAXPACKETSIZE(ep) \
   ((ep == 0) ? 64 : 1024)

/** Endpoints Number of Bank */
#define CHIP_USB_PIPE_BANKS(ep)                 ((ep==0)?1:((ep<=2)?3:2))
     
     
#define CHIP_USB_PIPE_HBW(ep)                   ((((ep)>=1) &&((ep)<=2))?true:false)

/** Endpoints DMA support */
#define CHIP_USB_PIPE_DMA(ep)                   ((((ep)>=1)&&((ep)<=7))?true:false)

 /**
 * \brief Sets USB host's speed to Normal , it sets to HS from FS
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_SetHostHighSpeed(Usbhs *pUsbhs)
{
   pUsbhs->USBHS_HSTCTRL |= USBHS_HSTCTRL_SPDCONF_NORMAL;
}

 /**
 * \brief Sets USB host's speed to Low speed
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_SetHostLowSpeed(Usbhs *pUsbhs)
{
   pUsbhs->USBHS_HSTCTRL |= USBHS_HSTCTRL_SPDCONF_LOW_POWER;
}

 /**
 * \brief Sets USB host's speed to forced Full speed
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_SetHostForcedFullSpeed(Usbhs *pUsbhs)
{
   pUsbhs->USBHS_HSTCTRL |= USBHS_HSTCTRL_SPDCONF_FORCED_FS;
}

 /**
 * \brief Sets USB host sends reste signal on USB Bus
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_Reset(void)
{
   USBHS->USBHS_HSTCTRL |= USBHS_HSTCTRL_RESET;
}

 /**
 * \brief Sets USB host sends reste signal on USB Bus
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_StopReset(void)
{
   USBHS->USBHS_HSTCTRL &= ~USBHS_HSTCTRL_RESET;
}

 /**
 * \brief Sets USB host send Resume on USB bus
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_Resume(void)
{
   USBHS->USBHS_HSTCTRL |= USBHS_HSTCTRL_RESUME;
}

 /**
 * \brief Sets USB host Enable the Generation of  Start of Frame
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_EnableSOF(Usbhs *pUsbhs)
{
   pUsbhs->USBHS_HSTCTRL |= USBHS_HSTCTRL_SOFE;
}

 /**
 * \brief Sets USB host Enable the Generation of  Start of Frame
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE uint8_t USBHS_IsEnableSOF(Usbhs *pUsbhs)
{
    return (pUsbhs->USBHS_HSTCTRL & USBHS_HSTCTRL_SOFE) >> 8;
}
 /**
 * \brief Sets USB host disable the Generation of  Start of Frame
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_DisableSOF(void)
{
   USBHS->USBHS_HSTCTRL &= ~USBHS_HSTCTRL_SOFE;
}

 /**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE uint32_t USBHS_GetHostStatus(Usbhs *pUsbhs, uint8_t IntType)
{
   return (pUsbhs->USBHS_HSTISR & IntType);
}


/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE uint32_t USBHS_GetHostPipeStatus(Usbhs *pUsbhs, uint8_t PipeInt)
{
   assert( PipeInt < CHIP_USB_NUMPIPE);
   return (pUsbhs->USBHS_HSTISR & ( USBHS_HSTISR_PEP_0 << PipeInt) );
}


/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE uint32_t USBHS_GetHostDmaPipeStatus(Usbhs *pUsbhs, uint8_t PipeInt)
{
    assert( PipeInt);
    assert( PipeInt < CHIP_USB_DMA_NUMPIPE);
    return (pUsbhs->USBHS_HSTISR & ( USBHS_HSTISR_DMA_1 << PipeInt) );
}

/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_ClearHostStatus(Usbhs *pUsbhs, uint32_t IntType)
{
    pUsbhs->USBHS_HSTICR = IntType;
}

/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_SetHostStatus(Usbhs *pUsbhs, uint32_t IntType)
{
    pUsbhs->USBHS_HSTIFR = IntType;
}

/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_SetHostDmaStatus(Usbhs *pUsbhs, uint8_t PipeInt)
{
    assert( PipeInt);
    assert( PipeInt < CHIP_USB_DMA_NUMPIPE);
    pUsbhs->USBHS_HSTIFR =  (USBHS_HSTIFR_DMA_1 << PipeInt) ;
}

/*** Interrupt Mask ****/
/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE uint8_t USBHS_IsHostIntEnable(Usbhs *pUsbhs, uint8_t IntType)
{
    return (pUsbhs->USBHS_HSTIMR & IntType) ;
}

/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE uint32_t USBHS_IsHostPipeIntEnable(Usbhs *pUsbhs, uint8_t PipeInt)
{
    assert( PipeInt < CHIP_USB_NUMPIPE);
    return ( pUsbhs->USBHS_HSTIMR & (USBHS_HSTIMR_PEP_0 << PipeInt) );
}

/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE uint32_t USBHS_IsHostDmaIntEnable(Usbhs *pUsbhs, uint8_t PipeInt)
{
    assert( PipeInt);
    assert( PipeInt < CHIP_USB_DMA_NUMPIPE);
    return ( pUsbhs->USBHS_HSTIMR & (USBHS_HSTIMR_DMA_1 << PipeInt) );
}

/*** Interrupt Disable ****/
/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_HostIntDisable(Usbhs *pUsbhs, uint32_t IntType)
{
    pUsbhs->USBHS_HSTIDR = IntType ;
}

/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_HostPipeIntDisable(Usbhs *pUsbhs, uint8_t PipeInt)
{
    assert( PipeInt < CHIP_USB_NUMPIPE);
    pUsbhs->USBHS_HSTIDR  = (USBHS_HSTIDR_PEP_0 << PipeInt);
}

/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_HostDmaIntDisable(Usbhs *pUsbhs, uint8_t PipeInt)
{
    assert( PipeInt);
    assert( PipeInt < CHIP_USB_DMA_NUMPIPE);
    pUsbhs->USBHS_HSTIDR = (USBHS_HSTIDR_DMA_1 << PipeInt) ;
}

/*** Interrupt Enable ****/

/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_HostIntEnable(Usbhs *pUsbhs, uint8_t IntType)
{
    pUsbhs->USBHS_HSTIER = IntType ;
}

/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_HostPipeIntEnable(Usbhs *pUsbhs, uint8_t PipeInt)
{
     assert( PipeInt < CHIP_USB_NUMPIPE);
     pUsbhs->USBHS_HSTIER =(USBHS_HSTIER_PEP_0 << PipeInt) ;
}

/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_HostDmaIntEnable(Usbhs *pUsbhs, uint8_t PipeInt)
{
    assert( PipeInt < CHIP_USB_DMA_NUMPIPE);
    pUsbhs->USBHS_HSTIER |= (USBHS_HSTIER_DMA_1 << PipeInt);
}

/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE uint16_t USBHS_HostGetSOF(void)
{
   return ( (USBHS->USBHS_HSTFNUM & USBHS_HSTFNUM_FNUM_Msk) >> USBHS_HSTFNUM_FNUM_Pos);
}

/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE uint16_t USBHS_HostGetMSOF(void)
{
   return ( (USBHS->USBHS_HSTFNUM & USBHS_HSTFNUM_MFNUM_Msk) >> USBHS_HSTFNUM_MFNUM_Pos);
}

__STATIC_INLINE void USBHS_HostSetAddr(Usbhs *pUsbhs, uint8_t Pipe, uint8_t Addr)
{
  assert( Pipe < CHIP_USB_NUMPIPE);
  if (Pipe <4)
  {
    pUsbhs->USBHS_HSTADDR1 |= (Addr << (8*Pipe));
  }
  else if( (Pipe <8) && (Pipe >=4))
  {
    pUsbhs->USBHS_HSTADDR2 |= (Addr << (8* (Pipe -4)));
  }
  else
  {
    pUsbhs->USBHS_HSTADDR3 |= (Addr << (8*(Pipe -8)));
  }
  
}

__STATIC_INLINE uint8_t USBHS_HostGetAddr(Usbhs *pUsbhs, uint8_t Pipe)
{
  assert( Pipe < CHIP_USB_NUMPIPE);
  if (Pipe <4)
  {
    return ( pUsbhs->USBHS_HSTADDR1 >>  (8*Pipe)) ;
  }
  else if( (Pipe <8) && (Pipe >=4))
  {
    return (pUsbhs->USBHS_HSTADDR2  >>  (8*(Pipe -4)));
  }
  else
  {
    return (pUsbhs->USBHS_HSTADDR3  >> (8*(Pipe -8)));
  }
  
}

/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_HostPipeEnable(Usbhs *pUsbhs, uint8_t Pipe)
{
    assert( Pipe < CHIP_USB_NUMPIPE);
    pUsbhs->USBHS_HSTPIP |= (USBHS_HSTPIP_PEN0 << Pipe);
}

/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_HostPipeDisable(Usbhs *pUsbhs, uint8_t Pipe)
{
    assert( Pipe < CHIP_USB_NUMPIPE);
    pUsbhs->USBHS_HSTPIP &= ~(USBHS_HSTPIP_PEN0 << Pipe);
}

/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE uint32_t USBHS_IsHostPipeEnable(Usbhs *pUsbhs, uint8_t Pipe)
{
    assert( Pipe < CHIP_USB_NUMPIPE);
    return (pUsbhs->USBHS_HSTPIP &(USBHS_HSTPIP_PEN0 << Pipe));
}
/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_HostPipeReset(Usbhs *pUsbhs, uint8_t Pipe)
{
    assert( Pipe < CHIP_USB_NUMPIPE);
    pUsbhs->USBHS_HSTPIP |= (USBHS_HSTPIP_PRST0 << Pipe);
    pUsbhs->USBHS_HSTPIP &= ~(USBHS_HSTPIP_PRST0 << Pipe);
}

/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_HostConfigure(Usbhs *pUsbhs, uint8_t Pipe, uint32_t pipeBank, uint8_t pipeSize, uint32_t pipeType, uint32_t pipeToken, uint8_t pipeEpNum, uint8_t PipeIntFreq)
{
    assert( Pipe < CHIP_USB_NUMPIPE);
    pUsbhs->USBHS_HSTPIPCFG[Pipe] |= ( pipeBank | pipeToken | USBHS_HSTPIPCFG_PSIZE(pipeSize) | pipeType | USBHS_HSTPIPCFG_PEPNUM(pipeEpNum) |  USBHS_HSTPIPCFG_INTFRQ(PipeIntFreq));
}

/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_HostAllocMem(Usbhs *pUsbhs, uint8_t Pipe)
{
  pUsbhs->USBHS_HSTPIPCFG[Pipe] |= USBHS_HSTPIPCFG_ALLOC;
  
}

/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_HostFreeMem(Usbhs *pUsbhs, uint8_t Pipe)
{
  pUsbhs->USBHS_HSTPIPCFG[Pipe] &= ~USBHS_HSTPIPCFG_ALLOC;
  
}


/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE uint16_t USBHS_HostGetSize(Usbhs *pUsbhs, uint8_t Pipe)
{
    return (8 << ((pUsbhs->USBHS_HSTPIPCFG[Pipe] & USBHS_HSTPIPCFG_PSIZE_Msk) >> USBHS_HSTPIPCFG_PSIZE_Pos)) ;
  
}

     /**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_HostSetToken(Usbhs *pUsbhs, uint8_t Pipe, uint32_t Token)
{
    pUsbhs->USBHS_HSTPIPCFG[Pipe] &= ~USBHS_HSTPIPCFG_PTOKEN_Msk;
    pUsbhs->USBHS_HSTPIPCFG[Pipe] |= Token;
  
}


/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE uint32_t USBHS_HostGetToken(Usbhs *pUsbhs, uint8_t Pipe)
{
    return (pUsbhs->USBHS_HSTPIPCFG[Pipe] & USBHS_HSTPIPCFG_PTOKEN_Msk) ;
  
}


/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_HostSetPipeType(Usbhs *pUsbhs, uint8_t Pipe, uint8_t PipeType)
{
    pUsbhs->USBHS_HSTPIPCFG[Pipe] &= ~USBHS_HSTPIPCFG_PTYPE_Msk ;
    pUsbhs->USBHS_HSTPIPCFG[Pipe] |= PipeType ;
  
}

/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE uint32_t USBHS_HostGetPipeType(Usbhs *pUsbhs, uint8_t Pipe )
{
    return (pUsbhs->USBHS_HSTPIPCFG[Pipe] & USBHS_HSTPIPCFG_PTYPE_Msk) ;
  
}

__STATIC_INLINE uint8_t USBHS_GetPipeEpAddr(Usbhs *pUsbhs, uint8_t Pipe)
{
  
   if( USBHS_HostGetToken(USBHS, Pipe) == USBHS_HSTPIPCFG_PTOKEN_IN)
   {
     return ( ((pUsbhs->USBHS_HSTPIPCFG[Pipe] & USBHS_HSTPIPCFG_PEPNUM_Msk) >> USBHS_HSTPIPCFG_PEPNUM_Pos) | 0x80);
   }
   else
   {
     return ( ((pUsbhs->USBHS_HSTPIPCFG[Pipe] & USBHS_HSTPIPCFG_PEPNUM_Msk) >> USBHS_HSTPIPCFG_PEPNUM_Pos) | 0x00) ;
   }  
}



/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_HostEnableAutoSw(Usbhs *pUsbhs, uint8_t Pipe)
{
  pUsbhs->USBHS_HSTPIPCFG[Pipe] |= USBHS_HSTPIPCFG_AUTOSW;  
}

/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_HostDisableAutoSw(Usbhs *pUsbhs, uint8_t Pipe)
{
  pUsbhs->USBHS_HSTPIPCFG[Pipe] &= ~USBHS_HSTPIPCFG_AUTOSW;  
}

/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_HostSetIntFreq(Usbhs *pUsbhs, uint8_t Pipe, uint8_t Freq)
{
  pUsbhs->USBHS_HSTPIPCFG[Pipe] |= USBHS_HSTPIPCFG_BINTERVAL(Freq);  
}


/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_HostEnablePing(Usbhs *pUsbhs, uint8_t Pipe)
{
  pUsbhs->USBHS_HSTPIPCFG[Pipe] |= USBHS_HSTPIPCFG_PINGEN;  
}


/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE uint8_t USBHS_HostGetDataTogSeq(Usbhs *pUsbhs, uint8_t Pipe)
{
    return ( (pUsbhs->USBHS_HSTPIPISR[Pipe] & USBHS_HSTPIPISR_DTSEQ_Msk) >> USBHS_HSTPIPISR_DTSEQ_Pos ) ;  
}


/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE uint8_t USBHS_HostGetNumOfBusyBank(Usbhs *pUsbhs, uint8_t Pipe)
{
    return ( (pUsbhs->USBHS_HSTPIPISR[Pipe] & USBHS_HSTPIPISR_NBUSYBK_Msk) >> USBHS_HSTPIPISR_NBUSYBK_Pos ) ;  
}


/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE uint8_t USBHS_HostGetCurrentBank(Usbhs *pUsbhs, uint8_t Pipe)
{
    return ( (pUsbhs->USBHS_HSTPIPISR[Pipe] & USBHS_HSTPIPISR_CURRBK_Msk) >> USBHS_HSTPIPISR_CURRBK_Pos ) ;  
}


/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE uint8_t USBHS_HostGetPipeByteCount(Usbhs *pUsbhs, uint8_t Pipe)
{
    return ( (pUsbhs->USBHS_HSTPIPISR[Pipe] & USBHS_HSTPIPISR_PBYCT_Msk) >> USBHS_HSTPIPISR_PBYCT_Pos ) ;  
}

/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE uint32_t USBHS_IsHostConfigOk(Usbhs *pUsbhs, uint8_t Pipe)
{
    return (pUsbhs->USBHS_HSTPIPISR[Pipe] & USBHS_DEVEPTISR_CFGOK);  
}

/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE uint32_t USBHS_HostGetIntTypeStatus(Usbhs *pUsbhs, uint8_t Pipe, uint32_t intType)
{
    return (pUsbhs->USBHS_HSTPIPISR[Pipe] & intType);  
}

/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_HostAckPipeIntType(Usbhs *pUsbhs, uint8_t Pipe, uint32_t intType)
{
    pUsbhs->USBHS_HSTPIPICR[Pipe] = intType;  
}

/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_HostSetPipeIntType(Usbhs *pUsbhs, uint8_t Pipe, uint32_t intType)
{
    pUsbhs->USBHS_HSTPIPIFR[Pipe] = intType;  
}

/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE uint32_t USBHS_IsHostPipeIntTypeEnable(Usbhs *pUsbhs, uint8_t Pipe, uint32_t intType)
{
    return ( pUsbhs->USBHS_HSTPIPIMR[Pipe] & intType);  
}

/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_HostDisablePipeIntType(Usbhs *pUsbhs, uint8_t Pipe, uint32_t intType)
{
    pUsbhs->USBHS_HSTPIPIDR[Pipe] = intType;  
}

/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_HostEnablePipeIntType(Usbhs *pUsbhs, uint8_t Pipe, uint32_t intType)
{
    pUsbhs->USBHS_HSTPIPIER[Pipe] = intType;  
}

/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_HostEnableInReq(Usbhs *pUsbhs, uint8_t Pipe)
{
    pUsbhs->USBHS_HSTPIPINRQ[Pipe] |= USBHS_HSTPIPINRQ_INMODE;  
}

/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_HostDisableInReq(Usbhs *pUsbhs, uint8_t Pipe)
{
    pUsbhs->USBHS_HSTPIPINRQ[Pipe] &= ~USBHS_HSTPIPINRQ_INMODE;  
}

/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE uint8_t USBHS_IsHostInReqEnable(Usbhs *pUsbhs, uint8_t Pipe)
{
    return ((pUsbhs->USBHS_HSTPIPINRQ[Pipe] & USBHS_HSTPIPINRQ_INMODE) >> 8); 
}

/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_HostInReq(Usbhs *pUsbhs, uint8_t Pipe, uint8_t InReq)
{
    pUsbhs->USBHS_HSTPIPINRQ[Pipe] = USBHS_HSTPIPINRQ_INRQ(InReq-1);  
}


/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_HostSetErr(Usbhs *pUsbhs, uint8_t Pipe, uint8_t Err)
{
    pUsbhs->USBHS_HSTPIPERR[Pipe] |= Err;  
}

/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE uint8_t USBHS_HostGetErr(Usbhs *pUsbhs, uint8_t Pipe, uint8_t Err)
{
    return (pUsbhs->USBHS_HSTPIPERR[Pipe] & Err);  
}


/**
 * \brief Gets USB host interrupt status
 * \param pUsbhs  USBHS host instance
 */ 
__STATIC_INLINE void USBHS_HostClearErr(Usbhs *pUsbhs, uint8_t Pipe, uint8_t Err)
{
    pUsbhs->USBHS_HSTPIPERR[Pipe] = Err;  
}


__STATIC_INLINE  uint8_t USBHS_GetInterruptPipeNum(void)
{
	uint32_t status = USBHS->USBHS_HSTISR;
	uint32_t mask = USBHS->USBHS_HSTIMR;
	return ctz(((status & mask) >> 8) | (1 << USBHS_EPT_NUM));
}

static inline uint8_t USBHS_GetInterruptPipeDmaNum(void)
{
	uint32_t status = USBHS->USBHS_HSTISR;
	uint32_t mask = USBHS->USBHS_HSTIMR;
	return (ctz(((status & mask) >> 25) | (1 << (USBHS_EPT_NUM-1))) + 1);
}
 /*--------------------------------------------------------
 * =========== USB Host's pipe DMA functions =========
 *---------------------------------------------------------*/

 /**
 * \brief Sets DMA next descriptor address
 * \param pUsbDma  USBHS device DMA instance
 * \param Desc NDA addrs
 */ 
__STATIC_INLINE void USBHS_SetHostDmaNDA(UsbhsHstdma *pUsbDma, uint32_t Desc)
{
  pUsbDma->USBHS_HSTDMANXTDSC = Desc;
}

 /**
 * \brief Gets DMA next descriptor address
 * \param pUsbDma  USBHS device DMA instance
 * \return Next DMA descriptor
 */ 
__STATIC_INLINE uint32_t USBHS_GetHostDmaNDA(UsbhsHstdma *pUsbDma)
{
   return (pUsbDma->USBHS_HSTDMANXTDSC);
}

 /**
 * \brief Sets USBHS's DMA Buffer addresse
 * \param pUsbDma  USBHS device DMA instance
 * \param Addr  DMA's buffer Addrs
 */ 
__STATIC_INLINE void USBHS_SetHostDmaBuffAdd(UsbhsHstdma *pUsbDma, uint32_t Addr)
{
  pUsbDma->USBHS_HSTDMAADDRESS = Addr;
}


 /**
 * \brief Gets USBHS's DMA Buffer addresse
 * \param pUsbDma  USBHS device DMA instance
 * \return DMA addrs
 */ 
__STATIC_INLINE uint32_t USBHS_GetHostDmaBuffAdd(UsbhsHstdma *pUsbDma)
{
   return (pUsbDma->USBHS_HSTDMAADDRESS);
}

 /**
 * \brief Setup the USBHS DMA
 * \param pUsbDma  USBHS device DMA instance
 * \param Cfg  DMA's configuration
 */ 
__STATIC_INLINE void USBHS_HostConfigureDma(UsbhsHstdma *pUsbDma, uint32_t Cfg)
{
  pUsbDma->USBHS_HSTDMACONTROL |= Cfg;
}

 /**
 * \brief Get DMA configuration
 * \param pUsbDma  USBHS device DMA instance
 * \return DMA control setup
 */ 
__STATIC_INLINE uint32_t USBHS_GetHostDmaConfiguration(UsbhsHstdma *pUsbDma)
{
   return (pUsbDma->USBHS_HSTDMACONTROL);
}


 /**
 * \brief Set DMA status
 * \param pUsbDma  USBHS device DMA instance
 * \Status Set DMA status
 */ 
__STATIC_INLINE void USBHS_SetHostPipeDmaStatus(UsbhsHstdma *pUsbDma, uint32_t Status)
{
  pUsbDma->USBHS_HSTDMASTATUS = Status;
}


 /**
 * \brief Get Dma Status
 * \param pUsbDma  USBHS device DMA instance
 * \return Dma status
 */ 
__STATIC_INLINE uint32_t USBHS_GetHostPipeDmaStatus(UsbhsHstdma *pUsbDma)
{
   return (pUsbDma->USBHS_HSTDMASTATUS);
}

/**@}*/
#endif /* #ifndef USBHS_H */
