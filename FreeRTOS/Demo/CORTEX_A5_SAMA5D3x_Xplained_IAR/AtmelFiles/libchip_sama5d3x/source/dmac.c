/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2011, Atmel Corporation
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

/**
 * \file
 *
 * Implementation of DMA controller (DMAC).
 *
 */
 
/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

#include <stdint.h>
#include <assert.h>
/** \addtogroup dmac_functions DMAC Functions
 *@{
 */

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Configures an DMAC peripheral with modified round robin arbiter.
 *
 * \param pDmac  Pointer to the DMAC peripheral.
 */
void DMAC_Modified_Arbiter( Dmac *pDmac)
{
    assert(pDmac);
    pDmac->DMAC_GCFG = DMAC_GCFG_ARB_CFG ;
}

/**
 * \brief Enables a DMAC peripheral.
 *
 * \param pDmac  Pointer to the DMAC peripheral.
 */
void DMAC_Enable( Dmac *pDmac )
{
    assert(pDmac);
    pDmac->DMAC_EN = DMAC_EN_ENABLE;
}

/**
 * \brief Disables a DMAC peripheral.
 *
 * \param pDmac Pointer to the DMAC peripheral .
 */
void DMAC_Disable( Dmac *pDmac )
{
    assert(pDmac);
    pDmac->DMAC_EN = ~(uint32_t)DMAC_EN_ENABLE;
}

/**
 * \brief Enables DMAC interrupt.
 *
 * \param pDmac Pointer to the DMAC peripheral.
 * \param dwInteruptMask IT to be enabled.
 */
void DMAC_EnableIt (Dmac *pDmac, uint32_t dwInteruptMask )
{
    assert(pDmac);
    pDmac->DMAC_EBCIER = dwInteruptMask;
}

/**
 * \brief Disables DMAC interrupt
 *
 * \param pDmac Pointer to the DMAC peripheral.
 * \param dwInteruptMask IT to be enabled
 */
void DMAC_DisableIt (Dmac *pDmac, uint32_t dwInteruptMask )
{
    assert(pDmac);
    pDmac->DMAC_EBCIDR = dwInteruptMask;
}

/**
 * \brief Get DMAC Interrupt Mask Status.
 *
 * \param pDmac Pointer to the DMAC peripheral.
 * \return DMAC Error, buffer transfer and chained buffer
 *  transfer interrupt mask register value.
 */
uint32_t DMAC_GetInterruptMask( Dmac *pDmac )
{
    assert(pDmac);
    return (pDmac->DMAC_EBCIMR);
}

/**
 * \brief Get DMAC Error, buffer transfer and chained buffer
 *  transfer status register.
 *
 * \param pDmac Pointer to the DMAC peripheral.
 * \return DMAC Error, buffer transfer and chained buffer
 *  transfer status register.
 */
uint32_t DMAC_GetStatus( Dmac *pDmac )
{
    assert(pDmac);
    return (pDmac->DMAC_EBCISR);
}

/**
 * \brief Get DMAC Error, buffer transfer and chained buffer
 *  transfer status register of the given DMAC peripheral, but
 *  masking interrupt sources which are not currently enabled.
 *
 * \param pDmac Pointer to the DMAC peripheral.
 * \return DMAC Error, buffer transfer and chained buffer
 *  transfer status register.
 */
uint32_t DMAC_GetMaskedStatus( Dmac *pDmac )
{
    uint32_t _dwStatus;
    assert(pDmac);
    _dwStatus = pDmac->DMAC_EBCISR;
    _dwStatus &= pDmac->DMAC_EBCIMR;
    return _dwStatus;
}

/**
 * \brief enables the relevant channel of given DMAC.
 *
 * \param pDmac Pointer to the DMAC peripheral.
 * \param channel Particular channel number.
 */
void DMAC_EnableChannel( Dmac *pDmac, uint8_t channel )
{
    assert(pDmac);
    assert(channel < DMAC_CHANNEL_NUM);
    pDmac->DMAC_CHER |= DMAC_CHER_ENA0 << channel;
}

/**
 * \brief enables the relevant channels of given DMAC.
 *
 * \param pDmac Pointer to the DMAC peripheral.
 * \param bmChannels Channels bitmap.
 */
void DMAC_EnableChannels( Dmac *pDmac, uint8_t bmChannels )
{
    assert(pDmac);
    pDmac->DMAC_CHER = bmChannels;
}

/**
 * \brief Disables the relevant channel of given DMAC.
 *
 * \param pDmac Pointer to the DMAC peripheral.
 * \param channel Particular channel number.
 */
void DMAC_DisableChannel( Dmac *pDmac, uint8_t channel )
{
    assert(pDmac);
    assert(channel < DMAC_CHANNEL_NUM);
    pDmac->DMAC_CHDR |= DMAC_CHDR_DIS0 << channel;
}

/**
 * \brief Disables the relevant channels of given DMAC.
 *
 * \param pDmac Pointer to the DMAC peripheral.
 * \param bmChannels Channels bitmap.
 */
void DMAC_DisableChannels( Dmac *pDmac, uint8_t bmChannels )
{
    assert(pDmac);
    pDmac->DMAC_CHDR = bmChannels;
}

/**
 * \brief freezes the relevant channel of given DMAC.
 *
 * \param pDmac Pointer to the DMAC peripheral.
 * \param channel Particular channel number.
 */
void DMAC_SuspendChannel( Dmac *pDmac, uint8_t channel )
{
    assert(pDmac);
    assert(channel < DMAC_CHANNEL_NUM);
    pDmac->DMAC_CHER |= DMAC_CHER_SUSP0 << channel;
}

/**
 * \brief resumes the current channel from an automatic
 * stall state of given DMAC.
 *
 * \param pDmac Pointer to the DMAC peripheral.
 * \param channel Particular channel number.
 */
void DMAC_KeepChannel( Dmac *pDmac, uint8_t channel )
{
    assert(pDmac);
    assert(channel < DMAC_CHANNEL_NUM);
    pDmac->DMAC_CHER |= DMAC_CHER_KEEP0 << channel;
}

/**
 * \brief resume the channel transfer restoring its context.
 *
 * \param pDmac Pointer to the DMAC peripheral.
 * \param channel Particular channel number.
 */
void DMAC_RestoreChannel( Dmac *pDmac, uint8_t channel )
{
    assert(pDmac);
    assert(channel < DMAC_CHANNEL_NUM);
    pDmac->DMAC_CHDR |= DMAC_CHDR_RES0 << channel;
}

/**
 * \brief Get DMAC channel handler Status.
 *
 * \param pDmac Pointer to the DMAC peripheral.
 * \return DMAC channel handler status register.
 */
uint32_t DMAC_GetChannelStatus( Dmac *pDmac )
{
    assert(pDmac);
    return (pDmac->DMAC_CHSR);
}

/**
 * \brief Set DMAC source address in a DMAC channel.
 *
 * \param pDmac Pointer to the DMAC peripheral.
 * \param channel Particular channel number.
 * \param saddr sources address.
 * \note This register must be aligned with the source transfer width.
 */
void DMAC_SetSourceAddr( Dmac *pDmac,
                         uint8_t channel,
                         uint32_t saddr )
{
    assert(pDmac);
    assert(channel < DMAC_CHANNEL_NUM);
    pDmac->DMAC_CH_NUM[channel].DMAC_SADDR = saddr;
}

/**
 * \brief Return DMAC source address of a DMAC channel.
 *
 * \param pDmac Pointer to the DMAC peripheral.
 * \param channel Particular channel number.
 */
uint32_t DMAC_GetSourceAddr( Dmac *pDmac,
                             uint8_t channel )
{
    assert(pDmac);
    assert(channel < DMAC_CHANNEL_NUM);
    return pDmac->DMAC_CH_NUM[channel].DMAC_SADDR;
}

/**
 * \brief Set DMAC destination address in a DMAC channel.
 *
 * \param pDmac Pointer to the DMAC peripheral.
 * \param channel Particular channel number.
 * \param daddr sources address.
 * \note This register must be aligned with the source transfer width.
 */
void DMAC_SetDestinationAddr( Dmac *pDmac,
                              uint8_t channel,
                              uint32_t daddr )
{
    assert(pDmac);
    assert(channel < DMAC_CHANNEL_NUM);
    pDmac->DMAC_CH_NUM[channel].DMAC_DADDR = daddr;
}

/**
 * \brief Return DMAC destination address of a DMAC channel.
 *
 * \param pDmac Pointer to the DMAC peripheral.
 * \param channel Particular channel number.
 */
uint32_t DMAC_GetDestinationAddr( Dmac *pDmac,
                                  uint8_t channel )
{
    assert(pDmac);
    assert(channel < DMAC_CHANNEL_NUM);
    return pDmac->DMAC_CH_NUM[channel].DMAC_DADDR;
}

/**
 * \brief Set DMAC descriptor address used by a DMAC channel.
 *
 * \param pDmac Pointer to the DMAC peripheral.
 * \param channel Particular channel number.
 * \param descr Buffer Transfer descriptor address
 * \param descrIf AHB-Lite interface to be fetched
 */
void DMAC_SetDescriptorAddr( Dmac *pDmac,
                             uint8_t channel,
                             uint32_t descr,
                             uint8_t descrif )
{
    assert(pDmac);
    assert(channel < DMAC_CHANNEL_NUM);
    assert(descrif < 2);
    //pDmac->DMAC_CH_NUM[channel].DMAC_DSCR = DMAC_DSCR_DSCR( descr ) | descrif;
    pDmac->DMAC_CH_NUM[channel].DMAC_DSCR = ( descr & 0xFFFFFFFC ) | descrif;
}

/**
 * \brief Set DMAC controlA used by a DMAC channel.
 *
 * \param pDmac Pointer to the DMAC peripheral.
 * \param channel Particular channel number.
 * \param controlA Configuration for controlA register.
 */
void DMAC_SetControlA( Dmac *pDmac,
                       uint8_t channel,
                       uint32_t controlA )
{
    assert(pDmac);
    assert(channel < DMAC_CHANNEL_NUM);
    pDmac->DMAC_CH_NUM[channel].DMAC_CTRLA = controlA;
}


/**
 * \brief Set DMAC buffer transfer size used by a DMAC channel.
 *
 * \param pDmac Pointer to the DMAC peripheral.
 * \param channel Particular channel number.
 * \param bsize number of transfers to be performed.
 */
void DMAC_SetBufferSize( Dmac *pDmac,
                         uint8_t channel,
                         uint16_t bsize)
{
   assert(pDmac);
   assert(channel < DMAC_CHANNEL_NUM);
   pDmac->DMAC_CH_NUM[channel].DMAC_CTRLA &= ~DMAC_CTRLA_BTSIZE_Msk;
   pDmac->DMAC_CH_NUM[channel].DMAC_CTRLA |= DMAC_CTRLA_BTSIZE( bsize );
}

/**
 * \brief Set DMAC single transfer size used by a DMAC channel.
 *
 * \param pDmac Pointer to the DMAC peripheral.
 * \param channel Particular channel number.
 * \param srcWidth source width for single transfer.
 * \param dstWidth destination width for single transfer.
 */
 void DMAC_SetSingleTransferSize ( Dmac *pDmac,
                                  uint8_t channel,
                                  uint8_t srcWidth,
                                  uint8_t dstWidth )
{
   assert(pDmac);
   assert(channel < DMAC_CHANNEL_NUM);
   pDmac->DMAC_CH_NUM[channel].DMAC_CTRLA &= ~DMAC_CTRLA_SRC_WIDTH_Msk;
   pDmac->DMAC_CH_NUM[channel].DMAC_CTRLA &= ~DMAC_CTRLA_DST_WIDTH_Msk;
   pDmac->DMAC_CH_NUM[channel].DMAC_CTRLA |= srcWidth | dstWidth;
}

/**
 * \brief Set DMAC single transfer size used by a DMAC channel.
 *
 * \param pDmac Pointer to the DMAC peripheral.
 * \param channel Particular channel number.
 * \param scSize Size of source chunk transfer.
 * \param dcSize Size of destination chunk transfer.
 */
void DMAC_SetChunkTransferSize ( Dmac *pDmac,
                                 uint8_t channel,
                                 uint8_t scSize,
                                 uint8_t dcSize)
{
   assert(pDmac);
   assert(channel < DMAC_CHANNEL_NUM);
   pDmac->DMAC_CH_NUM[channel].DMAC_CTRLA &= ~DMAC_CTRLA_SCSIZE_Msk;
   pDmac->DMAC_CH_NUM[channel].DMAC_CTRLA &= ~DMAC_CTRLA_DCSIZE_Msk;
   pDmac->DMAC_CH_NUM[channel].DMAC_CTRLA |= scSize | dcSize;
}

/**
 * \brief Set DMAC controlB used by a DMAC channel.
 *
 * \param pDmac Pointer to the DMAC peripheral.
 * \param channel Particular channel number.
 * \param controlB Configuration for controlA register.
 */
void DMAC_SetControlB( Dmac *pDmac,
                       uint8_t channel,
                       uint32_t controlB )
{
    assert(pDmac);
    assert(channel < DMAC_CHANNEL_NUM);
    pDmac->DMAC_CH_NUM[channel].DMAC_CTRLB = controlB;
}

/**
 * \brief Enables DMAC automatic multiple buffer transfer 
 *        mode used by a DMAC channel.
 *
 * \param pDmac Pointer to the DMAC peripheral.
 * \param channel Particular channel number.
 */
void DMAC_EnableAutoMode( Dmac *pDmac, uint8_t channel )
{
    assert(pDmac);
    assert(channel < DMAC_CHANNEL_NUM);
    pDmac->DMAC_CH_NUM[channel].DMAC_CTRLB |= DMAC_CTRLB_AUTO;
}

/**
 * \brief Disable DMAC automatic multiple buffer transfer 
 *        mode used by a DMAC channel.
 *
 * \param pDmac Pointer to the DMAC peripheral.
 * \param channel Particular channel number.
 */
void DMAC_DisableAutoMode( Dmac *pDmac, uint8_t channel )
{
    assert(pDmac);
    assert(channel < DMAC_CHANNEL_NUM);
    pDmac->DMAC_CH_NUM[channel].DMAC_CTRLB &= ~DMAC_CTRLB_AUTO;
}

/**
 * \brief Select DMAC AHB source interface.
 *
 * \param pDmac Pointer to the DMAC peripheral.
 * \param channel Particular channel number.
 * \param srcIf Source AHB-Lite interface.
 * \param dstIf Destination AHB-Lite interface.
 */
void DMAC_SelectAHBInterface( Dmac *pDmac,
                              uint8_t channel,
                              uint8_t srcIf,
                              uint8_t dstIf )
{
    assert(pDmac);
    assert(channel < DMAC_CHANNEL_NUM);
    pDmac->DMAC_CH_NUM[channel].DMAC_CTRLB &= ~DMAC_CTRLB_SIF_Msk;
    pDmac->DMAC_CH_NUM[channel].DMAC_CTRLB &= ~DMAC_CTRLB_DIF_Msk;
    pDmac->DMAC_CH_NUM[channel].DMAC_CTRLB |= srcIf | dstIf;
}


/**
 * \brief Set DMAC Picture-in-Picture mode for source and destination.
 *
 * \param pDmac Pointer to the DMAC peripheral.
 * \param channel Particular channel number.
 * \param srcPip Source picture-in-picture mode.
 * \param srcPip destination picture-in-picture mode.
 */
void DMAC_SetPipMode( Dmac *pDmac,
                      uint8_t channel,
                      uint8_t srcPip,
                      uint8_t dstPip )
{
    assert(pDmac);
    assert(channel < DMAC_CHANNEL_NUM );
    pDmac->DMAC_CH_NUM[channel].DMAC_CTRLB &= ~DMAC_CTRLB_SRC_PIP;
    pDmac->DMAC_CH_NUM[channel].DMAC_CTRLB &= ~DMAC_CTRLB_DST_PIP;
    pDmac->DMAC_CH_NUM[channel].DMAC_CTRLB |= srcPip | dstPip;
}

/**
 * \brief Set DMAC buffer descriptor fetch mode.
 *
 * \param pDmac Pointer to the DMAC peripheral.
 * \param channel Particular channel number.
 * \param srcDscr Source buffer descriptor fetch mode.
 * \param dstDscr destination buffer descriptor fetch mode.
 */
void DMAC_SetDescFetchMode( Dmac *pDmac,
                            uint8_t channel,
                            uint8_t srcDscr,
                            uint8_t dstDscr )
{
    assert(pDmac);
    assert(channel < DMAC_CHANNEL_NUM );
    pDmac->DMAC_CH_NUM[channel].DMAC_CTRLB &= ~DMAC_CTRLB_SRC_DSCR;
    pDmac->DMAC_CH_NUM[channel].DMAC_CTRLB &= ~DMAC_CTRLB_DST_DSCR;
    pDmac->DMAC_CH_NUM[channel].DMAC_CTRLB |= srcDscr | dstDscr;
}

/**
 * \brief Set DMAC control B register Flow control bit field.
 *
 * \param pDmac Pointer to the DMAC peripheral.
 * \param channel Particular channel number.
 * \param flow which device controls the size of the buffer transfer.
 */
void DMAC_SetFlowControl( Dmac *pDmac,
                          uint8_t channel,
                          uint8_t flowControl )
{
    assert(pDmac);
    assert(channel < DMAC_CHANNEL_NUM);
    pDmac->DMAC_CH_NUM[channel].DMAC_CTRLB &= ~DMAC_CTRLB_FC_Msk;
    pDmac->DMAC_CH_NUM[channel].DMAC_CTRLB |= flowControl;
}

/**
 * \brief Set DMAC CFG register used by a DMAC channel.
 *
 * \param pDmac Pointer to the DMAC peripheral.
 * \param channel Particular channel number.
 * \param configuration Configuration for CFG register.
 */
void DMAC_SetCFG( Dmac *pDmac,
                  uint8_t channel,
                  uint32_t configuration )
{
    assert(pDmac);
    assert(channel < DMAC_CHANNEL_NUM);
    pDmac->DMAC_CH_NUM[channel].DMAC_CFG = configuration;
}

/**
 * \brief Set DMAC buffer reload mode.
 *
 * \param pDmac Pointer to the DMAC peripheral.
 * \param channel Particular channel number.
 * \param srcRep Source buffer reload mode.
 * \param dstRep Destination buffer reload mode.
 */
void DMAC_SetReloadMode( Dmac *pDmac,
                         uint8_t channel,
                         uint8_t srcRep,
                         uint8_t dstRep )
{
    assert(pDmac);
    assert(channel < DMAC_CHANNEL_NUM );
    pDmac->DMAC_CH_NUM[channel].DMAC_CFG &= ~DMAC_CFG_SRC_REP;
    pDmac->DMAC_CH_NUM[channel].DMAC_CFG &= ~DMAC_CFG_DST_REP;
    pDmac->DMAC_CH_NUM[channel].DMAC_CFG |= srcRep | dstRep;
}

/**
 * \brief Set DMAC SW/HW handshaking interface used to 
 *        trigger a transfer request.
 *
 * \param pDmac Pointer to the DMAC peripheral.
 * \param channel Particular channel number.
 * \param srcH2sel Source handshaking interface. 
 * \param dstH2sel Destination handshaking interface.
 */
void DMAC_SethandshakeInterface( Dmac *pDmac,
                                 uint8_t channel,
                                 uint8_t srcH2sel,
                                 uint8_t dstH2sel )
{
    assert(pDmac);
    assert(channel < DMAC_CHANNEL_NUM );
    pDmac->DMAC_CH_NUM[channel].DMAC_CFG &= ~DMAC_CFG_SRC_H2SEL;
    pDmac->DMAC_CH_NUM[channel].DMAC_CFG &= ~DMAC_CFG_DST_H2SEL;
    pDmac->DMAC_CH_NUM[channel].DMAC_CFG |= srcH2sel | dstH2sel;
}


/**
 * \brief Set DMAC source PIP configuration used by a DMAC channel.
 *
 * \param pDmac Pointer to the DMAC peripheral.
 * \param channel Particular channel number.
 * \param pipHole the value to add to the address when the programmable
 *                boundary has been reached.
 * \param pipBoundary the number of source transfers to perform before
 *                the automatic address increment operation.
 */
void DMAC_SetSourcePip( Dmac *pDmac,
                        uint8_t channel,
                        uint16_t pipHole,
                        uint16_t pipBoundary)

{
   assert(pDmac);
   assert(channel < DMAC_CHANNEL_NUM);
   pDmac->DMAC_CH_NUM[channel].DMAC_SPIP = DMAC_SPIP_SPIP_HOLE( pipHole ) |
                                           DMAC_SPIP_SPIP_BOUNDARY( pipBoundary );
}

/**
 * \brief Set DMAC destination PIP configuration used by a DMAC channel.
 *
 * \param pDmac Pointer to the DMAC peripheral.
 * \param channel Particular channel number.
 * \param pipHole the value to add to the address when the programmable
 *                boundary has been reached.
 * \param pipBoundary the number of source transfers to perform before
 *                the automatic address increment operation.
 */
void DMAC_SetDestPip( Dmac *pDmac,
                      uint8_t channel,
                      uint16_t pipHole,
                      uint16_t pipBoundary)

{
   assert(pDmac);
   assert(channel < DMAC_CHANNEL_NUM);
   pDmac->DMAC_CH_NUM[channel].DMAC_DPIP = DMAC_DPIP_DPIP_HOLE( pipHole ) |
                                           DMAC_DPIP_DPIP_BOUNDARY( pipBoundary );
}

/**@}*/

