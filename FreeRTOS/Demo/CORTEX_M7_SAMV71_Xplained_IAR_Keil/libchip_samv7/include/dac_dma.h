/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2014, Atmel Corporation
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
 *  \file
 *
 *  \section Purpose
 *
 *  Interface for configuration the Analog-to-Digital Converter (DACC) peripheral.
 *
 *  \section Usage
 *
 *  -# Configurate the pins for DACC
 *  -# Initialize the DACC with DACC_Initialize().
 *  -# Select the active channel using DACC_EnableChannel()
 *  -# Start the conversion with DACC_StartConversion()
 *  -# Wait the end of the conversion by polling status with DACC_GetStatus()
 *  -# Finally, get the converted data using DACC_GetConvertedData()
 *
*/
#ifndef _DAC_DMA_
#define _DAC_DMA_

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/
#include "chip.h"

#include <stdint.h>
#include <assert.h>


#ifdef __cplusplus
 extern "C" {
#endif


/*----------------------------------------------------------------------------
 *        Types
 *----------------------------------------------------------------------------*/

/** DAC transfer complete callback. */
typedef void (*DacCallback)( uint8_t, void* ) ;

/** \brief Dac Transfer Request prepared by the application upper layer.
 *
 * This structure is sent to the DAC_SendCommand function to start the transfer.
 * At the end of the transfer, the callback is invoked by the interrupt handler.
 */
typedef struct
{
    /** Pointer to the Tx data. */
    uint8_t *pTxBuff;
    /** Tx size in bytes. */
    uint16_t TxSize;
    /** Tx loop back. */
    uint16_t loopback;
    /** DACC channel*/
    uint8_t dacChannel; 
    /** Callback function invoked at the end of transfer. */
    DacCallback callback;
    /** Callback arguments. */
    void *pArgument;
} DacCmd ;


/** Constant structure associated with DAC port. This structure prevents
    client applications to have access in the same time. */
typedef struct 
{
    /** Pointer to DAC Hardware registers */
    Dacc* pDacHw ;
    /** Current SpiCommand being processed */
    DacCmd *pCurrentCommand ;
    /** Pointer to DMA driver */
    sXdmad* pXdmad ;
    /** DACC Id as defined in the product datasheet */
    uint8_t dacId ;
    /** Mutual exclusion semaphore. */
    volatile int8_t semaphore ;
} DacDma;


/*------------------------------------------------------------------------------
 *         Definitions
 *------------------------------------------------------------------------------*/
#define DAC_OK          0
#define DAC_ERROR       1
#define DAC_ERROR_LOCK  2

#define DACC_CHANNEL_0 0
#define DACC_CHANNEL_1 1

/*------------------------------------------------------------------------------
 *         Exported functions
 *------------------------------------------------------------------------------*/
extern uint32_t Dac_ConfigureDma( DacDma *pDacd ,
                           Dacc *pDacHw ,
                           uint8_t DacId,
                           sXdmad *pXdmad );
extern uint32_t Dac_SendData( DacDma *pDacd, DacCmd *pCommand);


/*------------------------------------------------------------------------------
 *         Macros function of register access
 *------------------------------------------------------------------------------*/
#define DACC_SoftReset(pDACC)                 ((pDACC)->DACC_CR = DACC_CR_SWRST)
#define DACC_CfgModeReg(pDACC, mode)          { (pDACC)->DACC_MR = (mode); }
#define DACC_GetModeReg(pDACC)                ((pDACC)->DACC_MR)
#define DACC_CfgTrigger(pDACC, mode)          { (pDACC)->DACC_TRIGR = (mode); }

#define DACC_EnableChannel(pDACC, channel)    {(pDACC)->DACC_CHER = (1 << (channel));}
#define DACC_DisableChannel(pDACC, channel)   {(pDACC)->DACC_CHDR = (1 << (channel));}

#define DACC_EnableIt(pDACC, mode)            {(pDACC)->DACC_IER = (mode);}
#define DACC_DisableIt(pDACC, mode)           {(pDACC)->DACC_IDR = (mode);}
#define DACC_GetStatus(pDACC)                 ((pDACC)->DACC_ISR)
#define DACC_GetChannelStatus(pDACC)          ((pDACC)->DACC_CHSR)
#define DACC_GetInterruptMaskStatus(pDACC)    ((pDACC)->DACC_IMR)


#ifdef __cplusplus
}
#endif

#endif /* #ifndef _DAC_DMA_ */
