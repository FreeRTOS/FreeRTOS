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
 *  Interface for configuration the Analog-to-Digital Converter (AFEC) peripheral.
 *
 *  \section Usage
 *
 *  -# Configurate the pins for AFEC.
 *  -# Initialize the AFEC with AFEC_Initialize().
 *  -# Set AFEC clock and timing with AFEC_SetClock() and AFEC_SetTiming().
 *  -# Select the active channel using AFEC_EnableChannel().
 *  -# Start the conversion with AFEC_StartConversion().
 *  -# Wait the end of the conversion by polling status with AFEC_GetStatus().
 *  -# Finally, get the converted data using AFEC_GetConvertedData() or AFEC_GetLastConvertedData().
 *
*/
#ifndef _AFE_DMA_
#define _AFE_DMA_

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"


/*----------------------------------------------------------------------------
 *        Types
 *----------------------------------------------------------------------------*/

/** AFE transfer complete callback. */
typedef void (*AfeCallback)( uint8_t, void* ) ;

/** \brief Spi Transfer Request prepared by the application upper layer.
 *
 * This structure is sent to the AFE_SendCommand function to start the transfer.
 * At the end of the transfer, the callback is invoked by the interrupt handler.
 */
typedef struct
{
    /** Pointer to the Rx data. */
    uint32_t *pRxBuff;
    /** Rx size in bytes. */
    uint16_t RxSize;
    /** Callback function invoked at the end of transfer. */
    AfeCallback callback;
    /** Callback arguments. */
    void *pArgument;
} AfeCmd ;


/** Constant structure associated with AFE port. This structure prevents
    client applications to have access in the same time. */
typedef struct 
{
    /** Pointer to AFE Hardware registers */
    Afec* pAfeHw ;
    /** Current SpiCommand being processed */
    AfeCmd *pCurrentCommand ;
    /** Pointer to DMA driver */
    sXdmad* pXdmad;
    /** AFEC Id as defined in the product datasheet */
    uint8_t afeId ;
    /** Mutual exclusion semaphore. */
    volatile int8_t semaphore ;
} AfeDma;


/*------------------------------------------------------------------------------
 *         Definitions
 *------------------------------------------------------------------------------*/
#define AFE_OK          0
#define AFE_ERROR       1
#define AFE_ERROR_LOCK  2
/*------------------------------------------------------------------------------
 *         Exported functions
 *------------------------------------------------------------------------------*/
extern uint32_t Afe_ConfigureDma( AfeDma *pAfed ,
                           Afec *pAfeHw ,
                           uint8_t AfeId,
                           sXdmad *pXdmad );
extern uint32_t Afe_SendData( AfeDma *pAfed, AfeCmd *pCommand);


#endif /* #ifndef _AFE_DMA_ */

