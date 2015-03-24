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

#ifndef PIO_CAPTURE_H
#define PIO_CAPTURE_H

/*----------------------------------------------------------------------------
 *        Types
 *----------------------------------------------------------------------------*/

/** \brief PIO Parallel Capture structure for initialize.
 *
 * At the end of the transfer, the callback is invoked by the interrupt handler.
 */
typedef struct _SpioCaptureInit {

    /** PIO_PCRHR register is a BYTE, HALF-WORD or WORD */
    uint8_t dsize;
    /** PDC size, data to be received */
    uint16_t dPDCsize;
    /** Data to be received */
    uint32_t *pData;
    /** Parallel Capture Mode Always Sampling */
    uint8_t alwaysSampling;
    /** Parallel Capture Mode Half Sampling */
    uint8_t halfSampling;
    /** Parallel Capture Mode First Sample */
    uint8_t modeFirstSample;
    /** Callback function invoked at Mode Data Ready */
    void (*CbkDataReady)( struct _SpioCaptureInit* );
    /** Callback function invoked at Mode Overrun Error */
    void (*CbkOverrun)( struct _SpioCaptureInit* );
    /** Callback function invoked at End of Reception Transfer */
    void (*CbkEndReception)( struct _SpioCaptureInit* );
    /** Callback function invoked at Reception Buffer Full */
    void (*CbkBuffFull)( struct _SpioCaptureInit* );
    /** Callback arguments.*/
    void *pParam;

} SpioCaptureInit ;


/*----------------------------------------------------------------------------
 *        Global Functions
 *----------------------------------------------------------------------------*/
extern void PIO_CaptureDisableIt( uint32_t itToDisable ) ;
extern void PIO_CaptureEnableIt( uint32_t itToEnable ) ;
extern void PIO_CaptureEnable( void ) ;
extern void PIO_CaptureDisable( void ) ;
extern void PIO_CaptureInit( SpioCaptureInit* pInit ) ;

#endif /* #ifndef PIO_CAPTURE_H */

