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

/** \addtogroup pio_capture_module Working with PIO Parallel Capture Mode
 *  \ingroup peripherals_module
 * The PIO Parallel Capture Mode driver provides the interface to configure 
 * and use the PIO Parallel Capture Mode peripheral.\n
 *
 * The PIO Controller integrates an interface able to read data from a CMOS digital
 * image sensor, a high-speed parallel ADC, a DSP synchronous port in synchronous
 * mode, etc.... For better understanding and to ease reading, the following
 * description uses an example with a CMOS digital image sensor
 *
 * To use the PIO Parallel Capture, the user has to follow these few steps:
 * <ul>
 *   <li> Enable PIOA peripheral clock </li>
 *   <li> Configure the PDC </li>
 *   <li> Configure the PIO Capture interrupt </li>
 *   <li> Enable the PDC </li>
 *   <li> Enable the PIO Capture </li>
 *   <li> Wait for interrupt </li>
 *   <li> Disable the interrupt </li>
 *   <li> Read the DATA </li>
 * </ul>
 *
 * For more accurate information, please look at the PIO Parallel Capture Mode 
 * section of the Datasheet.
 *
 * <b>API Usage:</b>
 *
 *  -# Configurate the interrupt for PIOA, can be done by 
 * PIO_InitializeInterrupts()
 *  -# Initialize the PIO Parallel Capture API by filing the SpioCaptureInit 
 *     structure 
 * options:
 *       - alwaysSampling: for sample data with or without take in account
 *         ENABLE pins.
 *       - halfSampling: for sample all data or only one time out of two
 *  -# Call PIO_CaptureInit() for init and enable the PDC, init the PIO capture.
 *  -# Call PIO_CaptureEnable() for enable the PIO Parallel Capture.
 *  -# When an interrupt is received, the PIO_CaptureHandler() is call and the 
 *     respective callback is launch.
 *  -# When the transfer is complete, the user need to disable interrupt with
 *     PIO_CaptureDisableIt(). Otherwise, the PDC will send an interrupt.
 *  -# The data receive by the PIO Parallel Capture is inside the buffer passed 
 *     in the PIO_CaptureInit().
 *
 * Related files :\n
 * \ref pio_capture.c\n
 * \ref pio_capture.h\n
 */
/*@{*/
/*@}*/
/**
 * \file
 *
 * Implementation of PIO Parallel Capture.
 *
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

#include <assert.h>

#define PIO_PCISR_RXBUFF (0x1u<<3)
#define PIO_PCISR_ENDRX  (0x1u<<2)
/*----------------------------------------------------------------------------
 *        Local Functions
 *----------------------------------------------------------------------------*/
/** Copy the API structure for interrupt handler */
static SpioCaptureInit* _PioCaptureCopy;

/*----------------------------------------------------------------------------
 *        Global Functions
 *----------------------------------------------------------------------------*/

/*----------------------------------------------------------------------------*/
/**
 * \brief The PIO_CaptureHandler must be called by the PIO Capture Interrupt
 * Service Routine with the corresponding PIO Capture instance.
 */
/*----------------------------------------------------------------------------*/
extern void PIO_CaptureHandler( void )
{
	volatile uint32_t pio_captureSr;
	uint32_t k;

	/* Read the status register*/
	pio_captureSr = PIOA->PIO_PCISR ;
	k = pio_captureSr;
	pio_captureSr = k & PIOA->PIO_PCIMR ;

	if (pio_captureSr & PIO_PCISR_DRDY) {
		/* Parallel Capture Mode Data Ready */
		if ( _PioCaptureCopy->CbkDataReady != NULL ) {
			_PioCaptureCopy->CbkDataReady( _PioCaptureCopy );
		} else {
			TRACE_DEBUG("IT PIO Capture Data Ready received (no callback)\n\r");
		}
	}

	if (pio_captureSr & PIO_PCISR_OVRE) {
		/* Parallel Capture Mode Overrun Error */
		if ( _PioCaptureCopy->CbkOverrun != NULL ) 	{
			_PioCaptureCopy->CbkOverrun( _PioCaptureCopy );
		} else {
			TRACE_DEBUG("IT PIO Capture Overrun Error received (no callback)\n\r");
		}
	}

	if (pio_captureSr & PIO_PCISR_RXBUFF) {
		/* Reception Buffer Full */
		if ( _PioCaptureCopy->CbkBuffFull != NULL ) {
			_PioCaptureCopy->CbkBuffFull( _PioCaptureCopy );
		} else {
			TRACE_DEBUG("IT PIO Capture Reception Buffer Full received \
					(no callback)\n\r");
		}
	}

	if (pio_captureSr & PIO_PCISR_ENDRX) {
		/* End of Reception Transfer */
		if ( _PioCaptureCopy->CbkEndReception != NULL ) {
			_PioCaptureCopy->CbkEndReception( _PioCaptureCopy );
		} else {
			TRACE_DEBUG("IT PIO Capture End of Reception Transfer \
					received (no callback)\n\r");
		}
	}
}

/*----------------------------------------------------------------------------*/
/**
 * \brief Disable Interrupt of the PIO Capture
 * \param itToDisable : Interrupt to disable
 */
/*----------------------------------------------------------------------------*/
void PIO_CaptureDisableIt( uint32_t itToDisable )
{
	/* Parallel capture mode is enabled */
	PIOA->PIO_PCIDR = itToDisable;
}

/*----------------------------------------------------------------------------*/
/**
 * \brief Enable Interrupt of the PIO Capture
 * \param itToEnable : Interrupt to enable
 */
/*----------------------------------------------------------------------------*/
void PIO_CaptureEnableIt( uint32_t itToEnable )
{
	/* Parallel capture mode is enabled */
	PIOA->PIO_PCIER = itToEnable;
}

/*----------------------------------------------------------------------------*/
/**
 * \brief Enable the PIO Capture
 */
/*----------------------------------------------------------------------------*/
void PIO_CaptureEnable( void )
{
	/* PDC: Receive Pointer Register */
	//    PIOA->PIO_RPR = (uint32_t)_PioCaptureCopy->pData ;
	//    /* PDC: Receive Counter Register */
	//    /* Starts peripheral data transfer if corresponding channel is active */
	//    PIOA->PIO_RCR = PIO_RCR_RXCTR(_PioCaptureCopy->dPDCsize) ;

	/* Parallel capture mode is enabled */
	PIOA->PIO_PCMR |= PIO_PCMR_PCEN ;
}

/*----------------------------------------------------------------------------*/
/**
 * \brief Disable the PIO Capture
 */
/*----------------------------------------------------------------------------*/
void PIO_CaptureDisable( void )
{
	/* Parallel capture mode is disabled */
	PIOA->PIO_PCMR &= (uint32_t)(~PIO_PCMR_PCEN) ;
}

/*----------------------------------------------------------------------------*/
/**
 * \brief Initialize the PIO Capture
 * \param dsize :
 *  0 = The reception data in the PIO_PCRHR register is a BYTE (8-bit).
 *  1 = The reception data in the PIO_PCRHR register is a HALF-WORD (16-bit).
 * 2/3 = The reception data in the PIO_PCRHR register is a WORD (32-bit).
 * \param alwaysSampling: ALWYS: Parallel Capture Mode Always Sampling
 * 0 = The parallel capture mode samples the data when both data enables are active.
 * 1 = The parallel capture mode samples the data whatever the data enables are.
 * \param halfSampling: HALFS: Parallel Capture Mode Half Sampling
 * 0 = The parallel capture mode samples all the data.
 * 1 = The parallel capture mode samples the data only one time out of two.
 * \param modeFirstSample: FRSTS: Parallel Capture Mode First Sample
 * This bit is useful only if the HALFS bit is set to 1. If data are numbered
 * in the order that they are received with an index from 0 to n:
 * 0 = Only data with an even index are sampled.
 * 1 = Only data with an odd index are sampled.
 */
/*----------------------------------------------------------------------------*/
void PIO_CaptureInit( SpioCaptureInit *pInit )
{
	PMC_EnablePeripheral( ID_PIOA );

	assert( (pInit->dsize < 0x4) ) ;
	assert( (pInit->alwaysSampling < 2)  );
	assert( (pInit->halfSampling < 2) );
	assert( (pInit->modeFirstSample < 2) );
	/* Copy the API structure for interrupt handler */
	_PioCaptureCopy = pInit;

	if ( pInit->CbkDataReady != NULL ) {
		PIOA->PIO_PCIER = PIO_PCISR_DRDY;
	}

	if ( pInit->CbkOverrun != NULL ) {
		PIOA->PIO_PCIER = PIO_PCISR_OVRE;
	}

	if ( pInit->CbkEndReception != NULL ) {
		PIOA->PIO_PCIER = PIO_PCISR_ENDRX;
	}

	if ( pInit->CbkBuffFull != NULL ) {
		PIOA->PIO_PCIER = PIO_PCISR_RXBUFF;
	}
}

