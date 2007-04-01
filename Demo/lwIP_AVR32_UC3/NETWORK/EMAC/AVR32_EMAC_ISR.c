/* This source file is part of the ATMEL FREERTOS-0.9.0 Release */

/*This file has been prepared for Doxygen automatic documentation generation.*/
/*! \file *********************************************************************
 *
 * \brief EMAC abstraction layer for AVR32 UC3.
 *
 * - Compiler:           GNU GCC for AVR32
 * - Supported devices:  All AVR32 devices can be used.
 * - AppNote:
 *
 * \author               Atmel Corporation: http://www.atmel.com \n
 *                       Support email: avr32@atmel.com
 *
 *****************************************************************************/

/* Copyright (c) 2007, Atmel Corporation All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * 3. The name of ATMEL may not be used to endorse or promote products derived
 * from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL ``AS IS'' AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE EXPRESSLY AND
 * SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */



#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

#include "AVR32_EMAC.h"
#include "AVR32_CONF_EMAC.h"

#include "lwipopts.h"




/*-----------------------------------------------------------*/

/* The semaphore used to signal the arrival of new data to the interface
task. */
static xSemaphoreHandle xSemaphore = NULL;

static __attribute__((__noinline__)) portBASE_TYPE prvEMAC_ISR_NonNakedBehaviour( void );


/*
 * The EMAC ISR.  Handles both Tx and Rx complete interrupts.
 */
//__attribute__((naked,section (".handlers"))) void vEMAC_ISR( void )
__attribute__((naked)) void vEMAC_ISR( void )
{
 /* This ISR can cause a context switch, so the first statement must be a
     call to the portENTER_SWITCHING_ISR() macro.  This must be BEFORE any
     variable declarations. */
  portENTER_SWITCHING_ISR();

  prvEMAC_ISR_NonNakedBehaviour();
 /* Exit the ISR.  If a task was woken by either a character being received
     or transmitted then a context switch will occur. */

  portEXIT_SWITCHING_ISR();
}
/*-----------------------------------------------------------*/

static __attribute__((__noinline__)) portBASE_TYPE prvEMAC_ISR_NonNakedBehaviour( void )
{

  /* Variable definitions can be made now. */
  volatile unsigned portLONG ulIntStatus, ulEventStatus;
  portBASE_TYPE xSwitchRequired = pdFALSE;
  extern void vClearEMACTxBuffer( void );

  /* Find the cause of the interrupt. */
  ulIntStatus = AVR32_MACB.isr;
  ulEventStatus = AVR32_MACB.rsr;

  if( ( ulIntStatus & AVR32_MACB_IDR_RCOMP_MASK ) || ( ulEventStatus & AVR32_MACB_REC_MASK ) )
  {
    /* A frame has been received, signal the lwIP task so it can process
    the Rx descriptors. */
    portENTER_CRITICAL();
    xSwitchRequired = xSemaphoreGiveFromISR( xSemaphore, pdFALSE );
    portEXIT_CRITICAL();
    AVR32_MACB.rsr =  AVR32_MACB_REC_MASK;
    AVR32_MACB.rsr;
  }

  if( ulIntStatus & AVR32_MACB_TCOMP_MASK )
  {
   /* A frame has been transmitted.  Mark all the buffers used by the
    frame just transmitted as free again. */
    vClearEMACTxBuffer();
    AVR32_MACB.tsr =  AVR32_MACB_TSR_COMP_MASK;
    AVR32_MACB.tsr;
  }

  return ( xSwitchRequired );
}

/*-----------------------------------------------------------*/

void vPassEMACSemaphore( xSemaphoreHandle xCreatedSemaphore )
{
  /* Simply store the semaphore that should be used by the ISR. */
  xSemaphore = xCreatedSemaphore;
}


