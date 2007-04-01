/* This source file is part of the ATMEL FREERTOS-0.9.0 Release */

/*This file has been prepared for Doxygen automatic documentation generation.*/
/*! \file *********************************************************************
 *
 * \brief EMAC abstraction layer for AVR32 UC3.
 *
 * - Compiler:           GNU GCC for AVR32
 * - Supported devices:  All AVR32 devices with a MACB can be used.
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


/*
 * Interrupt driven driver for the EMAC peripheral.  This driver is not
 * reentrant, re-entrancy is handled by a semaphore at the network interface
 * level. 
 */


/* Standard includes. */
#include <stdio.h>
#include <string.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "semphr.h"
#include "task.h"

/* Demo app includes. */
#include "AVR32_EMAC.h"
#include "AVR32_CONF_EMAC.h"
#include "DP83848.h"
#include "intc.h"

/* Hardware specific includes. */
#include "gpio.h"

/* Size of each receive buffer - DO NOT CHANGE. */
#define ETH_RX_BUFFER_SIZE    128

/* The buffer addresses written into the descriptors must be aligned so the
last few bits are zero.  These bits have special meaning for the EMAC
peripheral and cannot be used as part of the address. */
#define emacADDRESS_MASK      ( ( unsigned portLONG ) 0xFFFFFFFC )

/* Bit used within the address stored in the descriptor to mark the last
descriptor in the array. */
#define emacRX_WRAP_BIT       ( ( unsigned portLONG ) 0x02 )


/* A short delay is used to wait for a buffer to become available, should
one not be immediately available when trying to transmit a frame. */
#define emacBUFFER_WAIT_DELAY   ( 2 )
#define emacMAX_WAIT_CYCLES     ( ( portBASE_TYPE ) ( configTICK_RATE_HZ / 40 ) )

/* The time to block waiting for input. */
#define emacBLOCK_TIME_WAITING_FOR_INPUT   ( ( portTickType ) 100 )

/* Misc defines. */
#define emacNO_DELAY        ( 0 )

/*-----------------------------------------------------------*/

/* Buffer written to by the EMAC DMA.  Must be aligned as described by the
comment above the emacADDRESS_MASK definition. */
static volatile portCHAR pcRxBuffer[ NB_RX_BUFFERS * ETH_RX_BUFFER_SIZE ] __attribute__ ((aligned (8)));

/* Buffer read by the EMAC DMA.  Must be aligned as described by the comment
above the emacADDRESS_MASK definition. */
static portCHAR pcTxBuffer[ NB_TX_BUFFERS * ETH_TX_BUFFER_SIZE ] __attribute__ ((aligned (8)));

/* Descriptors used to communicate between the program and the EMAC peripheral.
These descriptors hold the locations and state of the Rx and Tx buffers. */
static volatile AVR32_TxTdDescriptor xTxDescriptors[ NB_TX_BUFFERS ];
static volatile AVR32_RxTdDescriptor xRxDescriptors[ NB_RX_BUFFERS ];

/* The IP and Ethernet addresses are read from the header files. */
portCHAR cMACAddress[ 6 ] = { emacETHADDR0, emacETHADDR1, emacETHADDR2, emacETHADDR3, emacETHADDR4, emacETHADDR5 };

/*-----------------------------------------------------------*/

/* See the header file for descriptions of public functions. */

/*
 * Prototype for the EMAC interrupt function - called by the asm wrapper.
 */
void vEMAC_ISR( void ) __attribute__ ((naked));

/*
 * Initialise both the Tx and Rx descriptors used by the EMAC.
 */
static void prvSetupDescriptors(void);

/*
 * Write our MAC address into the EMAC.  
 */
static void prvSetupMACAddress( void );

/*
 * Configure the EMAC and AIC for EMAC interrupts.
 */
static void prvSetupEMACInterrupt( void );

/*
 * Some initialisation functions taken from the Atmel EMAC sample code.
 */
static unsigned portLONG vReadPHY( unsigned portCHAR ucAddress );

static void vWritePHY( unsigned portCHAR ucAddress, unsigned portLONG ulValue);

static portBASE_TYPE prvProbePHY( void );

/* The semaphore used by the EMAC ISR to wake the EMAC task. */
static xSemaphoreHandle xSemaphore = NULL;

/* Holds the index to the next buffer from which data will be read. */
static volatile unsigned portLONG ulNextRxBuffer = 0;

/*-----------------------------------------------------------*/

/* See the header file for descriptions of public functions. */
portLONG lEMACSend( portCHAR *pcFrom, unsigned portLONG ulLength, portLONG lEndOfFrame )
{
static unsigned portBASE_TYPE uxTxBufferIndex = 0;
//portBASE_TYPE xWaitCycles = 0;
portLONG lReturn = pdPASS;
portCHAR *pcBuffer;
unsigned portLONG ulLastBuffer, ulDataBuffered = 0, ulDataRemainingToSend, ulLengthToSend;

  /* If the length of data to be transmitted is greater than each individual
  transmit buffer then the data will be split into more than one buffer.
  Loop until the entire length has been buffered. */
  while( ulDataBuffered < ulLength )
  {
    /* Is a buffer available? */
    while( !( xTxDescriptors[ uxTxBufferIndex ].U_Status.status & AVR32_TRANSMIT_OK ) )
    {
      /* There is no room to write the Tx data to the Tx buffer.  Wait a
      short while, then try again. */
        vTaskDelay( emacBUFFER_WAIT_DELAY );
    }
  
    /* lReturn will only be pdPASS if a buffer is available. */
    if( lReturn == pdPASS )
    {
      portENTER_CRITICAL();
      {
        /* Get the address of the buffer from the descriptor, then copy
        the data into the buffer. */
        pcBuffer = ( portCHAR * ) xTxDescriptors[ uxTxBufferIndex ].addr;

        /* How much can we write to the buffer? */
        ulDataRemainingToSend = ulLength - ulDataBuffered;
        if( ulDataRemainingToSend <= ETH_TX_BUFFER_SIZE )
        {
          /* We can write all the remaining bytes. */
          ulLengthToSend = ulDataRemainingToSend;
        }
        else
        {
          /* We can not write more than ETH_TX_BUFFER_SIZE in one go. */
          ulLengthToSend = ETH_TX_BUFFER_SIZE;
        }

        /* Copy the data into the buffer. */
        memcpy( ( void * ) pcBuffer, ( void * ) &( pcFrom[ ulDataBuffered ] ), ulLengthToSend );
        ulDataBuffered += ulLengthToSend;

        /* Is this the last data for the frame? */
        if( lEndOfFrame && ( ulDataBuffered >= ulLength ) )
        {
          /* No more data remains for this frame so we can start the
          transmission. */
          ulLastBuffer = AVR32_LAST_BUFFER;
        }
        else
        {
          /* More data to come for this frame. */
          ulLastBuffer = 0;
        }
  
        /* Fill out the necessary in the descriptor to get the data sent,
        then move to the next descriptor, wrapping if necessary. */
        if( uxTxBufferIndex >= ( NB_TX_BUFFERS - 1 ) )
        {
          xTxDescriptors[ uxTxBufferIndex ].U_Status.status =   ( ulLengthToSend & ( unsigned portLONG ) AVR32_LENGTH_FRAME )
                                      | ulLastBuffer
                                      | AVR32_TRANSMIT_WRAP;
          uxTxBufferIndex = 0;
        }
        else
        {
          xTxDescriptors[ uxTxBufferIndex ].U_Status.status =   ( ulLengthToSend & ( unsigned portLONG ) AVR32_LENGTH_FRAME )
                                      | ulLastBuffer;
          uxTxBufferIndex++;
        }
  
        /* If this is the last buffer to be sent for this frame we can
        start the transmission. */
        if( ulLastBuffer )
        {
          AVR32_MACB.ncr |=  AVR32_MACB_TSTART_MASK;
        }
      }
      portEXIT_CRITICAL();
    }
    else
    {
      break;
    }
  }

  return lReturn;
}
/*-----------------------------------------------------------*/

/* See the header file for descriptions of public functions. */
unsigned portLONG ulEMACInputLength( void )
{
register unsigned portLONG ulIndex , ulLength = 0;

  /* Skip any fragments.  We are looking for the first buffer that contains
  data and has the SOF (start of frame) bit set. */
  while( ( xRxDescriptors[ ulNextRxBuffer ].addr & AVR32_OWNERSHIP_BIT ) && !( xRxDescriptors[ ulNextRxBuffer ].U_Status.status & AVR32_SOF ) )
  {
    /* Ignoring this buffer.  Mark it as free again. */
    xRxDescriptors[ ulNextRxBuffer ].addr &= ~( AVR32_OWNERSHIP_BIT );
    ulNextRxBuffer++;
    if( ulNextRxBuffer >= NB_RX_BUFFERS )
    {
      ulNextRxBuffer = 0;
    }
  }

  /* We are going to walk through the descriptors that make up this frame,
  but don't want to alter ulNextRxBuffer as this would prevent vEMACRead()
  from finding the data.  Therefore use a copy of ulNextRxBuffer instead. */
  ulIndex = ulNextRxBuffer;
  /* Walk through the descriptors until we find the last buffer for this
  frame.  The last buffer will give us the length of the entire frame. */
  while( ( xRxDescriptors[ ulIndex ].addr & AVR32_OWNERSHIP_BIT ) && !ulLength )
  {
    ulLength = xRxDescriptors[ ulIndex ].U_Status.status & AVR32_LENGTH_FRAME;
    /* Increment to the next buffer, wrapping if necessary. */
    ulIndex++;
    if( ulIndex >= NB_RX_BUFFERS )
    {
      ulIndex = 0;
    }
  }
  return ulLength;
}
/*-----------------------------------------------------------*/

/* See the header file for descriptions of public functions. */
void vEMACRead( portCHAR *pcTo, unsigned portLONG ulSectionLength, unsigned portLONG ulTotalFrameLength )
{
static unsigned portLONG ulSectionBytesReadSoFar = 0, ulBufferPosition = 0, ulFameBytesReadSoFar = 0;
static portCHAR *pcSource;
register unsigned portLONG ulBytesRemainingInBuffer, ulRemainingSectionBytes;

  /* Read ulSectionLength bytes from the Rx buffers.  This is not necessarily any
  correspondence between the length of our Rx buffers, and the length of the
  data we are returning or the length of the data being requested.  Therefore,
  between calls  we have to remember not only which buffer we are currently
  processing, but our position within that buffer.  This would be greatly
  simplified if PBUF_POOL_BUFSIZE could be guaranteed to be greater than
  the size of each Rx buffer, and that memory fragmentation did not occur.
  
  This function should only be called after a call to ulEMACInputLength().
  This will ensure ulNextRxBuffer is set to the correct buffer. */


  /* vEMACRead is called with pcTo set to NULL to indicate that we are about
  to read a new frame.  Any fragments remaining in the frame we were
  processing during the last call should be dropped. */
  if( pcTo == NULL )
  {
    /* How many bytes are indicated as being in this buffer?  If none then
    the buffer is completely full and the frame is contained within more
    than one buffer. */
    /* Reset our state variables ready for the next read from this buffer. */
        pcSource = ( portCHAR * )( xRxDescriptors[ ulNextRxBuffer ].addr & emacADDRESS_MASK );
        ulFameBytesReadSoFar = ( unsigned portLONG ) 0;
    ulBufferPosition = ( unsigned portLONG ) 0;
  }
  else
  {
    /* Loop until we have obtained the required amount of data. */
    ulSectionBytesReadSoFar = 0;
    while( ulSectionBytesReadSoFar < ulSectionLength )
    {
      /* We may have already read some data from this buffer.  How much
      data remains in the buffer? */
      ulBytesRemainingInBuffer = ( ETH_RX_BUFFER_SIZE - ulBufferPosition );

      /* How many more bytes do we need to read before we have the
      required amount of data? */
      ulRemainingSectionBytes = ulSectionLength - ulSectionBytesReadSoFar;

      /* Do we want more data than remains in the buffer? */
      if( ulRemainingSectionBytes > ulBytesRemainingInBuffer )
      {
        /* We want more data than remains in the buffer so we can
        write the remains of the buffer to the destination, then move
        onto the next buffer to get the rest. */
        memcpy( &( pcTo[ ulSectionBytesReadSoFar ] ), &( pcSource[ ulBufferPosition ] ), ulBytesRemainingInBuffer );
        ulSectionBytesReadSoFar += ulBytesRemainingInBuffer;
        ulFameBytesReadSoFar += ulBytesRemainingInBuffer;

        /* Mark the buffer as free again. */
        xRxDescriptors[ ulNextRxBuffer ].addr &= ~( AVR32_OWNERSHIP_BIT );
        /* Move onto the next buffer. */
        ulNextRxBuffer++;
        if( ulNextRxBuffer >= NB_RX_BUFFERS )
        {
          ulNextRxBuffer = ( unsigned portLONG ) 0;
        }

        /* Reset the variables for the new buffer. */
        pcSource = ( portCHAR * )( xRxDescriptors[ ulNextRxBuffer ].addr & emacADDRESS_MASK );
        ulBufferPosition = ( unsigned portLONG ) 0;
      }
      else
      {
        /* We have enough data in this buffer to send back.  Read out
        enough data and remember how far we read up to. */
        memcpy( &( pcTo[ ulSectionBytesReadSoFar ] ), &( pcSource[ ulBufferPosition ] ), ulRemainingSectionBytes );

        /* There may be more data in this buffer yet.  Increment our
        position in this buffer past the data we have just read. */
        ulBufferPosition += ulRemainingSectionBytes;
        ulSectionBytesReadSoFar += ulRemainingSectionBytes;
        ulFameBytesReadSoFar += ulRemainingSectionBytes;

        /* Have we now finished with this buffer? */
        if( ( ulBufferPosition >= ETH_RX_BUFFER_SIZE ) || ( ulFameBytesReadSoFar >= ulTotalFrameLength ) )
        {
          /* Mark the buffer as free again. */
          xRxDescriptors[ ulNextRxBuffer ].addr &= ~( AVR32_OWNERSHIP_BIT );
          /* Move onto the next buffer. */
          ulNextRxBuffer++;
          if( ulNextRxBuffer >= NB_RX_BUFFERS )
          {
            ulNextRxBuffer = 0;
          }
          pcSource = ( portCHAR * )( xRxDescriptors[ ulNextRxBuffer ].addr & emacADDRESS_MASK );
          ulBufferPosition = 0;
        }
      }
    }
  }
}
/*-----------------------------------------------------------*/
void vEMACSetMACAddress(const portCHAR * EMACAddress)
{
  memcpy(cMACAddress, EMACAddress, sizeof(cMACAddress));
}

/* See the header file for descriptions of public functions. */
xSemaphoreHandle xEMACInit( void )
{
unsigned long status;

  /* enable GPIO's */
  gpio_enable_module_pin(AVR32_MACB_TX_CLK_0_PIN, AVR32_MACB_TX_CLK_0_FUNCTION); //PB0
  gpio_enable_module_pin(AVR32_MACB_TX_EN_0_PIN, AVR32_MACB_TX_EN_0_FUNCTION);   //PB1
  gpio_enable_module_pin(AVR32_MACB_TXD_0_PIN, AVR32_MACB_TXD_0_FUNCTION);       //PB2
  gpio_enable_module_pin(AVR32_MACB_TXD_1_PIN, AVR32_MACB_TXD_1_FUNCTION);       //PB3

  gpio_enable_module_pin(AVR32_MACB_RXD_0_PIN, AVR32_MACB_RXD_0_FUNCTION);       //PB5
  gpio_enable_module_pin(AVR32_MACB_RXD_1_PIN, AVR32_MACB_RXD_1_FUNCTION);       //PB6
  gpio_enable_module_pin(AVR32_MACB_RX_ER_0_PIN, AVR32_MACB_RX_ER_0_FUNCTION);   //PB7
  gpio_enable_module_pin(AVR32_MACB_MDC_0_PIN, AVR32_MACB_MDC_0_FUNCTION);       //PB8
  gpio_enable_module_pin(AVR32_MACB_MDIO_0_PIN, AVR32_MACB_MDIO_0_FUNCTION);     //PB9

  gpio_enable_module_pin(AVR32_MACB_RX_DV_0_PIN, AVR32_MACB_RX_DV_0_FUNCTION);   //PB15


  /* set up registers */
  AVR32_MACB.ncr = 0;
  AVR32_MACB.tsr = ~0UL;
  AVR32_MACB.rsr = ~0UL;
  AVR32_MACB.idr = ~0UL;
  status = AVR32_MACB.isr;


#ifndef USE_RMII_INTERFACE
  // RMII not used, set 1 to the USRIO Register
  AVR32_MACB.usrio |= AVR32_MACB_RMII_MASK;
#else
  // RMII used, set 0 to the USRIO Register
  AVR32_MACB.usrio &= ~AVR32_MACB_RMII_MASK;
#endif

  /* Load our MAC address into the EMAC. */
  prvSetupMACAddress();

  /* Setup the buffers and descriptors. */
  prvSetupDescriptors();

#if configCPU_CLOCK_HZ <= 20000000
  AVR32_MACB.ncfgr |= (AVR32_MACB_NCFGR_CLK_DIV8 << AVR32_MACB_NCFGR_CLK_OFFSET);
#elif configCPU_CLOCK_HZ <= 40000000
  AVR32_MACB.ncfgr |= (AVR32_MACB_NCFGR_CLK_DIV16 << AVR32_MACB_NCFGR_CLK_OFFSET);
#elif configCPU_CLOCK_HZ <= 80000000
  AVR32_MACB.ncfgr |= AVR32_MACB_NCFGR_CLK_DIV32 << AVR32_MACB_NCFGR_CLK_OFFSET;
#elif configCPU_CLOCK_HZ <= 160000000
  AVR32_MACB.ncfgr |= AVR32_MACB_NCFGR_CLK_DIV64 << AVR32_MACB_NCFGR_CLK_OFFSET;
#else
# error System clock too fast
#endif

  /* Are we connected? */
  if( prvProbePHY() )
  {
    /* Enable the interrupt! */
    portENTER_CRITICAL();
    {
      prvSetupEMACInterrupt();
      vPassEMACSemaphore( xSemaphore );
    }
    portEXIT_CRITICAL();
    /* Enable Rx and Tx, plus the stats register. */
    AVR32_MACB.ncr = AVR32_MACB_NCR_TE_MASK | AVR32_MACB_NCR_RE_MASK;
  }
  return xSemaphore;
}

/* See the header file for descriptions of public functions. */
void vClearEMACTxBuffer( void )
{
static unsigned portBASE_TYPE uxNextBufferToClear = 0;

  /* Called on Tx interrupt events to set the AT91C_TRANSMIT_OK bit in each
  Tx buffer within the frame just transmitted.  This marks all the buffers
  as available again.

  The first buffer in the frame should have the bit set automatically. */
  if( xTxDescriptors[ uxNextBufferToClear ].U_Status.status & AVR32_TRANSMIT_OK )
  {
    /* Loop through the other buffers in the frame. */
    while( !( xTxDescriptors[ uxNextBufferToClear ].U_Status.status & AVR32_LAST_BUFFER ) )
    {
      uxNextBufferToClear++;

      if( uxNextBufferToClear >= NB_TX_BUFFERS )
      {
        uxNextBufferToClear = 0;
      }

      xTxDescriptors[ uxNextBufferToClear ].U_Status.status |= AVR32_TRANSMIT_OK;
    }

    /* Start with the next buffer the next time a Tx interrupt is called. */
    uxNextBufferToClear++;

    /* Do we need to wrap back to the first buffer? */
    if( uxNextBufferToClear >= NB_TX_BUFFERS )
    {
      uxNextBufferToClear = 0;
    }
  }
}
/*-----------------------------------------------------------*/

static void prvSetupDescriptors(void)
{
unsigned portBASE_TYPE xIndex;
unsigned portLONG ulAddress;

  /* Initialise xRxDescriptors descriptor. */
  for( xIndex = 0; xIndex < NB_RX_BUFFERS; ++xIndex )
  {
    /* Calculate the address of the nth buffer within the array. */
    ulAddress = ( unsigned portLONG )( pcRxBuffer + ( xIndex * ETH_RX_BUFFER_SIZE ) );

    /* Write the buffer address into the descriptor.  The DMA will place
    the data at this address when this descriptor is being used.  Mask off
    the bottom bits of the address as these have special meaning. */
    xRxDescriptors[ xIndex ].addr = ulAddress & emacADDRESS_MASK;
  }

  /* The last buffer has the wrap bit set so the EMAC knows to wrap back
  to the first buffer. */
  xRxDescriptors[ NB_RX_BUFFERS - 1 ].addr |= emacRX_WRAP_BIT;

  /* Initialise xTxDescriptors. */
  for( xIndex = 0; xIndex < NB_TX_BUFFERS; ++xIndex )
  {
    /* Calculate the address of the nth buffer within the array. */
    ulAddress = ( unsigned portLONG )( pcTxBuffer + ( xIndex * ETH_TX_BUFFER_SIZE ) );

    /* Write the buffer address into the descriptor.  The DMA will read
    data from here when the descriptor is being used. */
    xTxDescriptors[ xIndex ].addr = ulAddress & emacADDRESS_MASK;
    xTxDescriptors[ xIndex ].U_Status.status = AVR32_TRANSMIT_OK;
  }

  /* The last buffer has the wrap bit set so the EMAC knows to wrap back
  to the first buffer. */
  xTxDescriptors[ NB_TX_BUFFERS - 1 ].U_Status.status = AVR32_TRANSMIT_WRAP | AVR32_TRANSMIT_OK;

  /* Tell the EMAC where to find the descriptors. */
  AVR32_MACB.rbqp =   ( unsigned portLONG )xRxDescriptors;
  AVR32_MACB.tbqp =   ( unsigned portLONG )xTxDescriptors;

  /* Enable the copy of data into the buffers, ignore broadcasts,
  and don't copy FCS. */
  AVR32_MACB.ncfgr |= (AVR32_MACB_CAF_MASK |  AVR32_MACB_NBC_MASK | AVR32_MACB_NCFGR_DRFCS_MASK);

} 
/*-----------------------------------------------------------*/

static void prvSetupMACAddress( void )
{
  /* Must be written SA1L then SA1H. */
  AVR32_MACB.sa1b =  ( ( unsigned portLONG ) cMACAddress[ 3 ] << 24 ) |
                     ( ( unsigned portLONG ) cMACAddress[ 2 ] << 16 ) |
                     ( ( unsigned portLONG ) cMACAddress[ 1 ] << 8  ) |
                                             cMACAddress[ 0 ];

  AVR32_MACB.sa1t =  ( ( unsigned portLONG ) cMACAddress[ 5 ] << 8 ) |
                                             cMACAddress[ 4 ];
}
/*-----------------------------------------------------------*/

static void prvSetupEMACInterrupt( void )
{
  /* Create the semaphore used to trigger the EMAC task. */
  if (xSemaphore == NULL)
  {
    vSemaphoreCreateBinary( xSemaphore );
  }

  if( xSemaphore )
  {
    /* We start by 'taking' the semaphore so the ISR can 'give' it when the
    first interrupt occurs. */
    xSemaphoreTake( xSemaphore, emacNO_DELAY );
    portENTER_CRITICAL();
    {
    /* Setup the interrupt for USART0.
       Register the USART0 interrupt handler to the interrupt controller
       at interrupt level 2. */
    INTC_register_interrupt(&vEMAC_ISR, AVR32_MACB_IRQ, INT2);

    /* We want to interrupt on Rx and Tx events. */
    AVR32_MACB.ier = AVR32_MACB_IER_RCOMP_MASK | AVR32_MACB_IER_TCOMP_MASK;
    }
    portEXIT_CRITICAL();
  }
}

/*
 * The following functions are initialisation functions taken from the Atmel
 * EMAC sample code.
 */
static portBASE_TYPE prvProbePHY( void )
{
unsigned long mii_status, advertise, lpa, phy_ctrl;
unsigned long config;
unsigned long upper, lower,mode;
unsigned long physID;

  /* Read Phy Identifier register 1 & 2 */
  lower = vReadPHY(PHY_PHYSID2);
  upper = vReadPHY(PHY_PHYSID1);
  /* get Phy ID, ignore Revision */
  physID = ((upper << 16) & 0xFFFF0000) | (lower & 0xFFF0);
  /* check if it match config */
  if (physID == MII_DP83848_ID)
  {
    /* read RBR */
    mode = vReadPHY(PHY_RBR);
    /* set RMII mode if not done */
    if ((mode & RBR_RMII) != RBR_RMII)
    {
      /* force RMII flag if strap options are wrong */
      mode |= RBR_RMII;
    vWritePHY(PHY_RBR,mode);
    }

    /* set advertise register */
#if ETHERNET_CONF_AN_ENABLE == 1
    advertise = ADVERTISE_CSMA | ADVERTISE_ALL;
#else
    advertise = ADVERTISE_CSMA;
    #if ETHERNET_CONF_USE_100MB
      #if ETHERNET_CONF_USE_FULL_DUPLEX
        advertise |= ADVERTISE_100FULL;
      #else
        advertise |= ADVERTISE_100HALF;
      #endif
    #else
      #if ETHERNET_CONF_USE_FULL_DUPLEX
        advertise |= ADVERTISE_10FULL;
      #else
        advertise |= ADVERTISE_10HALF;
      #endif
    #endif
#endif
    /* write advertise register */
    vWritePHY(PHY_ADVERTISE, advertise);
    /* read Control register */
    config = vReadPHY(PHY_BMCR);
    /* read Phy Control register */
    phy_ctrl = vReadPHY(PHY_PHYCR);
#if ETHERNET_CONF_AN_ENABLE
  #if ETHERNET_CONF_AUTO_CROSS_ENABLE
    /* enable Auto MDIX */
    phy_ctrl |= PHYCR_MDIX_EN;
  #else
    /* disable Auto MDIX */
    phy_ctrl &= ~PHYCR_MDIX_EN;
    #if ETHERNET_CONF_CROSSED_LINK
      /* force direct link = Use crossed RJ45 cable */
      phy_ctrl &= ~PHYCR_MDIX_FORCE;
    #else
      /* force crossed link = Use direct RJ45 cable */
      phy_ctrl |= PHYCR_MDIX_FORCE;
    #endif
  #endif
  /* reset auto-negociation capability */
  config |= (BMCR_ANRESTART | BMCR_ANENABLE);
#else
  /* disable Auto MDIX */
  phy_ctrl &= ~PHYCR_MDIX_EN;
  #if ETHERNET_CONF_CROSSED_LINK
    /* force direct link = Use crossed RJ45 cable */
    phy_ctrl &= ~PHYCR_MDIX_FORCE;
  #else
    /* force crossed link = Use direct RJ45 cable */
    phy_ctrl |= PHYCR_MDIX_FORCE;
  #endif
  /* clear AN bit */
  config &= ~BMCR_ANENABLE;

  #if ETHERNET_CONF_USE_100MB
    config |= BMCR_SPEED100;
  #else
    config &= ~BMCR_SPEED100;
  #endif
  #if ETHERNET_CONF_USE_FULL_DUPLEX
    config |= BMCR_FULLDPLX;
  #else
    config &= ~BMCR_FULLDPLX;
  #endif
#endif
    /* update Phy ctrl register */
    vWritePHY(PHY_PHYCR, phy_ctrl);

    /* update ctrl register */
    vWritePHY(PHY_BMCR, config);

    /* loop while link status isn't OK */
    do {
      mii_status = vReadPHY(PHY_BMSR);
    } while (!(mii_status & BMSR_LSTATUS));

    /* read the LPA configuration of the PHY */
    lpa = vReadPHY(PHY_LPA);

    /* read the MACB config register */
    config = AVR32_MACB.ncfgr;

    /* if 100MB needed */
    if ((lpa & advertise) & (LPA_100HALF | LPA_100FULL))
    {
      config |= AVR32_MACB_SPD_MASK;
    }
    else
    {
      config &= ~(AVR32_MACB_SPD_MASK);
    }

    /* if FULL DUPLEX needed */
    if ((lpa & advertise) & (LPA_10FULL | LPA_100FULL))
    {
      config |= AVR32_MACB_FD_MASK;
    }
    else
    {
      config &= ~(AVR32_MACB_FD_MASK);
    }

    /* write the MACB config register */
    AVR32_MACB.ncfgr = config;

    return pdPASS;
  }
  return pdFAIL;
}

static unsigned portLONG vReadPHY( unsigned portCHAR ucAddress )
{
 unsigned portLONG pulValue;

  /* Enable management port */
  AVR32_MACB.ncr |= AVR32_MACB_NCR_MPE_MASK;

  /* configure MDIO frame in MAN register */
  AVR32_MACB.man =  (AVR32_MACB_SOF_MASK & (0x01<<AVR32_MACB_SOF_OFFSET))  // SOF
                    | (2 << AVR32_MACB_CODE_OFFSET)                        // Code
                    | (2 << AVR32_MACB_RW_OFFSET)                          // Read operation
                    | ((DP83848_PHY_ADDR & 0x1f) << AVR32_MACB_PHYA_OFFSET)  // Phy Add
                    | (ucAddress << AVR32_MACB_REGA_OFFSET);               // Reg Add

  /* Wait until IDLE bit in Network Status register is cleared. */
  while( !( AVR32_MACB.nsr & AVR32_MACB_NSR_IDLE_MASK ) )
  {
    __asm( "NOP" );
  }

  pulValue = (AVR32_MACB.man  & 0x0000ffff );

  /* Disable management port */
  AVR32_MACB.ncr &= ~AVR32_MACB_NCR_MPE_MASK;

  return (pulValue);
}


static void vWritePHY( unsigned portCHAR ucAddress, unsigned portLONG ulValue )
{
  /* Enable management port */
  AVR32_MACB.ncr |= AVR32_MACB_NCR_MPE_MASK;

  /* configure MDIO frame in MAN register */
  AVR32_MACB.man = (( AVR32_MACB_SOF_MASK & (0x01<<AVR32_MACB_SOF_OFFSET)) // SOF
                  | (2 << AVR32_MACB_CODE_OFFSET)                          // Code
                  | (1 << AVR32_MACB_RW_OFFSET)                            // Write operation
                  | ((DP83848_PHY_ADDR & 0x1f) << AVR32_MACB_PHYA_OFFSET)    // Phy Add
                  | (ucAddress << AVR32_MACB_REGA_OFFSET))                 // Reg Add
                  | (ulValue & 0xffff);                                    // Data

  /* Wait until IDLE bit in Network Status register is cleared */
  while( !( AVR32_MACB.nsr & AVR32_MACB_NSR_IDLE_MASK ) )
  {
    __asm( "NOP" );
  };

  /* Disable management port */
  AVR32_MACB.ncr &= ~AVR32_MACB_NCR_MPE_MASK;

}

void vEMACWaitForInput( void )
{
  /* Just wait until we are signled from an ISR that data is available, or
  we simply time out. */
  xSemaphoreTake( xSemaphore, emacBLOCK_TIME_WAITING_FOR_INPUT );
}
