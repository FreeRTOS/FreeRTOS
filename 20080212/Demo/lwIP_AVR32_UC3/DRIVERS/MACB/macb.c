/*This file has been prepared for Doxygen automatic documentation generation.*/
/*! \file *********************************************************************
 *
 * \brief MACB driver for EVK1100 board.
 *
 * This file defines a useful set of functions for the MACB interface on
 * AVR32 devices.
 *
 * - Compiler:           IAR EWAVR32 and GNU GCC for AVR32
 * - Supported devices:  All AVR32 devices with a MACB module can be used.
 * - AppNote:
 *
 * \author               Atmel Corporation: http://www.atmel.com \n
 *                       Support and FAQ: http://support.atmel.no/
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


#include <stdio.h>
#include <string.h>
#include <avr32/io.h>


#ifdef FREERTOS_USED
  #include "FreeRTOS.h" 
  #include "task.h"
  #include "semphr.h"
#endif
#include "macb.h"
#include "gpio.h"
#include "conf_eth.h"
#include "intc.h"


/* Size of each receive buffer - DO NOT CHANGE. */
#define RX_BUFFER_SIZE    128


/* The buffer addresses written into the descriptors must be aligned so the
last few bits are zero.  These bits have special meaning for the MACB
peripheral and cannot be used as part of the address. */
#define ADDRESS_MASK      ( ( unsigned long ) 0xFFFFFFFC )

/* Bit used within the address stored in the descriptor to mark the last
descriptor in the array. */
#define RX_WRAP_BIT       ( ( unsigned long ) 0x02 )

/* A short delay is used to wait for a buffer to become available, should
one not be immediately available when trying to transmit a frame. */
#define BUFFER_WAIT_DELAY   ( 2 )

#ifndef FREERTOS_USED
#define portENTER_CRITICAL           Disable_global_interrupt 
#define portEXIT_CRITICAL            Enable_global_interrupt
#define portENTER_SWITCHING_ISR()  
#define portEXIT_SWITCHING_ISR()  
#endif 


/* Buffer written to by the MACB DMA.  Must be aligned as described by the
comment above the ADDRESS_MASK definition. */
#if __GNUC__
static volatile char pcRxBuffer[ ETHERNET_CONF_NB_RX_BUFFERS * RX_BUFFER_SIZE ] __attribute__ ((aligned (8)));
#elif __ICCAVR32__
#pragma data_alignment=8
static volatile char pcRxBuffer[ ETHERNET_CONF_NB_RX_BUFFERS * RX_BUFFER_SIZE ];
#endif


/* Buffer read by the MACB DMA.  Must be aligned as described by the comment
above the ADDRESS_MASK definition. */
#if __GNUC__
static volatile char pcTxBuffer[ ETHERNET_CONF_NB_TX_BUFFERS * ETHERNET_CONF_TX_BUFFER_SIZE ] __attribute__ ((aligned (8)));
#elif __ICCAVR32__
#pragma data_alignment=8
static volatile char pcTxBuffer[ ETHERNET_CONF_NB_TX_BUFFERS * ETHERNET_CONF_TX_BUFFER_SIZE ];
#endif

/* Descriptors used to communicate between the program and the MACB peripheral.
These descriptors hold the locations and state of the Rx and Tx buffers. */
static volatile AVR32_TxTdDescriptor xTxDescriptors[ ETHERNET_CONF_NB_TX_BUFFERS ];
static volatile AVR32_RxTdDescriptor xRxDescriptors[ ETHERNET_CONF_NB_RX_BUFFERS ];

/* The IP and Ethernet addresses are read from the header files. */
char cMACAddress[ 6 ] = { ETHERNET_CONF_ETHADDR0,ETHERNET_CONF_ETHADDR1,ETHERNET_CONF_ETHADDR2,ETHERNET_CONF_ETHADDR3,ETHERNET_CONF_ETHADDR4,ETHERNET_CONF_ETHADDR5 };

/*-----------------------------------------------------------*/

/* See the header file for descriptions of public functions. */

/*
 * Prototype for the MACB interrupt function - called by the asm wrapper.
 */
#ifdef FREERTOS_USED
#if __GNUC__
__attribute__((naked))
#elif __ICCAVR32__
#pragma shadow_registers = full   // Naked.
#endif
#else
#if __GNUC__
__attribute__((__interrupt__))
#elif __ICCAVR32__
__interrupt
#endif
#endif
void vMACB_ISR( void );
static long prvMACB_ISR_NonNakedBehaviour( void );


#if ETHERNET_CONF_USE_PHY_IT
#ifdef FREERTOS_USED
#if __GNUC__
__attribute__((naked))
#elif __ICCAVR32__
#pragma shadow_registers = full   // Naked.
#endif
#else
#if __GNUC__
__attribute__((__interrupt__))
#elif __ICCAVR32__
__interrupt
#endif
#endif
void vPHY_ISR( void );
static long prvPHY_ISR_NonNakedBehaviour( void );
#endif


/*
 * Initialise both the Tx and Rx descriptors used by the MACB.
 */
static void prvSetupDescriptors(volatile avr32_macb_t * macb);

/*
 * Write our MAC address into the MACB.  
 */
static void prvSetupMACAddress( volatile avr32_macb_t * macb );

/*
 * Configure the MACB for interrupts.
 */
static void prvSetupMACBInterrupt( volatile avr32_macb_t * macb );

/*
 * Some initialisation functions.
 */
static Bool prvProbePHY( volatile avr32_macb_t * macb );
static unsigned long ulReadMDIO(volatile avr32_macb_t * macb, unsigned short usAddress); 
static void vWriteMDIO(volatile avr32_macb_t * macb, unsigned short usAddress, unsigned short usValue);


#ifdef FREERTOS_USED
/* The semaphore used by the MACB ISR to wake the MACB task. */
static xSemaphoreHandle xSemaphore = NULL;
#else
static volatile Bool DataToRead = FALSE;
#endif

/* Holds the index to the next buffer from which data will be read. */
volatile unsigned long ulNextRxBuffer = 0;


long lMACBSend(volatile avr32_macb_t * macb, char *pcFrom, unsigned long ulLength, long lEndOfFrame )
{
static unsigned long uxTxBufferIndex = 0;
char *pcBuffer;
unsigned long ulLastBuffer, ulDataBuffered = 0, ulDataRemainingToSend, ulLengthToSend;


  /* If the length of data to be transmitted is greater than each individual
  transmit buffer then the data will be split into more than one buffer.
  Loop until the entire length has been buffered. */
  while( ulDataBuffered < ulLength )
  {
    // Is a buffer available ?
    while( !( xTxDescriptors[ uxTxBufferIndex ].U_Status.status & AVR32_TRANSMIT_OK ) )
    {
      // There is no room to write the Tx data to the Tx buffer.  
      // Wait a short while, then try again.
#ifdef FREERTOS_USED
      vTaskDelay( BUFFER_WAIT_DELAY );
#else
      __asm__ __volatile__ ("nop");      
#endif
    }
  
    portENTER_CRITICAL();
    {
      // Get the address of the buffer from the descriptor, 
      // then copy the data into the buffer.
      pcBuffer = ( char * ) xTxDescriptors[ uxTxBufferIndex ].addr;

      // How much can we write to the buffer ?
      ulDataRemainingToSend = ulLength - ulDataBuffered;
      if( ulDataRemainingToSend <= ETHERNET_CONF_TX_BUFFER_SIZE )
      {
        // We can write all the remaining bytes.
        ulLengthToSend = ulDataRemainingToSend;
      }
      else
      {
        // We can't write more than ETH_TX_BUFFER_SIZE in one go.
        ulLengthToSend = ETHERNET_CONF_TX_BUFFER_SIZE;
      }
      // Copy the data into the buffer.
      memcpy( ( void * ) pcBuffer, ( void * ) &( pcFrom[ ulDataBuffered ] ), ulLengthToSend );
      ulDataBuffered += ulLengthToSend;
      // Is this the last data for the frame ? 
      if( lEndOfFrame && ( ulDataBuffered >= ulLength ) )
      {
        // No more data remains for this frame so we can start the transmission.
        ulLastBuffer = AVR32_LAST_BUFFER;
      }
      else
      {
        // More data to come for this frame.
        ulLastBuffer = 0;
      }
      // Fill out the necessary in the descriptor to get the data sent,
      // then move to the next descriptor, wrapping if necessary.
      if( uxTxBufferIndex >= ( ETHERNET_CONF_NB_TX_BUFFERS - 1 ) )
      {
        xTxDescriptors[ uxTxBufferIndex ].U_Status.status =   ( ulLengthToSend & ( unsigned long ) AVR32_LENGTH_FRAME )
                                    | ulLastBuffer
                                    | AVR32_TRANSMIT_WRAP;
        uxTxBufferIndex = 0;
      }
      else
      {
        xTxDescriptors[ uxTxBufferIndex ].U_Status.status =   ( ulLengthToSend & ( unsigned long ) AVR32_LENGTH_FRAME )
                                    | ulLastBuffer;
        uxTxBufferIndex++;
      }
      /* If this is the last buffer to be sent for this frame we can
         start the transmission. */
      if( ulLastBuffer )
      {
        macb->ncr |=  AVR32_MACB_TSTART_MASK;
      }
    }
    portEXIT_CRITICAL();
  }

  return PASS;
}


unsigned long ulMACBInputLength( void )
{
register unsigned long ulIndex , ulLength = 0;
unsigned int uiTemp;

  // Skip any fragments.  We are looking for the first buffer that contains
  // data and has the SOF (start of frame) bit set.
  while( ( xRxDescriptors[ ulNextRxBuffer ].addr & AVR32_OWNERSHIP_BIT ) && !( xRxDescriptors[ ulNextRxBuffer ].U_Status.status & AVR32_SOF ) )
  {
    // Ignoring this buffer.  Mark it as free again.
    uiTemp = xRxDescriptors[ ulNextRxBuffer ].addr;
    xRxDescriptors[ ulNextRxBuffer ].addr = uiTemp & ~( AVR32_OWNERSHIP_BIT );
    ulNextRxBuffer++;
    if( ulNextRxBuffer >= ETHERNET_CONF_NB_RX_BUFFERS )
    {
      ulNextRxBuffer = 0;
    }
  }

  // We are going to walk through the descriptors that make up this frame,
  // but don't want to alter ulNextRxBuffer as this would prevent vMACBRead()
  // from finding the data.  Therefore use a copy of ulNextRxBuffer instead. 
  ulIndex = ulNextRxBuffer;

  // Walk through the descriptors until we find the last buffer for this frame.
  // The last buffer will give us the length of the entire frame.
  while( ( xRxDescriptors[ ulIndex ].addr & AVR32_OWNERSHIP_BIT ) && !ulLength )
  {
    ulLength = xRxDescriptors[ ulIndex ].U_Status.status & AVR32_LENGTH_FRAME;
    // Increment to the next buffer, wrapping if necessary.
    ulIndex++;
    if( ulIndex >= ETHERNET_CONF_NB_RX_BUFFERS )
    {
      ulIndex = 0;
    }
  }
  return ulLength;
}
/*-----------------------------------------------------------*/

void vMACBRead( char *pcTo, unsigned long ulSectionLength, unsigned long ulTotalFrameLength )
{
static unsigned long ulSectionBytesReadSoFar = 0, ulBufferPosition = 0, ulFameBytesReadSoFar = 0;
static char *pcSource;
register unsigned long ulBytesRemainingInBuffer, ulRemainingSectionBytes;
unsigned int uiTemp;

  // Read ulSectionLength bytes from the Rx buffers. 
  // This is not necessarily any correspondence between the length of our Rx buffers, 
  // and the length of the data we are returning or the length of the data being requested.
  // Therefore, between calls  we have to remember not only which buffer we are currently
  // processing, but our position within that buffer.  
  // This would be greatly simplified if PBUF_POOL_BUFSIZE could be guaranteed to be greater 
  // than the size of each Rx buffer, and that memory fragmentation did not occur.
  
  // This function should only be called after a call to ulMACBInputLength().
  // This will ensure ulNextRxBuffer is set to the correct buffer. */

  // vMACBRead is called with pcTo set to NULL to indicate that we are about
  // to read a new frame.  Any fragments remaining in the frame we were
  // processing during the last call should be dropped.
  if( pcTo == NULL )
  {
    // How many bytes are indicated as being in this buffer?  
    // If none then the buffer is completely full and the frame is contained within more
    // than one buffer.
    // Reset our state variables ready for the next read from this buffer.
    pcSource = ( char * )( xRxDescriptors[ ulNextRxBuffer ].addr & ADDRESS_MASK );
    ulFameBytesReadSoFar = ( unsigned long ) 0;
    ulBufferPosition = ( unsigned long ) 0;
  }
  else
  {
    // Loop until we have obtained the required amount of data.
    ulSectionBytesReadSoFar = 0;
    while( ulSectionBytesReadSoFar < ulSectionLength )
    {
      // We may have already read some data from this buffer.
      // How much data remains in the buffer?
      ulBytesRemainingInBuffer = ( RX_BUFFER_SIZE - ulBufferPosition );

      // How many more bytes do we need to read before we have the
      // required amount of data?
      ulRemainingSectionBytes = ulSectionLength - ulSectionBytesReadSoFar;

      // Do we want more data than remains in the buffer? 
      if( ulRemainingSectionBytes > ulBytesRemainingInBuffer )
      {
        // We want more data than remains in the buffer so we can
        // write the remains of the buffer to the destination, then move
        // onto the next buffer to get the rest.
        memcpy( &( pcTo[ ulSectionBytesReadSoFar ] ), &( pcSource[ ulBufferPosition ] ), ulBytesRemainingInBuffer );
        ulSectionBytesReadSoFar += ulBytesRemainingInBuffer;
        ulFameBytesReadSoFar += ulBytesRemainingInBuffer;

        // Mark the buffer as free again.
        uiTemp = xRxDescriptors[ ulNextRxBuffer ].addr;
        xRxDescriptors[ ulNextRxBuffer ].addr = uiTemp & ~( AVR32_OWNERSHIP_BIT );
        // Move onto the next buffer.
        ulNextRxBuffer++;
       
        if( ulNextRxBuffer >= ETHERNET_CONF_NB_RX_BUFFERS )
        {
          ulNextRxBuffer = ( unsigned long ) 0;
        }
      
        // Reset the variables for the new buffer.
        pcSource = ( char * )( xRxDescriptors[ ulNextRxBuffer ].addr & ADDRESS_MASK );
        ulBufferPosition = ( unsigned long ) 0;
      }
      else
      {
        // We have enough data in this buffer to send back.
        // Read out enough data and remember how far we read up to.
        memcpy( &( pcTo[ ulSectionBytesReadSoFar ] ), &( pcSource[ ulBufferPosition ] ), ulRemainingSectionBytes );

        // There may be more data in this buffer yet.
        // Increment our position in this buffer past the data we have just read.
        ulBufferPosition += ulRemainingSectionBytes;
        ulSectionBytesReadSoFar += ulRemainingSectionBytes;
        ulFameBytesReadSoFar += ulRemainingSectionBytes;

        // Have we now finished with this buffer?
        if( ( ulBufferPosition >= RX_BUFFER_SIZE ) || ( ulFameBytesReadSoFar >= ulTotalFrameLength ) )
        {
          // Mark the buffer as free again.
          uiTemp = xRxDescriptors[ ulNextRxBuffer ].addr;
          xRxDescriptors[ ulNextRxBuffer ].addr = uiTemp & ~( AVR32_OWNERSHIP_BIT );
          // Move onto the next buffer.
          ulNextRxBuffer++;
         
          if( ulNextRxBuffer >= ETHERNET_CONF_NB_RX_BUFFERS )
          {
            ulNextRxBuffer = 0;
          }
       
          pcSource = ( char * )( xRxDescriptors[ ulNextRxBuffer ].addr & ADDRESS_MASK );
          ulBufferPosition = 0;
        }
      }
    }
  }
}
/*-----------------------------------------------------------*/
void vMACBSetMACAddress(const char * MACAddress)
{
  memcpy(cMACAddress, MACAddress, sizeof(cMACAddress));
}

Bool xMACBInit( volatile avr32_macb_t * macb )
{
volatile unsigned long status;

  // set up registers
  macb->ncr = 0;
  macb->tsr = ~0UL;
  macb->rsr = ~0UL;
  macb->idr = ~0UL;
  status = macb->isr;


#if ETHERNET_CONF_USE_RMII_INTERFACE
  // RMII used, set 0 to the USRIO Register
  macb->usrio &= ~AVR32_MACB_RMII_MASK;
#else
  // RMII not used, set 1 to the USRIO Register
  macb->usrio |= AVR32_MACB_RMII_MASK;
#endif

  // Load our MAC address into the MACB. 
  prvSetupMACAddress(macb);

  // Setup the buffers and descriptors.
  prvSetupDescriptors(macb);

#if ETHERNET_CONF_SYSTEM_CLOCK <= 20000000
  macb->ncfgr |= (AVR32_MACB_NCFGR_CLK_DIV8 << AVR32_MACB_NCFGR_CLK_OFFSET);
#elif ETHERNET_CONF_SYSTEM_CLOCK <= 40000000
  macb->ncfgr |= (AVR32_MACB_NCFGR_CLK_DIV16 << AVR32_MACB_NCFGR_CLK_OFFSET);
#elif ETHERNET_CONF_SYSTEM_CLOCK <= 80000000
  macb->ncfgr |= AVR32_MACB_NCFGR_CLK_DIV32 << AVR32_MACB_NCFGR_CLK_OFFSET;
#elif ETHERNET_CONF_SYSTEM_CLOCK <= 160000000
  macb->ncfgr |= AVR32_MACB_NCFGR_CLK_DIV64 << AVR32_MACB_NCFGR_CLK_OFFSET;
#else
# error System clock too fast
#endif

  // Are we connected?
  if( prvProbePHY(macb) == TRUE )
  {
    // Enable the interrupt!
    portENTER_CRITICAL();
    {
      prvSetupMACBInterrupt(macb);
    }
    portEXIT_CRITICAL();
    // Enable Rx and Tx, plus the stats register.
    macb->ncr = AVR32_MACB_NCR_TE_MASK | AVR32_MACB_NCR_RE_MASK;
    return (TRUE);
  }
  return (FALSE);
}

void vDisableMACBOperations(volatile avr32_macb_t * macb)
{
#if ETHERNET_CONF_USE_PHY_IT
volatile avr32_gpio_t *gpio = &AVR32_GPIO;
volatile avr32_gpio_port_t *gpio_port = &gpio->port[MACB_INTERRUPT_PIN/32];

  gpio_port->ierc =  1 << (MACB_INTERRUPT_PIN%32);
#endif

  // write the MACB control register : disable Tx & Rx
  macb->ncr &= ~((1 << AVR32_MACB_RE_OFFSET) | (1 << AVR32_MACB_TE_OFFSET));
  // We no more want to interrupt on Rx and Tx events.
  macb->idr = AVR32_MACB_IER_RCOMP_MASK | AVR32_MACB_IER_TCOMP_MASK;
}


void vClearMACBTxBuffer( void )
{
static unsigned long uxNextBufferToClear = 0;

  // Called on Tx interrupt events to set the AVR32_TRANSMIT_OK bit in each
  // Tx buffer within the frame just transmitted.  This marks all the buffers
  // as available again.

  // The first buffer in the frame should have the bit set automatically. */
  if( xTxDescriptors[ uxNextBufferToClear ].U_Status.status & AVR32_TRANSMIT_OK )
  {
    // Loop through the other buffers in the frame.
    while( !( xTxDescriptors[ uxNextBufferToClear ].U_Status.status & AVR32_LAST_BUFFER ) )
    {
      uxNextBufferToClear++;

      if( uxNextBufferToClear >= ETHERNET_CONF_NB_TX_BUFFERS )
      {
        uxNextBufferToClear = 0;
      }

      xTxDescriptors[ uxNextBufferToClear ].U_Status.status |= AVR32_TRANSMIT_OK;
    }

    // Start with the next buffer the next time a Tx interrupt is called.
    uxNextBufferToClear++;

    // Do we need to wrap back to the first buffer? 
    if( uxNextBufferToClear >= ETHERNET_CONF_NB_TX_BUFFERS )
    {
      uxNextBufferToClear = 0;
    }
  }
}

static void prvSetupDescriptors(volatile avr32_macb_t * macb)
{
unsigned long xIndex;
unsigned long ulAddress;

  // Initialise xRxDescriptors descriptor.
  for( xIndex = 0; xIndex < ETHERNET_CONF_NB_RX_BUFFERS; ++xIndex )
  {
    // Calculate the address of the nth buffer within the array.
    ulAddress = ( unsigned long )( pcRxBuffer + ( xIndex * RX_BUFFER_SIZE ) );

    // Write the buffer address into the descriptor.  
    // The DMA will place the data at this address when this descriptor is being used.
    // Mask off the bottom bits of the address as these have special meaning.
    xRxDescriptors[ xIndex ].addr = ulAddress & ADDRESS_MASK;
  }

  // The last buffer has the wrap bit set so the MACB knows to wrap back
  // to the first buffer.
  xRxDescriptors[ ETHERNET_CONF_NB_RX_BUFFERS - 1 ].addr |= RX_WRAP_BIT;

  // Initialise xTxDescriptors.
  for( xIndex = 0; xIndex < ETHERNET_CONF_NB_TX_BUFFERS; ++xIndex )
  {
    // Calculate the address of the nth buffer within the array.
    ulAddress = ( unsigned long )( pcTxBuffer + ( xIndex * ETHERNET_CONF_TX_BUFFER_SIZE ) );

    // Write the buffer address into the descriptor.  
    // The DMA will read data from here when the descriptor is being used.
    xTxDescriptors[ xIndex ].addr = ulAddress & ADDRESS_MASK;
    xTxDescriptors[ xIndex ].U_Status.status = AVR32_TRANSMIT_OK;
  }

  // The last buffer has the wrap bit set so the MACB knows to wrap back
  // to the first buffer.
  xTxDescriptors[ ETHERNET_CONF_NB_TX_BUFFERS - 1 ].U_Status.status = AVR32_TRANSMIT_WRAP | AVR32_TRANSMIT_OK;

  // Tell the MACB where to find the descriptors.
  macb->rbqp =   ( unsigned long )xRxDescriptors;
  macb->tbqp =   ( unsigned long )xTxDescriptors;

  // Enable the copy of data into the buffers, ignore broadcasts,
  // and don't copy FCS.
  macb->ncfgr |= (AVR32_MACB_CAF_MASK |  AVR32_MACB_NBC_MASK | AVR32_MACB_NCFGR_DRFCS_MASK);

} 

static void prvSetupMACAddress( volatile avr32_macb_t * macb )
{
  // Must be written SA1L then SA1H.
  macb->sa1b =  ( ( unsigned long ) cMACAddress[ 3 ] << 24 ) |
                ( ( unsigned long ) cMACAddress[ 2 ] << 16 ) |
                ( ( unsigned long ) cMACAddress[ 1 ] << 8  ) |
                                    cMACAddress[ 0 ];

  macb->sa1t =  ( ( unsigned long ) cMACAddress[ 5 ] << 8 ) |
                                    cMACAddress[ 4 ];
}

static void prvSetupMACBInterrupt( volatile avr32_macb_t * macb )
{
#ifdef FREERTOS_USED
  // Create the semaphore used to trigger the MACB task. 
  if (xSemaphore == NULL)
  {
    vSemaphoreCreateBinary( xSemaphore );
  }
#else 
  // Create the flag used to trigger the MACB polling task. 
  DataToRead = FALSE;
#endif


#ifdef FREERTOS_USED
  if( xSemaphore != NULL)
  {
    // We start by 'taking' the semaphore so the ISR can 'give' it when the
    // first interrupt occurs.
    xSemaphoreTake( xSemaphore, 0 );
#endif
    // Setup the interrupt for MACB.
    // Register the interrupt handler to the interrupt controller at interrupt level 2
    INTC_register_interrupt((__int_handler)&vMACB_ISR, AVR32_MACB_IRQ, INT2);

#if ETHERNET_CONF_USE_PHY_IT
    /* GPIO enable interrupt upon rising edge */
    gpio_enable_pin_interrupt(MACB_INTERRUPT_PIN, GPIO_FALLING_EDGE);
    // Setup the interrupt for PHY.
    // Register the interrupt handler to the interrupt controller at interrupt level 2
    INTC_register_interrupt((__int_handler)&vPHY_ISR, (AVR32_GPIO_IRQ_0 + (MACB_INTERRUPT_PIN/8)), INT2);
    /* enable interrupts on INT pin */
    vWriteMDIO( macb, PHY_MICR , ( MICR_INTEN | MICR_INTOE ));
    /* enable "link change" interrupt for Phy */
    vWriteMDIO( macb, PHY_MISR , MISR_LINK_INT_EN );
#endif

    // We want to interrupt on Rx and Tx events
    macb->ier = AVR32_MACB_IER_RCOMP_MASK | AVR32_MACB_IER_TCOMP_MASK;
#ifdef FREERTOS_USED
  }
#endif
}

/*! Read a register on MDIO bus (access to the PHY)
 *         This function is looping until PHY gets ready
 *
 * \param macb         Input. instance of the MACB to use
 * \param usAddress    Input. register to set.
 *
 * \return unsigned long data that has been read
 */
static unsigned long ulReadMDIO(volatile avr32_macb_t * macb, unsigned short usAddress)
{
unsigned long value, status;

  // initiate transaction : enable management port
  macb->ncr |= AVR32_MACB_NCR_MPE_MASK;
  // Write the PHY configuration frame to the MAN register
  macb->man = (AVR32_MACB_SOF_MASK & (0x01<<AVR32_MACB_SOF_OFFSET))  // SOF
            | (2 << AVR32_MACB_CODE_OFFSET)                          // Code
            | (2 << AVR32_MACB_RW_OFFSET)                            // Read operation
            | ((ETHERNET_CONF_PHY_ADDR & 0x1f) << AVR32_MACB_PHYA_OFFSET)  // Phy Add
            | (usAddress << AVR32_MACB_REGA_OFFSET);                 // Reg Add
  // wait for PHY to be ready
  do {
    status = macb->nsr;
  } while (!(status & AVR32_MACB_NSR_IDLE_MASK));
  // read the register value in maintenance register
  value = macb->man & 0x0000ffff;
  // disable management port
  macb->ncr &= ~AVR32_MACB_NCR_MPE_MASK;
  // return the read value
  return (value);
}

/*! Write a given value to a register on MDIO bus (access to the PHY)
 *         This function is looping until PHY gets ready
 *
 * \param *macb        Input. instance of the MACB to use
 * \param usAddress    Input. register to set.
 * \param usValue      Input. value to write.
 *
 */
static void vWriteMDIO(volatile avr32_macb_t * macb, unsigned short usAddress, unsigned short usValue)
{
unsigned long status;

  // initiate transaction : enable management port
  macb->ncr |= AVR32_MACB_NCR_MPE_MASK;
  // Write the PHY configuration frame to the MAN register
  macb->man = (( AVR32_MACB_SOF_MASK & (0x01<<AVR32_MACB_SOF_OFFSET)) // SOF
             | (2 << AVR32_MACB_CODE_OFFSET)                          // Code
             | (1 << AVR32_MACB_RW_OFFSET)                            // Write operation
             | ((ETHERNET_CONF_PHY_ADDR & 0x1f) << AVR32_MACB_PHYA_OFFSET)  // Phy Add
             | (usAddress << AVR32_MACB_REGA_OFFSET))                 // Reg Add
             | (usValue & 0xffff);                                    // Data
  // wait for PHY to be ready
  do {
    status = macb->nsr;
  } while (!(status & AVR32_MACB_NSR_IDLE_MASK));
  // disable management port
  macb->ncr &= ~AVR32_MACB_NCR_MPE_MASK;
}

static Bool prvProbePHY( volatile avr32_macb_t * macb )
{
volatile unsigned long mii_status, phy_ctrl;
volatile unsigned long config;
unsigned long upper, lower, mode, advertise, lpa;
volatile unsigned long physID;

  // Read Phy Identifier register 1 & 2
  lower = ulReadMDIO(macb, PHY_PHYSID2);
  upper = ulReadMDIO(macb, PHY_PHYSID1);
  // get Phy ID, ignore Revision
  physID = ((upper << 16) & 0xFFFF0000) | (lower & 0xFFF0);
  // check if it match config
  if (physID == ETHERNET_CONF_PHY_ID)
  {
    // read RBR
    mode = ulReadMDIO(macb, PHY_RBR);
    // set RMII mode if not done
    if ((mode & RBR_RMII) != RBR_RMII)
    {
      // force RMII flag if strap options are wrong
      mode |= RBR_RMII;
      vWriteMDIO(macb, PHY_RBR, mode);
    }

    // set advertise register
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
    // write advertise register
    vWriteMDIO(macb, PHY_ADVERTISE, advertise);
    // read Control register
    config = ulReadMDIO(macb, PHY_BMCR);
    // read Phy Control register
    phy_ctrl = ulReadMDIO(macb, PHY_PHYCR);
#if ETHERNET_CONF_AN_ENABLE
  #if ETHERNET_CONF_AUTO_CROSS_ENABLE
    // enable Auto MDIX
    phy_ctrl |= PHYCR_MDIX_EN;
  #else
    // disable Auto MDIX
    phy_ctrl &= ~PHYCR_MDIX_EN;
    #if ETHERNET_CONF_CROSSED_LINK
      // force direct link = Use crossed RJ45 cable
      phy_ctrl &= ~PHYCR_MDIX_FORCE;
    #else
      // force crossed link = Use direct RJ45 cable
      phy_ctrl |= PHYCR_MDIX_FORCE;
    #endif
  #endif
  // reset auto-negociation capability
  config |= (BMCR_ANRESTART | BMCR_ANENABLE);
#else
  // disable Auto MDIX
  phy_ctrl &= ~PHYCR_MDIX_EN;
  #if ETHERNET_CONF_CROSSED_LINK
    // force direct link = Use crossed RJ45 cable
    phy_ctrl &= ~PHYCR_MDIX_FORCE;
  #else
    // force crossed link = Use direct RJ45 cable
    phy_ctrl |= PHYCR_MDIX_FORCE;
  #endif
  // clear AN bit
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
    // update Phy ctrl register
    vWriteMDIO(macb, PHY_PHYCR, phy_ctrl);

    // update ctrl register
    vWriteMDIO(macb, PHY_BMCR, config);

    // loop while link status isn't OK
    do {
      mii_status = ulReadMDIO(macb, PHY_BMSR);
    } while (!(mii_status & BMSR_LSTATUS));

    // read the LPA configuration of the PHY
    lpa = ulReadMDIO(macb, PHY_LPA);

    // read the MACB config register
    config = AVR32_MACB.ncfgr;

    // if 100MB needed
    if ((lpa & advertise) & (LPA_100HALF | LPA_100FULL))
    {
      config |= AVR32_MACB_SPD_MASK;
    }
    else
    {
      config &= ~(AVR32_MACB_SPD_MASK);
    }

    // if FULL DUPLEX needed
    if ((lpa & advertise) & (LPA_10FULL | LPA_100FULL))
    {
      config |= AVR32_MACB_FD_MASK;
    }
    else
    {
      config &= ~(AVR32_MACB_FD_MASK);
    }

    // write the MACB config register
    macb->ncfgr = config;

    return TRUE;
  }
  return FALSE;
}


void vMACBWaitForInput( unsigned long ulTimeOut )
{
#ifdef FREERTOS_USED
  // Just wait until we are signled from an ISR that data is available, or
  // we simply time out.
  xSemaphoreTake( xSemaphore, ulTimeOut );
#else
unsigned long i;
  gpio_clr_gpio_pin(LED0_GPIO);
  i = ulTimeOut * 1000;  
  // wait for an interrupt to occurs
  do
  {
    if ( DataToRead == TRUE )
    {
      // IT occurs, reset interrupt flag
      portENTER_CRITICAL();
      DataToRead = FALSE;    
      portEXIT_CRITICAL();
      break;	
    }
    i--;
  }
  while(i != 0);
  gpio_set_gpio_pin(LED0_GPIO);  
#endif
}


/*
 * The MACB ISR.  Handles both Tx and Rx complete interrupts.
 */
#ifdef FREERTOS_USED
#if __GNUC__
__attribute__((naked))
#elif __ICCAVR32__
#pragma shadow_registers = full   // Naked.
#endif
#else
#if __GNUC__
__attribute__((__interrupt__))
#elif __ICCAVR32__
__interrupt
#endif
#endif
void vMACB_ISR( void )
{
  // This ISR can cause a context switch, so the first statement must be a
  // call to the portENTER_SWITCHING_ISR() macro.  This must be BEFORE any
  // variable declarations. 
  portENTER_SWITCHING_ISR();

  // the return value is used by FreeRTOS to change the context if needed after rete instruction
  // in standalone use, this value should be ignored 
  prvMACB_ISR_NonNakedBehaviour();

  // Exit the ISR.  If a task was woken by either a character being received
  // or transmitted then a context switch will occur.
  portEXIT_SWITCHING_ISR();
}
/*-----------------------------------------------------------*/

#if __GNUC__
__attribute__((__noinline__))
#elif __ICCAVR32__
#pragma optimize = no_inline
#endif
static long prvMACB_ISR_NonNakedBehaviour( void )
{

  // Variable definitions can be made now.
  volatile unsigned long ulIntStatus, ulEventStatus;
  long xSwitchRequired = FALSE;

  // Find the cause of the interrupt.
  ulIntStatus = AVR32_MACB.isr;
  ulEventStatus = AVR32_MACB.rsr;

  if( ( ulIntStatus & AVR32_MACB_IDR_RCOMP_MASK ) || ( ulEventStatus & AVR32_MACB_REC_MASK ) )
  {
    // A frame has been received, signal the IP task so it can process
    // the Rx descriptors.
    portENTER_CRITICAL();
#ifdef FREERTOS_USED
    xSwitchRequired = xSemaphoreGiveFromISR( xSemaphore, FALSE );
#else
    DataToRead = TRUE;   
#endif      
    portEXIT_CRITICAL();
    AVR32_MACB.rsr =  AVR32_MACB_REC_MASK;
    AVR32_MACB.rsr;
  }

  if( ulIntStatus & AVR32_MACB_TCOMP_MASK )
  {
    // A frame has been transmitted.  Mark all the buffers used by the
    // frame just transmitted as free again.
    vClearMACBTxBuffer();
    AVR32_MACB.tsr =  AVR32_MACB_TSR_COMP_MASK;
    AVR32_MACB.tsr;
  }

  return ( xSwitchRequired );
}



#if ETHERNET_CONF_USE_PHY_IT
/*
 * The PHY ISR.  Handles Phy interrupts.
 */
#ifdef FREERTOS_USED
#if __GNUC__
__attribute__((naked))
#elif __ICCAVR32__
#pragma shadow_registers = full   // Naked.
#endif
#else
#if __GNUC__
__attribute__((__interrupt__))
#elif __ICCAVR32__
__interrupt
#endif
#endif
void vPHY_ISR( void )
{
  // This ISR can cause a context switch, so the first statement must be a
  // call to the portENTER_SWITCHING_ISR() macro.  This must be BEFORE any
  // variable declarations. 
  portENTER_SWITCHING_ISR();

  // the return value is used by FreeRTOS to change the context if needed after rete instruction
  // in standalone use, this value should be ignored 
  prvPHY_ISR_NonNakedBehaviour();

  // Exit the ISR.  If a task was woken by either a character being received
  // or transmitted then a context switch will occur.
  portEXIT_SWITCHING_ISR();
}
/*-----------------------------------------------------------*/

#if __GNUC__
__attribute__((__noinline__))
#elif __ICCAVR32__
#pragma optimize = no_inline
#endif
static long prvPHY_ISR_NonNakedBehaviour( void )
{

  // Variable definitions can be made now.
  volatile unsigned long ulIntStatus, ulEventStatus;
  long xSwitchRequired = FALSE;
  volatile avr32_gpio_t *gpio = &AVR32_GPIO;
  volatile avr32_gpio_port_t *gpio_port = &gpio->port[MACB_INTERRUPT_PIN/32];

  // read Phy Interrupt register Status
  ulIntStatus = ulReadMDIO(&AVR32_MACB, PHY_MISR);
  
  // read Phy status register
  ulEventStatus = ulReadMDIO(&AVR32_MACB, PHY_BMSR);
  // dummy read
  ulEventStatus = ulReadMDIO(&AVR32_MACB, PHY_BMSR);

   // clear interrupt flag on GPIO
  gpio_port->ifrc =  1 << (MACB_INTERRUPT_PIN%32);
  
  return ( xSwitchRequired );
}
#endif
