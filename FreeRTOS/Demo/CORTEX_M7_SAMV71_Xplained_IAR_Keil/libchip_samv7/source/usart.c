/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support 
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
 * \file
 *
 * Implementation of USART (Universal Synchronous Asynchronous Receiver Transmitter)
 * controller.
 *
 */
/*------------------------------------------------------------------------------
 *         Headers
 *------------------------------------------------------------------------------*/
#include "chip.h"

#include <assert.h>
#include <string.h>

/*----------------------------------------------------------------------------
 *        Local definitions
 *----------------------------------------------------------------------------*/


/*------------------------------------------------------------------------------
 *         Exported functions
 *------------------------------------------------------------------------------*/

/**
 * \brief Configures an USART peripheral with the specified parameters.
 *
 *
 *  \param usart  Pointer to the USART peripheral to configure.
 *  \param mode  Desired value for the USART mode register (see the datasheet).
 *  \param baudrate  Baudrate at which the USART should operate (in Hz).
 *  \param masterClock  Frequency of the system master clock (in Hz).
 */
void USART_Configure(Usart *pUsart,
                            uint32_t mode,
                            uint32_t baudrate,
                            uint32_t masterClock)
{
  
   unsigned int CD, FP, BaudError, OVER, ActualBaudRate;
  
    /* Reset and disable receiver & transmitter*/
    pUsart->US_CR = US_CR_RSTRX | US_CR_RSTTX
                  | US_CR_RXDIS | US_CR_TXDIS | US_CR_RSTSTA;
    
    pUsart->US_IDR = 0xFFFFFFFF;
    
    /* Configure baudrate*/  
    BaudError = 10;
    OVER = 0;
    
    // Configure baud rate
    while (BaudError > 5)
    {
      
      CD = (masterClock / (baudrate * 8*(2-OVER)));
      FP = ((masterClock / (baudrate * (2-OVER)) ) - CD * 8);     
      ActualBaudRate = (masterClock/(CD*8 + FP))/(2-OVER);
      BaudError = (100-((baudrate*100/ActualBaudRate)));
        
      if (BaudError > 5)
      {
        OVER++;
        if(OVER>=2)
        {
          assert( 0 ) ;
        }
      }
    }
    
    pUsart->US_BRGR = ( US_BRGR_CD(CD) | US_BRGR_FP(FP));
    
    /* Configure mode*/
    pUsart->US_MR = (mode |  (OVER << 19) );

    // Enable receiver and transmitter
    pUsart->US_CR = US_CR_RXEN | US_CR_TXEN;
    

    /* Disable buffering for printf(). */
#if ( defined (__GNUC__) && !defined (__SAMBA__) )
        setvbuf(stdout, (char *)NULL, _IONBF, 0);
#endif

}
/**
 * \brief Enables or disables the transmitter of an USART peripheral.
 *
 *
 * \param usart  Pointer to an USART peripheral
 * \param enabled  If true, the transmitter is enabled; otherwise it is
 *                disabled.
 */
void USART_SetTransmitterEnabled(Usart *usart, uint8_t enabled)
{
    if (enabled) {

        usart->US_CR = US_CR_TXEN;
    }
    else {

        usart->US_CR = US_CR_TXDIS;
    }
}

/**
 * \brief Enables or disables the receiver of an USART peripheral
 *
 *
 * \param usart  Pointer to an USART peripheral
 * \param enabled  If true, the receiver is enabled; otherwise it is disabled.
 */
void USART_SetReceiverEnabled(Usart *usart, uint8_t enabled)
{
    if (enabled) {

        usart->US_CR = US_CR_RXEN;
    }
    else {

        usart->US_CR = US_CR_RXDIS;
    }
}

/**
 * \brief Enables or disables the Request To Send (RTS) of an USART peripheral
 *
 *
 * \param usart  Pointer to an USART peripheral
 * \param enabled  If true, the RTS is enabled (0); otherwise it is disabled.
 */
void USART_SetRTSEnabled( Usart *usart, uint8_t enabled)
{
    if (enabled) {
    
        usart->US_CR = US_CR_RTSEN;
    }
    else {
        
        usart->US_CR = US_CR_RTSDIS;
    }
}

/**
 * \brief Sends one packet of data through the specified USART peripheral. This
 * function operates synchronously, so it only returns when the data has been
 * actually sent.
 *
 *
 * \param usart  Pointer to an USART peripheral.
 * \param data  Data to send including 9nth bit and sync field if necessary (in
 *        the same format as the US_THR register in the datasheet).
 * \param timeOut  Time out value (0 = no timeout).
 */
void USART_Write( Usart *usart, uint16_t data, volatile uint32_t timeOut)
{
    if (timeOut == 0) {

        while ((usart->US_CSR & US_CSR_TXEMPTY) == 0);
    }
    else {

        while ((usart->US_CSR & US_CSR_TXEMPTY) == 0) {

            if (timeOut == 0) {

                TRACE_ERROR("USART_Write: Timed out.\n\r");
                return;
            }
            timeOut--;
        }
    }

    usart->US_THR = data;
}


/**
 * \brief  Reads and return a packet of data on the specified USART peripheral. This
 * function operates asynchronously, so it waits until some data has been
 * received.
 *
 * \param usart  Pointer to an USART peripheral.
 * \param timeOut  Time out value (0 -> no timeout).
 */
uint16_t USART_Read( Usart *usart, volatile uint32_t timeOut)
{
    if (timeOut == 0) {

        while ((usart->US_CSR & US_CSR_RXRDY) == 0);
    }
    else {

        while ((usart->US_CSR & US_CSR_RXRDY) == 0) {

            if (timeOut == 0) {

                TRACE_ERROR( "USART_Read: Timed out.\n\r" ) ;
                return 0;
            }
            timeOut--;
        }
    }

    return usart->US_RHR;
}

/**
 * \brief  Returns 1 if some data has been received and can be read from an USART;
 * otherwise returns 0.
 *
 * \param usart  Pointer to an Usart instance.
 */
uint8_t USART_IsDataAvailable(Usart *usart)
{
    if ((usart->US_CSR & US_CSR_RXRDY) != 0) {

        return 1;
    }
    else {

        return 0;
    }
}

/**
 * \brief  Sets the filter value for the IRDA demodulator.
 *
 * \param pUsart  Pointer to an Usart instance.
 * \param filter  Filter value.
 */
void USART_SetIrdaFilter(Usart *pUsart, uint8_t filter)
{
    assert( pUsart != NULL ) ;

    pUsart->US_IF = filter;
}

/**
 * \brief  Sends one packet of data through the specified USART peripheral. This
 * function operates synchronously, so it only returns when the data has been
 * actually sent.
 *
 * \param usart  Pointer to an USART peripheral.
 * \param c  Character to send
 */
void USART_PutChar( Usart *usart, uint8_t c)
{
    /* Wait for the transmitter to be ready*/
    while ((usart->US_CSR & US_CSR_TXEMPTY) == 0);

    /* Send character*/
    usart->US_THR = c;

    /* Wait for the transfer to complete*/
    while ((usart->US_CSR & US_CSR_TXEMPTY) == 0);
}

/**
 * \brief   Return 1 if a character can be read in USART
 * \param usart  Pointer to an USART peripheral.
 */
uint32_t USART_IsRxReady(Usart *usart)
{
    return (usart->US_CSR & US_CSR_RXRDY);
}

/**
 * \brief   Get present status
 * \param usart  Pointer to an USART peripheral.
 */
uint32_t USART_GetStatus(Usart *usart)
{
    return usart->US_CSR;
}

/**
 * \brief   Enable interrupt
 * \param usart  Pointer to an USART peripheral.
 * \param mode  Interrupt mode.
 */
void USART_EnableIt(Usart *usart,uint32_t mode)
{
    usart->US_IER = mode;
}

/**
 * \brief   Disable interrupt
 * \param usart  Pointer to an USART peripheral.
 * \param mode  Interrupt mode.
 */
void USART_DisableIt(Usart *usart,uint32_t mode)
{
    usart->US_IDR = mode;
}

/**
 * \brief   Return interrupt mask
 * \param usart  Pointer to an USART peripheral.
 */
uint32_t USART_GetItMask(Usart *usart)
{
    return usart->US_IMR;
}

/**
 * \brief  Reads and returns a character from the USART.
 *
 * \note This function is synchronous (i.e. uses polling).
 * \param usart  Pointer to an USART peripheral.
 * \return Character received.
 */
uint8_t USART_GetChar(Usart *usart)
{
    while ((usart->US_CSR & US_CSR_RXRDY) == 0);
    return usart->US_RHR;
}
