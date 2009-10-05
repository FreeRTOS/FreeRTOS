/*
    FreeRTOS MCF5235 port - Copyright (C) 2006 Christian Walter.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License** as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    FreeRTOS is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with FreeRTOS; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

    A special exception to the GPL can be applied should you wish to distribute
    a combined work that includes FreeRTOS, without being obliged to provide
    the source code for any proprietary components.  See the licensing section
    of http://www.FreeRTOS.org for full details of how and when the exception
    can be applied.

    ***************************************************************************
    ***************************************************************************
    *                                                                         *
    * Get the FreeRTOS eBook!  See http://www.FreeRTOS.org/Documentation      *
	*                                                                         *
	* This is a concise, step by step, 'hands on' guide that describes both   *
	* general multitasking concepts and FreeRTOS specifics. It presents and   *
	* explains numerous examples that are written using the FreeRTOS API.     *
	* Full source code for all the examples is provided in an accompanying    *
	* .zip file.                                                              *
    *                                                                         *
    ***************************************************************************
    ***************************************************************************

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and 
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety 
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting, 
	licensing and training services.
*/

/* ------------------------ MCF523x includes ------------------------------ */
#include "mcf5xxx.h"
#include "mcf523x.h"

/* ------------------------ FreeRTOS includes ----------------------------- */
#include "FreeRTOS.h"
#include "queue.h"
#include "task.h"

#include "serial.h"

/* ----------------------- Defines ----------------------------------------- */
#define BAUDRATE_VALUE(fsys, baud)      ( ( fsys )/(32UL * baud) )
#define MCF_UART_VECTOR                 ( 64 + 13 )
#define COM_NIFACE                      1
#define COM_BLOCK_RETRYTIME             10

/* ------------------------ Static functions ------------------------------ */
static void     prvSerialISR( void );

/* ------------------------ Static variables ------------------------------ */
typedef struct
{
    portBASE_TYPE xInitialized;
    xQueueHandle xRXChars;
    xQueueHandle xTXChars;
} xComPortIF_t;

static xComPortIF_t xComPortIF[ COM_NIFACE ];

/* ------------------------ Begin implementation -------------------------- */
xComPortHandle
xSerialPortInitMinimal( unsigned long ulWantedBaud,
                        unsigned portBASE_TYPE uxQueueLength )
{
    extern void     ( *__RAMVEC[] ) (  );
    xComPortHandle xReturn;
    portBASE_TYPE xOldIPL;

    /* Create the queues used to hold Rx and Tx characters. */
    xComPortIF[ 0 ].xRXChars =
        xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE )sizeof( signed char ) );
    xComPortIF[ 0 ].xTXChars =
        xQueueCreate( uxQueueLength + 1, ( unsigned portBASE_TYPE )sizeof( signed char ) );

    /* If the queues were created correctly then setup the serial port hardware. */
    if( ( xComPortIF[ 0 ].xRXChars != 0 ) && ( xComPortIF[ 0 ].xTXChars != 0 ) )
    {
        xOldIPL = portSET_IPL( portIPL_MAX );

        /* UART 0: Reset transmitter, receiver and mode register pointer */
        MCF_UART_UCR0 = MCF_UART_UCR_MISC( 0x3 );
        MCF_UART_UCR0 = MCF_UART_UCR_MISC( 0x2 );
        MCF_UART_UCR0 = MCF_UART_UCR_MISC( 0x1 );

        /* Enable receive interrupts. */
        MCF_UART_UIMR0 = MCF_UART_UIMR_RXRDY_FU;

        /* 8 Databits, 1 Stopbit and no parity */
        MCF_UART_UMR0 = MCF_UART_UMR_PM( 0x3 ) | MCF_UART_UMR_SB( 0x7 ) | MCF_UART_UMR_BC( 0x3 );

        /* UART 0 Clocking */
        MCF_UART_UCSR0 = MCF_UART_UCSR_RCS( 0xd ) | MCF_UART_UCSR_TCS( 0xd );
        MCF_UART_UBG10 = BAUDRATE_VALUE( FSYS_2, ulWantedBaud ) >> 8U;
        MCF_UART_UBG20 = BAUDRATE_VALUE( FSYS_2, ulWantedBaud ) & 0xFFU;

        /* UART 0: Enable interrupts */
        __RAMVEC[MCF_UART_VECTOR] = prvSerialISR;
        MCF_INTC0_ICR13 = MCF_INTC0_ICRn_IL( 0x2 ) | MCF_INTC0_ICRn_IP( 0x1 );
        MCF_INTC0_IMRL &= ~MCF_INTC0_IMRL_INT_MASK13;

        /* UART 0 Miscellaneous */
        MCF_UART_UACR0 = 0;

        /* UART 0: Enable pins */
        MCF_GPIO_PAR_UART = MCF_GPIO_PAR_UART_PAR_U0RXD | MCF_GPIO_PAR_UART_PAR_U0TXD;

        /* Enable the UART. */
        MCF_UART_UCR0 = MCF_UART_UCR_RXC( 0x1 ) | MCF_UART_UCR_TXC( 0x1 );

        xComPortIF[ 0 ].xInitialized = TRUE;
        xReturn = ( xComPortHandle ) &xComPortIF[ 0 ];

        ( void )portSET_IPL( xOldIPL );
    }
    else
    {
        xReturn = ( xComPortHandle ) 0;
    }

    return xReturn;
}

signed          portBASE_TYPE
xSerialGetChar( xComPortHandle pxPort, signed char * pcRxedChar,
                portTickType xBlockTime )
{
    int i;
    portBASE_TYPE xResult = pdFALSE;
    /* Lookup the correct interface. */
    for( i = 0; i < COM_NIFACE; i++ )
    {
        if( pxPort == ( xComPortHandle ) &xComPortIF[ i ] )
        {
            break;
        }
    }
    /* This COM port is available. */
    if( ( i != COM_NIFACE ) && xComPortIF[ i ].xInitialized )
    {
        /* Get the next character from the buffer.  Return false if no characters
         * are available, or arrive before xBlockTime expires.
         */
        if( xQueueReceive( xComPortIF[ i ].xRXChars, pcRxedChar, xBlockTime ) )
        {
            xResult = pdTRUE;
        }
    }
    return xResult;
}

void
vSerialPutString( xComPortHandle pxPort, const signed char *
                  const pcString, unsigned short usStringLength )
{
    int i;
    signed char *pChNext;

    /* Send each character in the string, one at a time. */
    pChNext = ( signed char * )pcString;
    for( i = 0; i < usStringLength; i++ )
    {
        /* Block until character has been transmitted. */
        while( xSerialPutChar( pxPort, *pChNext, COM_BLOCK_RETRYTIME ) != pdTRUE ); pChNext++;
    }
}

signed          portBASE_TYPE
xSerialPutChar( xComPortHandle pxPort, signed char cOutChar,
                portTickType xBlockTime )
{
    int i;
    portBASE_TYPE xResult = pdFALSE;
    portBASE_TYPE xOldIPL;
    /* Lookup the correct interface. */
    for( i = 0; i < COM_NIFACE; i++ )
    {
        if( pxPort == ( xComPortHandle ) &xComPortIF[ i ] )
        {
            break;
        }
    }
    /* This COM port is available. */
    if( ( i != COM_NIFACE ) && xComPortIF[ i ].xInitialized )
    {
        /* Place the character in the queue of characters to be transmitted. */
        if( xQueueSend( xComPortIF[ i ].xTXChars, &cOutChar, xBlockTime ) == pdPASS )
        {
            /* Turn on the Tx interrupt so the ISR will remove the character from the
             * queue and send it. */
            MCF_UART_UIMR0 = MCF_UART_UIMR_TXRDY | MCF_UART_UIMR_RXRDY_FU;
            xResult = pdTRUE;
        }
    }
    return xResult;
}

signed          portBASE_TYPE
xSerialPutCharNOISR( xComPortHandle pxPort, signed char cOutChar )
{
    int i;
    portBASE_TYPE xResult = pdFALSE;
    portBASE_TYPE xOldIPL = portSET_IPL( portIPL_MAX );
    /* Lookup the correct interface. */
    for( i = 0; i < COM_NIFACE; i++ )
    {
        if( pxPort == ( xComPortHandle ) &xComPortIF[ i ] )
        {
            break;
        }
    }
    /* This COM port is available. Support for this only available for COM1 right now. */
    if( ( i != COM_NIFACE ) && ( i == 0 ) )
    {
        /* Wait until the transmit buffer is ready. */
        while( !( MCF_UART_USR0 & MCF_UART_USR_TXRDY ) );
        /* Place the character in the transmit buffer. */
        MCF_UART_UTB0 = cOutChar;
        xResult = pdTRUE;
    }
    ( void )portSET_IPL( xOldIPL );
    return xResult;
}

void
vSerialPutStringNOISR( xComPortHandle pxPort, const signed char *
                       const pcString, unsigned short usStringLength )
{
    int i;
    signed char *pChNext;
    portBASE_TYPE xOldIPL = portSET_IPL( portIPL_MAX );

    /* Send each character in the string, one at a time. */
    pChNext = ( signed char * )pcString;
    for( i = 0; i < usStringLength; i++ )
    {
        /* Block until character has been transmitted. */
        while( xSerialPutCharNOISR( pxPort, *pChNext ) != pdTRUE );
        pChNext++;
    }
    ( void )portSET_IPL( xOldIPL );
}

void
vSerialClose( xComPortHandle xPort )
{
    /* Not supported as not required by the demo application. */
}

void
prvSerialISR( void )
{
    static signed char cChar;
    static portBASE_TYPE xHigherPriorityTaskWoken;

    /* We have to remvoe the effect of the GCC. Please note that the
     * __attribute__ ((interrupt_handler)) does not work here because we
     * have to do the storing of the registers ourself. Another problem
     * is the usage of a frame pointer which is unlinked on entry.
     */
#if _GCC_USES_FP == 1
    asm volatile ( "unlk %fp\n\t" );
#endif
    /* This ISR can cause a context switch, so the first statement must be
     * a call to the portENTER_SWITCHING_ISR() macro. This must be BEFORE any
     * variable declarations.
     */
    portENTER_SWITCHING_ISR();
	xHigherPriorityTaskWoken = pdFALSE;

    /* Ready to send a character from the buffer. */
    if( MCF_UART_USR0 & MCF_UART_USR_TXRDY )
    {
        /* Transmit buffer is ready. Test if there are characters available. */
        if( xQueueReceiveFromISR( xComPortIF[ 0 ].xTXChars, &cChar, &xHigherPriorityTaskWoken ) ==
            pdTRUE )
        {
            /* A character was retrieved from the queue so can be sent. */
            MCF_UART_UTB0 = cChar;
        }
        else
        {
            /* Leave only receiver enabled. */
            MCF_UART_UIMR0 = MCF_UART_UIMR_RXRDY_FU;
        }
    }
    if( MCF_UART_USR0 & MCF_UART_USR_RXRDY )
    {
        cChar = MCF_UART_URB0;
        xQueueSendFromISR( xComPortIF[ 0].xRXChars, &cChar, &xHigherPriorityTaskWoken );
    }
    /* Exit the ISR.  If a task was woken by either a character being
     * or transmitted then a context switch will occur.
     */
    portEXIT_SWITCHING_ISR( xHigherPriorityTaskWoken );
}
