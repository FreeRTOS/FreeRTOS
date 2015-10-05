/***********************************************************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only intended for use with Renesas products.
* No other uses are authorized. This software is owned by Renesas Electronics Corporation and is protected under all
* applicable laws, including copyright laws. 
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIESREGARDING THIS SOFTWARE, WHETHER EXPRESS, IMPLIED
* OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
* NON-INFRINGEMENT.  ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED.TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY
* LAW, NEITHER RENESAS ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE FOR ANY DIRECT,
* INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR ANY REASON RELATED TO THIS SOFTWARE, EVEN IF RENESAS OR
* ITS AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software and to discontinue the availability 
* of this software. By using this software, you agree to the additional terms and conditions found by accessing the 
* following link:
* http://www.renesas.com/disclaimer
*
* Copyright (C) 2015 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/

/***********************************************************************************************************************
* File Name    : r_cg_sci_user.c
* Version      : Code Generator for RX113 V1.02.01.02 [28 May 2015]
* Device(s)    : R5F51138AxFP
* Tool-Chain   : CCRX
* Description  : This file implements device driver for SCI module.
* Creation Date: 21/09/2015
***********************************************************************************************************************/

/***********************************************************************************************************************
Pragma directive
***********************************************************************************************************************/
/* Start user code for pragma. Do not edit comment generated here */


/*
 * This file originated from an example project for the RSK - it has been
 * adapted to allow it to be used in the FreeRTOS demo.  Functions required by
 * UARTCommandConsole.c have been added.
 *
 * ***NOTE***: Transmitting generates an interrupt for each character, which
 * consumes	CPU time, and can cause standard demo RTOS tasks that monitor their
 * own performance to fail asserts - therefore when using GCC it is best to
 * compile this file with maximum speed optimisation.
 */



/* End user code. Do not edit comment generated here */

/***********************************************************************************************************************
Includes
***********************************************************************************************************************/
#include "r_cg_macrodriver.h"
#include "r_cg_sci.h"
/* Start user code for include. Do not edit comment generated here */
#include "rskrx113def.h"
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "serial.h"
/* End user code. Do not edit comment generated here */
#include "r_cg_userdefine.h"

/***********************************************************************************************************************
Global variables and functions
***********************************************************************************************************************/
extern uint8_t * gp_sci1_tx_address;         /* SCI1 send buffer address */
extern uint16_t  g_sci1_tx_count;            /* SCI1 send data number */
extern uint8_t * gp_sci1_rx_address;         /* SCI1 receive buffer address */
extern uint16_t  g_sci1_rx_count;            /* SCI1 receive data number */
extern uint16_t  g_sci1_rx_length;           /* SCI1 receive data length */
/* Start user code for global. Do not edit comment generated here */

/* Global used to receive a character from the PC terminal */
uint8_t g_rx_char;

/* Flag used to control transmission to PC terminal */
volatile uint8_t g_tx_flag = FALSE;

/* Characters received from the UART are stored in this queue, ready to be
received by the application.  ***NOTE*** Using a queue in this way is very
convenient, but also very inefficient.  It can be used here because characters
will only arrive slowly.  In a higher bandwidth system a circular RAM buffer or
DMA should be used in place of this queue. */
static QueueHandle_t xRxQueue = NULL;

/* When a task calls vSerialPutString() its handle is stored in xSendingTask,
before being placed into the Blocked state (so does not use any CPU time) to
wait for the transmission to end.  The task handle is then used from the UART
transmit end interrupt to remove the task from the Blocked state. */
static TaskHandle_t xSendingTask = NULL;

/* Flag used locally to detect transmission complete.  This is used by the
auto generated API only. */
static volatile uint8_t sci1_txdone;

/* End user code. Do not edit comment generated here */

/***********************************************************************************************************************
* Function Name: r_sci1_transmit_interrupt
* Description  : None
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void r_sci1_transmit_interrupt(void) __attribute__((interrupt));
void r_sci1_transmit_interrupt(void)
{
    if (g_sci1_tx_count > 0U)
    {
        SCI1.TDR = *gp_sci1_tx_address;
        gp_sci1_tx_address++;
        g_sci1_tx_count--;
    }
    else 
    {
        SCI1.SCR.BIT.TIE = 0U;
        SCI1.SCR.BIT.TEIE = 1U;
    }
}
/***********************************************************************************************************************
* Function Name: r_sci1_transmitend_interrupt
* Description  : None
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void r_sci1_transmitend_interrupt(void) __attribute__((interrupt));
void r_sci1_transmitend_interrupt(void)
{
    /* Set TXD1 pin */
    PORT1.PMR.BYTE &= 0xBFU;
    SCI1.SCR.BIT.TIE = 0U;
    SCI1.SCR.BIT.TE = 0U;
    SCI1.SCR.BIT.TEIE = 0U;

    r_sci1_callback_transmitend();
}
/***********************************************************************************************************************
* Function Name: r_sci1_receive_interrupt
* Description  : None
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void r_sci1_receive_interrupt(void) __attribute__((interrupt));
void r_sci1_receive_interrupt(void)
{
    if (g_sci1_rx_length > g_sci1_rx_count)
    {
        *gp_sci1_rx_address = SCI1.RDR;
        gp_sci1_rx_address++;
        g_sci1_rx_count++;

        if (g_sci1_rx_length == g_sci1_rx_count)
        {
            r_sci1_callback_receiveend();
        }
    }
}
/***********************************************************************************************************************
* Function Name: r_sci1_receiveerror_interrupt
* Description  : None
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void r_sci1_receiveerror_interrupt(void) __attribute__((interrupt));
void r_sci1_receiveerror_interrupt(void)
{
    uint8_t err_type;

    r_sci1_callback_receiveerror();

    /* Clear overrun, framing and parity error flags */
    err_type = SCI1.SSR.BYTE;
    SCI1.SSR.BYTE = err_type & ( uint8_t ) 0xC7;
}
/***********************************************************************************************************************
* Function Name: r_sci1_callback_transmitend
* Description  : This function is a callback function when SCI1 finishes transmission.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void r_sci1_callback_transmitend(void)
{
    /* Start user code. Do not edit comment generated here */
	BaseType_t xHigherPriorityTaskWoken = pdFALSE;

	/* The sci1_txdone flag is used by the auto generated API only. */
	sci1_txdone = TRUE;

	if( xSendingTask != NULL )
	{
		/* A task is waiting for the end of the Tx, unblock it now.
		http://www.freertos.org/vTaskNotifyGiveFromISR.html */
		vTaskNotifyGiveFromISR( xSendingTask, &xHigherPriorityTaskWoken );
		xSendingTask = NULL;

		portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
	}
    /* End user code. Do not edit comment generated here */
}
/***********************************************************************************************************************
* Function Name: r_sci1_callback_receiveend
* Description  : This function is a callback function when SCI1 finishes reception.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void r_sci1_callback_receiveend(void)
{
    /* Start user code. Do not edit comment generated here */
	BaseType_t xHigherPriorityTaskWoken = pdFALSE;

    configASSERT( xRxQueue );

	/* Transmitting generates an interrupt for each character, which consumes
	CPU time, and can cause standard demo RTOS tasks that monitor their own
	performance to fail asserts - so don't receive new CLI commands if a
	transmit is not already in progress. */
	if( sci1_txdone == TRUE )
	{
		/* Characters received from the UART are stored in this queue, ready to be
		received by the application.  ***NOTE*** Using a queue in this way is very
		convenient, but also very inefficient.  It can be used here because
		characters will only arrive slowly.  In a higher bandwidth system a circular
		RAM buffer or DMA should be used in place of this queue. */
		xQueueSendFromISR( xRxQueue, &g_rx_char, &xHigherPriorityTaskWoken );
	}

    /* Set up SCI1 receive buffer again */
    R_SCI1_Serial_Receive((uint8_t *) &g_rx_char, 1);

    /* See http://www.freertos.org/xQueueOverwriteFromISR.html for information
    on the semantics of this ISR. */
    portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
    /* End user code. Do not edit comment generated here */
}
/***********************************************************************************************************************
* Function Name: r_sci1_callback_receiveerror
* Description  : This function is a callback function when SCI1 reception encounters error.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void r_sci1_callback_receiveerror(void)
{
    /* Start user code. Do not edit comment generated here */
    /* End user code. Do not edit comment generated here */
}

/* Start user code for adding. Do not edit comment generated here */
/***********************************************************************************************************************
 * Function Name: R_SCI1_AsyncTransmit
 * Description  : This function sends SCI1 data and waits for the transmit end flag.
 * Arguments    : tx_buf -
 *                    transfer buffer pointer
 *                tx_num -
 *                    buffer size
 * Return Value : status -
 *                    MD_OK or MD_ARGERROR
 ***********************************************************************************************************************/
MD_STATUS R_SCI1_AsyncTransmit (uint8_t * const tx_buf, const uint16_t tx_num)
{
    MD_STATUS status = MD_OK;

    /* clear the flag before initiating a new transmission */
    sci1_txdone = FALSE;

    /* Send the data using the API */
    status = R_SCI1_Serial_Send(tx_buf, tx_num);

    /* Wait for the transmit end flag */
    while (FALSE == sci1_txdone)
    {
        /* Wait */
    }
    return (status);
}
/***********************************************************************************************************************
 * End of function R_SCI1_AsyncTransmit
 ***********************************************************************************************************************/

/* Function required in order to link UARTCommandConsole.c - which is used by
multiple different demo application. */
xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
	( void ) ulWantedBaud;
	( void ) uxQueueLength;

	/* Characters received from the UART are stored in this queue, ready to be
	received by the application.  ***NOTE*** Using a queue in this way is very
	convenient, but also very inefficient.  It can be used here because
	characters will only arrive slowly.  In a higher bandwidth system a circular
	RAM buffer or DMA should be used in place of this queue. */
	xRxQueue = xQueueCreate( uxQueueLength, sizeof( char ) );
	configASSERT( xRxQueue );

	/* Set up SCI1 receive buffer */
	R_SCI1_Serial_Receive((uint8_t *) &g_rx_char, 1);

	/* Ensure the interrupt priority is at or below
	configMAX_SYSCALL_INTERRUPT_PRIORITY. */
    IPR( SCI1, ERI1 ) = configKERNEL_INTERRUPT_PRIORITY + 1;

	/* Enable SCI1 operations */
	R_SCI1_Start();

	/* Only one UART is supported, so it doesn't matter what is returned
	here. */
	return 0;
}

/* Function required in order to link UARTCommandConsole.c - which is used by
multiple different demo application. */
void vSerialPutString( xComPortHandle pxPort, const signed char * const pcString, unsigned short usStringLength )
{
const TickType_t xMaxBlockTime = pdMS_TO_TICKS( 5000 );

	/* Only one port is supported. */
	( void ) pxPort;

	/* Clear the flag before initiating a new transmission */
	sci1_txdone = FALSE;

	/* Don't send the string unless the previous string has been sent. */
	if( xSendingTask == NULL )
	{
		/* Ensure the calling task's notification state is not already
		pending. */
		vTaskNotifyClear( NULL );

		/* Store the handle of the transmitting task.  This is used to unblock
		the task when the transmission has completed. */
		xSendingTask = xTaskGetCurrentTaskHandle();

		/* Send the string using the auto-generated API. */
		R_SCI1_Serial_Send( ( uint8_t * ) pcString, usStringLength );

		/* Wait in the Blocked state (so not using any CPU time) until the
		transmission has completed. */
		ulTaskNotifyTake( pdTRUE, xMaxBlockTime );
	}
}

/* Function required in order to link UARTCommandConsole.c - which is used by
multiple different demo application. */
signed portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed char *pcRxedChar, TickType_t xBlockTime )
{
	/* Only one UART is supported. */
	( void ) pxPort;

	/* Return a received character, if any are available.  Otherwise block to
	wait for a character. */
	return xQueueReceive( xRxQueue, pcRxedChar, xBlockTime );
}

/* Function required in order to link UARTCommandConsole.c - which is used by
multiple different demo application. */
signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed char cOutChar, TickType_t xBlockTime )
{
	/* Just mapped to vSerialPutString() so the block time is not used. */
	( void ) xBlockTime;

	vSerialPutString( pxPort, &cOutChar, sizeof( cOutChar ) );
	return pdPASS;
}

/* End user code. Do not edit comment generated here */
