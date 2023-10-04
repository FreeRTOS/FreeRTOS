/******************************************************************************
*
* Copyright (C) 2010 - 2015 Xilinx, Inc.  All rights reserved.
*
* Permission is hereby granted, free of charge, to any person obtaining a copy
* of this software and associated documentation files (the "Software"), to deal
* in the Software without restriction, including without limitation the rights
* to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
* copies of the Software, and to permit persons to whom the Software is
* furnished to do so, subject to the following conditions:
*
* The above copyright notice and this permission notice shall be included in
* all copies or substantial portions of the Software.
*
* Use of the Software is limited solely to applications:
* (a) running on a Xilinx device, or
* (b) that interact with a Xilinx device through a bus or interconnect.
*
* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
* XILINX  BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
* WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
* OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
* SOFTWARE.
*
* Except as contained in this notice, the name of the Xilinx shall not be used
* in advertising or otherwise to promote the sale, use or other dealings in
* this Software without prior written authorization from Xilinx.
*
******************************************************************************/
/****************************************************************************/

/**
 *
 * @file xuartps.c
 * @addtogroup uartps_v3_5
 * @{
 *
 * This file contains the implementation of the interface functions for XUartPs
 * driver. Refer to the header file xuartps.h for more detailed information.
 *
 * <pre>
 * MODIFICATION HISTORY:
 *
 * Ver   Who    Date	 Changes
 * ----- ------ -------- ----------------------------------------------
 * 1.00	drg/jz 01/13/10 First Release
 * 2.2   hk     06/23/14 SW reset of RX and TX should be done when changing
 *                       baud rate. CR# 804281.
 * 3.00  kvn    02/13/15 Modified code for MISRA-C:2012 compliance.
 * 3.1	kvn    04/10/15 Modified code for latest RTL changes.
 * 3.5	NK     09/26/17 Fix the RX Buffer Overflow issue.
 * </pre>
 *
 *****************************************************************************/

/***************************** Include Files ********************************/

#include "xstatus.h"
#include "xuartps.h"
#include "xil_io.h"

/************************** Constant Definitions ****************************/

/* The following constant defines the amount of error that is allowed for
 * a specified baud rate. This error is the difference between the actual
 * baud rate that will be generated using the specified clock and the
 * desired baud rate.
 */
#define XUARTPS_MAX_BAUD_ERROR_RATE    3U   /* max % error allowed */

/**************************** Type Definitions ******************************/


/***************** Macros (Inline Functions) Definitions ********************/


/************************** Function Prototypes *****************************/

static void XUartPs_StubHandler( void * CallBackRef,
                                 u32 Event,
                                 u32 ByteCount );

u32 XUartPs_SendBuffer( XUartPs * InstancePtr );

u32 XUartPs_ReceiveBuffer( XUartPs * InstancePtr );

/************************** Variable Definitions ****************************/

/****************************************************************************/

/**
 *
 * Initializes a specific XUartPs instance such that it is ready to be used.
 * The data format of the device is setup for 8 data bits, 1 stop bit, and no
 * parity by default. The baud rate is set to a default value specified by
 * Config->DefaultBaudRate if set, otherwise it is set to 19.2K baud. The
 * receive FIFO threshold is set for 8 bytes. The default operating mode of the
 * driver is polled mode.
 *
 * @param	InstancePtr is a pointer to the XUartPs instance.
 * @param	Config is a reference to a structure containing information
 *		about a specific XUartPs driver.
 * @param	EffectiveAddr is the device base address in the virtual memory
 *		address space. The caller is responsible for keeping the address
 *		mapping from EffectiveAddr to the device physical base address
 *		unchanged once this function is invoked. Unexpected errors may
 *		occur if the address mapping changes after this function is
 *		called. If address translation is not used, pass in the physical
 *		address instead.
 *
 * @return
 *
 *		- XST_SUCCESS if initialization was successful
 *		- XST_UART_BAUD_ERROR if the baud rate is not possible because
 *		  the inputclock frequency is not divisible with an acceptable
 *		  amount of error
 *
 * @note
 *
 * The default configuration for the UART after initialization is:
 *
 * - 19,200 bps or XPAR_DFT_BAUDRATE if defined
 * - 8 data bits
 * - 1 stop bit
 * - no parity
 * - FIFO's are enabled with a receive threshold of 8 bytes
 * - The RX timeout is enabled with a timeout of 1 (4 char times)
 *
 *   All interrupts are disabled.
 *
 *****************************************************************************/
s32 XUartPs_CfgInitialize( XUartPs * InstancePtr,
                           XUartPs_Config * Config,
                           u32 EffectiveAddr )
{
    s32 Status;
    u32 ModeRegister;
    u32 BaudRate;

    /* Assert validates the input arguments */
    Xil_AssertNonvoid( InstancePtr != NULL );
    Xil_AssertNonvoid( Config != NULL );

    /* Setup the driver instance using passed in parameters */
    InstancePtr->Config.BaseAddress = EffectiveAddr;
    InstancePtr->Config.InputClockHz = Config->InputClockHz;
    InstancePtr->Config.ModemPinsConnected = Config->ModemPinsConnected;

    /* Initialize other instance data to default values */
    InstancePtr->Handler = XUartPs_StubHandler;

    InstancePtr->SendBuffer.NextBytePtr = NULL;
    InstancePtr->SendBuffer.RemainingBytes = 0U;
    InstancePtr->SendBuffer.RequestedBytes = 0U;

    InstancePtr->ReceiveBuffer.NextBytePtr = NULL;
    InstancePtr->ReceiveBuffer.RemainingBytes = 0U;
    InstancePtr->ReceiveBuffer.RequestedBytes = 0U;

    /* Initialize the platform data */
    InstancePtr->Platform = XGetPlatform_Info();

    InstancePtr->is_rxbs_error = 0U;

    /* Flag that the driver instance is ready to use */
    InstancePtr->IsReady = XIL_COMPONENT_IS_READY;

    /*
     * Set the default baud rate here, can be changed prior to
     * starting the device
     */
    BaudRate = ( u32 ) XUARTPS_DFT_BAUDRATE;
    Status = XUartPs_SetBaudRate( InstancePtr, BaudRate );

    if( Status != ( s32 ) XST_SUCCESS )
    {
        InstancePtr->IsReady = 0U;
    }
    else
    {
        /*
         * Set up the default data format: 8 bit data, 1 stop bit, no
         * parity
         */
        ModeRegister = XUartPs_ReadReg( InstancePtr->Config.BaseAddress,
                                        XUARTPS_MR_OFFSET );

        /* Mask off what's already there */
        ModeRegister &= ( ~( ( u32 ) XUARTPS_MR_CHARLEN_MASK |
                             ( u32 ) XUARTPS_MR_STOPMODE_MASK |
                             ( u32 ) XUARTPS_MR_PARITY_MASK ) );

        /* Set the register value to the desired data format */
        ModeRegister |= ( ( u32 ) XUARTPS_MR_CHARLEN_8_BIT |
                          ( u32 ) XUARTPS_MR_STOPMODE_1_BIT |
                          ( u32 ) XUARTPS_MR_PARITY_NONE );

        /* Write the mode register out */
        XUartPs_WriteReg( InstancePtr->Config.BaseAddress, XUARTPS_MR_OFFSET,
                          ModeRegister );

        /* Set the RX FIFO trigger at 8 data bytes. */
        XUartPs_WriteReg( InstancePtr->Config.BaseAddress,
                          XUARTPS_RXWM_OFFSET, 0x08U );

        /* Set the RX timeout to 1, which will be 4 character time */
        XUartPs_WriteReg( InstancePtr->Config.BaseAddress,
                          XUARTPS_RXTOUT_OFFSET, 0x01U );

        /* Disable all interrupts, polled mode is the default */
        XUartPs_WriteReg( InstancePtr->Config.BaseAddress, XUARTPS_IDR_OFFSET,
                          XUARTPS_IXR_MASK );

        Status = XST_SUCCESS;
    }

    return Status;
}

/****************************************************************************/

/**
 *
 * This functions sends the specified buffer using the device in either
 * polled or interrupt driven mode. This function is non-blocking, if the device
 * is busy sending data, it will return and indicate zero bytes were sent.
 * Otherwise, it fills the TX FIFO as much as it can, and return the number of
 * bytes sent.
 *
 * In a polled mode, this function will only send as much data as TX FIFO can
 * buffer. The application may need to call it repeatedly to send the entire
 * buffer.
 *
 * In interrupt mode, this function will start sending the specified buffer,
 * then the interrupt handler will continue sending data until the entire
 * buffer has been sent. A callback function, as specified by the application,
 * will be called to indicate the completion of sending.
 *
 * @param	InstancePtr is a pointer to the XUartPs instance.
 * @param	BufferPtr is pointer to a buffer of data to be sent.
 * @param   NumBytes contains the number of bytes to be sent. A value of
 *		zero will stop a previous send operation that is in progress
 *		in interrupt mode. Any data that was already put into the
 *		transmit FIFO will be sent.
 *
 * @return	The number of bytes actually sent.
 *
 * @note
 *
 * The number of bytes is not asserted so that this function may be called with
 * a value of zero to stop an operation that is already in progress.
 * <br><br>
 *
 *****************************************************************************/
u32 XUartPs_Send( XUartPs * InstancePtr,
                  u8 * BufferPtr,
                  u32 NumBytes )
{
    u32 BytesSent;

    /* Asserts validate the input arguments */
    Xil_AssertNonvoid( InstancePtr != NULL );
    Xil_AssertNonvoid( BufferPtr != NULL );
    Xil_AssertNonvoid( InstancePtr->IsReady == XIL_COMPONENT_IS_READY );

    /*
     * Disable the UART transmit interrupts to allow this call to stop a
     * previous operation that may be interrupt driven.
     */
    XUartPs_WriteReg( InstancePtr->Config.BaseAddress, XUARTPS_IDR_OFFSET,
                      ( XUARTPS_IXR_TXEMPTY | XUARTPS_IXR_TXFULL ) );

    /* Setup the buffer parameters */
    InstancePtr->SendBuffer.RequestedBytes = NumBytes;
    InstancePtr->SendBuffer.RemainingBytes = NumBytes;
    InstancePtr->SendBuffer.NextBytePtr = BufferPtr;

    /*
     * Transmit interrupts will be enabled in XUartPs_SendBuffer(), after
     * filling the TX FIFO.
     */
    BytesSent = XUartPs_SendBuffer( InstancePtr );

    return BytesSent;
}

/****************************************************************************/

/**
 *
 * This function attempts to receive a specified number of bytes of data
 * from the device and store it into the specified buffer. This function works
 * for both polled or interrupt driven modes. It is non-blocking.
 *
 * In a polled mode, this function will only receive the data already in the
 * RX FIFO. The application may need to call it repeatedly to receive the
 * entire buffer. Polled mode is the default mode of operation for the device.
 *
 * In interrupt mode, this function will start the receiving, if not the entire
 * buffer has been received, the interrupt handler will continue receiving data
 * until the entire buffer has been received. A callback function, as specified
 * by the application, will be called to indicate the completion of the
 * receiving or error conditions.
 *
 * @param	InstancePtr is a pointer to the XUartPs instance
 * @param	BufferPtr is pointer to buffer for data to be received into
 * @param	NumBytes is the number of bytes to be received. A value of zero
 *		will stop a previous receive operation that is in progress in
 *		interrupt mode.
 *
 * @return	The number of bytes received.
 *
 * @note
 *
 * The number of bytes is not asserted so that this function may be called
 * with a value of zero to stop an operation that is already in progress.
 *
 *****************************************************************************/
u32 XUartPs_Recv( XUartPs * InstancePtr,
                  u8 * BufferPtr,
                  u32 NumBytes )
{
    u32 ReceivedCount;
    u32 ImrRegister;

    /* Assert validates the input arguments */
    Xil_AssertNonvoid( InstancePtr != NULL );
    Xil_AssertNonvoid( BufferPtr != NULL );
    Xil_AssertNonvoid( InstancePtr->IsReady == XIL_COMPONENT_IS_READY );

    /*
     * Disable all the interrupts.
     * This stops a previous operation that may be interrupt driven
     */
    ImrRegister = XUartPs_ReadReg( InstancePtr->Config.BaseAddress,
                                   XUARTPS_IMR_OFFSET );
    XUartPs_WriteReg( InstancePtr->Config.BaseAddress, XUARTPS_IDR_OFFSET,
                      XUARTPS_IXR_MASK );

    /* Setup the buffer parameters */
    InstancePtr->ReceiveBuffer.RequestedBytes = NumBytes;
    InstancePtr->ReceiveBuffer.RemainingBytes = NumBytes;
    InstancePtr->ReceiveBuffer.NextBytePtr = BufferPtr;

    /* Receive the data from the device */
    ReceivedCount = XUartPs_ReceiveBuffer( InstancePtr );

    /* Restore the interrupt state */
    XUartPs_WriteReg( InstancePtr->Config.BaseAddress, XUARTPS_IER_OFFSET,
                      ImrRegister );

    return ReceivedCount;
}

/****************************************************************************/

/*
 *
 * This function sends a buffer that has been previously specified by setting
 * up the instance variables of the instance. This function is an internal
 * function for the XUartPs driver such that it may be called from a shell
 * function that sets up the buffer or from an interrupt handler.
 *
 * This function sends the specified buffer in either polled or interrupt
 * driven modes. This function is non-blocking.
 *
 * In a polled mode, this function only sends as much data as the TX FIFO
 * can buffer. The application may need to call it repeatedly to send the
 * entire buffer.
 *
 * In interrupt mode, this function starts the sending of the buffer, if not
 * the entire buffer has been sent, then the interrupt handler continues the
 * sending until the entire buffer has been sent. A callback function, as
 * specified by the application, will be called to indicate the completion of
 * sending.
 *
 * @param	InstancePtr is a pointer to the XUartPs instance
 *
 * @return	The number of bytes actually sent
 *
 * @note		None.
 *
 *****************************************************************************/
u32 XUartPs_SendBuffer( XUartPs * InstancePtr )
{
    u32 SentCount = 0U;
    u32 ImrRegister;

    /*
     * If the TX FIFO is full, send nothing.
     * Otherwise put bytes into the TX FIFO unil it is full, or all of the
     * data has been put into the FIFO.
     */
    while( ( !XUartPs_IsTransmitFull( InstancePtr->Config.BaseAddress ) ) &&
           ( InstancePtr->SendBuffer.RemainingBytes > SentCount ) )
    {
        /* Fill the FIFO from the buffer */
        XUartPs_WriteReg( InstancePtr->Config.BaseAddress,
                          XUARTPS_FIFO_OFFSET,
                          ( ( u32 ) InstancePtr->SendBuffer.
                               NextBytePtr[ SentCount ] ) );

        /* Increment the send count. */
        SentCount++;
    }

    /* Update the buffer to reflect the bytes that were sent from it */
    InstancePtr->SendBuffer.NextBytePtr += SentCount;
    InstancePtr->SendBuffer.RemainingBytes -= SentCount;

    /*
     * If interrupts are enabled as indicated by the receive interrupt, then
     * enable the TX FIFO empty interrupt, so further action can be taken
     * for this sending.
     */
    ImrRegister =
        XUartPs_ReadReg( InstancePtr->Config.BaseAddress,
                         XUARTPS_IMR_OFFSET );

    if( ( ( ImrRegister & XUARTPS_IXR_RXFULL ) != ( u32 ) 0 ) ||
        ( ( ImrRegister & XUARTPS_IXR_RXEMPTY ) != ( u32 ) 0 ) ||
        ( ( ImrRegister & XUARTPS_IXR_RXOVR ) != ( u32 ) 0 ) )
    {
        XUartPs_WriteReg( InstancePtr->Config.BaseAddress,
                          XUARTPS_IER_OFFSET,
                          ImrRegister | ( u32 ) XUARTPS_IXR_TXEMPTY );
    }

    return SentCount;
}

/****************************************************************************/

/*
 *
 * This function receives a buffer that has been previously specified by setting
 * up the instance variables of the instance. This function is an internal
 * function, and it may be called from a shell function that sets up the buffer
 * or from an interrupt handler.
 *
 * This function attempts to receive a specified number of bytes from the
 * device and store it into the specified buffer. This function works for
 * either polled or interrupt driven modes. It is non-blocking.
 *
 * In polled mode, this function only receives as much data as in the RX FIFO.
 * The application may need to call it repeatedly to receive the entire buffer.
 * Polled mode is the default mode for the driver.
 *
 * In interrupt mode, this function starts the receiving, if not the entire
 * buffer has been received, the interrupt handler will continue until the
 * entire buffer has been received. A callback function, as specified by the
 * application, will be called to indicate the completion of the receiving or
 * error conditions.
 *
 * @param	InstancePtr is a pointer to the XUartPs instance
 *
 * @return	The number of bytes received.
 *
 * @note		None.
 *
 *****************************************************************************/
u32 XUartPs_ReceiveBuffer( XUartPs * InstancePtr )
{
    u32 CsrRegister;
    u32 ReceivedCount = 0U;
    u32 ByteStatusValue, EventData;
    u32 Event;

    /*
     * Read the Channel Status Register to determine if there is any data in
     * the RX FIFO
     */
    CsrRegister = XUartPs_ReadReg( InstancePtr->Config.BaseAddress,
                                   XUARTPS_SR_OFFSET );

    /*
     * Loop until there is no more data in RX FIFO or the specified
     * number of bytes has been received
     */
    while( ( ReceivedCount < InstancePtr->ReceiveBuffer.RemainingBytes ) &&
           ( ( ( CsrRegister & XUARTPS_SR_RXEMPTY ) == ( u32 ) 0 ) ) )
    {
        if( InstancePtr->is_rxbs_error )
        {
            ByteStatusValue = XUartPs_ReadReg(
                InstancePtr->Config.BaseAddress,
                XUARTPS_RXBS_OFFSET );

            if( ( ByteStatusValue & XUARTPS_RXBS_MASK ) != ( u32 ) 0 )
            {
                EventData = ByteStatusValue;
                Event = XUARTPS_EVENT_PARE_FRAME_BRKE;

                /*
                 * Call the application handler to indicate that there is a receive
                 * error or a break interrupt, if the application cares about the
                 * error it call a function to get the last errors.
                 */
                InstancePtr->Handler( InstancePtr->CallBackRef,
                                      Event, EventData );
            }
        }

        InstancePtr->ReceiveBuffer.NextBytePtr[ ReceivedCount ] =
            XUartPs_ReadReg( InstancePtr->Config.
                                BaseAddress,
                             XUARTPS_FIFO_OFFSET );

        ReceivedCount++;

        CsrRegister = XUartPs_ReadReg( InstancePtr->Config.BaseAddress,
                                       XUARTPS_SR_OFFSET );
    }

    InstancePtr->is_rxbs_error = 0;

    /*
     * Update the receive buffer to reflect the number of bytes just
     * received
     */
    if( InstancePtr->ReceiveBuffer.NextBytePtr != NULL )
    {
        InstancePtr->ReceiveBuffer.NextBytePtr += ReceivedCount;
    }

    InstancePtr->ReceiveBuffer.RemainingBytes -= ReceivedCount;

    return ReceivedCount;
}

/*****************************************************************************/

/**
 *
 * Sets the baud rate for the device. Checks the input value for
 * validity and also verifies that the requested rate can be configured to
 * within the maximum error range specified by XUARTPS_MAX_BAUD_ERROR_RATE.
 * If the provided rate is not possible, the current setting is unchanged.
 *
 * @param	InstancePtr is a pointer to the XUartPs instance
 * @param	BaudRate to be set
 *
 * @return
 *		- XST_SUCCESS if everything configured as expected
 *		- XST_UART_BAUD_ERROR if the requested rate is not available
 *		  because there was too much error
 *
 * @note		None.
 *
 *****************************************************************************/
s32 XUartPs_SetBaudRate( XUartPs * InstancePtr,
                         u32 BaudRate )
{
    u32 IterBAUDDIV;      /* Iterator for available baud divisor values */
    u32 BRGR_Value;       /* Calculated value for baud rate generator */
    u32 CalcBaudRate;     /* Calculated baud rate */
    u32 BaudError;        /* Diff between calculated and requested baud rate */
    u32 Best_BRGR = 0U;   /* Best value for baud rate generator */
    u8 Best_BAUDDIV = 0U; /* Best value for baud divisor */
    u32 Best_Error = 0xFFFFFFFFU;
    u32 PercentError;
    u32 ModeReg;
    u32 InputClk;

    /* Asserts validate the input arguments */
    Xil_AssertNonvoid( InstancePtr != NULL );
    Xil_AssertNonvoid( InstancePtr->IsReady == XIL_COMPONENT_IS_READY );
    Xil_AssertNonvoid( BaudRate <= ( u32 ) XUARTPS_MAX_RATE );
    Xil_AssertNonvoid( BaudRate >= ( u32 ) XUARTPS_MIN_RATE );

    /*
     * Make sure the baud rate is not impossilby large.
     * Fastest possible baud rate is Input Clock / 2.
     */
    if( ( BaudRate * 2 ) > InstancePtr->Config.InputClockHz )
    {
        return XST_UART_BAUD_ERROR;
    }

    /* Check whether the input clock is divided by 8 */
    ModeReg = XUartPs_ReadReg( InstancePtr->Config.BaseAddress,
                               XUARTPS_MR_OFFSET );

    InputClk = InstancePtr->Config.InputClockHz;

    if( ModeReg & XUARTPS_MR_CLKSEL )
    {
        InputClk = InstancePtr->Config.InputClockHz / 8;
    }

    /*
     * Determine the Baud divider. It can be 4to 254.
     * Loop through all possible combinations
     */
    for( IterBAUDDIV = 4; IterBAUDDIV < 255; IterBAUDDIV++ )
    {
        /* Calculate the value for BRGR register */
        BRGR_Value = InputClk / ( BaudRate * ( IterBAUDDIV + 1 ) );

        /* Calculate the baud rate from the BRGR value */
        CalcBaudRate = InputClk / ( BRGR_Value * ( IterBAUDDIV + 1 ) );

        /* Avoid unsigned integer underflow */
        if( BaudRate > CalcBaudRate )
        {
            BaudError = BaudRate - CalcBaudRate;
        }
        else
        {
            BaudError = CalcBaudRate - BaudRate;
        }

        /* Find the calculated baud rate closest to requested baud rate. */
        if( Best_Error > BaudError )
        {
            Best_BRGR = BRGR_Value;
            Best_BAUDDIV = IterBAUDDIV;
            Best_Error = BaudError;
        }
    }

    /* Make sure the best error is not too large. */
    PercentError = ( Best_Error * 100 ) / BaudRate;

    if( XUARTPS_MAX_BAUD_ERROR_RATE < PercentError )
    {
        return XST_UART_BAUD_ERROR;
    }

    /* Disable TX and RX to avoid glitches when setting the baud rate. */
    XUartPs_DisableUart( InstancePtr );

    XUartPs_WriteReg( InstancePtr->Config.BaseAddress,
                      XUARTPS_BAUDGEN_OFFSET, Best_BRGR );
    XUartPs_WriteReg( InstancePtr->Config.BaseAddress,
                      XUARTPS_BAUDDIV_OFFSET, Best_BAUDDIV );

    /* RX and TX SW reset */
    XUartPs_WriteReg( InstancePtr->Config.BaseAddress, XUARTPS_CR_OFFSET,
                      XUARTPS_CR_TXRST | XUARTPS_CR_RXRST );

    /* Enable device */
    XUartPs_EnableUart( InstancePtr );

    InstancePtr->BaudRate = BaudRate;

    return XST_SUCCESS;
}

/****************************************************************************/

/**
 *
 * This function is a stub handler that is the default handler such that if the
 * application has not set the handler when interrupts are enabled, this
 * function will be called.
 *
 * @param	CallBackRef is unused by this function.
 * @param	Event is unused by this function.
 * @param	ByteCount is unused by this function.
 *
 * @return	None.
 *
 * @note		None.
 *
 *****************************************************************************/
static void XUartPs_StubHandler( void * CallBackRef,
                                 u32 Event,
                                 u32 ByteCount )
{
    ( void ) CallBackRef;
    ( void ) Event;
    ( void ) ByteCount;
    /* Assert occurs always since this is a stub and should never be called */
    Xil_AssertVoidAlways();
}
/** @} */
