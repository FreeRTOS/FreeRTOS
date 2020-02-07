/***********************************************************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only intended for use with Renesas products. No
* other uses are authorized. This software is owned by Renesas Electronics Corporation and is protected under all
* applicable laws, including copyright laws.
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING
* THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY,
* FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED. TO THE MAXIMUM
* EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES
* SHALL BE LIABLE FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR ANY REASON RELATED TO THIS
* SOFTWARE, EVEN IF RENESAS OR ITS AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software and to discontinue the availability of
* this software. By using this software, you agree to the additional terms and conditions found by accessing the
* following link:
* http://www.renesas.com/disclaimer
*
* Copyright (C) 2018 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/

/***********************************************************************************************************************
* File Name    : NetworkInterface.c
* Device(s)    : RX
* Description  : Interfaces FreeRTOS TCP/IP stack to RX Ethernet driver.
***********************************************************************************************************************/

/***********************************************************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 07.03.2018 0.1     Development
***********************************************************************************************************************/

/***********************************************************************************************************************
*  Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
/*#include "FreeRTOS_DNS.h" */
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"

#include "r_ether_rx_if.h"
#include "r_pinset.h"

/***********************************************************************************************************************
 * Macro definitions
 **********************************************************************************************************************/
#define ETHER_BUFSIZE_MIN    60

#if defined( BSP_MCU_RX65N ) || defined( BSP_MCU_RX64M ) || defined( BSP_MCU_RX71M )
    #if ETHER_CFG_MODE_SEL == 0
        #define R_ETHER_PinSet_CHANNEL_0()    R_ETHER_PinSet_ETHERC0_MII()
    #elif ETHER_CFG_MODE_SEL == 1
        #define R_ETHER_PinSet_CHANNEL_0()    R_ETHER_PinSet_ETHERC0_RMII()
    #endif
#elif defined( BSP_MCU_RX63N )
    #if ETHER_CFG_MODE_SEL == 0
        #define R_ETHER_PinSet_CHANNEL_0()    R_ETHER_PinSet_ETHERC_MII()
    #elif ETHER_CFG_MODE_SEL == 1
        #define R_ETHER_PinSet_CHANNEL_0()    R_ETHER_PinSet_ETHERC_RMII()
    #endif
#endif /* if defined( BSP_MCU_RX65N ) || defined( BSP_MCU_RX64M ) || defined( BSP_MCU_RX71M ) */

#ifndef PHY_LS_HIGH_CHECK_TIME_MS

/* Check if the LinkSStatus in the PHY is still high after 2 seconds of not
 * receiving packets. */
    #define PHY_LS_HIGH_CHECK_TIME_MS    2000
#endif

#ifndef PHY_LS_LOW_CHECK_TIME_MS
    /* Check if the LinkSStatus in the PHY is still low every second. */
    #define PHY_LS_LOW_CHECK_TIME_MS    1000
#endif

/***********************************************************************************************************************
 * Private global variables and functions
 **********************************************************************************************************************/
typedef enum
{
    eMACInit,   /* Must initialise MAC. */
    eMACPass,   /* Initialisation was successful. */
    eMACFailed, /* Initialisation failed. */
} eMAC_INIT_STATUS_TYPE;

static TaskHandle_t ether_receive_check_task_handle = 0;
static TaskHandle_t ether_link_check_task_handle = 0;
static TaskHandle_t xTaskToNotify = NULL;
static BaseType_t xPHYLinkStatus;
static BaseType_t xReportedStatus;
static eMAC_INIT_STATUS_TYPE xMacInitStatus = eMACInit;

static int16_t SendData( uint8_t * pucBuffer,
                         size_t length );
static int InitializeNetwork( void );
static void prvEMACDeferredInterruptHandlerTask( void * pvParameters );
static void clear_all_ether_rx_discriptors( uint32_t event );

int32_t callback_ether_regist( void );
void EINT_Trig_isr( void * );
void get_random_number( uint8_t * data,
                        uint32_t len );

void prvLinkStatusChange( BaseType_t xStatus );
#if ( ipconfigHAS_PRINTF != 0 )
    static void prvMonitorResources( void );
#endif

/***********************************************************************************************************************
 * Function Name: xNetworkInterfaceInitialise ()
 * Description  : Initialization of Ethernet driver.
 * Arguments    : none
 * Return Value : pdPASS, pdFAIL
 **********************************************************************************************************************/
BaseType_t xNetworkInterfaceInitialise( void )
{
    BaseType_t xReturn;

    if( xMacInitStatus == eMACInit )
    {
        /*
         * Perform the hardware specific network initialization here using the Ethernet driver library to initialize the
         * Ethernet hardware, initialize DMA descriptors, and perform a PHY auto-negotiation to obtain a network link.
         *
         * InitialiseNetwork() uses Ethernet peripheral driver library function, and returns 0 if the initialization fails.
         */
        if( InitializeNetwork() == pdFALSE )
        {
            xMacInitStatus = eMACFailed;
        }
        else
        {
            /* Indicate that the MAC initialisation succeeded. */
            xMacInitStatus = eMACPass;
        }

        FreeRTOS_printf( ( "InitializeNetwork returns %s\n", ( xMacInitStatus == eMACPass ) ? "OK" : " Fail" ) );
    }

    if( xMacInitStatus == eMACPass )
    {
        xReturn = xPHYLinkStatus;
    }
    else
    {
        xReturn = pdFAIL;
    }

    FreeRTOS_printf( ( "xNetworkInterfaceInitialise returns %d\n", xReturn ) );

    return xReturn;
} /* End of function xNetworkInterfaceInitialise() */


/***********************************************************************************************************************
 * Function Name: xNetworkInterfaceOutput ()
 * Description  : Simple network output interface.
 * Arguments    : pxDescriptor, xReleaseAfterSend
 * Return Value : pdTRUE, pdFALSE
 **********************************************************************************************************************/
BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t * const pxDescriptor,
                                    BaseType_t xReleaseAfterSend )
{
    BaseType_t xReturn = pdFALSE;

    /* Simple network interfaces (as opposed to more efficient zero copy network
     * interfaces) just use Ethernet peripheral driver library functions to copy
     * data from the FreeRTOS+TCP buffer into the peripheral driver's own buffer.
     * This example assumes SendData() is a peripheral driver library function that
     * takes a pointer to the start of the data to be sent and the length of the
     * data to be sent as two separate parameters.  The start of the data is located
     * by pxDescriptor->pucEthernetBuffer.  The length of the data is located
     * by pxDescriptor->xDataLength. */
    if( xPHYLinkStatus != 0 )
    {
        if( SendData( pxDescriptor->pucEthernetBuffer, pxDescriptor->xDataLength ) >= 0 )
        {
            xReturn = pdTRUE;
            /* Call the standard trace macro to log the send event. */
            iptraceNETWORK_INTERFACE_TRANSMIT();
        }
    }
    else
    {
        /* As the PHY Link Status is low, it makes no sense trying to deliver a packet. */
    }

    if( xReleaseAfterSend != pdFALSE )
    {
        /* It is assumed SendData() copies the data out of the FreeRTOS+TCP Ethernet
         * buffer.  The Ethernet buffer is therefore no longer needed, and must be
         * freed for re-use. */
        vReleaseNetworkBufferAndDescriptor( pxDescriptor );
    }

    return xReturn;
} /* End of function xNetworkInterfaceOutput() */


#if ( ipconfigHAS_PRINTF != 0 )
    static void prvMonitorResources()
    {
        static UBaseType_t uxLastMinBufferCount = 0u;
        static UBaseType_t uxCurrentBufferCount = 0u;
        static size_t uxMinLastSize = 0uL;
        static size_t uxCurLastSize = 0uL;
        size_t uxMinSize;
        size_t uxCurSize;

        uxCurrentBufferCount = uxGetMinimumFreeNetworkBuffers();

        if( uxLastMinBufferCount != uxCurrentBufferCount )
        {
            /* The logging produced below may be helpful
             * while tuning +TCP: see how many buffers are in use. */
            uxLastMinBufferCount = uxCurrentBufferCount;
            FreeRTOS_printf( ( "Network buffers: %lu lowest %lu\n",
                               uxGetNumberOfFreeNetworkBuffers(), uxCurrentBufferCount ) );
        }

        uxMinSize = xPortGetMinimumEverFreeHeapSize();
        uxCurSize = xPortGetFreeHeapSize();

        if( uxMinLastSize != uxMinSize )
        {
            uxCurLastSize = uxCurSize;
            uxMinLastSize = uxMinSize;
            FreeRTOS_printf( ( "Heap: current %lu lowest %lu\n", uxCurSize, uxMinSize ) );
        }

        #if ( ipconfigCHECK_IP_QUEUE_SPACE != 0 )
            {
                static UBaseType_t uxLastMinQueueSpace = 0;
                UBaseType_t uxCurrentCount = 0u;

                uxCurrentCount = uxGetMinimumIPQueueSpace();

                if( uxLastMinQueueSpace != uxCurrentCount )
                {
                    /* The logging produced below may be helpful
                     * while tuning +TCP: see how many buffers are in use. */
                    uxLastMinQueueSpace = uxCurrentCount;
                    FreeRTOS_printf( ( "Queue space: lowest %lu\n", uxCurrentCount ) );
                }
            }
        #endif /* ipconfigCHECK_IP_QUEUE_SPACE */
    }
#endif /* ( ipconfigHAS_PRINTF != 0 ) */

/***********************************************************************************************************************
 * Function Name: prvEMACDeferredInterruptHandlerTask ()
 * Description  : The deferred interrupt handler is a standard RTOS task.
 * Arguments    : pvParameters
 * Return Value : none
 **********************************************************************************************************************/
static void prvEMACDeferredInterruptHandlerTask( void * pvParameters )
{
    NetworkBufferDescriptor_t * pxBufferDescriptor;
    int32_t xBytesReceived = 0;

    /* Avoid compiler warning about unreferenced parameter. */
    ( void ) pvParameters;

    /* Used to indicate that xSendEventStructToIPTask() is being called because
     * of an Ethernet receive event. */
    IPStackEvent_t xRxEvent;

    uint8_t * buffer_pointer;

    /* Some variables related to monitoring the PHY. */
    TimeOut_t xPhyTime;
    TickType_t xPhyRemTime;
    const TickType_t ulMaxBlockTime = pdMS_TO_TICKS( 100UL );

    vTaskSetTimeOutState( &xPhyTime );
    xPhyRemTime = pdMS_TO_TICKS( PHY_LS_LOW_CHECK_TIME_MS );

    FreeRTOS_printf( ( "Deferred Interrupt Handler Task started\n" ) );
    xTaskToNotify = ether_receive_check_task_handle;

    for( ; ; )
    {
        #if ( ipconfigHAS_PRINTF != 0 )
            {
                prvMonitorResources();
            }
        #endif /* ipconfigHAS_PRINTF != 0 ) */

        /* Wait for the Ethernet MAC interrupt to indicate that another packet
         * has been received.  */
        if( xBytesReceived <= 0 )
        {
            ulTaskNotifyTake( pdFALSE, ulMaxBlockTime );
        }

        /* See how much data was received.  */
        xBytesReceived = R_ETHER_Read_ZC2( ETHER_CHANNEL_0, ( void ** ) &buffer_pointer );

        if( xBytesReceived < 0 )
        {
            /* This is an error. Logged. */
            FreeRTOS_printf( ( "R_ETHER_Read_ZC2: rc = %d\n", xBytesReceived ) );
        }
        else if( xBytesReceived > 0 )
        {
            /* Allocate a network buffer descriptor that points to a buffer
             * large enough to hold the received frame.  As this is the simple
             * rather than efficient example the received data will just be copied
             * into this buffer. */
            pxBufferDescriptor = pxGetNetworkBufferWithDescriptor( ( size_t ) xBytesReceived, 0 );

            if( pxBufferDescriptor != NULL )
            {
                /* pxBufferDescriptor->pucEthernetBuffer now points to an Ethernet
                 * buffer large enough to hold the received data.  Copy the
                 * received data into pcNetworkBuffer->pucEthernetBuffer.  Here it
                 * is assumed ReceiveData() is a peripheral driver function that
                 * copies the received data into a buffer passed in as the function's
                 * parameter.  Remember! While is is a simple robust technique -
                 * it is not efficient.  An example that uses a zero copy technique
                 * is provided further down this page. */
                memcpy( pxBufferDescriptor->pucEthernetBuffer, buffer_pointer, ( size_t ) xBytesReceived );
                /*ReceiveData( pxBufferDescriptor->pucEthernetBuffer ); */

                /* Set the actual packet length, in case a larger buffer was returned. */
                pxBufferDescriptor->xDataLength = ( size_t ) xBytesReceived;

                R_ETHER_Read_ZC2_BufRelease( ETHER_CHANNEL_0 );

                /* See if the data contained in the received Ethernet frame needs
                * to be processed.  NOTE! It is preferable to do this in
                * the interrupt service routine itself, which would remove the need
                * to unblock this task for packets that don't need processing. */
                if( eConsiderFrameForProcessing( pxBufferDescriptor->pucEthernetBuffer ) == eProcessBuffer )
                {
                    /* The event about to be sent to the TCP/IP is an Rx event. */
                    xRxEvent.eEventType = eNetworkRxEvent;

                    /* pvData is used to point to the network buffer descriptor that
                     * now references the received data. */
                    xRxEvent.pvData = ( void * ) pxBufferDescriptor;

                    /* Send the data to the TCP/IP stack. */
                    if( xSendEventStructToIPTask( &xRxEvent, 0 ) == pdFALSE )
                    {
                        /* The buffer could not be sent to the IP task so the buffer must be released. */
                        vReleaseNetworkBufferAndDescriptor( pxBufferDescriptor );

                        /* Make a call to the standard trace macro to log the occurrence. */
                        iptraceETHERNET_RX_EVENT_LOST();
                        clear_all_ether_rx_discriptors( 0 );
                    }
                    else
                    {
                        /* The message was successfully sent to the TCP/IP stack.
                        * Call the standard trace macro to log the occurrence. */
                        iptraceNETWORK_INTERFACE_RECEIVE();
                        R_NOP();
                    }
                }
                else
                {
                    /* The Ethernet frame can be dropped, but the Ethernet buffer must be released. */
                    vReleaseNetworkBufferAndDescriptor( pxBufferDescriptor );
                }
            }
            else
            {
                /* The event was lost because a network buffer was not available.
                 * Call the standard trace macro to log the occurrence. */
                iptraceETHERNET_RX_EVENT_LOST();
                clear_all_ether_rx_discriptors( 1 );
                FreeRTOS_printf( ( "R_ETHER_Read_ZC2: Cleared descriptors\n" ) );
            }
        }

        if( xBytesReceived > 0 )
        {
            /* A packet was received. No need to check for the PHY status now,
             * but set a timer to check it later on. */
            vTaskSetTimeOutState( &xPhyTime );
            xPhyRemTime = pdMS_TO_TICKS( PHY_LS_HIGH_CHECK_TIME_MS );

            /* Indicate that the Link Status is high, so that
             * xNetworkInterfaceOutput() can send packets. */
            if( xPHYLinkStatus == 0 )
            {
                xPHYLinkStatus = 1;
                FreeRTOS_printf( ( "prvEMACHandlerTask: PHY LS assume %d\n", xPHYLinkStatus ) );
            }
        }
        else if( ( xTaskCheckForTimeOut( &xPhyTime, &xPhyRemTime ) != pdFALSE ) || ( FreeRTOS_IsNetworkUp() == pdFALSE ) )
        {
            R_ETHER_LinkProcess( 0 );

            if( xPHYLinkStatus != xReportedStatus )
            {
                xPHYLinkStatus = xReportedStatus;
                FreeRTOS_printf( ( "prvEMACHandlerTask: PHY LS now %d\n", xPHYLinkStatus ) );
            }

            vTaskSetTimeOutState( &xPhyTime );

            if( xPHYLinkStatus != 0 )
            {
                xPhyRemTime = pdMS_TO_TICKS( PHY_LS_HIGH_CHECK_TIME_MS );
            }
            else
            {
                xPhyRemTime = pdMS_TO_TICKS( PHY_LS_LOW_CHECK_TIME_MS );
            }
        }
    }
} /* End of function prvEMACDeferredInterruptHandlerTask() */


/***********************************************************************************************************************
 * Function Name: vNetworkInterfaceAllocateRAMToBuffers ()
 * Description  : .
 * Arguments    : pxNetworkBuffers
 * Return Value : none
 **********************************************************************************************************************/
void vNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
{
    uint32_t ul;
    uint8_t * buffer_address;

    R_EXTERN_SEC( B_ETHERNET_BUFFERS_1 )

    buffer_address = R_SECTOP( B_ETHERNET_BUFFERS_1 );

    for( ul = 0; ul < ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS; ul++ )
    {
        pxNetworkBuffers[ ul ].pucEthernetBuffer = ( buffer_address + ( ETHER_CFG_BUFSIZE * ul ) );
    }
} /* End of function vNetworkInterfaceAllocateRAMToBuffers() */


/***********************************************************************************************************************
 * Function Name: prvLinkStatusChange ()
 * Description  : Function will be called when the Link Status of the phy has changed ( see ether_callback.c )
 * Arguments    : xStatus : true when statyus has become high
 * Return Value : void
 **********************************************************************************************************************/
void prvLinkStatusChange( BaseType_t xStatus )
{
    if( xReportedStatus != xStatus )
    {
        FreeRTOS_printf( ( "prvLinkStatusChange( %d )\n", xStatus ) );
        xReportedStatus = xStatus;
    }
}

/***********************************************************************************************************************
 * Function Name: InitializeNetwork ()
 * Description  :
 * Arguments    : none
 * Return Value : pdTRUE, pdFALSE
 **********************************************************************************************************************/
static int InitializeNetwork( void )
{
    ether_return_t eth_ret;
    BaseType_t return_code = pdFALSE;
    ether_param_t param;
    uint8_t myethaddr[ 6 ] =
    {
        configMAC_ADDR0,
        configMAC_ADDR1,
        configMAC_ADDR2,
        configMAC_ADDR3,
        configMAC_ADDR4,
        configMAC_ADDR5
    }; /*XXX Fix me */

    R_ETHER_PinSet_CHANNEL_0();
    R_ETHER_Initial();
    callback_ether_regist();

    param.channel = ETHER_CHANNEL_0;
    eth_ret = R_ETHER_Control( CONTROL_POWER_ON, param ); /* PHY mode settings, module stop cancellation */

    if( ETHER_SUCCESS != eth_ret )
    {
        return pdFALSE;
    }

    eth_ret = R_ETHER_Open_ZC2( ETHER_CHANNEL_0, myethaddr, ETHER_FLAG_OFF );

    if( ETHER_SUCCESS != eth_ret )
    {
        return pdFALSE;
    }

    return_code = xTaskCreate( prvEMACDeferredInterruptHandlerTask,
                               "ETHER_RECEIVE_CHECK_TASK",
                               512u,
                               0,
                               configMAX_PRIORITIES - 1,
                               &ether_receive_check_task_handle );

    if( pdFALSE == return_code )
    {
        return pdFALSE;
    }

    return pdTRUE;
} /* End of function InitializeNetwork() */


/***********************************************************************************************************************
 * Function Name: SendData ()
 * Description  :
 * Arguments    : pucBuffer, length
 * Return Value : 0 success, negative fail
 **********************************************************************************************************************/
static int16_t SendData( uint8_t * pucBuffer,
                         size_t length ) /*TODO complete stub function */
{
    ether_return_t ret;
    uint8_t * pwrite_buffer;
    uint16_t write_buf_size;

    /* (1) Retrieve the transmit buffer location controlled by the  descriptor. */
    ret = R_ETHER_Write_ZC2_GetBuf( ETHER_CHANNEL_0, ( void ** ) &pwrite_buffer, &write_buf_size );

    if( ETHER_SUCCESS == ret )
    {
        if( write_buf_size >= length )
        {
            memcpy( pwrite_buffer, pucBuffer, length );
        }

        if( length < ETHER_BUFSIZE_MIN )                                             /*under minimum*/
        {
            memset( ( pwrite_buffer + length ), 0, ( ETHER_BUFSIZE_MIN - length ) ); /*padding*/
            length = ETHER_BUFSIZE_MIN;                                              /*resize*/
        }

        ret = R_ETHER_Write_ZC2_SetBuf( ETHER_CHANNEL_0, ( uint16_t ) length );
        ret = R_ETHER_CheckWrite( ETHER_CHANNEL_0 );
    }

    if( ETHER_SUCCESS != ret )
    {
        return -5; /* XXX return meaningful value */
    }
    else
    {
        return 0;
    }
} /* End of function SendData() */


/***********************************************************************************************************************
* Function Name: EINT_Trig_isr
* Description  : Standard frame received interrupt handler
* Arguments    : ectrl - EDMAC and ETHERC control structure
* Return Value : None
* Note         : This callback function is executed when EINT0 interrupt occurred.
***********************************************************************************************************************/
void EINT_Trig_isr( void * ectrl )
{
    ether_cb_arg_t * pdecode;
    BaseType_t xHigherPriorityTaskWoken = pdFALSE;

    pdecode = ( ether_cb_arg_t * ) ectrl;

    if( pdecode->status_eesr & 0x00040000 ) /* EDMAC FR (Frame Receive Event) interrupt */
    {
        if( xTaskToNotify != NULL )
        {
            vTaskNotifyGiveFromISR( ether_receive_check_task_handle, &xHigherPriorityTaskWoken );
        }

        /* If xHigherPriorityTaskWoken is now set to pdTRUE then a context switch
         * should be performed to ensure the interrupt returns directly to the highest
         * priority task.  The macro used for this purpose is dependent on the port in
         * use and may be called portEND_SWITCHING_ISR(). */
        portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
        /*TODO complete interrupt handler for other events. */
    }
} /* End of function EINT_Trig_isr() */


static void clear_all_ether_rx_discriptors( uint32_t event )
{
    int32_t xBytesReceived;
    uint8_t * buffer_pointer;

    /* Avoid compiler warning about unreferenced parameter. */
    ( void ) event;

    while( 1 )
    {
        /* See how much data was received.  */
        xBytesReceived = R_ETHER_Read_ZC2( ETHER_CHANNEL_0, ( void ** ) &buffer_pointer );

        if( 0 > xBytesReceived )
        {
            /* This is an error. Ignored. */
        }
        else if( 0 < xBytesReceived )
        {
            R_ETHER_Read_ZC2_BufRelease( ETHER_CHANNEL_0 );
            iptraceETHERNET_RX_EVENT_LOST();
        }
        else
        {
            break;
        }
    }
}

/***********************************************************************************************************************
 * End of file "NetworkInterface.c"
 **********************************************************************************************************************/
