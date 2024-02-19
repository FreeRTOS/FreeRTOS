/*
 * FreeRTOS V202212.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

/**
 * @file main.c
 * @brief Implements the main function.
 */

/* FreeRTOS include. */
#include <FreeRTOS.h>
#include "task.h"

/* Standard includes. */
#include <signal.h>
#include <conio.h>
#include <setjmp.h>
#include <time.h>
#include <windows.h>

/* Test runner includes. */
#include "test_runner.h"

/* System application includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_DHCP.h"
#include "logging.h"
#include "errhandlingapi.h"
/*#include "iot_system_init.h" */

/*#include "aws_dev_mode_key_provisioning.h" */

/* Unity includes. */
#include "unity.h"

/* Define a name that will be used for LLMNR and NBNS searches. Once running,
 * you can "ping RTOSDemo" instead of pinging the IP address, which is useful when
 * using DHCP. */
#define mainHOST_NAME                  "TestRunner"
#define mainDEVICE_NICK_NAME           "windows_TestRunner"


#define TEST_RUNNER_TASK_STACK_SIZE    10000
#define FIRST_EXCEPTION_HANDLER        1
/* Windows-NT VectoredHandler callback function. */
static LONG CALLBACK prvExceptionHandler( _In_ PEXCEPTION_POINTERS ExceptionInfo );
jmp_buf xMark; /* Address for long jump to jump to. */

/*-----------------------------------------------------------*/

/* Notes if the trace is running or not. */
static BaseType_t xTraceRunning = pdTRUE;

/* Default MAC address configuration.  The demo creates a virtual network
 * connection that uses this MAC address by accessing the raw Ethernet data
 * to and from a real network connection on the host PC.  See the
 * configNETWORK_INTERFACE_TO_USE definition for information on how to configure
 * the real network connection to use. */
const uint8_t ucMACAddress[ 6 ] =
{
    configMAC_ADDR0,
    configMAC_ADDR1,
    configMAC_ADDR2,
    configMAC_ADDR3,
    configMAC_ADDR4,
    configMAC_ADDR5
};

/* The default IP and MAC address used by the demo.  The address configuration
 * defined here will be used if ipconfigUSE_DHCP is 0, or if ipconfigUSE_DHCP is
 * 1 but a DHCP server could not be contacted.  See the online documentation for
 * more information.  In both cases the node can be discovered using
 * "ping RTOSDemo". */
static const uint8_t ucIPAddress[ 4 ] =
{
    configIP_ADDR0,
    configIP_ADDR1,
    configIP_ADDR2,
    configIP_ADDR3
};
static const uint8_t ucNetMask[ 4 ] =
{
    configNET_MASK0,
    configNET_MASK1,
    configNET_MASK2,
    configNET_MASK3
};
static const uint8_t ucGatewayAddress[ 4 ] =
{
    configGATEWAY_ADDR0,
    configGATEWAY_ADDR1,
    configGATEWAY_ADDR2,
    configGATEWAY_ADDR3
};
static const uint8_t ucDNSServerAddress[ 4 ] =
{
    configDNS_SERVER_ADDR0,
    configDNS_SERVER_ADDR1,
    configDNS_SERVER_ADDR2,
    configDNS_SERVER_ADDR3
};

/* Use by the pseudo random number generator. */
static UBaseType_t ulNextRand;

/*-----------------------------------------------------------*/
int main( void )
{
    /* Register the Windows VEH for exceptions. */
    AddVectoredExceptionHandler( FIRST_EXCEPTION_HANDLER, prvExceptionHandler );

    /* Initialize logging for libraries that depend on it. */
    vLoggingInit(
        pdTRUE,
        pdFALSE,
        pdFALSE,
        0,
        0 );

    /* Initialize the network interface.
     *
     ***NOTE*** Tasks that use the network are created in the network event hook
     * when the network is connected and ready for use (see the definition of
     * vApplicationIPNetworkEventHook() below).  The address values passed in here
     * are used if ipconfigUSE_DHCP is set to 0, or if ipconfigUSE_DHCP is set to 1
     * but a DHCP server cannot be contacted. */
    FreeRTOS_printf( ( "FreeRTOS_IPInit\n" ) );
    FreeRTOS_IPInit(
        ucIPAddress,
        ucNetMask,
        ucGatewayAddress,
        ucDNSServerAddress,
        ucMACAddress );

    vTaskStartScheduler();

    return 0;
}
/*-----------------------------------------------------------*/

#if defined( ipconfigIPv4_BACKWARD_COMPATIBLE ) && ( ipconfigIPv4_BACKWARD_COMPATIBLE == 0 )
    void vApplicationIPNetworkEventHook_Multi( eIPCallbackEvent_t eNetworkEvent,
                                               struct xNetworkEndPoint * pxEndPoint )
#else
    void vApplicationIPNetworkEventHook( eIPCallbackEvent_t eNetworkEvent )
#endif /* defined( ipconfigIPv4_BACKWARD_COMPATIBLE ) && ( ipconfigIPv4_BACKWARD_COMPATIBLE == 0 ) */
{
    static BaseType_t xTasksAlreadyCreated = pdFALSE;

    /* If the network has just come up...*/
    if( ( eNetworkEvent == eNetworkUp ) && ( xTasksAlreadyCreated == pdFALSE ) )
    {
        xTaskCreate( TEST_RUNNER_RunTests_task,
                     "TestRunner",
                     TEST_RUNNER_TASK_STACK_SIZE,
                     NULL,
                     tskIDLE_PRIORITY, NULL );

        xTasksAlreadyCreated = pdTRUE;
    }
}

/*-----------------------------------------------------------*/

static LONG CALLBACK prvExceptionHandler( _In_ PEXCEPTION_POINTERS ExceptionInfo )
{
    /* Remove warning about unused parameter */
    ( void ) ExceptionInfo;
    /* If this function is called during a test, the test immediately fails. */
    TEST_FAIL();

    return EXCEPTION_CONTINUE_EXECUTION;
}

/*-----------------------------------------------------------*/

#if ( ( ipconfigUSE_LLMNR != 0 ) || \
    ( ipconfigUSE_NBNS != 0 ) ||    \
    ( ipconfigDHCP_REGISTER_HOSTNAME == 1 ) )

    const char * pcApplicationHostnameHook( void )
    {
        /* This function will be called during the DHCP: the machine will be registered
         * with an IP address plus this name. */
        return mainHOST_NAME;
    }

#endif /* if ( ( ipconfigUSE_LLMNR != 0 ) || ( ipconfigUSE_NBNS != 0 ) || ( ipconfigDHCP_REGISTER_HOSTNAME == 1 ) ) */
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_LLMNR != 0 ) || ( ipconfigUSE_NBNS != 0 )

    #if defined( ipconfigIPv4_BACKWARD_COMPATIBLE ) && ( ipconfigIPv4_BACKWARD_COMPATIBLE == 0 )
        BaseType_t xApplicationDNSQueryHook_Multi( struct xNetworkEndPoint * pxEndPoint,
                                                   const char * pcName )
    #else
        BaseType_t xApplicationDNSQueryHook( const char * pcName )
    #endif /* defined( ipconfigIPv4_BACKWARD_COMPATIBLE ) && ( ipconfigIPv4_BACKWARD_COMPATIBLE == 0 ) */
    {
        BaseType_t xReturn;

        /* Determine if a name lookup is for this node.  Two names are given
         * to this node: that returned by pcApplicationHostnameHook() and that set
         * by mainDEVICE_NICK_NAME. */
        if( _stricmp( pcName, pcApplicationHostnameHook() ) == 0 )
        {
            xReturn = pdPASS;
        }
        else if( _stricmp( pcName, mainDEVICE_NICK_NAME ) == 0 )
        {
            xReturn = pdPASS;
        }
        else
        {
            xReturn = pdFAIL;
        }

        return xReturn;
    }

#endif /* if ( ipconfigUSE_LLMNR != 0 ) || ( ipconfigUSE_NBNS != 0 ) */
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
    const uint32_t ulMSToSleep = 1;
    const TickType_t xKitHitCheckPeriod = pdMS_TO_TICKS( 1000UL );
    static TickType_t xTimeNow, xLastTimeCheck = 0;

    /* vApplicationIdleHook() will only be called if configUSE_IDLE_HOOK is set
     * to 1 in FreeRTOSConfig.h.  It will be called on each iteration of the idle
     * task.  It is essential that code added to this hook function never attempts
     * to block in any way (for example, call xQueueReceive() with a block time
     * specified, or call vTaskDelay()).  If application tasks make use of the
     * vTaskDelete() API function to delete themselves then it is also important
     * that vApplicationIdleHook() is permitted to return to its calling function,
     * because it is the responsibility of the idle task to clean up memory
     * allocated by the kernel to any task that has since deleted itself. */

    /* _kbhit() is a Windows system function, and system functions can cause
     * crashes if they somehow block the FreeRTOS thread.  The call to _kbhit()
     * can be removed if it causes problems.  Limiting the frequency of calls to
     * _kbhit() should minimize the potential for issues. */
    xTimeNow = xTaskGetTickCount();

    if( ( xTimeNow - xLastTimeCheck ) > xKitHitCheckPeriod )
    {
        /* Uncomment the print line to get confirmation that tests are still
         * running if you suspect a previous run resulted in a crash. */
        /* configPRINTF( ( "Running...\n" ) ); /**/
        xLastTimeCheck = xTimeNow;
    }

    /* This is just a trivial example of an idle hook.  It is called on each
     * cycle of the idle task if configUSE_IDLE_HOOK is set to 1 in
     * FreeRTOSConfig.h.  It must *NOT* attempt to block.  In this case the
     * idle task just sleeps to lower the CPU usage. */
    Sleep( ulMSToSleep );
}
/*-----------------------------------------------------------*/

void vAssertCalled( const char * pcFile,
                    uint32_t ulLine )
{
    const uint32_t ulLongSleep = 1000UL;
    volatile uint32_t ulBlockVariable = 0UL;
    volatile char * pcFileName = ( volatile char * ) pcFile;
    volatile uint32_t ulLineNumber = ulLine;

    ( void ) pcFileName;
    ( void ) ulLineNumber;

    printf( "vAssertCalled %s, %ld\n", pcFile, ( long ) ulLine );
    fflush( stdout );

    /* Setting ulBlockVariable to a non-zero value in the debugger will allow
     * this function to be exited. */
    taskDISABLE_INTERRUPTS();
    {
        while( ulBlockVariable == 0UL )
        {
            Sleep( ulLongSleep );
        }
    }
    taskENABLE_INTERRUPTS();
}
/*-----------------------------------------------------------*/

void getUserCmd( char * pucUserCmd )
{
    char cTmp;

    scanf( "%c%c", pucUserCmd, &cTmp );
}
/*-----------------------------------------------------------*/

UBaseType_t uxRand( void )
{
    const uint32_t ulMultiplier = 0x015a4e35UL, ulIncrement = 1UL;

    /* Utility function to generate a pseudo random number. */

    ulNextRand = ( ulMultiplier * ulNextRand ) + ulIncrement;
    return( ( int ) ( ulNextRand ) & 0x7fffUL );
}

BaseType_t xApplicationGetRandomNumber( uint32_t * pulNumber )
{
    *pulNumber = uxRand();

    return pdTRUE;
}

/*
 * Callback that provides the inputs necessary to generate a randomized TCP
 * Initial Sequence Number per RFC 6528.  THIS IS ONLY A DUMMY IMPLEMENTATION
 * THAT RETURNS A PSEUDO RANDOM NUMBER SO IS NOT INTENDED FOR USE IN PRODUCTION
 * SYSTEMS.
 */
extern uint32_t ulApplicationGetNextSequenceNumber( uint32_t ulSourceAddress,
                                                    uint16_t usSourcePort,
                                                    uint32_t ulDestinationAddress,
                                                    uint16_t usDestinationPort )
{
    ( void ) ulSourceAddress;
    ( void ) usSourcePort;
    ( void ) ulDestinationAddress;
    ( void ) usDestinationPort;

    return uxRand();
}
