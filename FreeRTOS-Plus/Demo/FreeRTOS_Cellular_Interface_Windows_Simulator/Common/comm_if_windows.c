/*
 * FreeRTOS V202112.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file comm_if_windows.c
 * @brief Windows Simulator file for cellular comm interface
 */

/*-----------------------------------------------------------*/

/* Windows include file for COM port I/O. */
#include <windows.h>

/* Platform layer includes. */
#include "cellular_platform.h"

/* Cellular comm interface include file. */
#include "cellular_config.h"
#include "cellular_config_defaults.h"
#include "cellular_comm_interface.h"

/*-----------------------------------------------------------*/

/* Define the COM port used as comm interface. */
#ifndef CELLULAR_COMM_INTERFACE_PORT
    #error "Define CELLULAR_COMM_INTERFACE_PORT in cellular_config.h"
#endif
#define CELLULAR_COMM_PATH                   "\\\\.\\"CELLULAR_COMM_INTERFACE_PORT

/* Define the simulated UART interrupt number. */
#define portINTERRUPT_UART                   ( 2UL )

/* Define the read write buffer size. */
#define COMM_TX_BUFFER_SIZE                  ( 8192 )
#define COMM_RX_BUFFER_SIZE                  ( 8192 )

/* Receive thread timeout in ms. */
#define COMM_RECV_THREAD_TIMEOUT             ( 5000 )

/* Write operation timeout in ms. */
#define COMM_WRITE_OPERATION_TIMEOUT         ( 500 )

/* Comm status. */
#define CELLULAR_COMM_OPEN_BIT               ( 0x01U )

/* Comm task event. */
#define COMMTASK_EVT_MASK_STARTED            ( 0x0001UL )
#define COMMTASK_EVT_MASK_ABORT              ( 0x0002UL )
#define COMMTASK_EVT_MASK_ABORTED            ( 0x0004UL )
#define COMMTASK_EVT_MASK_ALL_EVENTS \
    ( COMMTASK_EVT_MASK_STARTED      \
      | COMMTASK_EVT_MASK_ABORT      \
      | COMMTASK_EVT_MASK_ABORTED )
#define COMMTASK_POLLING_TIME_MS             ( 1UL )

/* Platform thread stack size and priority. */
#define COMM_IF_THREAD_DEFAULT_STACK_SIZE    ( 2048U )
#define COMM_IF_THREAD_DEFAULT_PRIORITY      ( tskIDLE_PRIORITY + 5U )

/*-----------------------------------------------------------*/

typedef struct _cellularCommContext
{
    CellularCommInterfaceReceiveCallback_t commReceiveCallback;
    HANDLE commReceiveCallbackThread;
    uint8_t commStatus;
    void * pUserData;
    HANDLE commFileHandle;
    CellularCommInterface_t * pCommInterface;
    bool commTaskThreadStarted;
    EventGroupHandle_t pCommTaskEvent;
} _cellularCommContext_t;

/*-----------------------------------------------------------*/

/**
 * @brief CellularCommInterfaceOpen_t implementation.
 */
static CellularCommInterfaceError_t _prvCommIntfOpen( CellularCommInterfaceReceiveCallback_t receiveCallback,
                                                      void * pUserData,
                                                      CellularCommInterfaceHandle_t * pCommInterfaceHandle );

/**
 * @brief CellularCommInterfaceSend_t implementation.
 */
static CellularCommInterfaceError_t _prvCommIntfSend( CellularCommInterfaceHandle_t commInterfaceHandle,
                                                      const uint8_t * pData,
                                                      uint32_t dataLength,
                                                      uint32_t timeoutMilliseconds,
                                                      uint32_t * pDataSentLength );

/**
 * @brief CellularCommInterfaceRecv_t implementation.
 */
static CellularCommInterfaceError_t _prvCommIntfReceive( CellularCommInterfaceHandle_t commInterfaceHandle,
                                                         uint8_t * pBuffer,
                                                         uint32_t bufferLength,
                                                         uint32_t timeoutMilliseconds,
                                                         uint32_t * pDataReceivedLength );

/**
 * @brief CellularCommInterfaceClose_t implementation.
 */
static CellularCommInterfaceError_t _prvCommIntfClose( CellularCommInterfaceHandle_t commInterfaceHandle );

/**
 * @brief Get default comm interface context.
 *
 * @return On success, SOCKETS_ERROR_NONE is returned. If an error occurred, error code defined
 * in sockets_wrapper.h is returned.
 */
static _cellularCommContext_t * _getCellularCommContext( void );

/**
 * @brief UART interrupt handler.
 *
 * @return pdTRUE if the operation is successful, otherwise
 * an error code indicating the cause of the error.
 */
static uint32_t prvProcessUartInt( void );

/**
 * @brief Set COM port timeout settings.
 *
 * @param[in] hComm COM handle returned by CreateFile.
 *
 * @return On success, IOT_COMM_INTERFACE_SUCCESS is returned. If an error occurred, error code defined
 * in CellularCommInterfaceError_t is returned.
 */
static CellularCommInterfaceError_t _setupCommTimeout( HANDLE hComm );

/**
 * @brief Set COM port control settings.
 *
 * @param[in] hComm COM handle returned by CreateFile.
 *
 * @return On success, IOT_COMM_INTERFACE_SUCCESS is returned. If an error occurred, error code defined
 * in CellularCommInterfaceError_t is returned.
 */
static CellularCommInterfaceError_t _setupCommSettings( HANDLE hComm );

/**
 * @brief Thread routine to generate simulated interrupt.
 *
 * @param[in] pUserData Pointer to _cellularCommContext_t allocated in comm interface open.
 */
static void commTaskThread( void * pUserData );

/**
 * @brief Helper function to setup and create commTaskThread.
 *
 * @param[in] pCellularCommContext Cellular comm interface context allocated in open.
 *
 * @return On success, IOT_COMM_INTERFACE_SUCCESS is returned. If an error occurred, error code defined
 * in CellularCommInterfaceError_t is returned.
 */
static CellularCommInterfaceError_t setupCommTaskThread( _cellularCommContext_t * pCellularCommContext );

/**
 * @brief Helper function to clean commTaskThread.
 *
 * @param[in] pCellularCommContext Cellular comm interface context allocated in open.
 *
 * @return On success, IOT_COMM_INTERFACE_SUCCESS is returned. If an error occurred, error code defined
 * in CellularCommInterfaceError_t is returned.
 */
static CellularCommInterfaceError_t cleanCommTaskThread( _cellularCommContext_t * pCellularCommContext );

/*-----------------------------------------------------------*/

CellularCommInterface_t CellularCommInterface =
{
    .open  = _prvCommIntfOpen,
    .send  = _prvCommIntfSend,
    .recv  = _prvCommIntfReceive,
    .close = _prvCommIntfClose
};

static _cellularCommContext_t _iotCellularCommContext =
{
    .commReceiveCallback       = NULL,
    .commReceiveCallbackThread = NULL,
    .pCommInterface            = &CellularCommInterface,
    .commFileHandle            = NULL,
    .pUserData                 = NULL,
    .commStatus                = 0U,
    .commTaskThreadStarted     = false,
    .pCommTaskEvent            = NULL
};

/* Indicate RX event is received in comm driver. */
static bool rxEvent = false;

/*-----------------------------------------------------------*/

static _cellularCommContext_t * _getCellularCommContext( void )
{
    return &_iotCellularCommContext;
}

/*-----------------------------------------------------------*/

static uint32_t prvProcessUartInt( void )
{
    _cellularCommContext_t * pCellularCommContext = _getCellularCommContext();
    CellularCommInterfaceError_t callbackRet = IOT_COMM_INTERFACE_FAILURE;
    uint32_t retUartInt = pdTRUE;

    if( pCellularCommContext->commReceiveCallback != NULL )
    {
        callbackRet = pCellularCommContext->commReceiveCallback( pCellularCommContext->pUserData,
                                                                 ( CellularCommInterfaceHandle_t ) pCellularCommContext );
    }

    if( callbackRet == IOT_COMM_INTERFACE_SUCCESS )
    {
        retUartInt = pdTRUE;
    }
    else
    {
        retUartInt = pdFALSE;
    }

    return retUartInt;
}

/*-----------------------------------------------------------*/

/**
 * @brief Communication receiver thread function.
 *
 * @param[in] pArgument windows COM port handle.
 * @return 0 if thread function exit without error. Others for error.
 */
DWORD WINAPI _CellularCommReceiveCBThreadFunc( LPVOID pArgument )
{
    DWORD dwCommStatus = 0;
    HANDLE hComm = ( HANDLE ) pArgument;
    BOOL retWait = FALSE;
    DWORD retValue = 0;

    if( hComm == ( HANDLE ) INVALID_HANDLE_VALUE )
    {
        retValue = ERROR_INVALID_HANDLE;
    }

    while( retValue == 0 )
    {
        retWait = WaitCommEvent( hComm, &dwCommStatus, NULL );

        if( ( retWait != FALSE ) && ( ( dwCommStatus & EV_RXCHAR ) != 0 ) )
        {
            if( ( dwCommStatus & EV_RXCHAR ) != 0 )
            {
                rxEvent = true;
            }
        }
        else
        {
            if( ( GetLastError() == ERROR_INVALID_HANDLE ) || ( GetLastError() == ERROR_OPERATION_ABORTED ) )
            {
                /* COM port closed. */
                LogInfo( ( "Cellular COM port %p closed", hComm ) );
            }
            else
            {
                LogInfo( ( "Cellular receiver thread wait comm error %p %d", hComm, GetLastError() ) );
            }

            retValue = GetLastError();

            break;
        }
    }

    return retValue;
}

/*-----------------------------------------------------------*/

static CellularCommInterfaceError_t _setupCommTimeout( HANDLE hComm )
{
    CellularCommInterfaceError_t commIntRet = IOT_COMM_INTERFACE_SUCCESS;
    COMMTIMEOUTS xCommTimeouts = { 0 };
    BOOL Status = TRUE;

    /* Set ReadIntervalTimeout to MAXDWORD and zero values for both
     * ReadTotalTimeoutConstant and ReadTotalTimeoutMultiplier to return
     * immediately with the bytes that already been received. */
    xCommTimeouts.ReadIntervalTimeout = MAXDWORD;
    xCommTimeouts.ReadTotalTimeoutConstant = 0;
    xCommTimeouts.ReadTotalTimeoutMultiplier = 0;
    xCommTimeouts.WriteTotalTimeoutConstant = COMM_WRITE_OPERATION_TIMEOUT;
    xCommTimeouts.WriteTotalTimeoutMultiplier = 0;
    Status = SetCommTimeouts( hComm, &xCommTimeouts );

    if( Status == FALSE )
    {
        LogError( ( "Cellular SetCommTimeouts fail %d", GetLastError() ) );
        commIntRet = IOT_COMM_INTERFACE_FAILURE;
    }

    return commIntRet;
}

/*-----------------------------------------------------------*/

static CellularCommInterfaceError_t _setupCommSettings( HANDLE hComm )
{
    CellularCommInterfaceError_t commIntRet = IOT_COMM_INTERFACE_SUCCESS;
    DCB dcbSerialParams = { 0 };
    BOOL Status = TRUE;

    ( void ) memset( &dcbSerialParams, 0, sizeof( dcbSerialParams ) );
    dcbSerialParams.DCBlength = sizeof( dcbSerialParams );
    dcbSerialParams.BaudRate = CBR_115200;
    dcbSerialParams.fBinary = 1;
    dcbSerialParams.ByteSize = 8;
    dcbSerialParams.StopBits = ONESTOPBIT;
    dcbSerialParams.Parity = NOPARITY;

    dcbSerialParams.fOutxCtsFlow = FALSE;
    dcbSerialParams.fOutxDsrFlow = FALSE;
    dcbSerialParams.fDtrControl = DTR_CONTROL_ENABLE;
    dcbSerialParams.fRtsControl = RTS_CONTROL_ENABLE;

    Status = SetCommState( hComm, &dcbSerialParams );

    if( Status == FALSE )
    {
        LogError( ( "Cellular SetCommState fail %d", GetLastError() ) );
        commIntRet = IOT_COMM_INTERFACE_FAILURE;
    }

    return commIntRet;
}

/*-----------------------------------------------------------*/

static void commTaskThread( void * pUserData )
{
    _cellularCommContext_t * pCellularCommContext = ( _cellularCommContext_t * ) pUserData;
    EventBits_t uxBits = 0;

    /* Inform thread ready. */
    LogInfo( ( "Cellular commTaskThread started" ) );

    if( pCellularCommContext != NULL )
    {
        ( void ) xEventGroupSetBits( pCellularCommContext->pCommTaskEvent,
                                     COMMTASK_EVT_MASK_STARTED );
    }

    while( true )
    {
        /* Wait for notification from eventqueue. */
        uxBits = xEventGroupWaitBits( ( pCellularCommContext->pCommTaskEvent ),
                                      ( ( EventBits_t ) COMMTASK_EVT_MASK_ABORT ),
                                      pdTRUE,
                                      pdFALSE,
                                      pdMS_TO_TICKS( COMMTASK_POLLING_TIME_MS ) );

        if( ( uxBits & ( EventBits_t ) COMMTASK_EVT_MASK_ABORT ) != 0U )
        {
            LogDebug( ( "Abort received, cleaning up!" ) );
            break;
        }
        else
        {
            /* Polling the global share variable to trigger the interrupt. */
            if( rxEvent == true )
            {
                rxEvent = false;
                vPortGenerateSimulatedInterrupt( portINTERRUPT_UART );
            }
        }
    }

    /* Inform thread ready. */
    if( pCellularCommContext != NULL )
    {
        ( void ) xEventGroupSetBits( pCellularCommContext->pCommTaskEvent, COMMTASK_EVT_MASK_ABORTED );
    }

    LogInfo( ( "Cellular commTaskThread exit" ) );
}

/*-----------------------------------------------------------*/

static CellularCommInterfaceError_t setupCommTaskThread( _cellularCommContext_t * pCellularCommContext )
{
    BOOL Status = TRUE;
    EventBits_t uxBits = 0;
    CellularCommInterfaceError_t commIntRet = IOT_COMM_INTERFACE_SUCCESS;

    pCellularCommContext->pCommTaskEvent = xEventGroupCreate();

    if( pCellularCommContext->pCommTaskEvent != NULL )
    {
        /* Create the FreeRTOS thread to generate the simulated interrupt. */
        Status = Platform_CreateDetachedThread( commTaskThread,
                                                ( void * ) pCellularCommContext,
                                                COMM_IF_THREAD_DEFAULT_PRIORITY,
                                                COMM_IF_THREAD_DEFAULT_STACK_SIZE );

        if( Status != true )
        {
            commIntRet = IOT_COMM_INTERFACE_FAILURE;
        }
    }
    else
    {
        commIntRet = IOT_COMM_INTERFACE_FAILURE;
    }

    if( commIntRet == IOT_COMM_INTERFACE_SUCCESS )
    {
        uxBits = xEventGroupWaitBits( ( pCellularCommContext->pCommTaskEvent ),
                                      ( ( EventBits_t ) COMMTASK_EVT_MASK_STARTED | ( EventBits_t ) COMMTASK_EVT_MASK_ABORTED ),
                                      pdTRUE,
                                      pdFALSE,
                                      portMAX_DELAY );

        if( ( uxBits & ( EventBits_t ) COMMTASK_EVT_MASK_STARTED ) == COMMTASK_EVT_MASK_STARTED )
        {
            pCellularCommContext->commTaskThreadStarted = true;
        }
        else
        {
            commIntRet = IOT_COMM_INTERFACE_FAILURE;
            pCellularCommContext->commTaskThreadStarted = false;
        }
    }

    return commIntRet;
}

/*-----------------------------------------------------------*/

static CellularCommInterfaceError_t cleanCommTaskThread( _cellularCommContext_t * pCellularCommContext )
{
    EventBits_t uxBits = 0;
    CellularCommInterfaceError_t commIntRet = IOT_COMM_INTERFACE_SUCCESS;

    /* Wait for the commTaskThreadStarted exit. */
    if( ( pCellularCommContext->commTaskThreadStarted == true ) && ( pCellularCommContext->pCommTaskEvent != NULL ) )
    {
        ( void ) xEventGroupSetBits( pCellularCommContext->pCommTaskEvent,
                                     COMMTASK_EVT_MASK_ABORT );
        uxBits = xEventGroupWaitBits( ( pCellularCommContext->pCommTaskEvent ),
                                      ( ( EventBits_t ) COMMTASK_EVT_MASK_ABORTED ),
                                      pdTRUE,
                                      pdFALSE,
                                      portMAX_DELAY );

        if( ( uxBits & ( EventBits_t ) COMMTASK_EVT_MASK_ABORTED ) != COMMTASK_EVT_MASK_ABORTED )
        {
            LogDebug( ( "Cellular close wait commTaskThread fail" ) );
            commIntRet = IOT_COMM_INTERFACE_FAILURE;
        }

        pCellularCommContext->commTaskThreadStarted = false;
    }

    /* Clean the event group. */
    if( pCellularCommContext->pCommTaskEvent != NULL )
    {
        vEventGroupDelete( pCellularCommContext->pCommTaskEvent );
        pCellularCommContext->pCommTaskEvent = NULL;
    }

    return commIntRet;
}

/*-----------------------------------------------------------*/

static CellularCommInterfaceError_t _prvCommIntfOpen( CellularCommInterfaceReceiveCallback_t receiveCallback,
                                                      void * pUserData,
                                                      CellularCommInterfaceHandle_t * pCommInterfaceHandle )
{
    CellularCommInterfaceError_t commIntRet = IOT_COMM_INTERFACE_SUCCESS;
    HANDLE hComm = ( HANDLE ) INVALID_HANDLE_VALUE;
    BOOL Status = TRUE;
    _cellularCommContext_t * pCellularCommContext = _getCellularCommContext();
    DWORD dwRes = 0;

    if( pCellularCommContext == NULL )
    {
        commIntRet = IOT_COMM_INTERFACE_FAILURE;
    }
    else if( ( pCellularCommContext->commStatus & CELLULAR_COMM_OPEN_BIT ) != 0 )
    {
        LogError( ( "Cellular comm interface opened already" ) );
        commIntRet = IOT_COMM_INTERFACE_FAILURE;
    }
    else
    {
        /* Clear the context. */
        memset( pCellularCommContext, 0, sizeof( _cellularCommContext_t ) );
        pCellularCommContext->pCommInterface = &CellularCommInterface;

        /* If CreateFile fails, the return value is INVALID_HANDLE_VALUE. */
        hComm = CreateFile( TEXT( CELLULAR_COMM_PATH ),
                            GENERIC_READ | GENERIC_WRITE,
                            0,
                            NULL,
                            OPEN_EXISTING,
                            FILE_FLAG_OVERLAPPED,
                            NULL );
    }

    /* Comm port is just closed. Wait 1 second and retry. */
    if( ( hComm == ( HANDLE ) INVALID_HANDLE_VALUE ) && ( GetLastError() == 5 ) )
    {
        vTaskDelay( pdMS_TO_TICKS( 1000UL ) );
        hComm = CreateFile( TEXT( CELLULAR_COMM_PATH ),
                            GENERIC_READ | GENERIC_WRITE,
                            0,
                            NULL,
                            OPEN_EXISTING,
                            FILE_FLAG_OVERLAPPED,
                            NULL );
    }

    if( hComm == ( HANDLE ) INVALID_HANDLE_VALUE )
    {
        LogError( ( "Cellular open COM port fail %d", GetLastError() ) );
        commIntRet = IOT_COMM_INTERFACE_FAILURE;
    }
    else
    {
        Status = SetupComm( hComm, COMM_TX_BUFFER_SIZE, COMM_RX_BUFFER_SIZE );

        if( Status == FALSE )
        {
            LogError( ( "Cellular setup COM port fail %d", GetLastError() ) );
            commIntRet = IOT_COMM_INTERFACE_FAILURE;
        }
    }

    if( commIntRet == IOT_COMM_INTERFACE_SUCCESS )
    {
        commIntRet = _setupCommTimeout( hComm );
    }

    if( commIntRet == IOT_COMM_INTERFACE_SUCCESS )
    {
        commIntRet = _setupCommSettings( hComm );
    }

    if( commIntRet == IOT_COMM_INTERFACE_SUCCESS )
    {
        Status = SetCommMask( hComm, EV_RXCHAR );

        if( Status == FALSE )
        {
            LogError( ( "Cellular SetCommMask fail %d", GetLastError() ) );
            commIntRet = IOT_COMM_INTERFACE_FAILURE;
        }
    }

    if( commIntRet == IOT_COMM_INTERFACE_SUCCESS )
    {
        pCellularCommContext->commReceiveCallback = receiveCallback;
        commIntRet = setupCommTaskThread( pCellularCommContext );
    }

    if( commIntRet == IOT_COMM_INTERFACE_SUCCESS )
    {
        vPortSetInterruptHandler( portINTERRUPT_UART, prvProcessUartInt );
        pCellularCommContext->commReceiveCallbackThread =
            CreateThread( NULL, 0, _CellularCommReceiveCBThreadFunc, hComm, 0, NULL );

        /* CreateThread return NULL for error. */
        if( pCellularCommContext->commReceiveCallbackThread == NULL )
        {
            LogError( ( "Cellular CreateThread fail %d", GetLastError() ) );
            commIntRet = IOT_COMM_INTERFACE_FAILURE;
        }
    }

    if( commIntRet == IOT_COMM_INTERFACE_SUCCESS )
    {
        pCellularCommContext->pUserData = pUserData;
        pCellularCommContext->commFileHandle = hComm;
        *pCommInterfaceHandle = ( CellularCommInterfaceHandle_t ) pCellularCommContext;
        pCellularCommContext->commStatus |= CELLULAR_COMM_OPEN_BIT;
    }
    else
    {
        /* Comm interface open fail. Clean the data. */
        if( hComm != ( HANDLE ) INVALID_HANDLE_VALUE )
        {
            ( void ) CloseHandle( hComm );
            hComm = INVALID_HANDLE_VALUE;
            commIntRet = IOT_COMM_INTERFACE_FAILURE;
        }

        /* Wait for the commReceiveCallbackThread exit. */
        if( pCellularCommContext->commReceiveCallbackThread != NULL )
        {
            dwRes = WaitForSingleObject( pCellularCommContext->commReceiveCallbackThread, COMM_RECV_THREAD_TIMEOUT );

            if( dwRes != WAIT_OBJECT_0 )
            {
                LogDebug( ( "Cellular close wait receiveCallbackThread %p fail %d",
                            pCellularCommContext->commReceiveCallbackThread, dwRes ) );
            }
        }

        pCellularCommContext->commReceiveCallbackThread = NULL;

        /* Wait for the commTaskThreadStarted exit. */
        ( void ) cleanCommTaskThread( pCellularCommContext );
    }

    return commIntRet;
}

/*-----------------------------------------------------------*/

static CellularCommInterfaceError_t _prvCommIntfClose( CellularCommInterfaceHandle_t commInterfaceHandle )
{
    CellularCommInterfaceError_t commIntRet = IOT_COMM_INTERFACE_SUCCESS;
    _cellularCommContext_t * pCellularCommContext = ( _cellularCommContext_t * ) commInterfaceHandle;
    HANDLE hComm = NULL;
    BOOL Status = TRUE;
    DWORD dwRes = 0;

    if( pCellularCommContext == NULL )
    {
        commIntRet = IOT_COMM_INTERFACE_FAILURE;
    }
    else if( ( pCellularCommContext->commStatus & CELLULAR_COMM_OPEN_BIT ) == 0 )
    {
        LogError( ( "Cellular close comm interface is not opened before." ) );
        commIntRet = IOT_COMM_INTERFACE_FAILURE;
    }
    else
    {
        /* clean the receive callback. */
        pCellularCommContext->commReceiveCallback = NULL;

        /* Close the COM port. */
        hComm = pCellularCommContext->commFileHandle;

        if( hComm != ( HANDLE ) INVALID_HANDLE_VALUE )
        {
            Status = CloseHandle( hComm );

            if( Status == FALSE )
            {
                LogDebug( ( "Cellular close CloseHandle %p fail", hComm ) );
                commIntRet = IOT_COMM_INTERFACE_FAILURE;
            }
        }
        else
        {
            commIntRet = IOT_COMM_INTERFACE_FAILURE;
        }

        pCellularCommContext->commFileHandle = NULL;

        /* Wait for the thread exit. */
        if( pCellularCommContext->commReceiveCallbackThread != NULL )
        {
            dwRes = WaitForSingleObject( pCellularCommContext->commReceiveCallbackThread, COMM_RECV_THREAD_TIMEOUT );

            if( dwRes != WAIT_OBJECT_0 )
            {
                LogDebug( ( "Cellular close wait receiveCallbackThread %p fail %d",
                            pCellularCommContext->commReceiveCallbackThread, dwRes ) );
                commIntRet = IOT_COMM_INTERFACE_FAILURE;
            }
            else
            {
                CloseHandle( pCellularCommContext->commReceiveCallbackThread );
            }
        }

        pCellularCommContext->commReceiveCallbackThread = NULL;

        /* Clean the commTaskThread. */
        ( void ) cleanCommTaskThread( pCellularCommContext );

        /* clean the data structure. */
        pCellularCommContext->commStatus &= ~( CELLULAR_COMM_OPEN_BIT );
    }

    return commIntRet;
}

/*-----------------------------------------------------------*/

static CellularCommInterfaceError_t _prvCommIntfSend( CellularCommInterfaceHandle_t commInterfaceHandle,
                                                      const uint8_t * pData,
                                                      uint32_t dataLength,
                                                      uint32_t timeoutMilliseconds,
                                                      uint32_t * pDataSentLength )
{
    CellularCommInterfaceError_t commIntRet = IOT_COMM_INTERFACE_SUCCESS;
    _cellularCommContext_t * pCellularCommContext = ( _cellularCommContext_t * ) commInterfaceHandle;
    HANDLE hComm = NULL;
    OVERLAPPED osWrite = { 0 };
    DWORD dwRes = 0;
    DWORD dwWritten = 0;
    BOOL Status = TRUE;

    if( pCellularCommContext == NULL )
    {
        commIntRet = IOT_COMM_INTERFACE_BAD_PARAMETER;
    }
    else if( ( pCellularCommContext->commStatus & CELLULAR_COMM_OPEN_BIT ) == 0 )
    {
        LogError( ( "Cellular send comm interface is not opened before." ) );
        commIntRet = IOT_COMM_INTERFACE_FAILURE;
    }
    else
    {
        hComm = pCellularCommContext->commFileHandle;
        osWrite.hEvent = CreateEvent( NULL, TRUE, FALSE, NULL );

        if( osWrite.hEvent == NULL )
        {
            LogError( ( "Cellular CreateEvent fail %d", GetLastError() ) );
            commIntRet = IOT_COMM_INTERFACE_FAILURE;
        }
    }

    if( commIntRet == IOT_COMM_INTERFACE_SUCCESS )
    {
        Status = WriteFile( hComm, pData, dataLength, &dwWritten, &osWrite );

        /* WriteFile fail and error is not the ERROR_IO_PENDING. */
        if( ( Status == FALSE ) && ( GetLastError() != ERROR_IO_PENDING ) )
        {
            LogError( ( "Cellular WriteFile fail %d", GetLastError() ) );
            commIntRet = IOT_COMM_INTERFACE_FAILURE;
        }

        if( Status == TRUE )
        {
            *pDataSentLength = ( uint32_t ) dwWritten;
        }
    }

    /* Handle pending I/O. */
    if( ( commIntRet == IOT_COMM_INTERFACE_SUCCESS ) && ( Status == FALSE ) )
    {
        dwRes = WaitForSingleObject( osWrite.hEvent, timeoutMilliseconds );

        switch( dwRes )
        {
            case WAIT_OBJECT_0:

                if( GetOverlappedResult( hComm, &osWrite, &dwWritten, FALSE ) == FALSE )
                {
                    LogError( ( "Cellular GetOverlappedResult fail %d", GetLastError() ) );
                    commIntRet = IOT_COMM_INTERFACE_FAILURE;
                }

                break;

            case STATUS_TIMEOUT:
                LogError( ( "Cellular WaitForSingleObject timeout" ) );
                commIntRet = IOT_COMM_INTERFACE_TIMEOUT;
                break;

            default:
                LogError( ( "Cellular WaitForSingleObject fail %d", dwRes ) );
                commIntRet = IOT_COMM_INTERFACE_FAILURE;
                break;
        }

        *pDataSentLength = ( uint32_t ) dwWritten;
    }

    if( osWrite.hEvent != NULL )
    {
        Status = CloseHandle( osWrite.hEvent );

        if( Status == FALSE )
        {
            LogDebug( ( "Cellular send CloseHandle fail" ) );
        }
    }

    return commIntRet;
}

/*-----------------------------------------------------------*/

static CellularCommInterfaceError_t _prvCommIntfReceive( CellularCommInterfaceHandle_t commInterfaceHandle,
                                                         uint8_t * pBuffer,
                                                         uint32_t bufferLength,
                                                         uint32_t timeoutMilliseconds,
                                                         uint32_t * pDataReceivedLength )
{
    CellularCommInterfaceError_t commIntRet = IOT_COMM_INTERFACE_SUCCESS;
    _cellularCommContext_t * pCellularCommContext = ( _cellularCommContext_t * ) commInterfaceHandle;
    HANDLE hComm = NULL;
    OVERLAPPED osRead = { 0 };
    BOOL Status = TRUE;
    DWORD dwRes = 0;
    DWORD dwRead = 0;

    if( pCellularCommContext == NULL )
    {
        commIntRet = IOT_COMM_INTERFACE_BAD_PARAMETER;
    }
    else if( ( pCellularCommContext->commStatus & CELLULAR_COMM_OPEN_BIT ) == 0 )
    {
        LogError( ( "Cellular read comm interface is not opened before." ) );
        commIntRet = IOT_COMM_INTERFACE_FAILURE;
    }
    else
    {
        hComm = pCellularCommContext->commFileHandle;
        osRead.hEvent = CreateEvent( NULL, TRUE, FALSE, NULL );

        if( osRead.hEvent == NULL )
        {
            LogError( ( "Cellular CreateEvent fail %d", GetLastError() ) );
            commIntRet = IOT_COMM_INTERFACE_FAILURE;
        }
    }

    if( commIntRet == IOT_COMM_INTERFACE_SUCCESS )
    {
        Status = ReadFile( hComm, pBuffer, bufferLength, &dwRead, &osRead );

        if( ( Status == FALSE ) && ( GetLastError() != ERROR_IO_PENDING ) )
        {
            LogError( ( "Cellular ReadFile fail %d", GetLastError() ) );
            commIntRet = IOT_COMM_INTERFACE_FAILURE;
        }

        if( Status == TRUE )
        {
            *pDataReceivedLength = ( uint32_t ) dwRead;
        }
    }

    /* Handle pending I/O. */
    if( ( commIntRet == IOT_COMM_INTERFACE_SUCCESS ) && ( Status == FALSE ) )
    {
        dwRes = WaitForSingleObject( osRead.hEvent, timeoutMilliseconds );

        switch( dwRes )
        {
            case WAIT_OBJECT_0:

                if( GetOverlappedResult( hComm, &osRead, &dwRead, FALSE ) == FALSE )
                {
                    LogError( ( "Cellular receive GetOverlappedResult fail %d", GetLastError() ) );
                    commIntRet = IOT_COMM_INTERFACE_FAILURE;
                }

                break;

            case STATUS_TIMEOUT:
                LogError( ( "Cellular receive WaitForSingleObject timeout" ) );
                commIntRet = IOT_COMM_INTERFACE_TIMEOUT;
                break;

            default:
                LogError( ( "Cellular receive WaitForSingleObject fail %d", dwRes ) );
                commIntRet = IOT_COMM_INTERFACE_FAILURE;
                break;
        }

        *pDataReceivedLength = ( uint32_t ) dwRead;
    }

    if( osRead.hEvent != NULL )
    {
        Status = CloseHandle( osRead.hEvent );

        if( Status == FALSE )
        {
            LogDebug( ( "Cellular recv CloseHandle fail" ) );
        }
    }

    return commIntRet;
}

/*-----------------------------------------------------------*/
