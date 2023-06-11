/*
 * FreeRTOS+TCP <DEVELOPMENT BRANCH>
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
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
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/* libc */
#include <stdlib.h>
#include <sys/types.h>

/* QEMU Slirp Library */
#include <libslirp.h>

#if defined( _WIN32 )
    #include <process.h>
    #include <WinSock2.h>
#else
    #include <poll.h>
    #include <pthread.h>
    #include <signal.h>
    #include <unistd.h>
    #include "wait_for_event.h"
#endif

#include "errno.h"

#include "FreeRTOS.h"
#include "message_buffer.h"
#include "FreeRTOSIPConfig.h"
#include "FreeRTOS_IP.h"

#ifndef IF_MTU_DEFAULT
    #define IF_MTU_DEFAULT    1500U
#endif

#ifndef IF_MRU_DEFAULT
    #define IF_MRU_DEFAULT    1500U
#endif

#define NETWORK_BUFFER_LEN    ( ipconfigNETWORK_MTU + ipSIZE_OF_ETH_HEADER )

#define xSEND_BUFFER_SIZE     ( 32U * NETWORK_BUFFER_LEN )
#define xRECV_BUFFER_SIZE     ( 32U * NETWORK_BUFFER_LEN )
#define xNUM_TIMERS           ( 10U )

#if defined( _WIN32 )
    typedef uintptr_t         Thread_t;
    typedef HANDLE            Mutex_t;
    #define THREAD_RETURN      unsigned
    #define THREAD_FUNC_DEF    __stdcall
    static LARGE_INTEGER xClockFrequency;
    typedef size_t            nfds_t;
#else
    typedef pthread_t         Thread_t;
    typedef pthread_mutex_t   Mutex_t;
    #define THREAD_RETURN    void *
    #define THREAD_FUNC_DEF
#endif /* if defined( _WIN32 ) */

#if !defined( slirp_ssize_t ) && defined( SSIZE_MAX )
    typedef ssize_t slirp_ssize_t;
#endif

typedef struct
{
    /* "Hardware" buffers */
    MessageBufferHandle_t xSendMsgBuffer;
    MessageBufferHandle_t xRecvMsgBuffer;
    StaticMessageBuffer_t xSendMsgBufferStatic;
    StaticMessageBuffer_t xRecvMsgBufferStatic;
    uint8_t pucTxBuffer[ xSEND_BUFFER_SIZE ];
    uint8_t pucRxBuffer[ xRECV_BUFFER_SIZE ];

    BaseType_t xExitFlag;

    /* libslirp context */
    struct Slirp * pxSlirp;

    /* File handle storage */
    nfds_t nfds;
    size_t xPollFdArraySize;
    struct pollfd * pxPollFdArray;

    /* Event used to signal when data is ready in xSendMsgBuffer */
    void * pvSendEvent;

    /*
     * Mutex to arbitrate access to libslirp api between
     * vTransmitThread and  vReceiveThread
     */
    Mutex_t xMutex;
    Thread_t xTxThread;
    Thread_t xRxThread;
} SlirpBackendContext_t;

static int64_t llSlirp_ClockGetNanoSeconds( void * pvOpaque );
static slirp_ssize_t xSlirp_WriteCallback( const void * pvBuffer,
                                           size_t uxLen,
                                           void * pvOpaque );
static void vSlirpGuestError( const char * msg,
                              void * pvOpaque );

/*
 * Stub functions for unimplemented timer feature
 * Should not be called.
 */
static void * pvSlirp_TimerNew( SlirpTimerCb cb,
                                void * pvCallbackContext,
                                void * pvOpaque );
static void vSlirp_TimerFree( void * pvTimer,
                              void * pvOpaque );
static void vSlirp_TimerModify( void * pvTimer,
                                int64_t expire_time,
                                void * pvOpaque );

#if SLIRP_CHECK_VERSION( 4U, 7U, 0U )
    static void * pvSlirpTimerNewOpaque( SlirpTimerId xTimerId,
                                         void * cb_opaque,
                                         void * pvOpaque );
#endif /* SLIRP_CHECK_VERSION( 4U, 7U, 0U ) */

/*
 * Other empty callbacks. Not used for linux port.
 */
static void vSlirp_RegisterPollFd( int lFd,
                                   void * pvCallbackContext );
static void vSlirp_UnRegisterPollFd( int lFd,
                                     void * pvCallbackContext );
static void vSlirp_Notify( void * pvCallbackContext );

#if SLIRP_CHECK_VERSION( 4U, 7U, 0U )
    static void vSlirp_InitCompleted( Slirp * pxSlirp,
                                      void * pvCallbackContext );
#endif /* SLIRP_CHECK_VERSION( 4U, 7U, 0U ) */

/* Receive and Transmit threads */
static THREAD_RETURN THREAD_FUNC_DEF vReceiveThread( void * pvParameters );
static THREAD_RETURN THREAD_FUNC_DEF vTransmitThread( void * pvParameters );

/**
 * @brief Initialize the slirp posix backend.
 *
 * @param[out] pxSendMsgBuffer Location to store the handle of the send message buffer.
 * @param[out] pxRecvMsgBuffer Location to store the handle of the receive message buffer.
 * @param[in] pvSendEvent Pointer of the event struct which the implemenbtation should pend on to receive frames.
 * @param[out] ppvBackendContext Location to store an implementation specific void pointer.
 */
void vMBuffNetifBackendInit( MessageBufferHandle_t * pxSendMsgBuffer,
                             MessageBufferHandle_t * pxRecvMsgBuffer,
                             void * pvSendEvent,
                             void ** ppvBackendContext )
{
    BaseType_t xErrorFlag = pdFALSE;
    void * pvContextBuffer = NULL;
    SlirpBackendContext_t * pxCtx = NULL;

    static const struct SlirpCb xSlirpCallbacks =
    {
        .send_packet          = xSlirp_WriteCallback,
        .guest_error          = vSlirpGuestError,
        .clock_get_ns         = llSlirp_ClockGetNanoSeconds,
        .timer_new            = pvSlirp_TimerNew,
        .timer_free           = vSlirp_TimerFree,
        .timer_mod            = vSlirp_TimerModify,
        .register_poll_fd     = vSlirp_RegisterPollFd,
        .unregister_poll_fd   = vSlirp_UnRegisterPollFd,
        .notify               = vSlirp_Notify,

        #if SLIRP_CHECK_VERSION( 4U, 7U, 0U )
            .init_completed   = vSlirp_InitCompleted,
            .timer_new_opaque = pvSlirpTimerNewOpaque,
        #endif
    };

    static struct SlirpConfig xSlirpConfig = { 0U };

    #if SLIRP_CHECK_VERSION( 4U, 7U, 0U )
        xSlirpConfig.version = 4U;
    #else
        xSlirpConfig.version = 3U;
    #endif

    xSlirpConfig.restricted = false;

    /* IPv4 Enabled */
    xSlirpConfig.in_enabled = true;
    xSlirpConfig.vnetwork.s_addr = FreeRTOS_inet_addr_quick( 10U, 0U, 2U, 0U );
    xSlirpConfig.vnetmask.s_addr = FreeRTOS_inet_addr_quick( 255U, 255U, 255U, 0U );
    xSlirpConfig.vhost.s_addr = FreeRTOS_inet_addr_quick( 10, 0U, 2U, 2U );

    /* IPv6 disabled */
    xSlirpConfig.in6_enabled = false;

    xSlirpConfig.vhostname = NULL;
    xSlirpConfig.tftp_server_name = NULL;
    xSlirpConfig.tftp_path = NULL;
    xSlirpConfig.bootfile = NULL;

    xSlirpConfig.vdhcp_start.s_addr = FreeRTOS_inet_addr_quick( 10U, 0U, 2U, 15U );
    xSlirpConfig.vnameserver.s_addr = FreeRTOS_inet_addr_quick( 10U, 0U, 2U, 3U );
    xSlirpConfig.vdnssearch = NULL;
    xSlirpConfig.vdomainname = NULL;

    xSlirpConfig.if_mtu = IF_MTU_DEFAULT;
    xSlirpConfig.if_mru = IF_MRU_DEFAULT;

    xSlirpConfig.disable_host_loopback = false;
    xSlirpConfig.enable_emu = false;
    // xSlirpConfig.disable_dns = false;
    

    #if SLIRP_CHECK_VERSION( 4U, 7U, 0U )
        xSlirpConfig.disable_dhcp = false;
    #endif /* SLIRP_CHECK_VERSION( 4U, 7U, 0U ) */

    if( ( pxSendMsgBuffer == NULL ) ||
        ( pxRecvMsgBuffer == NULL ) ||
        ( pvSendEvent == NULL ) ||
        ( ppvBackendContext == NULL ) )
    {
        fprintf( stderr, "NULL parameter passed to vMBuffNetifBackendInit.\n" );
    }
    else
    {
        pvContextBuffer = pvPortMalloc( sizeof( SlirpBackendContext_t ) );
    }

    if( pvContextBuffer != NULL )
    {
        pxCtx = ( SlirpBackendContext_t * ) pvContextBuffer;

        pxCtx->xSendMsgBuffer = xMessageBufferCreateStatic( xSEND_BUFFER_SIZE,
                                                            pxCtx->pucTxBuffer,
                                                            &( pxCtx->xSendMsgBufferStatic ) );

        if( pxCtx->xSendMsgBuffer == NULL )
        {
            xErrorFlag = pdTRUE;
        }

        pxCtx->xRecvMsgBuffer = xMessageBufferCreateStatic( xSEND_BUFFER_SIZE,
                                                            pxCtx->pucRxBuffer,
                                                            &( pxCtx->xRecvMsgBufferStatic ) );

        if( pxCtx->xRecvMsgBuffer == NULL )
        {
            xErrorFlag = pdTRUE;
        }

        /* Copy pointer to event struct */
        pxCtx->pvSendEvent = pvSendEvent;

        /* Initialize libslirp */
        pxCtx->pxSlirp = slirp_new( &xSlirpConfig, &xSlirpCallbacks, pvContextBuffer );

        if( pxCtx->pxSlirp )
        {
            #if defined( _WIN32 )
                pxCtx->xMutex = CreateMutex( NULL, FALSE, NULL );
                configASSERT( pxCtx->xMutex != ( Mutex_t ) NULL );

                pxCtx->xTxThread = _beginthreadex( NULL, 0, vTransmitThread, pvContextBuffer, 0, NULL );
                configASSERT( pxCtx->xTxThread != ( Thread_t ) NULL );

                pxCtx->xRxThread = _beginthreadex( NULL, 0, vReceiveThread, pvContextBuffer, 0, NULL );
                configASSERT( pxCtx->xRxThread != ( Thread_t ) NULL );

                ( void ) QueryPerformanceFrequency( &xClockFrequency );
            #else /* if defined( _WIN32 ) */
                int lRslt;
                lRslt = pthread_mutex_init( &( pxCtx->xMutex ), NULL );
                configASSERT( lRslt == 0U );

                lRslt = pthread_create( &( pxCtx->xTxThread ), NULL, vTransmitThread, pvContextBuffer );
                configASSERT( lRslt == 0U );

                lRslt = pthread_create( &( pxCtx->xRxThread ), NULL, vReceiveThread, pvContextBuffer );
                configASSERT( lRslt == 0U );
            #endif /* if defined( _WIN32 ) */
        }
    }

    /* vTaskDelay(2 * 1000); */

    if( pvContextBuffer != NULL )
    {
        *pxSendMsgBuffer = pxCtx->xSendMsgBuffer;
        *pxRecvMsgBuffer = pxCtx->xRecvMsgBuffer;
        *ppvBackendContext = pvContextBuffer;
    }
}

/**
 * @brief Lock the given SlirpBackendContext_t object.
 * @param [in] pxCtx Pointer to the relevant SlirpBackendContext_t.
 */
static inline void vLockSlirpContext( SlirpBackendContext_t * pxCtx )
{
    int lRslt;

    configASSERT( pxCtx != NULL );

    #if defined( _WIN32 )
        lRslt = WaitForSingleObject( pxCtx->xMutex, INFINITE );
        configASSERT( lRslt == 0 );
    #else /* _WIN32 */
        lRslt = pthread_mutex_lock( &( pxCtx->xMutex ) );
        configASSERT( lRslt == 0 );
    #endif /* _WIN32 */
}

/**
 * @brief Unlock the given SlirpBackendContext_t object.
 * @param [in] pxCtx Pointer to the relevant SlirpBackendContext_t.
 */
static inline void vUnlockSlirpContext( SlirpBackendContext_t * pxCtx )
{
    int lRslt;

    #if defined( _WIN32 )
        lRslt = ( int ) ReleaseMutex( pxCtx->xMutex );
        configASSERT( lRslt != 0 );
    #else /* _WIN32 */
        lRslt = pthread_mutex_unlock( &( pxCtx->xMutex ) );
        configASSERT( lRslt == 0 );
    #endif /* _WIN32 */
}

/**
 * @brief Deinitialize function for the slirp backend driver.
 *
 * @param [in,out] pvBackendContext Context to deinitialize / free.
 */
void vMBuffNetifBackendDeInit( void * pvBackendContext )
{
    SlirpBackendContext_t * pxCtx = NULL;

    if( pvBackendContext != NULL )
    {
        pxCtx = ( SlirpBackendContext_t * ) pvBackendContext;

        pxCtx->xExitFlag = pdTRUE;

        #if defined( _WIN32 )
            ( void ) WaitForSingleObject( ( HANDLE ) pxCtx->xTxThread, INFINITE );
            ( void ) WaitForSingleObject( ( HANDLE ) pxCtx->xRxThread, INFINITE );
        #else
            pthread_join( pxCtx->xTxThread, NULL );
            pthread_join( pxCtx->xRxThread, NULL );
        #endif

        vLockSlirpContext( pxCtx );

        #if defined( _WIN32 )
            ( void ) CloseHandle( pxCtx->xMutex );
        #else
            ( void ) pthread_mutex_destroy( &( pxCtx->xMutex ) );
        #endif

        slirp_cleanup( pxCtx->pxSlirp );

        vMessageBufferDelete( pxCtx->xSendMsgBuffer );
        vMessageBufferDelete( pxCtx->xRecvMsgBuffer );

        free( ( void * ) ( pxCtx->pxPollFdArray ) );
        free( ( void * ) pxCtx );
        pxCtx = NULL;
    }
}

/**
 * @brief Callback called by libslirp when an incomming frame is available.
 *
 * @param [in] pvBuffer Pointer to a buffer containing the incoming frame.
 * @param [in] uxLen Length of the incoming frame.
 * @param [in] pvOpaque Opaque context pointer ( points to a SlirpBackendContext_t ).
 * @return slirp_ssize_t 0U Always.
 */
static slirp_ssize_t xSlirp_WriteCallback( const void * pvBuffer,
                                           size_t uxLen,
                                           void * pvOpaque )
{
    SlirpBackendContext_t * pxCtx = ( SlirpBackendContext_t * ) pvOpaque;
    BaseType_t xHigherPriorityTaskWoken = pdFALSE;

    if( uxLen > ( NETWORK_BUFFER_LEN ) )
    {
        fprintf( stderr, "Dropping RX frame of length: %zu > %zu. Frame received from libslirp is too large.\n", uxLen, ( size_t ) NETWORK_BUFFER_LEN );
    }
    else if( uxLen < sizeof( EthernetHeader_t ) )
    {
        fprintf( stderr, "Dropping RX frame of length: %zu < %zu. Frame received from libslirp is too small.\n", uxLen, sizeof( EthernetHeader_t ) );
    }
    else if( xMessageBufferSpacesAvailable( pxCtx->xRecvMsgBuffer ) < ( uxLen + 4U ) )
    {
        fprintf( stderr, "Dropping RX frame of length: %zu. xRecvMsgBuffer is full\n", uxLen );
    }
    else
    {
        size_t uxBytesSent;

        uxBytesSent = xMessageBufferSendFromISR( pxCtx->xRecvMsgBuffer,
                                                 pvBuffer,
                                                 uxLen,
                                                 &xHigherPriorityTaskWoken );

        configASSERT( uxBytesSent == uxLen );

        portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
    }

    return 0U;
}


/**
 * @brief Checks that pxPollFdArray is large enough to accomodate the specified number of file descriptors.
 *
 * @param [in] pxCtx Pointer to the relevant SlirpBackendContext_t.
 * @param [in] xDesiredSize Desired number of file descriptors to store.
 */
static void vEnsurePollfdSize( SlirpBackendContext_t * pxCtx,
                               size_t xDesiredSize )
{
    configASSERT( pxCtx != NULL );

    if( pxCtx->xPollFdArraySize < xDesiredSize )
    {
        size_t xNewSize;

        if( pxCtx->xPollFdArraySize > 0 )
        {
            xNewSize = 2U * pxCtx->xPollFdArraySize;
        }
        else
        {
            xNewSize = 10U;
        }

        if( xDesiredSize > xNewSize )
        {
            xNewSize = xDesiredSize;
        }

        if( pxCtx->pxPollFdArray == NULL )
        {
            pxCtx->pxPollFdArray = ( struct pollfd * ) malloc( xNewSize * sizeof( struct pollfd ) );
        }
        else
        {
            pxCtx->pxPollFdArray = ( struct pollfd * ) realloc( pxCtx->pxPollFdArray, xNewSize * sizeof( struct pollfd ) );
        }

        configASSERT( pxCtx->pxPollFdArray != NULL );

        pxCtx->xPollFdArraySize = xNewSize;
    }
}

/**
 * @brief Convert from a libslirp poll event flag to a posix poll flag.
 * @param [in] lSlirpPollFlags libslirp poll event flags to be converted.
 * @return The equivalent posix poll events.
 */
static inline int lSlirpEventsToNativePollEvents( int lSlirpPollFlags )
{
    int lPosixPollFlags = 0U;

    if( lSlirpPollFlags & SLIRP_POLL_IN )
    {
        lPosixPollFlags |= POLLIN;
    }

    if( lSlirpPollFlags & SLIRP_POLL_OUT )
    {
        lPosixPollFlags |= POLLOUT;
    }

    if( lSlirpPollFlags & SLIRP_POLL_PRI )
    {
        lPosixPollFlags |= POLLPRI;
    }

    if( lSlirpPollFlags & SLIRP_POLL_ERR )
    {
        lPosixPollFlags |= POLLERR;
    }

    if( lSlirpPollFlags & SLIRP_POLL_HUP )
    {
        lPosixPollFlags |= POLLHUP;
    }

    return lPosixPollFlags;
}

/**
 * @brief Convert from posix poll event flags to libslirp poll event flags.
 * @param [in] lPosixPollFlags Posix poll event flags to be converted.
 * @return The equivalent libslirp poll events.
 */
static inline int lNativePollEventsToSlirpEvents( int lPosixPollFlags )
{
    int lSlirpPollFlags = 0U;

    if( lPosixPollFlags & POLLIN )
    {
        lSlirpPollFlags |= SLIRP_POLL_IN;
    }

    if( lPosixPollFlags & POLLOUT )
    {
        lSlirpPollFlags |= SLIRP_POLL_OUT;
    }

    if( lPosixPollFlags & POLLPRI )
    {
        lSlirpPollFlags |= SLIRP_POLL_PRI;
    }

    if( lPosixPollFlags & POLLERR )
    {
        lSlirpPollFlags |= SLIRP_POLL_ERR;
    }

    if( lPosixPollFlags & POLLHUP )
    {
        lSlirpPollFlags |= SLIRP_POLL_HUP;
    }

    return lSlirpPollFlags;
}

/**
 * @brief SlirpAddPollCb implementation passed to libslirp during initialization.
 * @param [in] fd File descriptor to add to the polling list.
 * @param [in] lSlirpFlags Flags to be placed in the relevant events field.
 * @param [in] pvOpaque Opaque pointer to the relevant SlirpBackendContext_t.
 */
static int lSlirpAddPollCallback( int lFd,
                                  int lSlirpFlags,
                                  void * pvOpaque )
{
    SlirpBackendContext_t * pxCtx = ( SlirpBackendContext_t * ) pvOpaque;

    configASSERT( pxCtx != NULL );
    configASSERT( pxCtx->nfds < INT_MAX );

    vEnsurePollfdSize( pxCtx, pxCtx->nfds + 1U );

    pxCtx->pxPollFdArray[ pxCtx->nfds ].fd = lFd;
    pxCtx->pxPollFdArray[ pxCtx->nfds ].events = lSlirpEventsToNativePollEvents( lSlirpFlags );
    pxCtx->pxPollFdArray[ pxCtx->nfds ].revents = 0U;

    pxCtx->nfds++;

    return ( int ) ( pxCtx->nfds - 1U );
}

/**
 * @brief SlirpGetREventsCb implementation passed to libslirp during initialization.
 * @param [in] lIdx Index returned by lSlirpAddPollCallback for the given file descriptor.
 * @param [in] pvOpaque Opaque pointer to the relevant SlirpBackendContext_t.
 * @return An integer with the relevant libslirp polling flags set.
 */
static int lSlirpGetREventsCallback( int lIdx,
                                     void * pvOpaque )
{
    SlirpBackendContext_t * pxCtx = ( SlirpBackendContext_t * ) pvOpaque;
    int rEvents = 0U;
    nfds_t xIndex;

    configASSERT( pxCtx );

    configASSERT( lIdx >= 0 );

    xIndex = ( nfds_t ) lIdx;
    configASSERT( xIndex < pxCtx->nfds );
    configASSERT( xIndex < pxCtx->xPollFdArraySize );

    rEvents = ( pxCtx->pxPollFdArray[ xIndex ].revents );

    return lNativePollEventsToSlirpEvents( rEvents );
}

/**
 * @brief Posix thread implementation which reads from xSendMsgBuffer and passes outgoing frames to libslirp.
 * @param [in] pvParameters Opaque pointer to the relevant SlirpBackendContext_t.
 * @return NULL
 */
static THREAD_RETURN THREAD_FUNC_DEF vTransmitThread( void * pvParameters )
{
    SlirpBackendContext_t * pxCtx = ( SlirpBackendContext_t * ) pvParameters;
    const time_t xMaxMSToWait = 1000;
    uint8_t ucFrameSendBuffer[ NETWORK_BUFFER_LEN ];

    #if !defined( _WIN32 )
        sigset_t set;

        /*
         * disable signals to avoid treating this thread as a FreeRTOS task and putting
         * it to sleep by the scheduler
         */
        sigfillset( &set );
        pthread_sigmask( SIG_SETMASK, &set, NULL );
    #endif /* !defined(_WIN32) */

    configASSERT( pxCtx != NULL );

    while( pxCtx->xExitFlag == pdFALSE )
    {
        /* Wait until notified of something to send. */
        #if defined( _WIN32 )
            ( void ) WaitForSingleObject( pxCtx->pvSendEvent, ( DWORD ) xMaxMSToWait );
        #else
            event_wait_timed( pxCtx->pvSendEvent, xMaxMSToWait );
        #endif

        while( xMessageBufferIsEmpty( pxCtx->xSendMsgBuffer ) == pdFALSE )
        {
            BaseType_t xHigherPriorityTaskWoken = pdFALSE;
            size_t uxFrameLen = xMessageBufferReceiveFromISR( pxCtx->xSendMsgBuffer, ucFrameSendBuffer, sizeof( ucFrameSendBuffer ), &xHigherPriorityTaskWoken );

            vLockSlirpContext( pxCtx );
            {
                slirp_input( pxCtx->pxSlirp, ucFrameSendBuffer, uxFrameLen );
            }
            vUnlockSlirpContext( pxCtx );

            portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
        }
    }

    return ( THREAD_RETURN ) NULL;
}

/**
 * @brief Posix thread implementation which polls file descriptors used by libslirp and forwards
 *        incoming frames to xRecvMsgBuffer indirectly by calling xSlirp_WriteCallback.
 * @param [in] pvParameters Opaque pointer to the relevant SlirpBackendContext_t.
 * @return NULL
 */
static THREAD_RETURN THREAD_FUNC_DEF vReceiveThread( void * pvParameters )
{
    SlirpBackendContext_t * pxCtx = ( SlirpBackendContext_t * ) pvParameters;

    #if !defined( _WIN32 )
        sigset_t set;

        /*
         * disable signals to avoid treating this thread as a FreeRTOS task and putting
         * it to sleep by the scheduler
         */
        sigfillset( &set );
        pthread_sigmask( SIG_SETMASK, &set, NULL );
    #endif /* !defined(_WIN32) */

    configASSERT( pxCtx != NULL );

    while( pxCtx->xExitFlag == pdFALSE )
    {
        int lPollRslt;

        uint32_t ulPollerTimeoutMs = 100 * 1000U;

        vLockSlirpContext( pxCtx );
        {
            pxCtx->nfds = 0;
            slirp_pollfds_fill( pxCtx->pxSlirp, &ulPollerTimeoutMs, lSlirpAddPollCallback, pxCtx );
        }
        vUnlockSlirpContext( pxCtx );

        errno = 0;
        #if defined( _WIN32 )
            lPollRslt = WSAPoll( pxCtx->pxPollFdArray, pxCtx->nfds, ( int ) ulPollerTimeoutMs );
        #else /* _WIN32 */
            lPollRslt = poll( pxCtx->pxPollFdArray, pxCtx->nfds, ulPollerTimeoutMs );
        #endif /* _WIN32 */

        if( lPollRslt > 0 )
        {
            lPollRslt = 0;
        }

        vLockSlirpContext( pxCtx );
        {
            slirp_pollfds_poll( pxCtx->pxSlirp, lPollRslt, lSlirpGetREventsCallback, ( void * ) pxCtx );
        }
        vUnlockSlirpContext( pxCtx );
    }

    return ( THREAD_RETURN ) NULL;
}

#if defined( _WIN32 )

/**
 * @brief Callback function passed to libslirp to get the current time in nanoseconds.
 *
 * @param [in] pvOpaque Opaque context pointer (unused).
 * @return int64_t Current time in nanoseconds.
 */
    static int64_t llSlirp_ClockGetNanoSeconds( void * pvOpaque )
    {
        LARGE_INTEGER xTime;
        int64_t lTime;

        ( void ) pvOpaque;

        QueryPerformanceCounter( &xTime );

        lTime = ( xTime.QuadPart * 1000000000 / xClockFrequency.QuadPart );

        return lTime;
    }
#else /* if defined( _WIN32 ) */

/**
 * @brief Callback function passed to libslirp to get the current time in nanoseconds.
 *
 * @param [in] pvOpaque Opaque context pointer (unused).
 * @return int64_t Current time in nanoseconds.
 */
    static int64_t llSlirp_ClockGetNanoSeconds( void * pvOpaque )
    {
        struct timespec ts;
        int64_t llTimeNs = 0;

        clock_gettime( CLOCK_MONOTONIC, &ts );

        ( void ) pvOpaque;

        llTimeNs = ( ts.tv_sec * 1000000000LL ) + ts.tv_nsec;
        return llTimeNs;
    }
#endif /* if defined( _WIN32 ) */

/**
 * @brief Callback funciton passed to libslirp to report a runtime error.
 *
 * @param [in] msg Error message
 * @param pvOpaque Opaque context pointer (unused).
 */
static void vSlirpGuestError( const char * msg,
                              void * pvOpaque )
{
    fprintf( stderr, "libslirp guest error: %s\n", msg );
    exit( 1 );
}

/**
 * @brief Stub callback function for libslirp timer API.
 *
 * @param cb Unused.
 * @param pvCallbackContext Unused.
 * @param pvOpaque Unused.
 * @return void* NULL
 */
static void * pvSlirp_TimerNew( SlirpTimerCb cb,
                                void * pvCallbackContext,
                                void * pvOpaque )
{
    /* Stub */
    ( void ) cb;
    ( void ) pvCallbackContext;
    ( void ) pvOpaque;
    configASSERT( 0 );
    return NULL;
}

/**
 * @brief Stub callback function for libslirp timer API.
 *
 * @param pvTimer Unused.
 * @param pvOpaque Unused.
 */
static void vSlirp_TimerFree( void * pvTimer,
                              void * pvOpaque )
{
    /* Stub */
    ( void ) pvTimer;
    ( void ) pvOpaque;
    configASSERT( 0 );
}

/**
 * @brief Stub callback function for libslirp timer API.
 *
 * @param pvTimer Unused.
 * @param expire_time Unused.
 * @param pvOpaque Unused.
 */
static void vSlirp_TimerModify( void * pvTimer,
                                int64_t expire_time,
                                void * pvOpaque )
{
    /* Stub */
    ( void ) pvTimer;
    ( void ) expire_time;
    ( void ) pvOpaque;
    configASSERT( 0 );
}

#if SLIRP_CHECK_VERSION( 4U, 7U, 0U )

/**
 * @brief Stub callback function for libslirp timer API.
 *
 * @param xTimerId Unused.
 * @param cb_opaque Unused.
 * @param pvOpaque Unused.
 * @return void* NULL
 */
    static void * pvSlirpTimerNewOpaque( SlirpTimerId xTimerId,
                                         void * cb_opaque,
                                         void * pvOpaque )
    {
        /* Stub */
        ( void ) xTimerId;
        ( void ) cb_opaque;
        ( void ) pvOpaque;
        configASSERT( 0 );
        return NULL;
    }
#endif /* SLIRP_CHECK_VERSION( 4U, 7U, 0U ) */

/**
 * @brief Called by libslipr when a new file descriptor / socket is opened.
 *
 * @param lFd File descriptor to watch.
 * @param pvOpaque Pointer to driver context.
 */
static void vSlirp_RegisterPollFd( int lFd,
                                   void * pvOpaque )
{
    SlirpBackendContext_t * pxCtx = ( SlirpBackendContext_t * ) pvOpaque;

    configASSERT( pxCtx != NULL );

    ( void ) lFd;

    vEnsurePollfdSize( pxCtx, pxCtx->nfds + 1 );
}

/**
 * @brief Stub callback function.
 *
 * @param lFd Unused.
 * @param pvOpaque Unused.
 */
static void vSlirp_UnRegisterPollFd( int lFd,
                                     void * pvOpaque )
{
    ( void ) lFd;
    ( void ) pvOpaque;
}

/**
 * @brief Stub callback function.
 *
 * @param pvOpaque Unused.
 */
static void vSlirp_Notify( void * pvOpaque )
{
    /* Stub */
    ( void ) pvOpaque;
}

#if SLIRP_CHECK_VERSION( 4U, 7U, 0U )

/**
 * @brief Stub callback function.
 *
 * @param pxSlirp Unused.
 * @param pvOpaque Unused.
 */
    static void vSlirp_InitCompleted( Slirp * pxSlirp,
                                      void * pvOpaque )
    {
        /* Stub */
        ( void ) pxSlirp;
        ( void ) pvOpaque;
    }
#endif /* SLIRP_CHECK_VERSION( 4U, 7U, 0U ) */
