/*
 * FreeRTOS OTA V1.2.0
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
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard library includes. */
#include <stddef.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "timers.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* OTA agent includes. */
#include "aws_iot_ota_agent.h"
#include "aws_ota_agent_config.h"

/* OTA pal includes. */
#include "aws_iot_ota_pal.h"

/* Internal header file for shared OTA definitions. */
#include "aws_iot_ota_agent_internal.h"

/* JSON job document parser includes. */
#include "jsmn.h"

/* Mbed tls base64 includes. */
#include "mbedtls/base64.h"

/* Application version includes. */
#include "aws_application_version.h"

/* OTA interface includes. */
#include "aws_iot_ota_interface.h"

/* OTA event handler definiton. */

typedef OTA_Err_t ( * OTAEventHandler_t )( OTA_EventData_t * pxEventMsg );

/* OTA Agent state table entry. */

typedef struct OTAStateTableEntry
{
    OTA_State_t xCurrentState;
    OTA_Event_t xEventId;
    OTAEventHandler_t xHandler;
    OTA_State_t xNextState;
} OTAStateTableEntry_t;

/*
 * This union allows us to access document model parameter addresses as their
 * actual type without casting every time we access a parameter.
 */

typedef union MultiParmPtr
{
    char ** ppcPtr;
    const char ** ppccPtr;
    uint32_t * pulPtr;
    uint32_t ulVal;
    bool * pbBoolPtr;
    Sig256_t ** ppxSig256Ptr;
    void ** ppvPtr;
} MultiParmPtr_t;

/* Array containing pointer to the OTA event structures used to send events to the OTA task. */

static OTA_EventMsg_t xQueueData[ OTA_NUM_MSG_Q_ENTRIES ];

/* Buffers used to push event data. */

static OTA_EventData_t xEventBuffer[ otaconfigMAX_NUM_OTA_DATA_BUFFERS ];

/* OTA control interface. */

static OTA_ControlInterface_t xOTA_ControlInterface;

/* OTA data interface. */

static OTA_DataInterface_t xOTA_DataInterface;

/*
 * Test a null terminated string against a JSON string of known length and return whether
 * it is the same or not.
 */

static bool JSON_IsCStringEqual( const char * pcJSONString,
                                 uint32_t ulLen,
                                 const char * pcCString );

/* OTA agent private function prototypes. */

/* OTA agent task fucntion. */

static void prvOTAAgentTask( void * pvUnused );

/* Start a timer used for sending data requests. */

static void prvStartRequestTimer( uint32_t xPeriodMS );

/* Stop the data request timer. */

static void prvStopRequestTimer( void );

/* Data request timer callback. */

static void prvRequestTimer_Callback( TimerHandle_t T );

/* Start the self test timer if in self-test mode. */

static BaseType_t prvStartSelfTestTimer( void );

/* Stop the OTA self test timer if it is running. */

static void prvStopSelfTestTimer( void );

/* Self-test timer callback, reset the device if this timer expires. */

static void prvSelfTestTimer_Callback( TimerHandle_t T );

/* Called when the OTA agent receives a file data block message. */

static IngestResult_t prvIngestDataBlock( OTA_FileContext_t * C,
                                          uint8_t * pcRawMsg,
                                          uint32_t ulMsgSize,
                                          OTA_Err_t * pxCloseResult );

/* Called to update the filecontext structure from the job. */

static OTA_FileContext_t * prvGetFileContextFromJob( const char * pcRawMsg,
                                                     uint32_t ulMsgLen );

/* Get an available OTA file context structure or NULL if none available. */

static OTA_FileContext_t * prvGetFreeContext( void );

/* Parse a JSON document using the specified document model. */

static DocParseErr_t prvParseJSONbyModel( const char * pcJSON,
                                          uint32_t ulMsgLen,
                                          JSON_DocModel_t * pxDocModel );

/* Parse the OTA job document, validate and return the populated OTA context if valid. */

static OTA_FileContext_t * prvParseJobDoc( const char * pcJSON,
                                           uint32_t ulMsgLen,
                                           bool * pbUpdateJob );

/* Close an open OTA file context and free it. */

static bool prvOTA_Close( OTA_FileContext_t * const C );


/* Internal function to set the image state including an optional reason code. */

static OTA_Err_t prvSetImageStateWithReason( OTA_ImageState_t eState,
                                             uint32_t ulReason );

/* The default OTA callback handler if not provided to OTA_AgentInit(). */

static void prvDefaultOTACompleteCallback( OTA_JobEvent_t eEvent );

/* Default Custom Callback handler if not provided to OTA_AgentInit() */

static OTA_JobParseErr_t prvDefaultCustomJobCallback( const char * pcJSON,
                                                      uint32_t ulMsgLen );

/* Default Reset Device handler if not provided to OTA_AgentInit() */

static OTA_Err_t prvPAL_DefaultResetDevice( uint32_t ulServerFileID );

/* Default Get Platform Image State handler if not provided to OTA_AgentInit() */

static OTA_PAL_ImageState_t prvPAL_DefaultGetPlatformImageState( uint32_t ulServerFileID );

/* Default Set Platform Image State handler if not provided to OTA_AgentInit() */

static OTA_Err_t prvPAL_DefaultSetPlatformImageState( uint32_t ulServerFileID,
                                                      OTA_ImageState_t eState );

/* Default Activate New Image handler if not provided to OTA_AgentInit() */

static OTA_Err_t prvPAL_DefaultActivateNewImage( uint32_t ulServerFileID );

/* A helper function to cleanup resources during OTA agent shutdown. */

static void prvAgentShutdownCleanup( void );

/* Search the document model for a key that matches the specified JSON key. */

static DocParseErr_t prvSearchModelForTokenKey( JSON_DocModel_t * pxDocModel,
                                                const char * pcJSONString,
                                                uint32_t ulStrLen,
                                                uint16_t * pulMatchingIndexResult );

/*
 * Prepare the document model for use by sanity checking the initialization parameters
 * and detecting all required parameters.
 */

static DocParseErr_t prvInitDocModel( JSON_DocModel_t * pxDocModel,
                                      const JSON_DocParam_t * pxBodyDef,
                                      uint32_t ulContextBaseAddr,
                                      uint32_t ulContextSize,
                                      uint16_t usNumJobParams );

/* Attempt to force reset the device. Normally called by the agent when a self test rejects the update. */

static OTA_Err_t prvResetDevice( void );

/* Check if the platform is in self-test. */

static bool prvInSelftest( void );

/* Function to handle events that were unexpected in the current state. */

static void prvHandleUnexpectedEvents( OTA_EventMsg_t * pxEventMsg );

/* OTA state event handler functions. */

static OTA_Err_t prvStartHandler( OTA_EventData_t * pxEventData );
static OTA_Err_t prvRequestJobHandler( OTA_EventData_t * pxEventData );
static OTA_Err_t prvProcessJobHandler( OTA_EventData_t * pxEventData );
static OTA_Err_t prvInSelfTestHandler( OTA_EventData_t * pxEventData );
static OTA_Err_t prvInitFileHandler( OTA_EventData_t * pxEventData );
static OTA_Err_t prvProcessDataHandler( OTA_EventData_t * pxEventData );
static OTA_Err_t prvRequestDataHandler( OTA_EventData_t * pxEventData );
static OTA_Err_t prvShutdownHandler( OTA_EventData_t * pxEventData );
static OTA_Err_t prvCloseFileHandler( OTA_EventData_t * pxEventData );
static OTA_Err_t prvUserAbortHandler( OTA_EventData_t * pxEventData );
static OTA_Err_t prvSuspendHandler( OTA_EventData_t * pxEventData );
static OTA_Err_t prvResumeHandler( OTA_EventData_t * pxEventData );
static OTA_Err_t prvJobNotificationHandler( OTA_EventData_t * pxEventData );

/* OTA default callback initializer. */

#define OTA_JOB_CALLBACK_DEFAULT_INITIALIZER                           \
    {                                                                  \
        .xAbort = prvPAL_Abort,                                        \
        .xActivateNewImage = prvPAL_DefaultActivateNewImage,           \
        .xCloseFile = prvPAL_CloseFile,                                \
        .xCreateFileForRx = prvPAL_CreateFileForRx,                    \
        .xGetPlatformImageState = prvPAL_DefaultGetPlatformImageState, \
        .xResetDevice = prvPAL_DefaultResetDevice,                     \
        .xSetPlatformImageState = prvPAL_DefaultSetPlatformImageState, \
        .xWriteBlock = prvPAL_WriteBlock,                              \
        .xCompleteCallback = prvDefaultOTACompleteCallback,            \
        .xCustomJobCallback = prvDefaultCustomJobCallback              \
    }

/* This is THE OTA agent context and initialization state. */

static OTA_AgentContext_t xOTA_Agent =
{
    .eState                        = eOTA_AgentState_Stopped,
    .pcThingName                   = { 0 },
    .pvConnectionContext           = NULL,
    .pxOTA_Files                   = { { 0 } }, /*lint !e910 !e9080 Zero initialization of all members of the single file context structure.*/
    .ulServerFileID                = 0,
    .pcOTA_Singleton_ActiveJobName = NULL,
    .pcClientTokenFromJob          = NULL,
    .ulTimestampFromJob            = 0,
    .pvSelfTestTimer               = NULL,
    .xRequestTimer                 = NULL,
    .xOTA_EventQueue               = NULL,
    .eImageState                   = eOTA_ImageState_Unknown,
    .xPALCallbacks                 = OTA_JOB_CALLBACK_DEFAULT_INITIALIZER,
    .ulNumOfBlocksToReceive        = 1,
    .xStatistics                   = { 0 },
    .xOTA_ThreadSafetyMutex        = NULL,
    .ulRequestMomentum             = 0
};

static OTAStateTableEntry_t OTATransitionTable[] =
{
    /*STATE ,                              EVENT ,                               ACTION ,               NEXT STATE                         */
    { eOTA_AgentState_Ready,               eOTA_AgentEvent_Start,               prvStartHandler,           eOTA_AgentState_RequestingJob       },
    { eOTA_AgentState_RequestingJob,       eOTA_AgentEvent_RequestJobDocument,  prvRequestJobHandler,      eOTA_AgentState_WaitingForJob       },
    { eOTA_AgentState_RequestingJob,       eOTA_AgentEvent_RequestTimer,        prvRequestJobHandler,      eOTA_AgentState_WaitingForJob       },
    { eOTA_AgentState_WaitingForJob,       eOTA_AgentEvent_ReceivedJobDocument, prvProcessJobHandler,      eOTA_AgentState_CreatingFile        },
    { eOTA_AgentState_CreatingFile,        eOTA_AgentEvent_StartSelfTest,       prvInSelfTestHandler,      eOTA_AgentState_WaitingForJob       },
    { eOTA_AgentState_CreatingFile,        eOTA_AgentEvent_CreateFile,          prvInitFileHandler,        eOTA_AgentState_RequestingFileBlock },
    { eOTA_AgentState_CreatingFile,        eOTA_AgentEvent_RequestTimer,        prvInitFileHandler,        eOTA_AgentState_RequestingFileBlock },
    { eOTA_AgentState_RequestingFileBlock, eOTA_AgentEvent_RequestFileBlock,    prvRequestDataHandler,     eOTA_AgentState_WaitingForFileBlock },
    { eOTA_AgentState_RequestingFileBlock, eOTA_AgentEvent_RequestTimer,        prvRequestDataHandler,     eOTA_AgentState_WaitingForFileBlock },
    { eOTA_AgentState_WaitingForFileBlock, eOTA_AgentEvent_ReceivedFileBlock,   prvProcessDataHandler,     eOTA_AgentState_WaitingForFileBlock },
    { eOTA_AgentState_WaitingForFileBlock, eOTA_AgentEvent_RequestTimer,        prvRequestDataHandler,     eOTA_AgentState_WaitingForFileBlock },
    { eOTA_AgentState_WaitingForFileBlock, eOTA_AgentEvent_RequestFileBlock,    prvRequestDataHandler,     eOTA_AgentState_WaitingForFileBlock },
    { eOTA_AgentState_WaitingForFileBlock, eOTA_AgentEvent_RequestJobDocument,  prvRequestJobHandler,      eOTA_AgentState_WaitingForJob       },
    { eOTA_AgentState_WaitingForFileBlock, eOTA_AgentEvent_ReceivedJobDocument, prvJobNotificationHandler, eOTA_AgentState_RequestingJob       },
    { eOTA_AgentState_WaitingForFileBlock, eOTA_AgentEvent_CloseFile,           prvCloseFileHandler,       eOTA_AgentState_WaitingForJob       },
    { eOTA_AgentState_Suspended,           eOTA_AgentEvent_Resume,              prvResumeHandler,          eOTA_AgentState_RequestingJob       },
    { eOTA_AgentState_All,                 eOTA_AgentEvent_Suspend,             prvSuspendHandler,         eOTA_AgentState_Suspended           },
    { eOTA_AgentState_All,                 eOTA_AgentEvent_UserAbort,           prvUserAbortHandler,       eOTA_AgentState_WaitingForJob       },
    { eOTA_AgentState_All,                 eOTA_AgentEvent_Shutdown,            prvShutdownHandler,        eOTA_AgentState_ShuttingDown        },
};

static const char * pcOTA_AgentState_Strings[ eOTA_AgentState_All ] =
{
    "Init",
    "Ready",
    "RequestingJob",
    "WaitingForJob",
    "CreatingFile",
    "RequestingFileBlock",
    "WaitingForFileBlock",
    "ClosingFile",
    "Suspended",
    "ShuttingDown",
    "Stopped"
};

static const char * pcOTA_Event_Strings[ eOTA_AgentEvent_Max ] =
{
    "Start",
    "StartSelfTest",
    "RequestJobDocument",
    "ReceivedJobDocument",
    "CreateFile",
    "RequestFileBlock",
    "ReceivedFileBlock",
    "RequestTimer",
    "CloseFile",
    "Suspend",
    "Resume",
    "UserAbort",
    "Shutdown"
};

/*
 * This is a private function which checks if the platform is in self-test.
 */
static bool prvInSelftest( void )
{
    bool bSelfTest = false;

    /*
     * Get the platform state from the OTA pal layer.
     */
    if( xOTA_Agent.xPALCallbacks.xGetPlatformImageState( xOTA_Agent.ulServerFileID ) == eOTA_PAL_ImageState_PendingCommit )
    {
        bSelfTest = true;
    }

    return bSelfTest;
}

/*
 * If we're in self test mode, start the self test timer. The latest job should
 * also be in the self test state. We must complete the self test and either
 * accept or reject the image before the timer expires or we shall reset the
 * device to initiate a roll back of the MCU firmware bundle. This will catch
 * issues like improper credentials or a device that is connected to a non-
 * production stage of the job service resulting in a different job queue being
 * used.
 */
static BaseType_t prvStartSelfTestTimer( void )
{
    DEFINE_OTA_METHOD_NAME( "prvStartSelfTestTimer" );
    static const char pcTimerName[] = "OTA_SelfTest";
    BaseType_t xTimerStarted = pdFALSE;
    static StaticTimer_t xTimerBuffer;

    if( prvInSelftest() == true )
    {
        if( xOTA_Agent.pvSelfTestTimer == NULL )
        {
            xOTA_Agent.pvSelfTestTimer = xTimerCreateStatic( pcTimerName,
                                                             pdMS_TO_TICKS( otaconfigSELF_TEST_RESPONSE_WAIT_MS ),
                                                             pdFALSE, NULL, prvSelfTestTimer_Callback,
                                                             &xTimerBuffer );

            if( xOTA_Agent.pvSelfTestTimer != NULL )
            {
                xTimerStarted = xTimerStart( xOTA_Agent.pvSelfTestTimer, portMAX_DELAY );
            }
            else
            {
                /* Static timers are guaranteed to be created unless we pass in a NULL buffer. */
            }
        }
        else
        {
            xTimerStarted = xTimerReset( xOTA_Agent.pvSelfTestTimer, portMAX_DELAY );
        }

        /* Common check for whether the timer was started or not. It should be impossible to not start. */
        if( xTimerStarted == pdTRUE )
        {
            OTA_LOG_L1( "[%s] Starting %s timer.\r\n", OTA_METHOD_NAME, pcTimerName );
        }
        else
        {
            OTA_LOG_L1( "[%s] ERROR: failed to reset/start %s timer.\r\n", OTA_METHOD_NAME, pcTimerName );
        }
    }

    return xTimerStarted;
}

/* When the self test response timer expires, reset the device since we're likely broken. */

static void prvSelfTestTimer_Callback( TimerHandle_t T )
{
    DEFINE_OTA_METHOD_NAME( "prvSelfTestTimer_Callback" );
    ( void ) T;

    OTA_LOG_L1( "[%s] Self test failed to complete within %ums\r\n", OTA_METHOD_NAME, otaconfigSELF_TEST_RESPONSE_WAIT_MS );
    ( void ) xOTA_Agent.xPALCallbacks.xResetDevice( xOTA_Agent.ulServerFileID );
}

/* Stop the OTA self test timer if it is running. */

static void prvStopSelfTestTimer( void )
{
    DEFINE_OTA_METHOD_NAME( "prvStopSelfTestTimer" );

    if( xOTA_Agent.pvSelfTestTimer != NULL )
    {
        ( void ) xTimerStop( xOTA_Agent.pvSelfTestTimer, portMAX_DELAY );
        OTA_LOG_L1( "[%s] Stopping the self test timer.\r\n", OTA_METHOD_NAME );
    }
}

/*
 * When the OTA request timer expires, signal the OTA task to request the file.
 */

static void prvRequestTimer_Callback( TimerHandle_t T )
{
    ( void ) T;
    OTA_EventMsg_t xEventMsg = { 0 };

    /*
     * Send event to OTA agent task.
     */
    xEventMsg.xEventId = eOTA_AgentEvent_RequestTimer;
    ( void ) OTA_SignalEvent( &xEventMsg );
}

/* Create and start or reset the OTA request timer to kick off the process if needed.
 * Do not output an important log message on reset since this gets called every time a file
 * block is received. Use log level 2 at most.
 */
static void prvStartRequestTimer( uint32_t xPeriodMS )
{
    DEFINE_OTA_METHOD_NAME( "prvStartRequestTimer" );
    static const char pcTimerName[] = "OTA_FileRequest";

    BaseType_t xTimerStarted = pdFALSE;

    if( xOTA_Agent.xRequestTimer == NULL )
    {
        xOTA_Agent.xRequestTimer = xTimerCreate( pcTimerName,
                                                 pdMS_TO_TICKS( xPeriodMS ),
                                                 pdFALSE,
                                                 NULL,
                                                 prvRequestTimer_Callback );

        if( xOTA_Agent.xRequestTimer != NULL )
        {
            xTimerStarted = xTimerStart( xOTA_Agent.xRequestTimer, 0 );
        }
    }
    else
    {
        xTimerStarted = xTimerReset( xOTA_Agent.xRequestTimer, portMAX_DELAY );
    }

    if( xTimerStarted == pdTRUE )
    {
        OTA_LOG_L2( "[%s] Starting %s timer.\r\n", OTA_METHOD_NAME, pcTimerName );
    }
    else
    {
        OTA_LOG_L1( "[%s] ERROR: failed to reset/start %s timer.\r\n", OTA_METHOD_NAME, pcTimerName );
    }
}

/* Stop the firmware request timer if it is running. */

static void prvStopRequestTimer( void )
{
    DEFINE_OTA_METHOD_NAME( "prvStopRequestTimer" );

    if( xOTA_Agent.xRequestTimer != NULL )
    {
        ( void ) xTimerStop( xOTA_Agent.xRequestTimer, 0 );
        OTA_LOG_L1( "[%s] Stopping request timer.\r\n", OTA_METHOD_NAME );
    }
}

static OTA_Err_t prvUpdateJobStatusFromImageState( OTA_ImageState_t eState,
                                                   int32_t lSubReason )
{
    OTA_Err_t xErr = kOTA_Err_Uninitialized;
    int32_t lReason = 0;

    if( eState == eOTA_ImageState_Testing )
    {
        /* We discovered we're ready for test mode, put job status in self_test active. */
        xErr = xOTA_ControlInterface.prvUpdateJobStatus( &xOTA_Agent, eJobStatus_InProgress, eJobReason_SelfTestActive, 0 );
    }
    else
    {
        if( eState == eOTA_ImageState_Accepted )
        {
            /* Now that we've accepted the firmware update, we can complete the job. */
            prvStopSelfTestTimer();
            xErr = xOTA_ControlInterface.prvUpdateJobStatus( &xOTA_Agent, eJobStatus_Succeeded, eJobReason_Accepted, xAppFirmwareVersion.u.lVersion32 );
        }
        else
        {
            /*
             * The firmware update was either rejected or aborted, complete the job as FAILED (Job service
             * doesn't allow us to set REJECTED after the job has been started already).
             */
            lReason = ( eState == eOTA_ImageState_Rejected ) ? eJobReason_Rejected : eJobReason_Aborted;
            xErr = xOTA_ControlInterface.prvUpdateJobStatus( &xOTA_Agent, eJobStatus_Failed, lReason, lSubReason );
        }

        /*
         * We don't need the job name memory anymore since we're done with this job.
         */
        vPortFree( xOTA_Agent.pcOTA_Singleton_ActiveJobName );
        xOTA_Agent.pcOTA_Singleton_ActiveJobName = NULL;
    }

    return xErr;
}

static OTA_Err_t prvSetImageStateWithReason( OTA_ImageState_t eState,
                                             uint32_t ulReason )
{
    OTA_Err_t xErr = kOTA_Err_Uninitialized;

    configASSERT( ( eState > eOTA_ImageState_Unknown ) && ( eState <= eOTA_LastImageState ) );

    /* Call the platform specific code to set the image state. */
    xErr = xOTA_Agent.xPALCallbacks.xSetPlatformImageState( xOTA_Agent.ulServerFileID, eState );

    /*
     * If the platform image state couldn't be set correctly, force fail the update by setting the
     * image state to "Rejected" unless it's already in "Aborted".
     */
    if( ( xErr != kOTA_Err_None ) && ( eState != eOTA_ImageState_Aborted ) )
    {
        eState = eOTA_ImageState_Rejected; /*lint !e9044 intentionally override eState since we failed within this function. */

        /*
         * Capture the failure reason if not already set (and we're not already Aborted as checked above). Otherwise Keep
         * the original reject reason code since it is possible for the PAL to fail to update the image state in some
         * cases (e.g. a reset already caused the bundle rollback and we failed to rollback again).
         */
        if( ulReason == kOTA_Err_None )
        {
            ulReason = xErr; /*lint !e9044 intentionally override ulReason since we failed within this function. */
        }
    }

    /* Now update the image state and job status on service side. */
    xOTA_Agent.eImageState = eState;

    if( xOTA_Agent.pcOTA_Singleton_ActiveJobName != NULL )
    {
        xErr = prvUpdateJobStatusFromImageState( eState, ( int32_t ) ulReason );
    }
    else
    {
        xErr = kOTA_Err_NoActiveJob;
    }

    return xErr;
}

static OTA_Err_t prvPAL_DefaultResetDevice( uint32_t ulServerFileID )
{
    ( void ) ulServerFileID;
    return prvPAL_ResetDevice();
}

static OTA_PAL_ImageState_t prvPAL_DefaultGetPlatformImageState( uint32_t ulServerFileID )
{
    ( void ) ulServerFileID;
    return prvPAL_GetPlatformImageState();
}

static OTA_Err_t prvPAL_DefaultSetPlatformImageState( uint32_t ulServerFileID,
                                                      OTA_ImageState_t eState )
{
    ( void ) ulServerFileID;
    ( void ) eState;
    return prvPAL_SetPlatformImageState( eState );
}

static OTA_Err_t prvPAL_DefaultActivateNewImage( uint32_t ulServerFileID )
{
    ( void ) ulServerFileID;
    return prvPAL_ActivateNewImage();
}

/* This is the default OTA callback handler if the user does not provide
 * one. It will do the basic activation and commit of accepted images.
 *
 * The OTA agent has completed the update job or determined we're in self
 * test mode. If the update was accepted, we want to activate the new image
 * by resetting the device to boot the new firmware.  If now is not a good
 * time to reset the device, the user should have registered their own
 * callback function instead of this default callback to allow user level
 * self tests and a user scheduled reset.
 * If the update was rejected, just return without doing anything and we'll
 * wait for another job. If it reported that we're in self test mode, we've
 * already successfully connected to the AWS IoT broker and received the
 * latest job so go ahead and set the image as accepted since there is no
 * additional user level tests to run.
 */
static void prvDefaultOTACompleteCallback( OTA_JobEvent_t eEvent )
{
    DEFINE_OTA_METHOD_NAME( "prvDefaultOTACompleteCallback" );

    OTA_Err_t xErr = kOTA_Err_Uninitialized;

    if( eEvent == eOTA_JobEvent_Activate )
    {
        OTA_LOG_L1( "[%s] Received eOTA_JobEvent_Activate callback from OTA Agent.\r\n", OTA_METHOD_NAME );
        ( void ) OTA_ActivateNewImage();
    }
    else if( eEvent == eOTA_JobEvent_Fail )
    {
        OTA_LOG_L1( "[%s] Received eOTA_JobEvent_Fail callback from OTA Agent.\r\n", OTA_METHOD_NAME );
        /* Nothing special to do. The OTA agent handles it. */
    }
    else if( eEvent == eOTA_JobEvent_StartTest )
    {
        /* Accept the image since it was a good transfer
         * and networking and services are all working.
         * and networking and services are all working.
         */
        OTA_LOG_L1( "[%s] Received eOTA_JobEvent_StartTest callback from OTA Agent.\r\n", OTA_METHOD_NAME );
        xErr = OTA_SetImageState( eOTA_ImageState_Accepted );

        if( xErr != kOTA_Err_None )
        {
            OTA_LOG_L1( "[%s] Error! Failed to set image state.\r\n", OTA_METHOD_NAME );
        }
    }
    else
    {
        OTA_LOG_L1( "[%s] Received invalid job event %d from OTA Agent.\r\n", OTA_METHOD_NAME, eEvent );
    }
}

static OTA_JobParseErr_t prvDefaultCustomJobCallback( const char * pcJSON,
                                                      uint32_t ulMsgLen )
{
    DEFINE_OTA_METHOD_NAME( "prvDefaultCustomJobCallback" );
    ( void ) ulMsgLen;
    ( void ) pcJSON;

    /*
     * The JOB document received is not conforming to AFR OTA job document and it could be a
     * custom OTA job. No applciation callback for handling custom job document is registered so just
     * return error code for non conforming job document from this default handler.
     */
    OTA_LOG_L2( "[%s] Received Custom Job inside OTA Agent which is not supported.\r\n", OTA_METHOD_NAME );

    return eOTA_JobParseErr_NonConformingJobDoc;
}

static void prvSetPALCallbacks( const OTA_PAL_Callbacks_t * pxCallbacks )
{
    configASSERT( pxCallbacks != NULL );

    if( pxCallbacks->xAbort != NULL )
    {
        xOTA_Agent.xPALCallbacks.xAbort = pxCallbacks->xAbort;
    }
    else
    {
        xOTA_Agent.xPALCallbacks.xAbort = prvPAL_Abort;
    }

    if( pxCallbacks->xActivateNewImage != NULL )
    {
        xOTA_Agent.xPALCallbacks.xActivateNewImage = pxCallbacks->xActivateNewImage;
    }
    else
    {
        xOTA_Agent.xPALCallbacks.xActivateNewImage = prvPAL_DefaultActivateNewImage;
    }

    if( pxCallbacks->xCloseFile != NULL )
    {
        xOTA_Agent.xPALCallbacks.xCloseFile = pxCallbacks->xCloseFile;
    }
    else
    {
        xOTA_Agent.xPALCallbacks.xCloseFile = prvPAL_CloseFile;
    }

    if( pxCallbacks->xCreateFileForRx != NULL )
    {
        xOTA_Agent.xPALCallbacks.xCreateFileForRx = pxCallbacks->xCreateFileForRx;
    }
    else
    {
        xOTA_Agent.xPALCallbacks.xCreateFileForRx = prvPAL_CreateFileForRx;
    }

    if( pxCallbacks->xGetPlatformImageState != NULL )
    {
        xOTA_Agent.xPALCallbacks.xGetPlatformImageState = pxCallbacks->xGetPlatformImageState;
    }
    else
    {
        xOTA_Agent.xPALCallbacks.xGetPlatformImageState = prvPAL_DefaultGetPlatformImageState;
    }

    if( pxCallbacks->xResetDevice != NULL )
    {
        xOTA_Agent.xPALCallbacks.xResetDevice = pxCallbacks->xResetDevice;
    }
    else
    {
        xOTA_Agent.xPALCallbacks.xResetDevice = prvPAL_DefaultResetDevice;
    }

    if( pxCallbacks->xSetPlatformImageState != NULL )
    {
        xOTA_Agent.xPALCallbacks.xSetPlatformImageState = pxCallbacks->xSetPlatformImageState;
    }
    else
    {
        xOTA_Agent.xPALCallbacks.xSetPlatformImageState = prvPAL_DefaultSetPlatformImageState;
    }

    if( pxCallbacks->xWriteBlock != NULL )
    {
        xOTA_Agent.xPALCallbacks.xWriteBlock = pxCallbacks->xWriteBlock;
    }
    else
    {
        xOTA_Agent.xPALCallbacks.xWriteBlock = prvPAL_WriteBlock;
    }

    if( pxCallbacks->xCompleteCallback != NULL )
    {
        xOTA_Agent.xPALCallbacks.xCompleteCallback = pxCallbacks->xCompleteCallback;
    }
    else
    {
        xOTA_Agent.xPALCallbacks.xCompleteCallback = prvDefaultOTACompleteCallback;
    }

    if( pxCallbacks->xCustomJobCallback != NULL )
    {
        xOTA_Agent.xPALCallbacks.xCustomJobCallback = pxCallbacks->xCustomJobCallback;
    }
    else
    {
        xOTA_Agent.xPALCallbacks.xCustomJobCallback = prvDefaultCustomJobCallback;
    }
}

static OTA_Err_t prvStartHandler( OTA_EventData_t * pxEventData )
{
    DEFINE_OTA_METHOD_NAME( "prvStartHandler" );

    ( void ) pxEventData;
    OTA_Err_t xReturn = kOTA_Err_None;
    OTA_EventMsg_t xEventMsg = { 0 };

    /* Start self-test timer, if platform is in self-test. */
    prvStartSelfTestTimer();

    /* Send event to OTA task to get job document. */
    xEventMsg.xEventId = eOTA_AgentEvent_RequestJobDocument;

    if( !OTA_SignalEvent( &xEventMsg ) )
    {
        xReturn = kOTA_Err_EventQueueSendFailed;
    }

    return xReturn;
}

static OTA_Err_t prvInSelfTestHandler( OTA_EventData_t * pxEventData )
{
    DEFINE_OTA_METHOD_NAME( "prvInSelfTestHandler" );

    ( void ) pxEventData;

    OTA_LOG_L1( "[%s] prvInSelfTestHandler, platform is in self-test.\r\n", OTA_METHOD_NAME );

    /* Check the platform's OTA update image state. It should also be in self test. */
    if( prvInSelftest() == true )
    {
        /* Callback for application specific self-test. */
        xOTA_Agent.xPALCallbacks.xCompleteCallback( eOTA_JobEvent_StartTest );
    }
    else
    {
        /* The job is in self test but the platform image state is not so it could be
         * an attack on the platform image state. Reject the update (this should also
         * cause the image to be erased), aborting the job and reset the device. */
        OTA_LOG_L1( "[%s] Job in self test but platform state is not!\r\n", OTA_METHOD_NAME );
        ( void ) prvSetImageStateWithReason( eOTA_ImageState_Rejected, kOTA_Err_ImageStateMismatch );
        ( void ) prvResetDevice(); /* Ignore return code since there's nothing we can do if we can't force reset. */
    }

    return kOTA_Err_None;
}

static OTA_Err_t prvRequestJobHandler( OTA_EventData_t * pxEventData )
{
    DEFINE_OTA_METHOD_NAME( "prvRequestJobHandler" );

    ( void ) pxEventData;
    OTA_Err_t xReturn = kOTA_Err_Uninitialized;
    OTA_EventMsg_t xEventMsg = { 0 };

    /*
     * Check if any pending jobs are available from job service.
     */
    xReturn = xOTA_ControlInterface.prvRequestJob( &xOTA_Agent );

    if( xReturn != kOTA_Err_None )
    {
        if( xOTA_Agent.ulRequestMomentum < otaconfigMAX_NUM_REQUEST_MOMENTUM )
        {
            /* Start the request timer. */
            prvStartRequestTimer( otaconfigFILE_REQUEST_WAIT_MS );
            xOTA_Agent.ulRequestMomentum++;

            xReturn = kOTA_Err_PublishFailed;
        }
        else
        {
            /* Stop the request timer. */
            prvStopRequestTimer();

            /* Send shutdown event to the OTA Agent task. */
            xEventMsg.xEventId = eOTA_AgentEvent_Shutdown;

            if( !OTA_SignalEvent( &xEventMsg ) )
            {
                xReturn = kOTA_Err_EventQueueSendFailed;
            }
            else
            {
                /*
                 * Too many requests have been sent without a response or too many failures
                 * when trying to publish the request message. Abort. Store attempt count in low bits.
                 */
                xReturn = ( uint32_t ) kOTA_Err_MomentumAbort | ( otaconfigMAX_NUM_REQUEST_MOMENTUM & ( uint32_t ) kOTA_PAL_ErrMask );
            }
        }
    }
    else
    {
        /* Stop the timer as job request was successful. */
        prvStopRequestTimer();

        /* Reset the request momentum. */
        xOTA_Agent.ulRequestMomentum = 0;
    }

    return xReturn;
}

static OTA_Err_t prvProcessJobHandler( OTA_EventData_t * pxEventData )
{
    DEFINE_OTA_METHOD_NAME( "prvProcessJobHandler" );

    OTA_Err_t xReturn = kOTA_Err_Uninitialized;
    OTA_FileContext_t * xOTAFileContext = NULL;
    OTA_EventMsg_t xEventMsg = { 0 };

    /*
     * Parse the job document and update file information in the file context.
     */
    xOTAFileContext = prvGetFileContextFromJob( ( const char * ) pxEventData->ucData,
                                                pxEventData->ulDataLength );

    /*
     * A null context here could either mean we didn't receive a valid job or it could
     * signify that we're in the self test phase (where the OTA file transfer is already
     * completed and we've reset the device and are now running the new firmware). We
     * will check the state to determine which case we're in.
     */
    if( xOTAFileContext == NULL )
    {
        /*
         * If the OTA job is in the self_test state, alert the application layer.
         */
        if( OTA_GetImageState() == eOTA_ImageState_Testing )
        {
            /* Send event to OTA task to start self-test. */
            xEventMsg.xEventId = eOTA_AgentEvent_StartSelfTest;

            if( !OTA_SignalEvent( &xEventMsg ) )
            {
                xReturn = kOTA_Err_EventQueueSendFailed;
            }
            else
            {
                xReturn = kOTA_Err_None;
            }
        }
        else
        {
            /*
             * If the job context returned NULL and the image state is not in the self_test state,
             * then an error occurred parsing the OTA job message.  Abort the OTA job with a parse error.
             *
             * If there is a valid job id, then a job status update will be sent.
             */
            ( void ) prvSetImageStateWithReason( eOTA_ImageState_Aborted, kOTA_Err_JobParserError );

            xReturn = kOTA_Err_JobParserError;
        }
    }
    else
    {
        /*
         * If the platform is not in the self_test state, initiate file download.
         */
        if( prvInSelftest() == false )
        {
            /* Init data interface routines */
            xReturn = prvSetDataInterface( &xOTA_DataInterface, xOTA_Agent.pxOTA_Files[ xOTA_Agent.ulFileIndex ].pucProtocols );

            if( xReturn == kOTA_Err_None )
            {
                OTA_LOG_L1( "[%s] Setting OTA data inerface.\r\n", OTA_METHOD_NAME );

                /* Received a valid context so send event to request file blocks. */
                xEventMsg.xEventId = eOTA_AgentEvent_CreateFile;

                /*Send the event to OTA Agent task. */
                if( !OTA_SignalEvent( &xEventMsg ) )
                {
                    xReturn = kOTA_Err_EventQueueSendFailed;
                }
            }
            else
            {
                /*
                 * Failed to set the data interface so abort the OTA.If there is a valid job id,
                 * then a job status update will be sent.
                 */
                ( void ) prvSetImageStateWithReason( eOTA_ImageState_Aborted, xReturn );
            }
        }
        else
        {
            /*
             * Received a job that is not in self-test but platform is, so reboot the device to allow
             * roll back to previous image.
             */
            OTA_LOG_L1( "[%s] Platform is in self-test but job is not, rebooting !  \r\n", OTA_METHOD_NAME );
            ( void ) xOTA_Agent.xPALCallbacks.xResetDevice( xOTA_Agent.ulServerFileID );
        }
    }

    /*Free the OTA event buffer. */
    prvOTAEventBufferFree( pxEventData );

    return xReturn;
}

static OTA_Err_t prvInitFileHandler( OTA_EventData_t * pxEventData )
{
    ( void ) pxEventData;
    OTA_Err_t xErr = kOTA_Err_Uninitialized;
    OTA_EventMsg_t xEventMsg = { 0 };

    xErr = xOTA_DataInterface.prvInitFileTransfer( &xOTA_Agent );

    if( xErr != kOTA_Err_None )
    {
        if( xOTA_Agent.ulRequestMomentum < otaconfigMAX_NUM_REQUEST_MOMENTUM )
        {
            /* Start the request timer. */
            prvStartRequestTimer( otaconfigFILE_REQUEST_WAIT_MS );
            xOTA_Agent.ulRequestMomentum++;
            xErr = kOTA_Err_PublishFailed;
        }
        else
        {
            /* Stop the request timer. */
            prvStopRequestTimer();

            /* Send shutdown event. */
            xEventMsg.xEventId = eOTA_AgentEvent_Shutdown;

            if( !OTA_SignalEvent( &xEventMsg ) )
            {
                xErr = kOTA_Err_EventQueueSendFailed;
            }
            else
            {
                /* Too many requests have been sent without a response or too many failures
                 * when trying to publish the request message. Abort. Store attempt count in low bits. */
                xErr = ( uint32_t ) kOTA_Err_MomentumAbort | ( otaconfigMAX_NUM_REQUEST_MOMENTUM & ( uint32_t ) kOTA_PAL_ErrMask );
            }
        }
    }
    else
    {
        /* Reset the request momentum. */
        xOTA_Agent.ulRequestMomentum = 0;

        xEventMsg.xEventId = eOTA_AgentEvent_RequestFileBlock;

        if( !OTA_SignalEvent( &xEventMsg ) )
        {
            xErr = kOTA_Err_EventQueueSendFailed;
        }
    }

    return xErr;
}

static OTA_Err_t prvRequestDataHandler( OTA_EventData_t * pxEventData )
{
    ( void ) pxEventData;
    OTA_Err_t xErr = kOTA_Err_Uninitialized;
    OTA_EventMsg_t xEventMsg = { 0 };

    if( xOTA_Agent.pxOTA_Files[ xOTA_Agent.ulFileIndex ].ulBlocksRemaining > 0U )
    {
        /* Start the request timer. */
        prvStartRequestTimer( otaconfigFILE_REQUEST_WAIT_MS );

        if( xOTA_Agent.ulRequestMomentum < otaconfigMAX_NUM_REQUEST_MOMENTUM )
        {
            /* Request data blocks. */
            xErr = xOTA_DataInterface.prvRequestFileBlock( &xOTA_Agent );

            /* Each request increases the momentum until a response is received. Too much momentum is
             * interpreted as a failure to communicate and will cause us to abort the OTA. */
            xOTA_Agent.ulRequestMomentum++;
        }
        else
        {
            /* Stop the request timer. */
            prvStopRequestTimer();

            /* Failed to send data request abort and close file. */
            ( void ) prvSetImageStateWithReason( eOTA_ImageState_Aborted, xErr );

            /* Send shutdown event. */
            xEventMsg.xEventId = eOTA_AgentEvent_Shutdown;

            if( !OTA_SignalEvent( &xEventMsg ) )
            {
                xErr = kOTA_Err_EventQueueSendFailed;
            }
            else
            {
                /* Too many requests have been sent without a response or too many failures
                 * when trying to publish the request message. Abort. Store attempt count in low bits. */
                xErr = ( uint32_t ) kOTA_Err_MomentumAbort | ( otaconfigMAX_NUM_REQUEST_MOMENTUM & ( uint32_t ) kOTA_PAL_ErrMask );

                /* Reset the request momentum. */
                xOTA_Agent.ulRequestMomentum = 0;
            }
        }
    }

    return xErr;
}

static OTA_Err_t prvProcessDataHandler( OTA_EventData_t * pxEventData )
{
    DEFINE_OTA_METHOD_NAME( "prvProcessDataMessage" );

    OTA_Err_t xErr = kOTA_Err_Uninitialized;
    OTA_Err_t xCloseResult = kOTA_Err_Uninitialized;
    OTA_EventMsg_t xEventMsg = { 0 };

    /* Get the file context. */
    OTA_FileContext_t * pxFileContext = &xOTA_Agent.pxOTA_Files[ xOTA_Agent.ulFileIndex ];

    /* Ingest data blocks received. */
    IngestResult_t xResult = prvIngestDataBlock( pxFileContext,
                                                 pxEventData->ucData,
                                                 pxEventData->ulDataLength,
                                                 &xCloseResult );

    if( xResult < eIngest_Result_Accepted_Continue )
    {
        /* Negative result codes mean we should stop the OTA process
         * because we are either done or in an unrecoverable error state.
         * We don't want to hang on to the resources. */

        /* Stop the request timer.*/
        prvStopRequestTimer();

        if( xResult == eIngest_Result_FileComplete )
        {
            /* File receive is complete and authenticated. Update the job status with the self_test ready identifier. */
            xErr = xOTA_ControlInterface.prvUpdateJobStatus( &xOTA_Agent, eJobStatus_InProgress, eJobReason_SigCheckPassed, 0 );

            if( xErr != kOTA_Err_None )
            {
                OTA_LOG_L2( "[%s] Failed to update job status %d\r\n", OTA_METHOD_NAME, xErr );
            }
        }
        else
        {
            OTA_LOG_L1( "[%s] Aborting due to IngestResult_t error %d\r\n", OTA_METHOD_NAME, ( int32_t ) xResult );

            /* Call the platform specific code to reject the image. */
            xErr = xOTA_Agent.xPALCallbacks.xSetPlatformImageState( xOTA_Agent.ulServerFileID, eOTA_ImageState_Rejected );

            if( xErr != kOTA_Err_None )
            {
                OTA_LOG_L2( "[%s] Error trying to set platform image state (0x%08x)\r\n", OTA_METHOD_NAME, ( int32_t ) xErr );
            }

            /* Update the job status with the with failure code. */
            xErr = xOTA_ControlInterface.prvUpdateJobStatus( &xOTA_Agent, eJobStatus_FailedWithVal, ( int32_t ) xCloseResult, ( int32_t ) xResult );

            if( xErr != kOTA_Err_None )
            {
                OTA_LOG_L2( "[%s] Failed to update job status %d\r\n", OTA_METHOD_NAME, xErr );
            }
        }

        /* Send event to close file. */
        xEventMsg.xEventId = eOTA_AgentEvent_CloseFile;

        if( !OTA_SignalEvent( &xEventMsg ) )
        {
            OTA_LOG_L2( "[%s] Failed to singal OTA agent to close file.", OTA_METHOD_NAME );
        }

        /* Let main application know of our result. */
        xOTA_Agent.xPALCallbacks.xCompleteCallback( ( xResult == eIngest_Result_FileComplete ) ? eOTA_JobEvent_Activate : eOTA_JobEvent_Fail );

        /* Free any remaining string memory holding the job name since this job is done. */
        if( xOTA_Agent.pcOTA_Singleton_ActiveJobName != NULL )
        {
            vPortFree( xOTA_Agent.pcOTA_Singleton_ActiveJobName );
            xOTA_Agent.pcOTA_Singleton_ActiveJobName = NULL;
        }
    }
    else
    {
        if( xResult == eIngest_Result_Accepted_Continue )
        {
            /* We're actively receiving a file so update the job status as needed. */
            /* First reset the momentum counter since we received a good block. */
            xOTA_Agent.ulRequestMomentum = 0;
            xErr = xOTA_ControlInterface.prvUpdateJobStatus( &xOTA_Agent, eJobStatus_InProgress, eJobReason_Receiving, 0 );

            if( xErr != kOTA_Err_None )
            {
                OTA_LOG_L2( "[%s] Failed to update job status %d\r\n", OTA_METHOD_NAME, xErr );
            }
        }

        if( xOTA_Agent.ulNumOfBlocksToReceive > 1U )
        {
            xOTA_Agent.ulNumOfBlocksToReceive--;
        }
        else
        {
            prvStartRequestTimer( otaconfigFILE_REQUEST_WAIT_MS );

            xEventMsg.xEventId = eOTA_AgentEvent_RequestFileBlock;

            if( !OTA_SignalEvent( &xEventMsg ) )
            {
                OTA_LOG_L2( "[%s] Failed to signal OTA agent to close file.", OTA_METHOD_NAME );
            }
        }
    }

    /* Release the data buffer. */
    prvOTAEventBufferFree( pxEventData );

    return kOTA_Err_None;
}

static OTA_Err_t prvCloseFileHandler( OTA_EventData_t * pxEventData )
{
    DEFINE_OTA_METHOD_NAME( "prvCloseFileHandler" );

    ( void ) pxEventData;

    OTA_LOG_L2( "[%s] Closing File. %d\r\n", OTA_METHOD_NAME );

    ( void ) prvOTA_Close( &( xOTA_Agent.pxOTA_Files[ xOTA_Agent.ulFileIndex ] ) );

    return kOTA_Err_None;
}

static OTA_Err_t prvUserAbortHandler( OTA_EventData_t * pxEventData )
{
    ( void ) pxEventData;
    OTA_Err_t xErr = kOTA_Err_Uninitialized;

    /* If we have active Job abort it and close the file. */
    if( xOTA_Agent.pcOTA_Singleton_ActiveJobName != NULL )
    {
        xErr = prvSetImageStateWithReason( eOTA_ImageState_Aborted, kOTA_Err_UserAbort );

        if( xErr == kOTA_Err_None )
        {
            ( void ) prvOTA_Close( &( xOTA_Agent.pxOTA_Files[ xOTA_Agent.ulFileIndex ] ) );
        }
    }

    return xErr;
}

static OTA_Err_t prvShutdownHandler( OTA_EventData_t * pxEventData )
{
    DEFINE_OTA_METHOD_NAME( "prvShutdownHandler" );
    ( void ) pxEventData;

    OTA_LOG_L2( "[%s] Shutting Down OTA Agent. %d\r\n", OTA_METHOD_NAME );

    /* If we're here, we're shutting down the OTA agent. Free up all resources and quit. */
    prvAgentShutdownCleanup();

    /* Clear the entire agent context. This includes the OTA agent state. */
    ( void ) memset( &xOTA_Agent, 0, sizeof( xOTA_Agent ) );

    xOTA_Agent.eState = eOTA_AgentState_Stopped;

    /* Delete the OTA agent task. */
    vTaskDelete( NULL );

    return kOTA_Err_None;
}

static OTA_Err_t prvSuspendHandler( OTA_EventData_t * pxEventData )
{
    DEFINE_OTA_METHOD_NAME( "prvSuspendHandler" );

    ( void ) pxEventData;
    OTA_Err_t xErr = kOTA_Err_None;

    /* Log the state change to suspended state.*/
    OTA_LOG_L1( "[%s] OTA Agent is suspended.\r\n", OTA_METHOD_NAME );

    return xErr;
}

static OTA_Err_t prvResumeHandler( OTA_EventData_t * pxEventData )
{
    DEFINE_OTA_METHOD_NAME( "prvResumeHandler" );

    ( void ) pxEventData;

    OTA_EventMsg_t xEventMsg = { 0 };

    /*
     * Update the connection handle before resuming the OTA process.
     */

    OTA_LOG_L2( "[%s] Updating the connection handle. %d\r\n", OTA_METHOD_NAME );

    xOTA_Agent.pvConnectionContext = pxEventData;

    /*
     * Send signal to request job document.
     */
    xEventMsg.xEventId = eOTA_AgentEvent_RequestJobDocument;

    return OTA_SignalEvent( &xEventMsg ) ? kOTA_Err_None : kOTA_Err_EventQueueSendFailed;
}

static OTA_Err_t prvJobNotificationHandler( OTA_EventData_t * pxEventData )
{
    ( void ) pxEventData;
    OTA_Err_t xErr = kOTA_Err_Uninitialized;
    OTA_EventMsg_t xEventMsg = { 0 };

    /*  We receieved job notification so stop the data request timer. */
    prvStopRequestTimer();

    /* Abort the current job. */
    ( void ) xOTA_Agent.xPALCallbacks.xSetPlatformImageState( xOTA_Agent.ulServerFileID, eOTA_ImageState_Aborted );
    ( void ) prvOTA_Close( &xOTA_Agent.pxOTA_Files[ xOTA_Agent.ulFileIndex ] );

    /* Free the active job name as its no longer required. */
    if( xOTA_Agent.pcOTA_Singleton_ActiveJobName != NULL )
    {
        vPortFree( xOTA_Agent.pcOTA_Singleton_ActiveJobName );
        xOTA_Agent.pcOTA_Singleton_ActiveJobName = NULL;
    }

    /*
     * Send signal to request next OTA job document from service.
     */
    xEventMsg.xEventId = eOTA_AgentEvent_RequestJobDocument;

    return OTA_SignalEvent( &xEventMsg ) ? kOTA_Err_None : kOTA_Err_EventQueueSendFailed;
}

/*
 * This is a private function only meant to be called by the OTA agent after the
 * currently running image that is in the self test phase rejects the update.
 * It simply calls the platform specific code required to reset the device.
 */
static OTA_Err_t prvResetDevice( void )
{
    DEFINE_OTA_METHOD_NAME( "prvResetDevice" );

    OTA_Err_t xErr = kOTA_Err_Uninitialized;

    /*
     * Call platform specific code to reset the device. This should not return unless
     * there is a problem within the PAL layer. If it does return, output an error
     * message. The device may need to be reset manually.
     */
    OTA_LOG_L1( "[%s] Attempting forced reset of device...\r\n", OTA_METHOD_NAME );
    xErr = xOTA_Agent.xPALCallbacks.xResetDevice( xOTA_Agent.ulServerFileID );

    /*
     * We should not get here, OTA pal call for resetting device failed.
     */
    OTA_LOG_L1( "[%s] Failed to reset the device (0x%08x). Please reset manually.\r\n", OTA_METHOD_NAME, xErr );

    return xErr;
}

void prvOTAEventBufferFree( OTA_EventData_t * const pxBuffer )
{
    DEFINE_OTA_METHOD_NAME( "prvOTAEventBufferFree" );

    if( xSemaphoreTake( xOTA_Agent.xOTA_ThreadSafetyMutex, portMAX_DELAY ) == pdPASS )
    {
        pxBuffer->bBufferUsed = false;
        ( void ) xSemaphoreGive( xOTA_Agent.xOTA_ThreadSafetyMutex );
    }
    else
    {
        OTA_LOG_L1( "Error: Could not take semaphore for freeing message buffer.\r\n" );
    }
}

OTA_EventData_t * prvOTAEventBufferGet( void )
{
    DEFINE_OTA_METHOD_NAME( "prvOTAEventBufferGet" );

    uint32_t ulIndex = 0;
    OTA_EventData_t * pxOTAFreeMsg = NULL;

    /* Wait at most 1 task switch for a buffer so as not to block the callback. */
    if( xSemaphoreTake( xOTA_Agent.xOTA_ThreadSafetyMutex, 1 ) == pdPASS )
    {
        for( ulIndex = 0; ulIndex < otaconfigMAX_NUM_OTA_DATA_BUFFERS; ulIndex++ )
        {
            if( xEventBuffer[ ulIndex ].bBufferUsed == false )
            {
                xEventBuffer[ ulIndex ].bBufferUsed = true;
                pxOTAFreeMsg = &xEventBuffer[ ulIndex ];
                break;
            }
        }

        ( void ) xSemaphoreGive( xOTA_Agent.xOTA_ThreadSafetyMutex );
    }
    else
    {
        OTA_LOG_L1( "Error: Could not take semaphore for getting message buffer.\r\n" );
    }

    return pxOTAFreeMsg;
}

static void prvOTA_FreeContext( OTA_FileContext_t * const C )
{
    if( C != NULL )
    {
        if( C->pucStreamName != NULL )
        {
            vPortFree( C->pucStreamName ); /* Free any previously allocated stream name memory. */
            C->pucStreamName = NULL;
        }

        if( C->pucJobName != NULL )
        {
            vPortFree( C->pucJobName ); /* Free the job name memory. */
            C->pucJobName = NULL;
        }

        if( C->pucRxBlockBitmap != NULL )
        {
            vPortFree( C->pucRxBlockBitmap ); /* Free the previously allocated block bitmap. */
            C->pucRxBlockBitmap = NULL;
        }

        if( C->pxSignature != NULL )
        {
            vPortFree( C->pxSignature ); /* Free the image signature memory. */
            C->pxSignature = NULL;
        }

        if( C->pucFilePath != NULL )
        {
            vPortFree( C->pucFilePath ); /* Free the file path name string memory. */
            C->pucFilePath = NULL;
        }

        if( C->pucCertFilepath != NULL )
        {
            vPortFree( C->pucCertFilepath ); /* Free the certificate path name string memory. */
            C->pucCertFilepath = NULL;
        }

        if( C->pucUpdateUrlPath != NULL )
        {
            vPortFree( C->pucUpdateUrlPath ); /* Free the url path name string memory. */
            C->pucUpdateUrlPath = NULL;
        }

        if( C->pucAuthScheme != NULL )
        {
            vPortFree( C->pucAuthScheme ); /* Free the pucAuthScheme name string memory. */
            C->pucAuthScheme = NULL;
        }

        if( C->pucProtocols != NULL )
        {
            vPortFree( C->pucProtocols ); /* Free the pucProtocols string memory. */
            C->pucProtocols = NULL;
        }
    }
}

/* Close an existing OTA context and free its resources. */

static bool prvOTA_Close( OTA_FileContext_t * const C )
{
    DEFINE_OTA_METHOD_NAME( "prvOTA_Close" );

    bool bResult = false;

    OTA_LOG_L2( "[%s] Context->0x%p\r\n", OTA_METHOD_NAME, C );

    /* Cleanup related to selected protocol. */
    if( xOTA_DataInterface.prvCleanup != NULL )
    {
        ( void ) xOTA_DataInterface.prvCleanup( &xOTA_Agent );
    }

    if( C != NULL )
    {
        /*
         * Abort any active file access and release the file resource, if needed.
         */
        ( void ) xOTA_Agent.xPALCallbacks.xAbort( C );

        /* Free the resources. */
        prvOTA_FreeContext( C );

        /* Clear the entire structure now that it is free. */
        ( void ) memset( C, 0, sizeof( OTA_FileContext_t ) );

        bResult = true;
    }

    return bResult;
}


/* Find an available OTA transfer context structure. */

static OTA_FileContext_t * prvGetFreeContext( void )
{
    uint32_t ulIndex = 0U;
    OTA_FileContext_t * C = NULL;

    while( ( ulIndex < OTA_MAX_FILES ) && ( xOTA_Agent.pxOTA_Files[ ulIndex ].pucFilePath != NULL ) )
    {
        ulIndex++;
    }

    if( ulIndex != OTA_MAX_FILES )
    {
        ( void ) memset( &xOTA_Agent.pxOTA_Files[ ulIndex ], 0, sizeof( OTA_FileContext_t ) );
        C = &xOTA_Agent.pxOTA_Files[ ulIndex ];
        xOTA_Agent.ulFileIndex = ulIndex;
    }
    else
    {
        /* Not able to support this request so we'll return NULL. */
    }

    return C;
}

static bool JSON_IsCStringEqual( const char * pcJSONString,
                                 uint32_t ulLen,
                                 const char * pcCString )
{
    bool bResult;

    if( ( ulLen <= OTA_MAX_JSON_STR_LEN ) &&
        ( strncmp( pcJSONString, pcCString, ulLen ) == 0 ) && /*lint !e9007 I see no side effect. Possibly a lint bug. */
        ( pcCString[ ulLen ] == '\0' ) )
    {
        bResult = true;
    }
    else
    {
        bResult = false;
    }

    return bResult;
}


/* Search our document model for a key match with the given token. */

static DocParseErr_t prvSearchModelForTokenKey( JSON_DocModel_t * pxDocModel,
                                                const char * pcJSONString,
                                                uint32_t ulStrLen,
                                                uint16_t * pulMatchingIndexResult )
{
    DocParseErr_t eErr = eDocParseErr_ParamKeyNotInModel;
    uint16_t usParamIndex;

    for( usParamIndex = 0; usParamIndex < pxDocModel->usNumModelParams; usParamIndex++ )
    {
        if( JSON_IsCStringEqual( pcJSONString, ulStrLen,
                                 pxDocModel->pxBodyDef[ usParamIndex ].pcSrcKey ) )
        {
            /* Per Security, don't allow multiple entries of the same parameter. */
            if( ( pxDocModel->ulParamsReceivedBitmap & ( ( uint32_t ) 1U << usParamIndex ) ) != 0U ) /*lint !e9032 usParamIndex will never be greater than kDocModel_MaxParams, which is the the size of the bitmap. */
            {
                eErr = eDocParseErr_DuplicatesNotAllowed;
            }
            else
            {
                /* Mark parameter as received in the bitmap. */
                pxDocModel->ulParamsReceivedBitmap |= ( ( uint32_t ) 1U << usParamIndex ); /*lint !e9032 usParamIndex will never be greater than kDocModel_MaxParams, which is the the size of the bitmap. */
                *pulMatchingIndexResult = usParamIndex;                                    /* Save result index for caller. */
                eErr = eDocParseErr_None;                                                  /* We found a matching key in the document model. */
            }

            break; /* We found a key match so stop searching. */
        }
    }

    return eErr;
}

/* Extract the desired fields from the JSON document based on the specified document model. */

static DocParseErr_t prvParseJSONbyModel( const char * pcJSON,
                                          uint32_t ulMsgLen,
                                          JSON_DocModel_t * pxDocModel )
{
    DEFINE_OTA_METHOD_NAME( "prvParseJSONbyModel" );

    const JSON_DocParam_t * pxModelParam = NULL;
    jsmn_parser xParser;
    jsmntok_t * pxTokens = NULL;
    const jsmntok_t * pxValTok = NULL;
    int32_t jsmn_result = 0;
    uint32_t ulNumTokens = 0, ulTokenLen = 0;
    MultiParmPtr_t xParamAddr; /*lint !e9018 We intentionally use this union to cast the parameter address to the proper type. */
    uint32_t ulIndex = 0;
    uint16_t usModelParamIndex = 0;
    uint32_t ulScanIndex = 0;
    DocParseErr_t eErr = eDocParseErr_None;

    /* Reset the Jasmine tokenizer. */
    jsmn_init( &xParser );

    /* Check if document model is valid. */
    if( pxDocModel == NULL )
    {
        OTA_LOG_L1( "[%s] The pointer to the document model is NULL.\r\n", OTA_METHOD_NAME );
        eErr = eDocParseErr_NullModelPointer;
    }

    /* Check if document model body ponter is valid.*/
    if( eErr == eDocParseErr_None )
    {
        if( pxDocModel->pxBodyDef == NULL )
        {
            OTA_LOG_L1( "[%s] Document model 0x%08x body pointer is NULL.\r\n", OTA_METHOD_NAME, pxDocModel );
            eErr = eDocParseErr_NullBodyPointer;
        }
    }

    /* Check number of parameters is valid.*/
    if( eErr == eDocParseErr_None )
    {
        if( pxDocModel->usNumModelParams > OTA_DOC_MODEL_MAX_PARAMS )
        {
            OTA_LOG_L1( "[%s] Model has too many parameters (%u).\r\n", OTA_METHOD_NAME, pxDocModel->usNumModelParams );
            eErr = eDocParseErr_TooManyParams;
        }
    }

    /* Check JSON document pointer is valid.*/
    if( eErr == eDocParseErr_None )
    {
        if( pcJSON == NULL )
        {
            OTA_LOG_L1( "[%s] JSON document pointer is NULL!\r\n", OTA_METHOD_NAME );
            eErr = eDocParseErr_NullDocPointer;
        }
    }

    /* Check if token numbe is valid. */
    if( eErr == eDocParseErr_None )
    {
        pxModelParam = pxDocModel->pxBodyDef;

        /* Count the total number of tokens in our JSON document. */
        jsmn_result = jsmn_parse( &xParser, pcJSON, ( size_t ) ulMsgLen, NULL, 1UL );
        ulNumTokens = jsmn_result < 0 ? 0 : ( uint32_t ) jsmn_result;

        if( ulNumTokens == 0 )
        {
            OTA_LOG_L1( "[%s] Invalid JSON document. No tokens parsed. \r\n", OTA_METHOD_NAME );
            eErr = eDocParseErr_NoTokens;
        }
    }

    /* Check if the JSON document isn't too big for our token array. */
    if( eErr == eDocParseErr_None )
    {
        if( ulNumTokens > OTA_MAX_JSON_TOKENS )
        {
            OTA_LOG_L1( "[%s] Document has too many keys.\r\n", OTA_METHOD_NAME );
            eErr = eDocParseErr_TooManyTokens;
        }
    }

    /* Allocate space on heap for temporary token array. */
    if( eErr == eDocParseErr_None )
    {
        /* Allocate space for the document JSON tokens. */
        pxTokens = ( jsmntok_t * ) pvPortMalloc( ulNumTokens * sizeof( jsmntok_t ) );

        if( pxTokens == NULL )
        {
            OTA_LOG_L1( "[%s] No memory for JSON tokens.\r\n", OTA_METHOD_NAME );
            eErr = eDocParseErr_OutOfMemory;
        }
    }

    /* Init Jasmine and check number of tokens.*/
    if( eErr == eDocParseErr_None )
    {
        /* Reset Jasmine again and tokenize the document for real. */
        jsmn_init( &xParser );
        ulIndex = ( uint32_t ) jsmn_parse( &xParser, pcJSON, ulMsgLen, pxTokens, ulNumTokens );

        if( ulIndex != ulNumTokens )
        {
            OTA_LOG_L1( "[%s] jsmn_parse didn't match token count when parsing.\r\n", OTA_METHOD_NAME );
            eErr = eDocParseErr_JasmineCountMismatch;
        }
    }

    /* Process JSON tokens. */
    if( eErr == eDocParseErr_None )
    {
        /* Examine each JSON token, searching for job parameters based on our document model. */
        for( ulIndex = 0U; ( eErr == eDocParseErr_None ) && ( ulIndex < ulNumTokens ); ulIndex++ )
        {
            /* All parameter keys are JSON strings. */
            if( pxTokens[ ulIndex ].type == JSMN_STRING )
            {
                /* Search the document model to see if it matches the current key. */
                ulTokenLen = ( uint32_t ) pxTokens[ ulIndex ].end - ( uint32_t ) pxTokens[ ulIndex ].start;
                eErr = prvSearchModelForTokenKey( pxDocModel, &pcJSON[ pxTokens[ ulIndex ].start ], ulTokenLen, &usModelParamIndex );

                /* If we didn't find a match in the model, skip over it and its descendants. */
                if( eErr == eDocParseErr_ParamKeyNotInModel )
                {
                    int32_t iRoot = ( int32_t ) ulIndex; /* Create temp root from the unrecognized tokens index. Use signed int since the parent index is signed. */
                    ulIndex++;                           /* Skip the active key since it's the one we don't recognize. */

                    /* Skip tokens whose parents are equal to or deeper than the unrecognized temporary root token level. */
                    while( ( ulIndex < ulNumTokens ) && ( pxTokens[ ulIndex ].parent >= iRoot ) )
                    {
                        ulIndex++; /* Skip over all descendants of the unknown parent. */
                    }

                    --ulIndex;                /* Adjust for outer for-loop increment. */
                    eErr = eDocParseErr_None; /* Unknown key structures are simply skipped so clear the error state to continue. */
                }
                else if( eErr == eDocParseErr_None )
                {
                    /* We found the parameter key in the document model. */

                    /* Get the value field (i.e. the following token) for the parameter. */
                    pxValTok = &pxTokens[ ulIndex + 1UL ];

                    /* Verify the field type is what we expect for this parameter. */
                    if( pxValTok->type != pxModelParam[ usModelParamIndex ].eJasmineType )
                    {
                        ulTokenLen = ( uint32_t ) ( pxValTok->end ) - ( uint32_t ) ( pxValTok->start );
                        OTA_LOG_L1( "[%s] parameter type mismatch [ %s : %.*s ] type %u, expected %u\r\n",
                                    OTA_METHOD_NAME, pxModelParam[ usModelParamIndex ].pcSrcKey, ulTokenLen,
                                    &pcJSON[ pxValTok->start ],
                                    pxValTok->type, pxModelParam[ usModelParamIndex ].eJasmineType );
                        eErr = eDocParseErr_FieldTypeMismatch;
                    }
                    else if( OTA_DONT_STORE_PARAM == pxModelParam[ usModelParamIndex ].ulDestOffset )
                    {
                        /* Nothing to do with this parameter since we're not storing it. */
                        continue;
                    }
                    else
                    {
                        /* Get destination offset to parameter storage location. */

                        /* If it's within the models context structure, add in the context instance base address. */
                        if( pxModelParam[ usModelParamIndex ].ulDestOffset < pxDocModel->ulContextSize )
                        {
                            xParamAddr.ulVal = pxDocModel->ulContextBase + pxModelParam[ usModelParamIndex ].ulDestOffset;
                        }
                        else
                        {
                            /* It's a raw pointer so keep it as is. */
                            xParamAddr.ulVal = pxModelParam[ usModelParamIndex ].ulDestOffset;
                        }

                        if( eModelParamType_StringCopy == pxModelParam[ usModelParamIndex ].xModelParamType )
                        {
                            /* Malloc memory for a copy of the value string plus a zero terminator. */
                            ulTokenLen = ( uint32_t ) ( pxValTok->end ) - ( uint32_t ) ( pxValTok->start );
                            void * pvStringCopy = pvPortMalloc( ulTokenLen + 1U );

                            if( pvStringCopy != NULL )
                            {
                                *xParamAddr.ppvPtr = pvStringCopy;
                                char * pcStringCopy = *xParamAddr.ppcPtr;
                                /* Copy parameter string into newly allocated memory. */
                                ( void ) memcpy( pcStringCopy, &pcJSON[ pxValTok->start ], ulTokenLen );
                                /* Zero terminate the new string. */
                                pcStringCopy[ ulTokenLen ] = '\0';
                                OTA_LOG_L1( "[%s] Extracted parameter [ %s: %s ]\r\n",
                                            OTA_METHOD_NAME,
                                            pxModelParam[ usModelParamIndex ].pcSrcKey,
                                            pcStringCopy );
                            }
                            else
                            { /* Stop processing on error. */
                                eErr = eDocParseErr_OutOfMemory;
                            }
                        }
                        else if( eModelParamType_StringInDoc == pxModelParam[ usModelParamIndex ].xModelParamType )
                        {
                            /* Copy pointer to source string instead of duplicating the string. */
                            const char * pcStringInDoc = &pcJSON[ pxValTok->start ];
                            *xParamAddr.ppccPtr = pcStringInDoc;
                            ulTokenLen = ( uint32_t ) ( pxValTok->end ) - ( uint32_t ) ( pxValTok->start );
                            OTA_LOG_L1( "[%s] Extracted parameter [ %s: %.*s ]\r\n",
                                        OTA_METHOD_NAME,
                                        pxModelParam[ usModelParamIndex ].pcSrcKey,
                                        ulTokenLen, pcStringInDoc );
                        }
                        else if( eModelParamType_UInt32 == pxModelParam[ usModelParamIndex ].xModelParamType )
                        {
                            char * pEnd;
                            const char * pStart = &pcJSON[ pxValTok->start ];
                            *xParamAddr.pulPtr = strtoul( pStart, &pEnd, 0 );

                            if( pEnd == &pcJSON[ pxValTok->end ] )
                            {
                                OTA_LOG_L1( "[%s] Extracted parameter [ %s: %u ]\r\n",
                                            OTA_METHOD_NAME,
                                            pxModelParam[ usModelParamIndex ].pcSrcKey,
                                            *xParamAddr.pulPtr );
                            }
                            else
                            {
                                eErr = eDocParseErr_InvalidNumChar;
                            }
                        }
                        else if( eModelParamType_SigBase64 == pxModelParam[ usModelParamIndex ].xModelParamType )
                        {
                            /* Allocate space for and decode the base64 signature. */
                            void * pvSignature = pvPortMalloc( sizeof( Sig256_t ) );

                            if( pvSignature != NULL )
                            {
                                size_t xActualLen = 0;
                                *xParamAddr.ppvPtr = pvSignature;
                                Sig256_t * pxSig256 = *xParamAddr.ppxSig256Ptr;
                                ulTokenLen = ( uint32_t ) ( pxValTok->end ) - ( uint32_t ) ( pxValTok->start );

                                if( mbedtls_base64_decode( pxSig256->ucData, sizeof( pxSig256->ucData ), &xActualLen,
                                                           ( const uint8_t * ) &pcJSON[ pxValTok->start ], ulTokenLen ) != 0 )
                                { /* Stop processing on error. */
                                    OTA_LOG_L1( "[%s] mbedtls_base64_decode failed.\r\n", OTA_METHOD_NAME );
                                    eErr = eDocParseErr_Base64Decode;
                                }
                                else
                                {
                                    pxSig256->usSize = ( uint16_t ) xActualLen;
                                    OTA_LOG_L1( "[%s] Extracted parameter [ %s: %.32s... ]\r\n",
                                                OTA_METHOD_NAME,
                                                pxModelParam[ usModelParamIndex ].pcSrcKey,
                                                &pcJSON[ pxValTok->start ] );
                                }
                            }
                            else
                            {
                                /* We failed to allocate needed memory. Everything will be freed below upon failure. */
                                eErr = eDocParseErr_OutOfMemory;
                            }
                        }
                        else if( eModelParamType_Ident == pxModelParam[ usModelParamIndex ].xModelParamType )
                        {
                            OTA_LOG_L1( "[%s] Identified parameter [ %s ]\r\n",
                                        OTA_METHOD_NAME,
                                        pxModelParam[ usModelParamIndex ].pcSrcKey );
                            *xParamAddr.pbBoolPtr = true;
                        }

                        if( eModelParamType_ArrayCopy == pxModelParam[ usModelParamIndex ].xModelParamType )
                        {
                            /* Malloc memory for a copy of the value string plus a zero terminator. */
                            ulTokenLen = ( uint32_t ) ( pxValTok->end ) - ( uint32_t ) ( pxValTok->start );
                            void * pvStringCopy = pvPortMalloc( ulTokenLen + 1U );

                            if( pvStringCopy != NULL )
                            {
                                *xParamAddr.ppvPtr = pvStringCopy;
                                char * pcStringCopy = *xParamAddr.ppcPtr;
                                /* Copy parameter string into newly allocated memory. */
                                ( void ) memcpy( pcStringCopy, &pcJSON[ pxValTok->start ], ulTokenLen );
                                /* Zero terminate the new string. */
                                pcStringCopy[ ulTokenLen ] = '\0';
                                OTA_LOG_L1( "[%s] Extracted parameter [ %s: %s ]\r\n",
                                            OTA_METHOD_NAME,
                                            pxModelParam[ usModelParamIndex ].pcSrcKey,
                                            pcStringCopy );
                            }
                            else
                            { /* Stop processing on error. */
                                eErr = eDocParseErr_OutOfMemory;
                            }
                        }
                        else
                        {
                            /* Ignore invalid document model type. */
                        }
                    }
                }
                else
                {
                    /* Nothing special to do. The error will break us out of the loop. */
                }
            }
            else
            {
                /* Ignore tokens that are not strings and move on to the next. */
            }
        }
    }

    if( pxTokens != NULL )
    {
        /* Free the token memory. */
        vPortFree( pxTokens ); /*lint !e850 ulIndex is intentionally modified within the loop to skip over unknown tags. */
    }

    if( eErr == eDocParseErr_None )
    {
        uint32_t ulMissingParams = ( pxDocModel->ulParamsReceivedBitmap & pxDocModel->ulParamsRequiredBitmap )
                                   ^ pxDocModel->ulParamsRequiredBitmap;

        if( ulMissingParams != 0U )
        {
            /* The job document did not have all required document model parameters. */
            for( ulScanIndex = 0UL; ulScanIndex < pxDocModel->usNumModelParams; ulScanIndex++ )
            {
                if( ( ulMissingParams & ( 1UL << ulScanIndex ) ) != 0UL )
                {
                    OTA_LOG_L1( "[%s] parameter not present: %s\r\n",
                                OTA_METHOD_NAME,
                                pxModelParam[ ulScanIndex ].pcSrcKey );
                }
            }

            eErr = eDocParseErr_MalformedDoc;
        }
    }
    else
    {
        OTA_LOG_L1( "[%s] Error (%d) parsing JSON document.\r\n", OTA_METHOD_NAME, ( int32_t ) eErr );
    }

    configASSERT( eErr != eDocParseErr_Unknown );
    return eErr;
}

/* Prepare the document model for use by sanity checking the initialization parameters
 * and detecting all required parameters. */

static DocParseErr_t prvInitDocModel( JSON_DocModel_t * pxDocModel,
                                      const JSON_DocParam_t * pxBodyDef,
                                      uint32_t ulContextBaseAddr,
                                      uint32_t ulContextSize,
                                      uint16_t usNumJobParams )
{
    DEFINE_OTA_METHOD_NAME( "prvInitDocModel" );

    DocParseErr_t eErr = eDocParseErr_Unknown;
    uint32_t ulScanIndex;

    /* Sanity check the model pointers and parameter count. Exclude the context base address and size since
     * it is technically possible to create a model that writes entirely into absolute memory locations.
     */
    if( pxDocModel == NULL )
    {
        OTA_LOG_L1( "[%s] The pointer to the document model is NULL.\r\n", OTA_METHOD_NAME );
        eErr = eDocParseErr_NullModelPointer;
    }
    else if( pxBodyDef == NULL )
    {
        OTA_LOG_L1( "[%s] Document model 0x%08x body pointer is NULL.\r\n", OTA_METHOD_NAME, pxDocModel );
        eErr = eDocParseErr_NullBodyPointer;
    }
    else if( usNumJobParams > OTA_DOC_MODEL_MAX_PARAMS )
    {
        OTA_LOG_L1( "[%s] Model has too many parameters (%u).\r\n", OTA_METHOD_NAME, pxDocModel->usNumModelParams );
        eErr = eDocParseErr_TooManyParams;
    }
    else
    {
        pxDocModel->ulContextBase = ulContextBaseAddr;
        pxDocModel->ulContextSize = ulContextSize;
        pxDocModel->pxBodyDef = pxBodyDef;
        pxDocModel->usNumModelParams = usNumJobParams;
        pxDocModel->ulParamsReceivedBitmap = 0;
        pxDocModel->ulParamsRequiredBitmap = 0;

        /* Scan the model and detect all required parameters (i.e. not optional). */
        for( ulScanIndex = 0; ulScanIndex < pxDocModel->usNumModelParams; ulScanIndex++ )
        {
            if( pxDocModel->pxBodyDef[ ulScanIndex ].bRequired )
            {
                /* Add parameter to the required bitmap. */
                pxDocModel->ulParamsRequiredBitmap |= ( 1UL << ulScanIndex );
            }
        }

        eErr = eDocParseErr_None;
    }

    return eErr;
}

/*
 * Validate the version of the update received.
 */
static OTA_Err_t prvValidateUpdateVersion( OTA_FileContext_t * C )
{
    DEFINE_OTA_METHOD_NAME( "prvValidateUpdateVersion" );

    OTA_Err_t xErr = kOTA_Err_Uninitialized;

    /* Only check for versions if the target is self */
    if( xOTA_Agent.ulServerFileID == 0 )
    {
        /* Check if update version received is newer than current version.*/
        if( C->ulUpdaterVersion < xAppFirmwareVersion.u.ulVersion32 )
        {
            OTA_LOG_L1( "[%s] The update version is newer than the version on device.\r\n", OTA_METHOD_NAME );

            xErr = kOTA_Err_None;
        }
        /* Check if update version received is older than current version.*/
        else if( C->ulUpdaterVersion > xAppFirmwareVersion.u.ulVersion32 )
        {
            OTA_LOG_L1( "[%s] The update version is older than the version on device.\r\n", OTA_METHOD_NAME );

            xErr = kOTA_Err_DowngradeNotAllowed;
        }
        /* Check if version reported is the same as the running version. */
        else if( C->ulUpdaterVersion == xAppFirmwareVersion.u.ulVersion32 )
        {
            /* The version is the same so either we're not actually the new firmware or
             * someone messed up and sent firmware with the same version. In either case,
             * this is a failure of the OTA update so reject the job.
             */
            OTA_LOG_L1( "[%s] We rebooted and the version is still the same.\r\n", OTA_METHOD_NAME );

            xErr = kOTA_Err_SameFirmwareVersion;
        }
    }
    else
    {
        /* For any other ulServerFileID.*/
        xErr = kOTA_Err_None;
    }

    return xErr;
}

/* Parse the OTA job document and validate. Return the populated
 * OTA context if valid otherwise return NULL.
 */

static OTA_FileContext_t * prvParseJobDoc( const char * pcJSON,
                                           uint32_t ulMsgLen,
                                           bool * pbUpdateJob )
{
    DEFINE_OTA_METHOD_NAME( "prvParseJobDoc" );

    /* This is the OTA job document model describing the parameters, their types, destination and how to extract. */
    /*lint -e{708} We intentionally do some things lint warns about but produce the proper model. */
    /* Namely union initialization and pointers converted to values. */
    static const JSON_DocParam_t xOTA_JobDocModelParamStructure[ OTA_NUM_JOB_PARAMS ] =
    {
        { OTA_JSON_CLIENT_TOKEN_KEY,    OTA_JOB_PARAM_OPTIONAL, { ( uint32_t ) &xOTA_Agent.pcClientTokenFromJob }, eModelParamType_StringInDoc, JSMN_STRING    }, /*lint !e9078 !e923 Get address of token as value. */
        { OTA_JSON_TIMESTAMP_KEY,       OTA_JOB_PARAM_OPTIONAL, { ( uint32_t ) &xOTA_Agent.ulTimestampFromJob   }, eModelParamType_UInt32,      JSMN_PRIMITIVE },
        { OTA_JSON_EXECUTION_KEY,       OTA_JOB_PARAM_REQUIRED, { OTA_DONT_STORE_PARAM                          }, eModelParamType_Object,      JSMN_OBJECT    },
        { OTA_JSON_JOB_ID_KEY,          OTA_JOB_PARAM_REQUIRED, { offsetof( OTA_FileContext_t, pucJobName )     }, eModelParamType_StringCopy,  JSMN_STRING    },
        { OTA_JSON_STATUS_DETAILS_KEY,  OTA_JOB_PARAM_OPTIONAL, { OTA_DONT_STORE_PARAM                          }, eModelParamType_Object,      JSMN_OBJECT    },
        { OTA_JSON_SELF_TEST_KEY,       OTA_JOB_PARAM_OPTIONAL, { offsetof( OTA_FileContext_t, bIsInSelfTest )  }, eModelParamType_Ident,       JSMN_STRING    },
        { OTA_JSON_UPDATED_BY_KEY,      OTA_JOB_PARAM_OPTIONAL, { offsetof( OTA_FileContext_t, ulUpdaterVersion )}, eModelParamType_UInt32,      JSMN_STRING    },
        { OTA_JSON_JOB_DOC_KEY,         OTA_JOB_PARAM_REQUIRED, { OTA_DONT_STORE_PARAM                          }, eModelParamType_Object,      JSMN_OBJECT    },
        { OTA_JSON_OTA_UNIT_KEY,        OTA_JOB_PARAM_REQUIRED, { OTA_DONT_STORE_PARAM                          }, eModelParamType_Object,      JSMN_OBJECT    },
        { OTA_JSON_STREAM_NAME_KEY,     OTA_JOB_PARAM_OPTIONAL, { offsetof( OTA_FileContext_t, pucStreamName )  }, eModelParamType_StringCopy,  JSMN_STRING    },
        { OTA_JSON_PROTOCOLS_KEY,       OTA_JOB_PARAM_REQUIRED, { offsetof( OTA_FileContext_t, pucProtocols )   }, eModelParamType_ArrayCopy,   JSMN_ARRAY     },
        { OTA_JSON_FILE_GROUP_KEY,      OTA_JOB_PARAM_REQUIRED, { OTA_DONT_STORE_PARAM                          }, eModelParamType_Array,       JSMN_ARRAY     },
        { OTA_JSON_FILE_PATH_KEY,       OTA_JOB_PARAM_REQUIRED, { offsetof( OTA_FileContext_t, pucFilePath )    }, eModelParamType_StringCopy,  JSMN_STRING    },
        { OTA_JSON_FILE_SIZE_KEY,       OTA_JOB_PARAM_REQUIRED, { offsetof( OTA_FileContext_t, ulFileSize )     }, eModelParamType_UInt32,      JSMN_PRIMITIVE },
        { OTA_JSON_FILE_ID_KEY,         OTA_JOB_PARAM_REQUIRED, { offsetof( OTA_FileContext_t, ulServerFileID ) }, eModelParamType_UInt32,      JSMN_PRIMITIVE },
        { OTA_JSON_FILE_CERT_NAME_KEY,  OTA_JOB_PARAM_REQUIRED, { offsetof( OTA_FileContext_t, pucCertFilepath )}, eModelParamType_StringCopy,  JSMN_STRING    },
        { OTA_JSON_UPDATE_DATA_URL_KEY, OTA_JOB_PARAM_OPTIONAL, { offsetof( OTA_FileContext_t, pucUpdateUrlPath )}, eModelParamType_StringCopy,  JSMN_STRING    },
        { OTA_JSON_AUTH_SCHEME_KEY,     OTA_JOB_PARAM_OPTIONAL, { offsetof( OTA_FileContext_t, pucAuthScheme )  }, eModelParamType_StringCopy,  JSMN_STRING    },
        { cOTA_JSON_FileSignatureKey,   OTA_JOB_PARAM_REQUIRED, { offsetof( OTA_FileContext_t, pxSignature )    }, eModelParamType_SigBase64,   JSMN_STRING    },
        { OTA_JSON_FILE_ATTRIBUTE_KEY,  OTA_JOB_PARAM_OPTIONAL, { offsetof( OTA_FileContext_t, ulFileAttributes )}, eModelParamType_UInt32,      JSMN_PRIMITIVE },
    };

    OTA_Err_t xOTAErr = kOTA_Err_None;
    OTA_JobParseErr_t eErr = eOTA_JobParseErr_Unknown;
    OTA_FileContext_t * pxFinalFile = NULL;
    OTA_FileContext_t xFileContext = { 0 };
    OTA_FileContext_t * C = &xFileContext;
    OTA_Err_t xErrVersionCheck = kOTA_Err_Uninitialized;

    JSON_DocModel_t xOTA_JobDocModel;

    if( prvInitDocModel( &xOTA_JobDocModel,
                         xOTA_JobDocModelParamStructure,
                         ( uint32_t ) C, /*lint !e9078 !e923 Intentionally casting context pointer to a value for prvInitDocModel. */
                         sizeof( OTA_FileContext_t ),
                         OTA_NUM_JOB_PARAMS ) != eDocParseErr_None )
    {
        eErr = eOTA_JobParseErr_BadModelInitParams;
    }
    else if( prvParseJSONbyModel( pcJSON, ulMsgLen, &xOTA_JobDocModel ) == eDocParseErr_None )
    { /* Validate the job document parameters. */
        eErr = eOTA_JobParseErr_None;

        if( C->ulFileSize == 0U )
        {
            OTA_LOG_L1( "[%s] Zero file size is not allowed!\r\n", OTA_METHOD_NAME );
            eErr = eOTA_JobParseErr_ZeroFileSize;
        }
        /* If there's an active job, verify that it's the same as what's being reported now. */
        /* We already checked for missing parameters so we SHOULD have a job name in the context. */
        else if( xOTA_Agent.pcOTA_Singleton_ActiveJobName != NULL )
        {
            if( C->pucJobName != NULL )
            {
                /* C->pucJobName is guaranteed to be zero terminated. */
                if( strcmp( ( char * ) xOTA_Agent.pcOTA_Singleton_ActiveJobName, ( char * ) C->pucJobName ) != 0 )
                {
                    OTA_LOG_L1( "[%s] New job document received,aborting current job.\r\n", OTA_METHOD_NAME );

                    /* Abort the current job. */
                    ( void ) xOTA_Agent.xPALCallbacks.xSetPlatformImageState( xOTA_Agent.ulServerFileID, eOTA_ImageState_Aborted );
                    ( void ) prvOTA_Close( &xOTA_Agent.pxOTA_Files[ xOTA_Agent.ulFileIndex ] );

                    /* Set new active job name. */
                    vPortFree( xOTA_Agent.pcOTA_Singleton_ActiveJobName );
                    xOTA_Agent.pcOTA_Singleton_ActiveJobName = C->pucJobName;
                    C->pucJobName = NULL;

                    eErr = eOTA_JobParseErr_None;
                }
                else
                { /* The same job is being reported so update the url. */
                    OTA_LOG_L1( "[%s] Job received is current active job.\r\n", OTA_METHOD_NAME );

                    if( xOTA_Agent.pxOTA_Files[ xOTA_Agent.ulFileIndex ].pucUpdateUrlPath != NULL )
                    {
                        vPortFree( xOTA_Agent.pxOTA_Files[ xOTA_Agent.ulFileIndex ].pucUpdateUrlPath );
                        xOTA_Agent.pxOTA_Files[ xOTA_Agent.ulFileIndex ].pucUpdateUrlPath = C->pucUpdateUrlPath;
                        C->pucUpdateUrlPath = NULL;
                    }

                    prvOTA_FreeContext( C );

                    pxFinalFile = &xOTA_Agent.pxOTA_Files[ xOTA_Agent.ulFileIndex ];
                    *pbUpdateJob = true;

                    eErr = eOTA_JobParseErr_UpdateCurrentJob;
                }
            }
            else
            {
                OTA_LOG_L1( "[%s] Null job reported while busy. Ignoring.\r\n", OTA_METHOD_NAME );
                eErr = eOTA_JobParseErr_NullJob;
            }
        }
        else
        { /* Assume control of the job name from the context. */
            xOTA_Agent.pcOTA_Singleton_ActiveJobName = C->pucJobName;
            C->pucJobName = NULL;
        }

        /* Store the File ID received in the job */
        xOTA_Agent.ulServerFileID = C->ulServerFileID;

        if( eErr == eOTA_JobParseErr_None )
        {
            /* If the job is in self test mode, don't start an
             * OTA update but instead do the following:
             *
             * If the firmware that performed the update was older
             * than the currently running firmware, set the image
             * state to "Testing." This is the success path.
             *
             * If it's the same or newer, reject the job since
             * either the firmware wasn't accepted during self
             * test or an incorrect image was sent by the OTA
             * operator.
             */
            if( C->bIsInSelfTest )
            {
                OTA_LOG_L1( "[%s] In self test mode.\r\n", OTA_METHOD_NAME );

                /* Validate version of the update received.*/
                xErrVersionCheck = prvValidateUpdateVersion( C );

                if( otaconfigAllowDowngrade || ( xErrVersionCheck == kOTA_Err_None ) )
                {
                    /* The running firmware version is newer than the firmware that performed
                     * the update or downgrade is allowed so this means we're ready to start
                     * the self test phase.
                     *
                     * Set image state accordingly and update job status with self test identifier.
                     */
                    OTA_LOG_L1( "[%s] Setting image state to Testing for file ID %d\r\n", OTA_METHOD_NAME, xOTA_Agent.ulServerFileID );

                    ( void ) prvSetImageStateWithReason( eOTA_ImageState_Testing, xErrVersionCheck );
                }
                else
                {
                    OTA_LOG_L1( "[%s] Downgrade or same version not allowed, rejecting the update & rebooting.\r\n", OTA_METHOD_NAME );
                    ( void ) prvSetImageStateWithReason( eOTA_ImageState_Rejected, xErrVersionCheck );

                    /* All reject cases must reset the device. */
                    ( void ) prvResetDevice(); /* Ignore return code since there's nothing we can do if we can't force reset. */
                }
            }
            else
            {
                pxFinalFile = prvGetFreeContext();

                if( pxFinalFile == NULL )
                {
                    OTA_LOG_L1( "[%s] Job parsing successful but no file context available, aborting.\r\n", OTA_METHOD_NAME );
                }
                else
                {
                    *pxFinalFile = *C;

                    /* Everything looks OK. Set final context structure to start OTA. */
                    OTA_LOG_L1( "[%s] Job was accepted. Attempting to start transfer.\r\n", OTA_METHOD_NAME );
                }
            }
        }
        else
        {
            OTA_LOG_L1( "[%s] Error %d parsing job document.\r\n", OTA_METHOD_NAME, eErr );
        }
    }
    else
    { /* We have an unknown job parser error. Check to see if we can pass control to a callback for parsing */
        eErr = xOTA_Agent.xPALCallbacks.xCustomJobCallback( pcJSON, ulMsgLen );

        if( eErr == eOTA_JobParseErr_None )
        {
            /* Custom job was parsed by external callback successfully. Grab the job name from the file
             *  context and save that in the ota agent */
            if( C->pucJobName != NULL )
            {
                xOTA_Agent.pcOTA_Singleton_ActiveJobName = C->pucJobName;
                C->pucJobName = NULL;
                xOTAErr = xOTA_ControlInterface.prvUpdateJobStatus( &xOTA_Agent,
                                                                    eJobStatus_Succeeded,
                                                                    eJobReason_Accepted,
                                                                    0 );

                if( xOTAErr != kOTA_Err_None )
                {
                    OTA_LOG_L2( "[%s] Failed to update job status %d\r\n", OTA_METHOD_NAME, xOTAErr );
                }

                /* We don't need the job name memory anymore since we're done with this job. */
                vPortFree( xOTA_Agent.pcOTA_Singleton_ActiveJobName );
                xOTA_Agent.pcOTA_Singleton_ActiveJobName = NULL;
            }
            else
            {
                /* Job is malformed - return an error */
                OTA_LOG_L1( "[%s] Job does not have context or has no ID but has been processed\r\n", OTA_METHOD_NAME );
                eErr = eOTA_JobParseErr_NonConformingJobDoc;
            }
        }
        else
        {
            /*Check if we received a timestamp and client token but no job ID.*/
            if( ( xOTA_Agent.pcClientTokenFromJob != NULL ) && ( xOTA_Agent.ulTimestampFromJob != 0 ) && ( C->pucJobName == NULL ) )
            {
                /* Received job docuement with no execution so no active job is available.*/
                OTA_LOG_L1( "[%s] No active jobs available in the service for execution.\r\n", OTA_METHOD_NAME );
                eErr = eOTA_JobParseErr_NoActiveJobs;
            }
            else
            {
                /* Job is malformed - return an error */
                eErr = eOTA_JobParseErr_NonConformingJobDoc;
            }
        }
    }

    configASSERT( eErr != eOTA_JobParseErr_Unknown );

    if( eErr != eOTA_JobParseErr_None )
    {
        /* If job parsing failed AND there's a job ID, update the job state to FAILED with
         * a reason code.  Without a job ID, we can't update the status in the job service. */
        if( C->pucJobName != NULL )
        {
            OTA_LOG_L1( "[%s] Rejecting job due to OTA_JobParseErr_t %d\r\n", OTA_METHOD_NAME, eErr );
            /* Assume control of the job name from the context. */
            xOTA_Agent.pcOTA_Singleton_ActiveJobName = C->pucJobName;
            C->pucJobName = NULL;
            xOTAErr = xOTA_ControlInterface.prvUpdateJobStatus( &xOTA_Agent,
                                                                eJobStatus_FailedWithVal,
                                                                ( int32_t ) kOTA_Err_JobParserError,
                                                                ( int32_t ) eErr );

            if( xOTAErr != kOTA_Err_None )
            {
                OTA_LOG_L2( "[%s] Failed to update job status %d\r\n", OTA_METHOD_NAME, xOTAErr );
            }

            /* We don't need the job name memory anymore since we're done with this job. */
            vPortFree( xOTA_Agent.pcOTA_Singleton_ActiveJobName );
            xOTA_Agent.pcOTA_Singleton_ActiveJobName = NULL;
        }
        else
        {
            OTA_LOG_L1( "[%s] Ignoring job without ID.\r\n", OTA_METHOD_NAME );
        }
    }

    /* If we failed, close the open files. */
    if( pxFinalFile == NULL )
    {
        /* Free the current reserved file context. */
        prvOTA_FreeContext( C );

        /* Close any open files. */
        ( void ) prvOTA_Close( &xOTA_Agent.pxOTA_Files[ xOTA_Agent.ulFileIndex ] );
    }

    /* Return pointer to populated file context or NULL if it failed. */
    return pxFinalFile;
}


/* prvGetFileContextFromJob
 *
 * We received an OTA update job message from the job service so process
 * the message and update the file context.
 */

static OTA_FileContext_t * prvGetFileContextFromJob( const char * pcRawMsg,
                                                     uint32_t ulMsgLen )
{
    DEFINE_OTA_METHOD_NAME( "prvGetFileContextFromJob" );

    uint32_t ulIndex;
    uint32_t ulNumBlocks;              /* How many data pages are in the expected update image. */
    uint32_t ulBitmapLen;              /* Length of the file block bitmap in bytes. */
    OTA_FileContext_t * pstUpdateFile; /* Pointer to an OTA update context. */
    OTA_Err_t xErr = kOTA_Err_Uninitialized;

    bool bUpdateJob = false;

    /* Populate an OTA file context from the OTA job document. */

    pstUpdateFile = prvParseJobDoc( pcRawMsg, ulMsgLen, &bUpdateJob );

    if( bUpdateJob )
    {
        OTA_LOG_L1( "[%s] We receive a job update.\r\n", OTA_METHOD_NAME );
    }

    if( ( bUpdateJob == false ) && ( pstUpdateFile != NULL ) && ( prvInSelftest() == false ) )
    {
        if( pstUpdateFile->pucRxBlockBitmap != NULL )
        {
            vPortFree( pstUpdateFile->pucRxBlockBitmap ); /* Free any previously allocated bitmap. */
            pstUpdateFile->pucRxBlockBitmap = NULL;
        }

        /* Calculate how many bytes we need in our bitmap for tracking received blocks.
         * The below calculation requires power of 2 page sizes. */

        ulNumBlocks = ( pstUpdateFile->ulFileSize + ( OTA_FILE_BLOCK_SIZE - 1U ) ) >> otaconfigLOG2_FILE_BLOCK_SIZE;
        ulBitmapLen = ( ulNumBlocks + ( BITS_PER_BYTE - 1U ) ) >> LOG2_BITS_PER_BYTE;
        pstUpdateFile->pucRxBlockBitmap = ( uint8_t * ) pvPortMalloc( ulBitmapLen ); /*lint !e9079 FreeRTOS malloc port returns void*. */

        if( pstUpdateFile->pucRxBlockBitmap != NULL )
        {
            /* Set all bits in the bitmap to the erased state (we use 1 for erased just like flash memory). */
            ( void ) memset( pstUpdateFile->pucRxBlockBitmap, ( int32_t ) OTA_ERASED_BLOCKS_VAL, ulBitmapLen );

            /* Mark as used any pages in the bitmap that are out of range, based on the file size.
             * This keeps us from requesting those pages during retry processing or if using a windowed
             * block request. It also avoids erroneously accepting an out of range data block should it
             * get past any safety checks.
             * Files aren't always a multiple of 8 pages (8 bits/pages per byte) so some bits of the
             * last byte may be out of range and those are the bits we want to clear. */

            uint8_t ulBit = 1U << ( BITS_PER_BYTE - 1U );
            uint32_t ulNumOutOfRange = ( ulBitmapLen * BITS_PER_BYTE ) - ulNumBlocks;

            for( ulIndex = 0U; ulIndex < ulNumOutOfRange; ulIndex++ )
            {
                pstUpdateFile->pucRxBlockBitmap[ ulBitmapLen - 1U ] &= ~ulBit;
                ulBit >>= 1U;
            }

            pstUpdateFile->ulBlocksRemaining = ulNumBlocks; /* Initialize our blocks remaining counter. */

            /* Create/Open the OTA file on the file system. */
            xErr = xOTA_Agent.xPALCallbacks.xCreateFileForRx( pstUpdateFile );

            if( xErr != kOTA_Err_None )
            {
                ( void ) prvSetImageStateWithReason( eOTA_ImageState_Aborted, xErr );
                ( void ) prvOTA_Close( pstUpdateFile ); /* Ignore false result since we're setting the pointer to null on the next line. */
                pstUpdateFile = NULL;
            }
        }
        else
        {
            /* Can't receive the image without enough memory. */
            ( void ) prvOTA_Close( pstUpdateFile );
            pstUpdateFile = NULL;
        }
    }

    return pstUpdateFile; /* Return the OTA file context. */
}

/*
 * prvValidateDataBlock
 *
 * Validate the block index and size. If it is NOT the last block, it MUST be equal to a full block size.
 * If it IS the last block, it MUST be equal to the expected remainder. If the block ID is out of range,
 * that's an error.
 */
static bool prvValidateDataBlock( const OTA_FileContext_t * C,
                                  uint32_t ulBlockIndex,
                                  uint32_t ulBlockSize )
{
    bool bRet = false;
    uint32_t ulLastBlock = 0;

    ulLastBlock = ( ( C->ulFileSize + ( OTA_FILE_BLOCK_SIZE - 1U ) ) >> otaconfigLOG2_FILE_BLOCK_SIZE ) - 1U;

    if( ( ( ulBlockIndex < ulLastBlock ) && ( ulBlockSize == OTA_FILE_BLOCK_SIZE ) ) ||
        ( ( ulBlockIndex == ulLastBlock ) && ( ulBlockSize == ( C->ulFileSize - ( ulLastBlock * OTA_FILE_BLOCK_SIZE ) ) ) ) )
    {
        bRet = true;
    }

    return bRet;
}

/*
 * prvIngestDataBlock
 *
 * A block of file data was received by the application via some configured communication protocol.
 * If it looks like it is in range, write it to persistent storage. If it's the last block we're
 * expecting, close the file and perform the final signature check on it. If the close and signature
 * check are OK, let the caller know so it can be used by the system. Firmware updates generally
 * reboot the system and perform a self test phase. If the close or signature check fails, abort
 * the file transfer and return the result and any available details to the caller.
 */
static IngestResult_t prvIngestDataBlock( OTA_FileContext_t * C,
                                          uint8_t * pcRawMsg,
                                          uint32_t ulMsgSize,
                                          OTA_Err_t * pxCloseResult )
{
    DEFINE_OTA_METHOD_NAME( "prvIngestDataBlock" );

    IngestResult_t eIngestResult = eIngest_Result_Uninitialized;
    int32_t lFileId = 0;
    int32_t lBlockSize = 0;
    int32_t lBlockIndex = 0;
    uint32_t ulBlockSize = 0;
    uint32_t ulBlockIndex = 0;
    uint8_t * pucPayload = NULL;
    size_t xPayloadSize = 0;
    uint32_t ulByte = 0;
    uint8_t ucBitMask = 0;

    /* Check if the file context is NULL. */
    if( C == NULL )
    {
        eIngestResult = eIngest_Result_NullContext;
    }

    /* Check if the result pointer is NULL. */
    if( eIngestResult == eIngest_Result_Uninitialized )
    {
        if( pxCloseResult == NULL )
        {
            eIngestResult = eIngest_Result_NullResultPointer;
        }
        else
        {
            /* Default to a generic ingest function error until we prove success. */
            *pxCloseResult = kOTA_Err_GenericIngestError;
        }
    }

    /* Decode the received data block. */
    if( eIngestResult == eIngest_Result_Uninitialized )
    {
        /* If we have a block bitmap available then process the message. */
        if( ( C->pucRxBlockBitmap != NULL ) && ( C->ulBlocksRemaining > 0U ) )
        {
            /* Reset or start the firmware request timer. */
            prvStartRequestTimer( otaconfigFILE_REQUEST_WAIT_MS );

            /* Decode the file block received. */
            if( kOTA_Err_None != xOTA_DataInterface.prvDecodeFileBlock(
                    pcRawMsg,
                    ulMsgSize,
                    &lFileId,
                    &lBlockIndex,
                    &lBlockSize,
                    &pucPayload,
                    &xPayloadSize ) )
            {
                eIngestResult = eIngest_Result_BadData;
            }
            else
            {
                ulBlockIndex = ( uint32_t ) lBlockIndex;
                ulBlockSize = ( uint32_t ) lBlockSize;
            }
        }
        else
        {
            eIngestResult = eIngest_Result_UnexpectedBlock;
        }
    }

    /* Validate the received data block.*/
    if( eIngestResult == eIngest_Result_Uninitialized )
    {
        if( prvValidateDataBlock( C, ulBlockIndex, ulBlockSize ) )
        {
            OTA_LOG_L1( "[%s] Received file block %u, size %u\r\n", OTA_METHOD_NAME, ulBlockIndex, ulBlockSize );

            /* Create bit mask for use in our bitmap. */
            ucBitMask = 1U << ( ulBlockIndex % BITS_PER_BYTE ); /*lint !e9031 The composite expression will never be greater than BITS_PER_BYTE(8). */

            /* Calculate byte offset into bitmap. */
            ulByte = ulBlockIndex >> LOG2_BITS_PER_BYTE;

            /* Check if we've already received this block. */
            if( ( ( C->pucRxBlockBitmap[ ulByte ] ) & ucBitMask ) == 0U )
            {
                OTA_LOG_L1( "[%s] block %u is a DUPLICATE. %u blocks remaining.\r\n", OTA_METHOD_NAME,
                            ulBlockIndex,
                            C->ulBlocksRemaining );

                eIngestResult = eIngest_Result_Duplicate_Continue;
                *pxCloseResult = kOTA_Err_None; /* This is a success path. */
            }
        }
        else
        {
            OTA_LOG_L1( "[%s] Error! Block %u out of expected range! Size %u\r\n", OTA_METHOD_NAME, ulBlockIndex, ulBlockSize );
            eIngestResult = eIngest_Result_BlockOutOfRange;
        }
    }

    /* Process the received data block. */
    if( eIngestResult == eIngest_Result_Uninitialized )
    {
        if( C->pucFile != NULL )
        {
            int32_t iBytesWritten = xOTA_Agent.xPALCallbacks.xWriteBlock( C, ( ulBlockIndex * OTA_FILE_BLOCK_SIZE ), pucPayload, ulBlockSize );

            if( iBytesWritten < 0 )
            {
                OTA_LOG_L1( "[%s] Error (%d) writing file block\r\n", OTA_METHOD_NAME, iBytesWritten );
                eIngestResult = eIngest_Result_WriteBlockFailed;
            }
            else
            {
                C->pucRxBlockBitmap[ ulByte ] &= ~ucBitMask; /* Mark this block as received in our bitmap. */
                C->ulBlocksRemaining--;
                eIngestResult = eIngest_Result_Accepted_Continue;
                *pxCloseResult = kOTA_Err_None;
            }
        }
        else
        {
            OTA_LOG_L1( "[%s] Error: Unable to write block, file handle is NULL.\r\n", OTA_METHOD_NAME );
            eIngestResult = eIngest_Result_BadFileHandle;
        }
    }

    /* Close the file and cleanup.*/
    if( eIngestResult == eIngest_Result_Accepted_Continue )
    {
        if( C->ulBlocksRemaining == 0U )
        {
            OTA_LOG_L1( "[%s] Received final expected block of file.\r\n", OTA_METHOD_NAME );

            prvStopRequestTimer();            /* Don't request any more since we're done. */
            vPortFree( C->pucRxBlockBitmap ); /* Free the bitmap now that we're done with the download. */
            C->pucRxBlockBitmap = NULL;

            if( C->pucFile != NULL )
            {
                *pxCloseResult = xOTA_Agent.xPALCallbacks.xCloseFile( C );

                if( *pxCloseResult == kOTA_Err_None )
                {
                    OTA_LOG_L1( "[%s] File receive complete and signature is valid.\r\n", OTA_METHOD_NAME );
                    eIngestResult = eIngest_Result_FileComplete;
                }
                else
                {
                    uint32_t ulCloseResult = ( uint32_t ) *pxCloseResult;

                    OTA_LOG_L1( "[%s] Error (%u:0x%06x) closing OTA file.\r\n",
                                OTA_METHOD_NAME,
                                ulCloseResult >> kOTA_MainErrShiftDownBits,
                                ulCloseResult & ( uint32_t ) kOTA_PAL_ErrMask );

                    if( ( ( ulCloseResult ) & ( kOTA_Main_ErrMask ) ) == kOTA_Err_SignatureCheckFailed )
                    {
                        eIngestResult = eIngest_Result_SigCheckFail;
                    }
                    else
                    {
                        eIngestResult = eIngest_Result_FileCloseFail;
                    }
                }

                C->pucFile = NULL; /* File is now closed so clear the file handle in the context. */
            }
            else
            {
                OTA_LOG_L1( "[%s] Error: File handle is NULL after last block received.\r\n", OTA_METHOD_NAME );
                eIngestResult = eIngest_Result_BadFileHandle;
            }
        }
        else
        {
            OTA_LOG_L1( "[%s] Remaining: %u\r\n", OTA_METHOD_NAME, C->ulBlocksRemaining );
        }
    }

    return eIngestResult;
}

/*
 * Clean up after the OTA process is done. Possibly free memory for re-use.
 */
static void prvAgentShutdownCleanup( void )
{
    DEFINE_OTA_METHOD_NAME( "prvAgentShutdownCleanup" );

    uint32_t ulIndex;

    xOTA_Agent.eState = eOTA_AgentState_ShuttingDown;

    /*
     * Stop and delete any existing self test timer.
     */
    if( xOTA_Agent.pvSelfTestTimer != NULL )
    {
        ( void ) xTimerStop( xOTA_Agent.pvSelfTestTimer, 0 );
        ( void ) xTimerDelete( xOTA_Agent.pvSelfTestTimer, 0 );
        xOTA_Agent.pvSelfTestTimer = NULL;
    }

    /*
     * Stop and delete any existing transfer request timer.
     */
    if( xOTA_Agent.xRequestTimer != NULL )
    {
        ( void ) xTimerStop( xOTA_Agent.xRequestTimer, 0 );
        ( void ) xTimerDelete( xOTA_Agent.xRequestTimer, 0 );
        xOTA_Agent.xRequestTimer = NULL;
    }

    /* Cleanup related to selected protocol. */
    if( xOTA_DataInterface.prvCleanup != NULL )
    {
        ( void ) xOTA_DataInterface.prvCleanup( &xOTA_Agent );
    }

    /*
     * Close any open OTA transfers.
     */
    for( ulIndex = 0; ulIndex < OTA_MAX_FILES; ulIndex++ )
    {
        ( void ) prvOTA_Close( &xOTA_Agent.pxOTA_Files[ ulIndex ] );
    }

    /*
     * Free any remaining string memory holding the job name.
     */
    if( xOTA_Agent.pcOTA_Singleton_ActiveJobName != NULL )
    {
        vPortFree( xOTA_Agent.pcOTA_Singleton_ActiveJobName );
        xOTA_Agent.pcOTA_Singleton_ActiveJobName = NULL;
    }

    /* Delete the OTA Agent Queue.*/
    if( xOTA_Agent.xOTA_EventQueue != NULL )
    {
        vQueueDelete( xOTA_Agent.xOTA_EventQueue );
    }

    /*
     * Free OTA event buffers.
     */
    for( ulIndex = 0; ulIndex < otaconfigMAX_NUM_OTA_DATA_BUFFERS; ulIndex++ )
    {
        xEventBuffer[ ulIndex ].bBufferUsed = false;
    }

    /* Delete the semaphore.*/
    if( xOTA_Agent.xOTA_ThreadSafetyMutex != NULL )
    {
        vSemaphoreDelete( xOTA_Agent.xOTA_ThreadSafetyMutex );
    }
}

/*
 * Handle any events that were unexpected in the current state.
 */
static void prvHandleUnexpectedEvents( OTA_EventMsg_t * pxEventMsg )
{
    DEFINE_OTA_METHOD_NAME( "prvHandleUnexpectedEvents" );

    configASSERT( pxEventMsg );

    OTA_LOG_L1( "[%s] Unexpected Event. Current State [%s] Received Event  [%s] \n",
                OTA_METHOD_NAME,
                pcOTA_AgentState_Strings[ xOTA_Agent.eState ],
                pcOTA_Event_Strings[ pxEventMsg->xEventId ] );

    /* Perform any cleanup operations required for specifc unhandled events.*/
    switch( pxEventMsg->xEventId )
    {
        case eOTA_AgentEvent_ReceivedJobDocument:

            /* Received job event is not handled , release the buffer.*/
            prvOTAEventBufferFree( pxEventMsg->pxEventData );

            break;

        case eOTA_AgentEvent_ReceivedFileBlock:

            /* Received file data event is not handled , release the buffer.*/
            prvOTAEventBufferFree( pxEventMsg->pxEventData );

            break;

        default:

            /* Nothing to do here.*/
            break;
    }
}

/*
 * Execute the handler for selected index from the transition table.
 */
static void prvExecuteHandler( uint32_t index,
                               const OTA_EventMsg_t * const pxEventMsg )
{
    DEFINE_OTA_METHOD_NAME( "prvExecuteHandler" );

    OTA_Err_t xErr = kOTA_Err_Uninitialized;

    if( OTATransitionTable[ index ].xHandler )
    {
        xErr = OTATransitionTable[ index ].xHandler( pxEventMsg->pxEventData );

        if( xErr == kOTA_Err_None )
        {
            OTA_LOG_L1( "[%s] Called handler. Current State [%s] Event [%s] New state [%s] \n",
                        OTA_METHOD_NAME,
                        pcOTA_AgentState_Strings[ xOTA_Agent.eState ],
                        pcOTA_Event_Strings[ pxEventMsg->xEventId ],
                        pcOTA_AgentState_Strings[ OTATransitionTable[ index ].xNextState ] );

            /*
             * Update the current state in OTA agent context.
             */
            xOTA_Agent.eState = OTATransitionTable[ index ].xNextState;
        }
        else
        {
            OTA_LOG_L1( "[%s] Handler failed. Current State [%s] Event  [%s] Error Code [%d] \n",
                        OTA_METHOD_NAME,
                        pcOTA_AgentState_Strings[ xOTA_Agent.eState ],
                        pcOTA_Event_Strings[ pxEventMsg->xEventId ],
                        xErr );
        }
    }
}

static void prvOTAAgentTask( void * pvUnused )
{
    DEFINE_OTA_METHOD_NAME( "prvOTAAgentTask" );

    ( void ) pvUnused;

    OTA_EventMsg_t xEventMsg = { 0 };
    uint32_t ulTransitionTableLen = sizeof( OTATransitionTable ) / sizeof( OTATransitionTable[ 0 ] );
    uint32_t i = 0;

    /*
     * OTA Agent is ready to receive and process events so update the state to ready.
     */
    xOTA_Agent.eState = eOTA_AgentState_Ready;

    for( ; ; )
    {
        /*
         * Receive the next event form the OTA event queue to process.
         */
        if( xQueueReceive( xOTA_Agent.xOTA_EventQueue, &xEventMsg, portMAX_DELAY ) == pdTRUE )
        {
            /*
             * Search for the state and event from the table.
             */
            for( i = 0; i < ulTransitionTableLen; i++ )
            {
                if( ( ( OTATransitionTable[ i ].xCurrentState == xOTA_Agent.eState ) ||
                      ( OTATransitionTable[ i ].xCurrentState == eOTA_AgentState_All ) ) &&
                    ( OTATransitionTable[ i ].xEventId == xEventMsg.xEventId ) )
                {
                    OTA_LOG_L3( "[%s] , State matched [%s],  Event matched  [%s]\n",
                                OTA_METHOD_NAME,
                                pcOTA_AgentState_Strings[ i ]
                                pcOTA_Event_Strings[ i ] );

                    /*
                     * Execute the handler function.
                     */
                    prvExecuteHandler( i, &xEventMsg );
                    break;
                }
            }

            if( i == ulTransitionTableLen )
            {
                /*
                 * Handle unexpected events.
                 */
                prvHandleUnexpectedEvents( &xEventMsg );
            }
        }
    }
}

static BaseType_t prvStartOTAAgentTask( void * pvConnectionContext,
                                        TickType_t xTicksToWait )
{
    BaseType_t xReturn = 0;
    uint32_t ulIndex = 0;

    /*
     * The actual OTA Task and queue control structure. Only created once.
     */
    static TaskHandle_t pxOTA_TaskHandle;
    static StaticQueue_t xStaticQueue;

    portENTER_CRITICAL();

    /*
     * The current OTA image state as set by the OTA agent.
     */
    xOTA_Agent.eImageState = eOTA_ImageState_Unknown;

    /*
     * Save the current connection context provided by the user.
     */
    xOTA_Agent.pvConnectionContext = pvConnectionContext;

    /*
     * Create the queue used to pass event messages to the OTA task.
     */
    xOTA_Agent.xOTA_EventQueue = xQueueCreateStatic( ( UBaseType_t ) OTA_NUM_MSG_Q_ENTRIES, ( UBaseType_t ) sizeof( OTA_EventMsg_t ), ( uint8_t * ) xQueueData, &xStaticQueue );
    configASSERT( xOTA_Agent.xOTA_EventQueue != NULL );

    /*
     * Create the queue used to pass event messages to the OTA task.
     */
    xOTA_Agent.xOTA_ThreadSafetyMutex = xSemaphoreCreateMutex();
    configASSERT( xOTA_Agent.xOTA_ThreadSafetyMutex != NULL );

    /*
     * Initialize all file paths to NULL.
     */
    for( ulIndex = 0; ulIndex < OTA_MAX_FILES; ulIndex++ )
    {
        xOTA_Agent.pxOTA_Files[ ulIndex ].pucFilePath = NULL;
    }

    /*
     * Make sure OTA event buffers are clear.
     */
    for( ulIndex = 0; ulIndex < otaconfigMAX_NUM_OTA_DATA_BUFFERS; ulIndex++ )
    {
        xEventBuffer[ ulIndex ].bBufferUsed = false;
    }

    xReturn = xTaskCreate( prvOTAAgentTask, "OTA Agent Task", otaconfigSTACK_SIZE, NULL, otaconfigAGENT_PRIORITY, &pxOTA_TaskHandle );

    portEXIT_CRITICAL(); /* Protected elements are initialized. It's now safe to context switch. */

    /*
     * If task creation succeed, wait for the OTA agent to be ready before proceeding. Otherwise,
     * let it fall through to exit.
     */
    if( xReturn == pdPASS )
    {
        while( ( xTicksToWait-- > 0U ) && ( xOTA_Agent.eState != eOTA_AgentState_Ready ) )
        {
            vTaskDelay( 1 );
        }
    }

    return xReturn;
}

bool OTA_SignalEvent( const OTA_EventMsg_t * const pxEventMsg )
{
    DEFINE_OTA_METHOD_NAME( "OTA_SignalEvent" );

    bool bReturn = false;
    BaseType_t xErr = pdFALSE;

    /*
     * Send event to back of the queue.
     */
    if( xOTA_Agent.xOTA_EventQueue != NULL )
    {
        xErr = xQueueSendToBack( xOTA_Agent.xOTA_EventQueue, pxEventMsg, ( TickType_t ) 0 );
    }

    if( xErr == pdTRUE )
    {
        bReturn = true;
        OTA_LOG_L3( "Success: Pushed event message to queue.\r\n" );
    }
    else
    {
        bReturn = false;
        OTA_LOG_L1( "Error: Could not push event message to queue.\r\n" );
    }

    return bReturn;
}

/*
 * Public API to initialize the OTA Agent.
 *
 * If the Application calls OTA_AgentInit() after it is already initialized, we will
 * only reset the statistics counters and set the job complete callback but will not
 * modify the existing OTA agent context. You must first call OTA_AgentShutdown()
 * successfully.
 */
OTA_State_t OTA_AgentInit( void * pvConnectionContext,
                           const uint8_t * pucThingName,
                           pxOTACompleteCallback_t xFunc,
                           TickType_t xTicksToWait )
{
    OTA_State_t xState;

    if( xOTA_Agent.eState == eOTA_AgentState_Stopped )
    {
        /* Init default OTA pal callbacks. */
        OTA_PAL_Callbacks_t xPALCallbacks = OTA_JOB_CALLBACK_DEFAULT_INITIALIZER;

        /* Set the OTA complete callback. */
        xPALCallbacks.xCompleteCallback = xFunc;

        xState = OTA_AgentInit_internal( pvConnectionContext, pucThingName, &xPALCallbacks, xTicksToWait );
    }
    /* If OTA agent is already running, just update the CompleteCallback and reset the statistics. */
    else
    {
        if( xFunc != NULL )
        {
            xOTA_Agent.xPALCallbacks.xCompleteCallback = xFunc;
        }

        ( void ) memset( &xOTA_Agent.xStatistics, 0, sizeof( xOTA_Agent.xStatistics ) );
        xState = xOTA_Agent.eState;
    }

    return xState;
}

OTA_State_t OTA_AgentInit_internal( void * pvConnectionContext,
                                    const uint8_t * pucThingName,
                                    const OTA_PAL_Callbacks_t * pxCallbacks,
                                    TickType_t xTicksToWait )
{
    DEFINE_OTA_METHOD_NAME( "OTA_AgentInit_internal" );

    BaseType_t xReturn = 0;
    OTA_EventMsg_t xEventMsg = { 0 };

    /*
     * OTA Task is not running yet so update the state to init direclty in OTA context.
     */
    xOTA_Agent.eState = eOTA_AgentState_Init;

    /*
     * Check all the callbacks for null values and initialize the values in the ota agent context.
     * The OTA agent context is initialized with the prvPAL values. So, if null is passed in, don't
     * do anything and just use the defaults in the OTA structure.
     */
    prvSetPALCallbacks( pxCallbacks );

    /*
     * Initialize the OTA control interface based on the application protocol
     * selected.
     */
    prvSetControlInterface( &xOTA_ControlInterface );

    /*
     * Reset all the statistics counters.
     */
    xOTA_Agent.xStatistics.ulOTA_PacketsReceived = 0;
    xOTA_Agent.xStatistics.ulOTA_PacketsDropped = 0;
    xOTA_Agent.xStatistics.ulOTA_PacketsQueued = 0;
    xOTA_Agent.xStatistics.ulOTA_PacketsProcessed = 0;

    if( pucThingName == NULL )
    {
        OTA_LOG_L1( "[%s]Error: Thing name is NULL.\r\n", OTA_METHOD_NAME );
    }
    else
    {
        uint32_t ulStrLen = strlen( ( const char * ) pucThingName );

        if( ulStrLen <= otaconfigMAX_THINGNAME_LEN )
        {
            /*
             * Store the Thing name to be used for topics later.
             */
            ( void ) memcpy( xOTA_Agent.pcThingName, pucThingName, ulStrLen + 1UL ); /* Include zero terminator when saving the Thing name. */
        }

        xReturn = prvStartOTAAgentTask( pvConnectionContext, xTicksToWait );
    }

    if( xOTA_Agent.eState == eOTA_AgentState_Ready )
    {
        OTA_LOG_L1( "[%s] OTA Task is Ready.\r\n", OTA_METHOD_NAME );

        /*
         * OTA agent is ready so send event to start update process.
         */
        xEventMsg.xEventId = eOTA_AgentEvent_Start;

        /* Send signal to OTA task. */
        if( !OTA_SignalEvent( &xEventMsg ) )
        {
            OTA_LOG_L1( "[%s] Failed to signal the OTA agent to start.", OTA_METHOD_NAME );
        }
    }
    else
    {
        OTA_LOG_L1( "[%s] Failed to start the OTA Task, Error Code :%08x  Queue:%08x\r\n", OTA_METHOD_NAME, xReturn );

        xOTA_Agent.eState = eOTA_AgentState_Stopped;
    }

    /* Return status of agent. */
    return xOTA_Agent.eState;
}

/*
 * Public API to shutdown the OTA Agent.
 */
OTA_State_t OTA_AgentShutdown( TickType_t xTicksToWait )
{
    DEFINE_OTA_METHOD_NAME( "OTA_AgentShutdown" );

    OTA_EventMsg_t xEventMsg = { 0 };

    OTA_LOG_L2( "[%s] Start: %u ticks\r\n", OTA_METHOD_NAME, xTicksToWait );

    if( ( xOTA_Agent.eState != eOTA_AgentState_Stopped ) && ( xOTA_Agent.eState != eOTA_AgentState_ShuttingDown ) )
    {
        /*
         * Send shutdown signal to OTA Agent task.
         */
        xEventMsg.xEventId = eOTA_AgentEvent_Shutdown;

        /* Send signal to OTA task. */
        if( !OTA_SignalEvent( &xEventMsg ) )
        {
            OTA_LOG_L1( "[%s] Failed to signal the OTA agent to shutdown.", OTA_METHOD_NAME );
        }
        else
        {
            /*
             * Wait for the OTA agent to complete shutdown, if requested.
             */
            while( ( xTicksToWait > 0U ) && ( xOTA_Agent.eState != eOTA_AgentState_Stopped ) )
            {
                vTaskDelay( 1 );
                xTicksToWait--;
            }
        }
    }
    else
    {
        OTA_LOG_L1( "[%s] Nothing to do: Already in state [%s]\r\n", OTA_METHOD_NAME, pcOTA_AgentState_Strings[ xOTA_Agent.eState ] );
    }

    OTA_LOG_L2( "[%s] End: %u ticks\r\n", OTA_METHOD_NAME, xTicksToWait );

    return xOTA_Agent.eState;
}

/*
 * Return the current state of the OTA agent.
 */
OTA_State_t OTA_GetAgentState( void )
{
    return xOTA_Agent.eState;
}

/*
 * Return the number of packets dropped.
 */
uint32_t OTA_GetPacketsDropped( void )
{
    return xOTA_Agent.xStatistics.ulOTA_PacketsDropped;
}

/*
 * Return the number of packets queued.
 */
uint32_t OTA_GetPacketsQueued( void )
{
    return xOTA_Agent.xStatistics.ulOTA_PacketsQueued;
}

/*
 * Return the number of packets processed.
 */
uint32_t OTA_GetPacketsProcessed( void )
{
    return xOTA_Agent.xStatistics.ulOTA_PacketsProcessed;
}

/*
 * Return the number of packets received.
 */
uint32_t OTA_GetPacketsReceived( void )
{
    return xOTA_Agent.xStatistics.ulOTA_PacketsReceived;
}

OTA_Err_t OTA_CheckForUpdate( void )
{
    DEFINE_OTA_METHOD_NAME( "OTA_CheckForUpdate" );

    OTA_Err_t xReturn = kOTA_Err_None;
    OTA_EventMsg_t xEventMsg = { 0 };

    OTA_LOG_L1( "[%s] Sending event to check for update.\r\n", OTA_METHOD_NAME );

    /*
     * Send event to get OTA job document.
     */
    xEventMsg.xEventId = eOTA_AgentEvent_RequestJobDocument;

    if( !OTA_SignalEvent( &xEventMsg ) )
    {
        xReturn = kOTA_Err_EventQueueSendFailed;
    }

    /*
     * The event will be processed later so return kOTA_Err_None.
     */
    return xReturn;
}

/*
 * This should be called by the user application or the default OTA callback handler
 * after an OTA update is considered accepted. It simply calls the platform specific
 * code required to activate the received OTA update (usually just a device reset).
 */
OTA_Err_t OTA_ActivateNewImage( void )
{
    DEFINE_OTA_METHOD_NAME( "OTA_ActivateNewImage" );

    OTA_Err_t xErr = kOTA_Err_Uninitialized;

    /*
     * Call platform specific code to activate the image. This should reset the device
     * and not return unless there is a problem within the PAL layer. If it does return,
     * output an error message. The device may need to be reset manually.
     */
    if( xOTA_Agent.xPALCallbacks.xActivateNewImage != NULL )
    {
        xErr = xOTA_Agent.xPALCallbacks.xActivateNewImage( xOTA_Agent.ulServerFileID );
    }

    OTA_LOG_L1( "[%s] Error: Failed to activate new image, Error code - (0x%08x). Please reset manually.\r\n", OTA_METHOD_NAME, xErr );

    return xErr;
}

/*
 * Accept, reject or abort the OTA image transfer.
 *
 * If accepting or rejecting an image transfer, this API
 * will set the OTA image state and update the job status
 * appropriately.
 * If aborting a transfer, it will trigger the OTA task to
 * abort via an RTOS event asynchronously and therefore do
 * not set the image state here.
 *
 * NOTE: This call may block due to the status update message.
 */

OTA_Err_t OTA_SetImageState( OTA_ImageState_t eState )
{
    DEFINE_OTA_METHOD_NAME( "OTA_SetImageState" );

    OTA_Err_t xErr = kOTA_Err_Uninitialized;
    OTA_EventMsg_t xEventMsg = { 0 };

    switch( eState )
    {
        case eOTA_ImageState_Aborted:

            if( xOTA_Agent.xOTA_EventQueue != NULL )
            {
                xEventMsg.xEventId = eOTA_AgentEvent_UserAbort;

                /*
                 * Send the event, xOTA_Agent.eImageState will be set later when the event is processed.
                 */
                xErr = OTA_SignalEvent( &xEventMsg ) ? kOTA_Err_None : kOTA_Err_EventQueueSendFailed;
            }
            else
            {
                OTA_LOG_L1( "[%s] Error: OTA event queue is not initialized.\r\n", OTA_METHOD_NAME );

                xErr = kOTA_Err_Panic;
            }

            break;

        case eOTA_ImageState_Rejected:

            /*
             * Set the image state as rejected.
             */
            xErr = prvSetImageStateWithReason( eState, 0 );

            break;

        case eOTA_ImageState_Accepted:

            /*
             * Set the image state as accepted.
             */
            xErr = prvSetImageStateWithReason( eState, 0 );

            break;

        default:

            /*lint -e788 Keep lint quiet about the obvious unused states we're catching here. */
            xErr = kOTA_Err_BadImageState;

            break;
    }

    return xErr;
}

OTA_ImageState_t OTA_GetImageState( void )
{
    /*
     * Return the current OTA image state.
     */
    return xOTA_Agent.eImageState;
}

/*
 * Suspend OTA Agent task.
 */
OTA_Err_t OTA_Suspend( void )
{
    DEFINE_OTA_METHOD_NAME( "OTA_Suspend" );

    OTA_Err_t xErr = kOTA_Err_Uninitialized;
    OTA_EventMsg_t xEventMsg = { 0 };

    /* Stop the request timer. */
    prvStopRequestTimer();

    /* Check if OTA Agent is running. */
    if( xOTA_Agent.eState != eOTA_AgentState_Stopped )
    {
        /*
         * Send event to OTA agent task.
         */
        xEventMsg.xEventId = eOTA_AgentEvent_Suspend;
        xErr = OTA_SignalEvent( &xEventMsg ) ? kOTA_Err_None : kOTA_Err_EventQueueSendFailed;
    }
    else
    {
        OTA_LOG_L1( "[%s] Error: OTA Agent is not running, cannot suspend.\r\n", OTA_METHOD_NAME );

        xErr = kOTA_Err_OTAAgentStopped;
    }

    return xErr;
}

/*
 * Resume OTA Agent task.
 */
OTA_Err_t OTA_Resume( void * pxConnection )
{
    DEFINE_OTA_METHOD_NAME( "OTA_Resume" );

    OTA_Err_t xErr = kOTA_Err_Uninitialized;
    OTA_EventMsg_t xEventMsg = { 0 };

    xEventMsg.pxEventData = pxConnection;

    /* Check if OTA Agent is running. */
    if( xOTA_Agent.eState != eOTA_AgentState_Stopped )
    {
        /*
         * Send event to OTA agent task.
         */
        xEventMsg.xEventId = eOTA_AgentEvent_Resume;
        xErr = OTA_SignalEvent( &xEventMsg ) ? kOTA_Err_None : kOTA_Err_EventQueueSendFailed;
    }
    else
    {
        OTA_LOG_L1( "[%s] Error: OTA Agent is not running, cannot resume.\r\n", OTA_METHOD_NAME );

        xErr = kOTA_Err_OTAAgentStopped;
    }

    return xErr;
}

/*-----------------------------------------------------------*/

/* Provide access to private members for testing. */
#if IOT_BUILD_TESTS == 1
    #include "aws_ota_agent_test_access_define.h"
#endif
