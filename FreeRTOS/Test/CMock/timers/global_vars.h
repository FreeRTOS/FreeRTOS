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

#ifndef GLOBAL_VARS_H
#define GLOBAL_VARS_H

#include "timers.h"
/* ======================  DEFINITIONS FROM timers.c ======================== */
#define tmrNO_DELAY                             ( TickType_t ) 0U

#define tmrSTATUS_IS_ACTIVE                     ( ( uint8_t ) 0x01 )
#define tmrSTATUS_IS_STATICALLY_ALLOCATED       ( ( uint8_t ) 0x02 )
#define tmrSTATUS_IS_AUTORELOAD                 ( ( uint8_t ) 0x04 )

#define tmrCOMMAND_EXECUTE_CALLBACK_FROM_ISR    ( ( BaseType_t ) -2 )
#define tmrCOMMAND_EXECUTE_CALLBACK             ( ( BaseType_t ) -1 )
#define tmrCOMMAND_START_DONT_TRACE             ( ( BaseType_t ) 0 )
#define tmrCOMMAND_START                        ( ( BaseType_t ) 1 )
#define tmrCOMMAND_RESET                        ( ( BaseType_t ) 2 )
#define tmrCOMMAND_STOP                         ( ( BaseType_t ) 3 )
#define tmrCOMMAND_CHANGE_PERIOD                ( ( BaseType_t ) 4 )
#define tmrCOMMAND_DELETE                       ( ( BaseType_t ) 5 )

#define tmrFIRST_FROM_ISR_COMMAND               ( ( BaseType_t ) 6 )
#define tmrCOMMAND_START_FROM_ISR               ( ( BaseType_t ) 6 )
#define tmrCOMMAND_RESET_FROM_ISR               ( ( BaseType_t ) 7 )
#define tmrCOMMAND_STOP_FROM_ISR                ( ( BaseType_t ) 8 )
#define tmrCOMMAND_CHANGE_PERIOD_FROM_ISR       ( ( BaseType_t ) 9 )

typedef struct tmrTimerControl                  /* The old naming convention is used to prevent breaking kernel aware debuggers. */
{
    const char * pcTimerName;                   /*<< Text name.  This is not used by the kernel, it is included simply to make debugging easier. */ /*lint !e971 Unqualified char types are allowed for strings and single characters only. */
    ListItem_t xTimerListItem;                  /*<< Standard linked list item as used by all kernel features for event management. */
    TickType_t xTimerPeriodInTicks;             /*<< How quickly and often the timer expires. */
    void * pvTimerID;                           /*<< An ID to identify the timer.  This allows the timer to be identified when the same callback is used for multiple timers. */
    TimerCallbackFunction_t pxCallbackFunction; /*<< The function that will be called when the timer expires. */
    #if ( configUSE_TRACE_FACILITY == 1 )
        UBaseType_t uxTimerNumber;              /*<< An ID assigned by trace tools such as FreeRTOS+Trace */
    #endif
    uint8_t ucStatus;                           /*<< Holds bits to say if the timer was statically allocated or not, and if it is active or not. */
} xTIMER;

typedef xTIMER Timer_t;

typedef struct tmrTimerParameters
{
    TickType_t xMessageValue; /*<< An optional value used by a subset of commands, for example, when changing the period of a timer. */
    Timer_t * pxTimer;        /*<< The timer to which the command will be applied. */
} TimerParameter_t;

typedef struct tmrCallbackParameters
{
    PendedFunction_t pxCallbackFunction; /* << The callback function to execute. */
    void * pvParameter1;                 /* << The value that will be used as the callback functions first parameter. */
    uint32_t ulParameter2;               /* << The value that will be used as the callback functions second parameter. */
} CallbackParameters_t;

typedef struct tmrTimerQueueMessage
{
    BaseType_t xMessageID; /*<< The command being sent to the timer service task. */
    union
    {
        TimerParameter_t xTimerParameters;

        /* Don't include xCallbackParameters if it is not going to be used as
         * it makes the structure (and therefore the timer queue) larger. */
        #if ( INCLUDE_xTimerPendFunctionCall == 1 )
            CallbackParameters_t xCallbackParameters;
        #endif /* INCLUDE_xTimerPendFunctionCall */
    } u;
} DaemonTaskMessage_t;


#define HOOK_DIAG()                            \
    do {                                       \
        printf( "%s Called\n", __FUNCTION__ ); \
    } while( 0 )


/*#undef HOOK_DIAG */
/*#idefine HOOK_DIAG() */
#endif /* ifndef GLOBAL_VARS_H */
