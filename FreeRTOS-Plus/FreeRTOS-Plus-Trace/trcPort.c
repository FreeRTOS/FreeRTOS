/*******************************************************************************
 * FreeRTOS+Trace v2.2.3 Recorder Library
 * Percepio AB, www.percepio.se
 *
 * trcPort.c
 *
 * Contains all portability issues of the trace recorder library. 
 * See also trcPort.h, where port-specific macros are defined.
 *
 * Terms of Use
 * This software is copyright Percepio AB. The recorder library is free for
 * use together with Percepio products. You may distribute the recorder library
 * in its original form, including modifications in trcPort.c and trcPort.h
 * given that these modification are clearly marked as your own modifications
 * and documented in the initial comment section of these source files. 
 * This software is the intellectual property of Percepio AB and may not be 
 * sold or in other ways commercially redistributed without explicit written 
 * permission by Percepio AB.
 *
 * Disclaimer 
 * The trace tool and recorder library is being delivered to you AS IS and 
 * Percepio AB makes no warranty as to its use or performance. Percepio AB does 
 * not and cannot warrant the performance or results you may obtain by using the 
 * software or documentation. Percepio AB make no warranties, express or 
 * implied, as to noninfringement of third party rights, merchantability, or 
 * fitness for any particular purpose. In no event will Percepio AB, its 
 * technology partners, or distributors be liable to you for any consequential, 
 * incidental or special damages, including any lost profits or lost savings, 
 * even if a representative of Percepio AB has been advised of the possibility 
 * of such damages, or for any claim by any third party. Some jurisdictions do 
 * not allow the exclusion or limitation of incidental, consequential or special 
 * damages, or the exclusion of implied warranties or limitations on how long an 
 * implied warranty may last, so the above limitations may not apply to you.
 *
 * OFFER FROM PERCEPIO:
 * For silicon companies and non-corporate FreeRTOS users (researchers, students
 * , hobbyists or early-phase startups) we have an attractive offer: 
 * Provide a hardware timer port and get a FREE single-user licence for
 * FreeRTOS+Trace Professional Edition. Read more about this offer at 
 * www.percepio.se or contact us directly at support@percepio.se.
 *
 * FreeRTOS+Trace is available as Free Edition and in two premium editions.
 * You may use the premium features during 30 days for evaluation.
 * Download FreeRTOS+Trace at http://www.percepio.se/index.php?page=downloads
 *
 * Copyright Percepio AB, 2012.
 * www.percepio.se
 ******************************************************************************/
#include "FreeRTOS.h"
#include "trcPort.h"
#include "trcUser.h"

#if (configUSE_TRACE_FACILITY == 1)

#if (INCLUDE_SAVE_TO_FILE == 1)
static char* prvFileName = NULL;
#endif

/*******************************************************************************
 * uiTraceTickCount
 *
 * This variable is updated by the traceTASK_INCREMENT_TICK macro in the 
 * FreeRTOS tick handler. This does not need to be modified when developing a 
 * new timer port. It is prefered to keep any timer port changes in the HWTC 
 * macro definitions, which typically give sufficient flexibility.
 ******************************************************************************/
uint32_t uiTraceTickCount = 0;

/******************************************************************************
 * uiTracePortGetTimeStamp
 *
 * Returns the current time based on the HWTC macros which provide a hardware
 * isolation layer towards the hardware timer/counter.
 *
 * The HWTC macros and uiTracePortGetTimeStamp is the main porting issue
 * or the trace recorder library. Typically you should not need to change
 * the code of uiTracePortGetTimeStamp if using the HWTC macros.
 *
 * OFFER FROM PERCEPIO:
 * For silicon companies and non-corporate FreeRTOS users (researchers, students
 * , hobbyists or early-phase startups) we have an attractive offer: 
 * Provide a hardware timer port and get a FREE single-user licence for
 * FreeRTOS+Trace Professional Edition. Read more about this offer at 
 * www.percepio.se or contact us directly at support@percepio.se.
 ******************************************************************************/
uint32_t uiTracePortGetTimeStamp()
{
    /* Keep these static to avoid using more stack than necessary */
    static uint32_t last_timestamp = 0;
    static uint32_t timestamp;

#if (HWTC_COUNT_DIRECTION == DIRECTION_INCREMENTING)
    timestamp = ((uiTraceTickCount * HWTC_PERIOD) + HWTC_COUNT) / HWTC_DIVISOR;
#else
#if (HWTC_COUNT_DIRECTION == DIRECTION_DECREMENTING)
    timestamp = ((uiTraceTickCount * HWTC_PERIOD) + (HWTC_PERIOD - HWTC_COUNT)) / HWTC_DIVISOR;
#else
    Junk text to cause compiler error - HWTC_COUNT_DIRECTION is not set correctly!
    Should be DIRECTION_INCREMENTING or DIRECTION_DECREMENTING
#endif
#endif

    /* May occur due to overflow, if the update of uiTraceTickCount has been 
    delayed due to disabled interrupts. */
    if (timestamp < last_timestamp)
    {
        timestamp += (HWTC_PERIOD / HWTC_DIVISOR);
    }

    last_timestamp = timestamp;

    return timestamp;
}

/*******************************************************************************
 * vTracePortEnd
 * 
 * This function is called by the monitor when a recorder stop is detected.
 * This is used by the Win32 port to store the trace to a file. The file path is
 * set using vTracePortSetOutFile.
 ******************************************************************************/
void vTracePortEnd()
{
    vTraceConsoleMessage("\n\r[FreeRTOS+Trace] Running vTracePortEnd.\n\r");

    #if (WIN32_PORT_SAVE_WHEN_STOPPED == 1)
    vTracePortSave();
    #endif

    #if (WIN32_PORT_EXIT_WHEN_STOPPED == 1)
    /* In the FreeRTOS/Win32 demo, this allows for killing the application 
    when the recorder is stopped (e.g., when the buffer is full) */
    system("pause");
    exit(0);
    #endif
}

#if (INCLUDE_SAVE_TO_FILE == 1)
/*******************************************************************************
 * vTracePortSetOutFile
 *
 * Sets the filename/path used in vTracePortSave.
 * This is set in a separate function, since the Win32 port calls vTracePortSave
 * in vTracePortEnd if WIN32_PORT_SAVE_WHEN_STOPPED is set.
 ******************************************************************************/
void vTracePortSetOutFile(char* path)
{
    prvFileName = path;
}

/*******************************************************************************
 * vTracePortSave
 *
 * Saves the trace to a file on a local file system. The path is set in a 
 * separate function, vTracePortSetOutFile, since the Win32 port calls 
 * vTracePortSave in vTracePortEnd if WIN32_PORT_SAVE_WHEN_STOPPED is set.
 ******************************************************************************/
void vTracePortSave()
{
    char buf[180];
    FILE* f;

    if (prvFileName == NULL)
    {
        prvFileName = "FreeRTOSPlusTrace.dump";
        sprintf(buf, "No filename specified, using default \"%s\".", prvFileName);
        vTraceConsoleMessage(buf);
    }

    fopen_s(&f, prvFileName, "wb");
    if (f)
    {
        fwrite(RecorderDataPtr, sizeof(RecorderDataType), 1, f);
        fclose(f);
        sprintf(buf, "\n\r[FreeRTOS+Trace] Saved in: %s\n\r", prvFileName);
        vTraceConsoleMessage(buf);
    }
    else
    {
        sprintf(buf, "\n\r[FreeRTOS+Trace] Failed to write to output file!\n\r");
        vTraceConsoleMessage(buf);
    }
}
#endif
#endif