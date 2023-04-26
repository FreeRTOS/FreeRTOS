/*
* Trace Recorder for Tracealyzer v4.6.0
* Copyright 2021 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The interface definitions for trace streaming ("stream ports").
* This "stream port" sets up the recorder to stream to a Ring Buffer.
*/

#ifndef TRC_STREAM_PORT_H
#define TRC_STREAM_PORT_H

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#include <trcTypes.h>
#include <trcStreamPortConfig.h>
#include <trcRecorder.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @def TRC_EXTERNAL_BUFFERS
 * 
 * @brief This Stream Port houses the EntryTable and Timestamp buffers
 */
#define TRC_EXTERNAL_BUFFERS 1

/**
 * @def TRC_SEND_NAME_ONLY_ON_DELETE
 *
 * @brief This Stream Port requires additional information to be sent when objects are deleted
 */
#define TRC_SEND_NAME_ONLY_ON_DELETE 1

/**
 * @def TRC_USE_INTERNAL_BUFFER
 * 
 * @brief This Stream Port uses the Multi Core Buffer directly.
 */

#define TRC_USE_INTERNAL_BUFFER 0

#define TRC_STREAM_PORT_BUFFER_SIZE ((((TRC_CFG_STREAM_PORT_BUFFER_SIZE) + sizeof(uint32_t) - 1) / sizeof(uint32_t)) * sizeof(uint32_t))

/**
* @brief
*/
typedef struct TraceMultiCoreBuffer
{
	uint32_t uiSize;
	uint8_t uiBuffer[TRC_STREAM_PORT_BUFFER_SIZE];
} TraceMultiCoreBuffer_t;

/**
 * @brief
 */
typedef struct TraceRingBuffer
{
	volatile uint8_t START_MARKERS[12];
	TraceHeaderBuffer_t xHeaderBuffer;
	TraceTimestampBuffer_t xTimestampInfo;
	TraceEntryTableBuffer_t xEntryTableBuffer;
	TraceMultiCoreBuffer_t xEventBuffer;
	volatile uint8_t END_MARKERS[12];
} TraceRingBuffer_t;

/**
 * @brief
 */
typedef struct TraceStreamPortData
{
	TraceMultiCoreEventBuffer_t xMultiCoreEventBuffer;
	TraceRingBuffer_t xRingBuffer;
} TraceStreamPortData_t;

extern TraceStreamPortData_t* pxStreamPortData;

/**
* @def TRC_STREAM_PORT_BUFFER_SIZE
* @brief The buffer size, aligned to base type.
*/
#define TRC_STREAM_PORT_DATA_BUFFER_SIZE (sizeof(TraceStreamPortData_t))

/**
 * @brief A structure representing the trace stream port buffer.
 */
typedef struct TraceStreamPortBuffer
{
	uint8_t buffer[(TRC_STREAM_PORT_DATA_BUFFER_SIZE)];
} TraceStreamPortBuffer_t;

/**
 * @internal Stream port initialize callback.
 * 
 * This function is called by the recorder as part of its initialization phase.
 * 
 * @param[in] pxBuffer Buffer
 * 
 * @retval TRC_FAIL Initialization failed
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceStreamPortInitialize(TraceStreamPortBuffer_t* pxBuffer);

/**
 * @brief Allocates data from the stream port.
 * 
 * @param[in] uiSize Allocation size
 * @param[out] ppvData Allocation data pointer
 * 
 * @retval TRC_FAIL Allocate failed
 * @retval TRC_SUCCESS Success
 */
#define xTraceStreamPortAllocate(uiSize, ppvData) ((void)uiSize, xTraceStaticBufferGet(ppvData))

/**
 * @brief Commits data to the stream port, depending on the implementation/configuration of the
 * stream port this data might be directly written to the stream port interface, buffered, or
 * something else.
 * 
 * @param[in] pvData Data to commit
 * @param[in] uiSize Data to commit size
 * @param[out] piBytesCommitted Bytes commited
 * 
 * @retval TRC_FAIL Commit failed
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceStreamPortCommit(void* pvData, uint32_t uiSize, int32_t* piBytesCommitted);

/**
 * @brief Writes data through the stream port interface.
 * 
 * @param[in] pvData Data to write
 * @param[in] uiSize Data to write size
 * @param[out] piBytesWritten Bytes written
 * 
 * @retval TRC_FAIL Write failed
 * @retval TRC_SUCCESS Success
 */
#define xTraceStreamPortWriteData(pvData, uiSize, piBytesWritten) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_4((void)pvData, (void)uiSize, (void)piBytesWritten, TRC_SUCCESS)

/**
 * @brief Reads data through the stream port interface.
 * 
 * @param[in] pvData Destination data buffer 
 * @param[in] uiSize Destination data buffer size
 * @param[out] piBytesRead Bytes read
 * 
 * @retval TRC_FAIL Read failed
 * @retval TRC_SUCCESS Success
 */
#define xTraceStreamPortReadData(pvData, uiSize, piBytesRead) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_4((void)pvData, (void)uiSize, (void)piBytesRead, TRC_SUCCESS)

/**
 * @brief Callback for when recorder is enabled
 * 
 * @param[in] uiStartOption Start option used when enabling trace recorder
 *
 * @retval TRC_FAIL Read failed
 * @retval TRC_SUCCESS Success
 */
#define xTraceStreamPortOnEnable(uiStartOption) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2((void)(uiStartOption), TRC_SUCCESS)

/**
 * @brief Callback for when recorder is disabled
 *
 * @retval TRC_FAIL Read failed
 * @retval TRC_SUCCESS Success
 */
#define xTraceStreamPortOnDisable() TRC_COMMA_EXPR_TO_STATEMENT_EXPR_1(TRC_SUCCESS)

/**
 * @brief Callback for when tracing begins
 *
 * @retval TRC_FAIL Read failed
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceStreamPortOnTraceBegin();

/**
 * @brief Callback for when tracing ends
 *
 * @retval TRC_FAIL Read failed
 * @retval TRC_SUCCESS Success
 */
#define xTraceStreamPortOnTraceEnd() TRC_COMMA_EXPR_TO_STATEMENT_EXPR_1(TRC_SUCCESS)

#ifdef __cplusplus
}
#endif

#endif /*(TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)*/

#endif /*(TRC_USE_TRACEALYZER_RECORDER == 1)*/

#endif /* TRC_STREAM_PORT_H */
