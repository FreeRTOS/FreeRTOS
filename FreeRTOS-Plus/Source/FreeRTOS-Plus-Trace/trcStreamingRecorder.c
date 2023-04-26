/*
 * Trace Recorder for Tracealyzer v4.6.0
 * Copyright 2021 Percepio AB
 * www.percepio.com
 *
 * SPDX-License-Identifier: Apache-2.0
 *
 * The generic core of the trace recorder's streaming mode.
 */

#include <trcRecorder.h>

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

typedef struct TraceHeader
{
	uint32_t uiPSF;
	uint16_t uiVersion;
	uint16_t uiPlatform;
	uint32_t uiOptions;
	uint32_t uiNumCores;
	uint32_t isrTailchainingThreshold;
	char platformCfg[8];
	uint16_t uiPlatformCfgPatch;
	uint8_t uiPlatformCfgMinor;
	uint8_t uiPlatformCfgMajor;
} TraceHeader_t;

/* The data structure for commands (a bit overkill) */
typedef struct TraceCommandType_t
{
	unsigned char cmdCode;
	unsigned char param1;
	unsigned char param2;
	unsigned char param3;
	unsigned char param4;
	unsigned char param5;
	unsigned char checksumLSB;
	unsigned char checksumMSB;
} TraceCommand_t;

#ifndef TRC_CFG_RECORDER_DATA_INIT
#define TRC_CFG_RECORDER_DATA_INIT 1
#endif

/* Used to interpret the data format */
#define TRACE_FORMAT_VERSION ((uint16_t)0x000A)

/* Used to determine endian of data (big/little) */
#define TRACE_PSF_ENDIANESS_IDENTIFIER ((uint32_t)0x50534600)

#if (TRC_CFG_RECORDER_BUFFER_ALLOCATION == TRC_RECORDER_BUFFER_ALLOCATION_STATIC)
static TraceRecorderData_t xRecorderData TRC_CFG_RECORDER_DATA_ATTRIBUTE;
TraceRecorderData_t* pxTraceRecorderData = &xRecorderData;
#else
/* If using DYNAMIC or CUSTOM allocation */
TraceRecorderData_t* pxTraceRecorderData TRC_CFG_RECORDER_DATA_ATTRIBUTE;
#endif

static TraceHeader_t* pxHeader;

/*******************************************************************************
* RecorderInitialized
*
* Makes sure the recorder data is only initialized once.
*
* NOTE: RecorderInitialized is only initialized to 0 if
* TRC_CFG_RECORDER_DATA_INIT is non-zero.
* This will avoid issues where the recorder must be started before main(),
* which can lead to RecorderInitialized be cleared by late initialization after
* xTraceEnable(TRC_INIT) was called and assigned RecorderInitialized its'
* value.
******************************************************************************/
#if (TRC_CFG_RECORDER_DATA_INIT != 0)
uint32_t RecorderInitialized = 0;
#else /* (TRC_CFG_RECORDER_DATA_INIT != 0) */
uint32_t RecorderInitialized TRC_CFG_RECORDER_DATA_ATTRIBUTE;
#endif /* (TRC_CFG_RECORDER_DATA_INIT != 0) */

#if (TRC_EXTERNAL_BUFFERS == 0)
/* Stores the header information on Start */
static void prvTraceStoreHeader(void);

/* Store the Timestamp info */
static void prvTraceStoreTimestampInfo(void);

/* Stores the entry table on Start */
static void prvTraceStoreEntryTable(void);

#else /* (TRC_EXTERNAL_BUFFERS == 0) */

#define prvTraceStoreHeader() 
#define prvTraceStoreTimestampInfo() 
#define prvTraceStoreEntryTable() 

#endif /* (TRC_EXTERNAL_BUFFERS == 0) */

/* Store start event. */
static void prvTraceStoreStartEvent(void);

/* Checks if the provided command is a valid command */
static int prvIsValidCommand(TraceCommand_t* cmd);

/* Executed the received command (Start or Stop) */
static void prvProcessCommand(TraceCommand_t* cmd);

/* Internal function for starting the recorder */
static void prvSetRecorderEnabled(void);

/* Internal function for stopping the recorder */
static void prvSetRecorderDisabled(void);

/******************************************************************************
* xTraceInitialize
*
* Initializes the recorder data.
* This function will be called by xTraceEnable(...).
* Only needs to be called manually if traced objects are created before the
* trace recorder can be enabled, at which point make sure to call this function
* as early as possible.
* See TRC_CFG_RECORDER_DATA_INIT in trcConfig.h.
******************************************************************************/
traceResult xTraceInitialize(void)
{
	TRC_ASSERT_EQUAL_SIZE(TraceRecorderDataBuffer_t, TraceRecorderData_t);
	
	if (RecorderInitialized != 0)
	{
		return TRC_SUCCESS;
	}

#if (TRC_CFG_RECORDER_BUFFER_ALLOCATION == TRC_RECORDER_BUFFER_ALLOCATION_DYNAMIC)
	pxRecorderData = TRC_MALLOC(sizeof(TraceRecorderData_t));
#endif

	/* These are set on init so they aren't overwritten by late initialization values. */
	pxTraceRecorderData->uiSessionCounter = 0;
	pxTraceRecorderData->uiRecorderEnabled = 0;
	pxTraceRecorderData->uiTraceSystemState = TRC_STATE_IN_STARTUP;

#if (TRC_EXTERNAL_BUFFERS == 0)
	if (xTraceHeaderInitialize(&pxTraceRecorderData->xHeaderBuffer) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	if (xTraceEntryTableInitialize(&pxTraceRecorderData->xEntryTableBuffer) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	if (xTraceTimestampInitialize(&pxTraceRecorderData->xTimestampBuffer) == TRC_FAIL)
	{
		return TRC_FAIL;
	}
#endif

	if (xTraceStackMonitorInitialize(&pxTraceRecorderData->xStackMonitorBuffer) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	if (xTraceStreamPortInitialize(&pxTraceRecorderData->xStreamPortBuffer) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	if (xTraceAssertInitialize(&pxTraceRecorderData->xAssertBuffer) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	if (xTraceDiagnosticsInitialize(&pxTraceRecorderData->xDiagnosticsBuffer) == TRC_FAIL)
	{
		return TRC_FAIL;
	}
	
	if (xTraceStaticBufferInitialize(&pxTraceRecorderData->xStaticBufferBuffer) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	if (xTraceEventInitialize(&pxTraceRecorderData->xEventDataBuffer) == TRC_FAIL)
	{
		return TRC_FAIL;
	}
	
	if (xTracePrintInitialize(&pxTraceRecorderData->xPrintBuffer) == TRC_FAIL)
	{
		return TRC_FAIL;
	}
	
	if (xTraceErrorInitialize(&pxTraceRecorderData->xErrorBuffer) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	if (xTraceISRInitialize(&pxTraceRecorderData->xISRInfoBuffer) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	if (xTraceTaskInitialize(&pxTraceRecorderData->xTaskInfoBuffer) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	if (xTraceKernelPortInitialize(&pxTraceRecorderData->xKernelPortBuffer) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	xTraceSetComponentInitialized(TRC_RECORDER_COMPONENT_CORE);

	return TRC_SUCCESS;
}

traceResult xTraceHeaderInitialize(TraceHeaderBuffer_t *pxBuffer)
{
	uint32_t i;
	char* platform_cfg = TRC_PLATFORM_CFG;

	TRC_ASSERT_EQUAL_SIZE(TraceHeaderBuffer_t, TraceHeader_t);

	if (pxBuffer == 0)
	{
		return TRC_FAIL;
	}

	pxHeader = (TraceHeader_t*)pxBuffer;

	pxHeader->uiPSF = TRACE_PSF_ENDIANESS_IDENTIFIER;
	pxHeader->uiVersion = TRACE_FORMAT_VERSION;
	pxHeader->uiPlatform = TRACE_KERNEL_VERSION;

	for (i = 0; i < TRC_PLATFORM_CFG_LENGTH; i++)
	{
		pxHeader->platformCfg[i] = platform_cfg[i];
		if (platform_cfg[i] == 0)
		{
			break;
		}
	}
	pxHeader->uiPlatformCfgPatch = TRC_PLATFORM_CFG_PATCH;
	pxHeader->uiPlatformCfgMinor = TRC_PLATFORM_CFG_MINOR;
	pxHeader->uiPlatformCfgMajor = TRC_PLATFORM_CFG_MAJOR;
	pxHeader->uiNumCores = TRC_CFG_CORE_COUNT;
	pxHeader->isrTailchainingThreshold = TRC_CFG_ISR_TAILCHAINING_THRESHOLD;

	/* Lowest bit used for TRC_IRQ_PRIORITY_ORDER */
	pxHeader->uiOptions = ((TRC_IRQ_PRIORITY_ORDER) << 0);

	/* 3rd bit used for TRC_CFG_TEST_MODE */
	pxHeader->uiOptions |= ((TRC_CFG_TEST_MODE) << 2);

	return TRC_SUCCESS;
}

traceResult xTraceEnable(uint32_t uiStartOption)
{
	TraceCommand_t xCommand;
	int32_t iBytes = 0;

	if (xTraceInitialize() == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	xTraceStreamPortOnEnable(uiStartOption);

	if (xTraceKernelPortEnable() == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	if (uiStartOption == TRC_START_AWAIT_HOST)
	{
		/* We keep trying to read commands from host until the recorder has been started */
		do
		{
			iBytes = 0;

			if (xTraceStreamPortReadData(&xCommand, sizeof(TraceCommand_t), (int32_t*)&iBytes) == TRC_FAIL)
			{
				xTraceWarning(TRC_WARNING_STREAM_PORT_READ);
			}

			if (iBytes == sizeof(TraceCommand_t))
			{
				if (prvIsValidCommand(&xCommand))
				{
					if (xCommand.cmdCode == CMD_SET_ACTIVE && xCommand.param1 == 1)
					{
						/* On start, init and reset the timestamping */
						TRC_PORT_SPECIFIC_INIT();
					}

					prvProcessCommand(&xCommand);
				}
			}
		} while (pxTraceRecorderData->uiRecorderEnabled == 0);
	}
	else if (uiStartOption == TRC_START)
	{
		/* We start streaming directly - this assumes that the host interface is ready! */
		TRC_PORT_SPECIFIC_INIT();

		xCommand.cmdCode = CMD_SET_ACTIVE;
		xCommand.param1 = 1;
		prvProcessCommand(&xCommand);
	}
	else if (uiStartOption == TRC_START_FROM_HOST)
	{
		/* We prepare the system to receive commands from host, but let system resume execution until that happens */
		TRC_PORT_SPECIFIC_INIT();
	}

	return TRC_SUCCESS;
}

traceResult xTraceDisable(void)
{
	prvSetRecorderDisabled();

	xTraceStreamPortOnDisable();
	
	return TRC_SUCCESS;
}

#if (TRC_CFG_RECORDER_BUFFER_ALLOCATION == TRC_RECORDER_BUFFER_ALLOCATION_CUSTOM)
traceResult xTraceSetBuffer(TraceRecorderDataBuffer_t* pxBuffer)
{
	if (pxBuffer == 0)
	{
		return TRC_FAIL;
	}
	
	pxTraceRecorderData = (TraceRecorderData_t*)pxBuffer;

	return TRC_SUCCESS;
}
#endif

traceResult xTraceGetEventBuffer(void **ppvBuffer, TraceUnsignedBaseType_t *puiSize)
{
	if (pxTraceRecorderData == 0 || ppvBuffer == 0 || puiSize == 0)
	{
		return TRC_FAIL;
	}
	
	/* Returns the xStreamPortBuffer since that is the one containing trace data */
	*ppvBuffer = (void*)&pxTraceRecorderData->xStreamPortBuffer;
	*puiSize = sizeof(pxTraceRecorderData->xStreamPortBuffer);
	
	return TRC_SUCCESS;
}

traceResult xTraceTzCtrl(void)
{
	TraceCommand_t xCommand;
	int32_t iBytes = 0;
	
	do
	{
		/* Listen for new commands */
		iBytes = 0;
		if (xTraceStreamPortReadData(&xCommand, sizeof(TraceCommand_t), &iBytes) == TRC_FAIL)
		{
			/* The connection has failed, stop tracing */
			xTraceDisable();

			return TRC_FAIL;
		}

		if (iBytes == sizeof(TraceCommand_t))
		{
			if (prvIsValidCommand(&xCommand))
			{
				prvProcessCommand(&xCommand); /* Start or Stop currently... */
			}
		}

#if (TRC_USE_INTERNAL_BUFFER == 1)
		xTraceInternalEventBufferTransfer(&iBytes);
#endif

		/* If there was data sent or received (bytes != 0), loop around and repeat, if there is more data to send or receive.
		Otherwise, step out of this loop and sleep for a while. */

	} while (iBytes != 0);

	if (xTraceIsRecorderEnabled())
	{
		xTraceDiagnosticsCheckStatus();
		xTraceStackMonitorReport();
	}

	return TRC_SUCCESS;
}

void vTraceSetFilterGroup(uint16_t filterGroup)
{
	(void)filterGroup;
}

void vTraceSetFilterMask(uint16_t filterMask)
{
	(void)filterMask;
}

/******************************************************************************/
/*** INTERNAL FUNCTIONS *******************************************************/
/******************************************************************************/
/* Internal function for starting/stopping the recorder. */
static void prvSetRecorderEnabled(void)
{
	uint32_t timestampFrequency = 0;
	
	TRACE_ALLOC_CRITICAL_SECTION();
	
	if (pxTraceRecorderData->uiRecorderEnabled == 1)
	{
		return;
	}

	xTraceTimestampGetFrequency(&timestampFrequency);
	/* If not overridden using 	xTraceTimestampSetFrequency(...), use default value */
	if (timestampFrequency == 0)
	{
		timestampFrequency = TRC_HWTC_FREQ_HZ;
		xTraceTimestampSetFrequency(timestampFrequency);
	}

	TRACE_ENTER_CRITICAL_SECTION();

	/* If the internal event buffer is used, we must clear it */
	xTraceInternalEventBufferClear();
	
	xTraceStreamPortOnTraceBegin();

	prvTraceStoreHeader();
	prvTraceStoreTimestampInfo();
	prvTraceStoreEntryTable();
	prvTraceStoreStartEvent();

	pxTraceRecorderData->uiSessionCounter++;

	pxTraceRecorderData->uiRecorderEnabled = 1;

	TRACE_EXIT_CRITICAL_SECTION();
}

static void prvSetRecorderDisabled(void)
{
	TRACE_ALLOC_CRITICAL_SECTION();

	if (pxTraceRecorderData->uiRecorderEnabled == 0)
	{
		return;
	}

	TRACE_ENTER_CRITICAL_SECTION();
	
	pxTraceRecorderData->uiRecorderEnabled = 0;

	xTraceStreamPortOnTraceEnd();

	TRACE_EXIT_CRITICAL_SECTION();
}

#if (TRC_EXTERNAL_BUFFERS == 0)
/* Stores the header information on Start */
static void prvTraceStoreHeader(void)
{
	TraceEventHandle_t xEventHandle;

	if (xTraceEventBeginRawOfflineBlocking(sizeof(TraceHeader_t), &xEventHandle) == TRC_SUCCESS)
	{
		xTraceEventAddData(xEventHandle, pxHeader, sizeof(TraceHeader_t));
		xTraceEventEndOfflineBlocking(xEventHandle);
	}
}

/* Store the Timestamp */
static void prvTraceStoreTimestampInfo(void)
{
	TraceEventHandle_t xEventHandle;
	uint32_t timestampFrequency = 0;

	xTraceTimestampGetFrequency(&timestampFrequency);

	if (xTraceEventBeginRawOfflineBlocking(sizeof(TraceTimestampBuffer_t), &xEventHandle) == TRC_SUCCESS)
	{
		xTraceEventAddData(xEventHandle, &pxTraceRecorderData->xTimestampBuffer, sizeof(TraceTimestampBuffer_t));
		xTraceEventEndOfflineBlocking(xEventHandle);
	}
}

/* Stores the entry table on Start */
static void prvTraceStoreEntryTable(void)
{
	uint32_t i = 0;
	TraceEventHandle_t xEventHandle;
	TraceEntryHandle_t xEntryHandle;
	uint32_t uiEntryCount;
	void *pvEntryAddress;

	xTraceEntryGetCount(&uiEntryCount);
	
	if (xTraceEventBeginRawOfflineBlocking(sizeof(uint32_t) + sizeof(uint32_t) + sizeof(uint32_t), &xEventHandle) == TRC_SUCCESS)
	{
		xTraceEventAdd32(xEventHandle, uiEntryCount);
		xTraceEventAdd32(xEventHandle, TRC_ENTRY_TABLE_SLOT_SYMBOL_SIZE);
		xTraceEventAdd32(xEventHandle, TRC_ENTRY_TABLE_STATE_COUNT);
		xTraceEventEndOfflineBlocking(xEventHandle);
	}
	
	for (i = 0; i < (TRC_ENTRY_TABLE_SLOTS); i++)
	{
		xTraceEntryGetAtIndex(i, &xEntryHandle);
		xTraceEntryGetAddress(xEntryHandle, &pvEntryAddress);
		/* We only send used entry slots */
		if (pvEntryAddress != 0)
		{
			/* Send entry */
			if (xTraceEventBeginRawOfflineBlocking(sizeof(TraceEntry_t), &xEventHandle) == TRC_SUCCESS)
			{
				xTraceEventAddData(xEventHandle, (void*)xEntryHandle, sizeof(TraceEntry_t));
				xTraceEventEndOfflineBlocking(xEventHandle);
			}
		}
	}
}
#endif /* (TRC_EXTERNAL_BUFFERS == 0) */

static void prvTraceStoreStartEvent()
{
	TraceEventHandle_t xEventHandle;
	void* pvCurrentTask;

	xTraceTaskGetCurrent(&pvCurrentTask);

	if (xTraceEventBeginOffline(PSF_EVENT_TRACE_START, sizeof(uint32_t), &xEventHandle) == TRC_SUCCESS)
	{
		xTraceEventAdd32(xEventHandle, (uint32_t)pvCurrentTask);
		xTraceEventEndOffline(xEventHandle);
	}
}

/* Checks if the provided command is a valid command */
static int prvIsValidCommand(TraceCommand_t* cmd)
{
  	uint16_t checksum = (uint16_t)(0xFFFF - (	cmd->cmdCode +
												cmd->param1 +
												cmd->param2 +
												cmd->param3 +
												cmd->param4 +
												cmd->param5));

	if (cmd->checksumMSB != (unsigned char)(checksum >> 8))
		return 0;

	if (cmd->checksumLSB != (unsigned char)(checksum & 0xFF))
		return 0;

	if (cmd->cmdCode > CMD_LAST_COMMAND)
		return 0;

	return 1;
}

/* Executed the received command (Start or Stop) */
static void prvProcessCommand(TraceCommand_t* cmd)
{
  	switch(cmd->cmdCode)
	{
		case CMD_SET_ACTIVE:
			if (cmd->param1 == 1)
			{
				prvSetRecorderEnabled();
			}
			else
			{
				prvSetRecorderDisabled();
			}
		  	break;
		default:
		  	break;
	}
}

#endif /* (TRC_USE_TRACEALYZER_RECORDER == 1) */

#endif /*(TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)*/
