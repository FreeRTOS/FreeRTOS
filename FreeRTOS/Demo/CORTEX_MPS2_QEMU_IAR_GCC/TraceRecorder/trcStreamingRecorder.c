/*
 * Trace Recorder for Tracealyzer v4.10.2
 * Copyright 2023 Percepio AB
 * www.percepio.com
 *
 * SPDX-License-Identifier: Apache-2.0
 *
 * The generic core of the trace recorder's streaming mode.
 */

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1) && (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#ifndef TRC_KERNEL_PORT_HEAP_INIT
#define TRC_KERNEL_PORT_HEAP_INIT(__size) 
#endif

/* Entry symbol length maximum check */
#if ((TRC_CFG_ENTRY_SYMBOL_MAX_LENGTH) > 28UL)
#error Maximum entry symbol length is 28!
#endif

/* Entry symbol length minimum check */
#if ((TRC_CFG_ENTRY_SYMBOL_MAX_LENGTH) < 4UL)
#error Minimum entry symbol length is 4!
#endif

typedef struct TraceHeader
{
	uint32_t uiPSF;
	uint16_t uiVersion;
	uint16_t uiPlatform;
	uint32_t uiOptions;
	uint32_t uiNumCores;
	uint32_t isrTailchainingThreshold;
	uint16_t uiPlatformCfgPatch;
	uint8_t uiPlatformCfgMinor;
	uint8_t uiPlatformCfgMajor;
	char platformCfg[8];
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
#define TRACE_FORMAT_VERSION ((uint16_t)0x000E)

/* Used to determine endian of data (big/little) */
#define TRACE_PSF_ENDIANESS_IDENTIFIER ((uint32_t)0x50534600)

#if (TRC_CFG_RECORDER_BUFFER_ALLOCATION == TRC_RECORDER_BUFFER_ALLOCATION_STATIC)
static TraceRecorderData_t xRecorderData TRC_CFG_RECORDER_DATA_ATTRIBUTE; /*cstat !MISRAC2004-8.7 !MISRAC2012-Rule-8.9_a !MISRAC2012-Rule-8.9_b Suppress global variable check*/
TraceRecorderData_t* pxTraceRecorderData TRC_CFG_RECORDER_DATA_ATTRIBUTE;
#else
/* If using DYNAMIC or CUSTOM allocation */
TraceRecorderData_t* pxTraceRecorderData TRC_CFG_RECORDER_DATA_ATTRIBUTE;
#endif

static TraceHeader_t* pxHeader TRC_CFG_RECORDER_DATA_ATTRIBUTE; /*cstat !MISRAC2004-8.7 !MISRAC2012-Rule-8.9_a !MISRAC2012-Rule-8.9_b Suppress global variable check*/

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
uint32_t RecorderInitialized = 0u;
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
static int32_t prvIsValidCommand(const TraceCommand_t* const cmd);

/* Executed the received command (Start or Stop) */
static void prvProcessCommand(const TraceCommand_t* const cmd);

/* Internal function for starting the recorder */
static void prvSetRecorderEnabled(void);

/* Internal function for stopping the recorder */
static void prvSetRecorderDisabled(void);

/* Internal function for verifying size */
static traceResult prvVerifySizeAlignment(uint32_t ulSize);

static TraceUnsignedBaseType_t prvIs64bit(void);

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
	TraceUnsignedBaseType_t i;
	TRC_ASSERT_EQUAL_SIZE(TraceUnsignedBaseType_t, TraceBaseType_t);

	/* TraceUnsignedBaseType_t is used to store handles (addresses) */
	TRC_ASSERT_EQUAL_SIZE(TraceUnsignedBaseType_t, TraceHandleBaseType_t);
	
	if (RecorderInitialized != 0u)
	{
		return TRC_SUCCESS;
	}

	TRC_PORT_SPECIFIC_INIT();
#if (TRC_CFG_RECORDER_BUFFER_ALLOCATION == TRC_RECORDER_BUFFER_ALLOCATION_STATIC)
	pxTraceRecorderData = &xRecorderData;
#elif (TRC_CFG_RECORDER_BUFFER_ALLOCATION == TRC_RECORDER_BUFFER_ALLOCATION_DYNAMIC)
	/* Initialize heap */
	TRC_KERNEL_PORT_HEAP_INIT(sizeof(TraceRecorderData_t));

	/* Allocate data */
	pxTraceRecorderData = TRC_KERNEL_PORT_HEAP_MALLOC(sizeof(TraceRecorderData_t));
#endif

	/* These are set on init so they aren't overwritten by late initialization values. */
	pxTraceRecorderData->uiSessionCounter = 0u;
	pxTraceRecorderData->uiRecorderEnabled = 0u;
	
	for (i = 0; i < TRC_CFG_CORE_COUNT; i++)
	{
		pxTraceRecorderData->uxTraceSystemStates[i] = (TraceUnsignedBaseType_t)TRC_STATE_IN_STARTUP;
	}
	
	/*cstat !MISRAC2004-13.7_b Suppress always false check*/
	if (xTraceEntryIndexTableInitialize(&pxTraceRecorderData->xEntryIndexTableBuffer) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

#if (TRC_EXTERNAL_BUFFERS == 0)
	if (xTraceHeaderInitialize(&pxTraceRecorderData->xHeaderBuffer) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	if (xTraceEntryTableInitialize(&pxTraceRecorderData->xEntryTable) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	if (xTraceTimestampInitialize(&pxTraceRecorderData->xTimestampBuffer) == TRC_FAIL)
	{
		return TRC_FAIL;
	}
#endif
	
	if (xTraceCounterInitialize(&pxTraceRecorderData->xCounterBuffer) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	/*cstat !MISRAC2004-13.7_b !MISRAC2012-Rule-14.3_b Suppress always false check*/
	if (xTraceStackMonitorInitialize(&pxTraceRecorderData->xStackMonitorBuffer) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	/*cstat !MISRAC2004-13.7_b !MISRAC2012-Rule-14.3_b Suppress always false check*/
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

	/*cstat !MISRAC2004-13.7_b Suppress always false check*/
	if (xTraceExtensionInitialize(&pxTraceRecorderData->xExtensionBuffer) == TRC_FAIL)
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

	if (xTraceISRInitialize(&pxTraceRecorderData->xISRBuffer) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	if (xTraceTaskInitialize(&pxTraceRecorderData->xTaskInfoBuffer) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	/*cstat !MISRAC2004-13.7_b !MISRAC2012-Rule-14.3_b Suppress always false check*/
	if (xTraceKernelPortInitialize(&pxTraceRecorderData->xKernelPortBuffer) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	pxTraceRecorderData->reserved = 0xFFFFFFFFUL;

	(void)xTraceSetComponentInitialized(TRC_RECORDER_COMPONENT_CORE);

	return TRC_SUCCESS;
}

traceResult xTraceHeaderInitialize(TraceHeaderBuffer_t *pxBuffer)
{
	uint32_t i;
	const char* platform_cfg = TRC_PLATFORM_CFG; /*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/

	TRC_ASSERT_EQUAL_SIZE(TraceHeaderBuffer_t, TraceHeader_t);

	if (pxBuffer == (void*)0)
	{
		return TRC_FAIL;
	}

	if (prvVerifySizeAlignment(sizeof(TraceStreamPortBuffer_t)) == TRC_FAIL)
	{
		/* TraceStreamPortBuffer_t size is not aligned to TraceUnsignedBaseType_t */
		return TRC_FAIL;
	}

	if (prvVerifySizeAlignment(sizeof(TraceEventDataTable_t)) == TRC_FAIL)
	{
		/* TraceEventDataTable_t size is not aligned to TraceUnsignedBaseType_t */
		return TRC_FAIL;
	}

	if (prvVerifySizeAlignment(sizeof(TraceKernelPortDataBuffer_t)) == TRC_FAIL)
	{
		/* TraceKernelPortDataBuffer_t size is not aligned to TraceUnsignedBaseType_t */
		return TRC_FAIL;
	}

	pxHeader = (TraceHeader_t*)pxBuffer; /*cstat !MISRAC2004-11.4 !MISRAC2012-Rule-11.3 Suppress conversion between pointer types checks*/

	pxHeader->uiPSF = TRACE_PSF_ENDIANESS_IDENTIFIER;
	pxHeader->uiVersion = TRACE_FORMAT_VERSION;
	pxHeader->uiPlatform = TRACE_KERNEL_VERSION;

	for (i = 0u; i < (uint32_t)(TRC_PLATFORM_CFG_LENGTH); i++)
	{
		pxHeader->platformCfg[i] = platform_cfg[i]; /*cstat !MISRAC2004-17.4_b We need to access every character in the string*/
		if (platform_cfg[i] == (char)0) /*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/ /*cstat !MISRAC2004-17.4_b We need to access every character in the string*/
		{
			break;
		}
	}
	pxHeader->uiPlatformCfgPatch = (uint16_t)TRC_PLATFORM_CFG_PATCH;
	pxHeader->uiPlatformCfgMinor = (uint8_t)TRC_PLATFORM_CFG_MINOR;
	pxHeader->uiPlatformCfgMajor = (uint8_t)TRC_PLATFORM_CFG_MAJOR;
	pxHeader->uiNumCores = (uint32_t)TRC_CFG_CORE_COUNT;
	
#ifdef TRC_STREAM_PORT_MULTISTREAM_SUPPORT
	pxHeader->uiNumCores |= 2 << 8;
#else
	pxHeader->uiNumCores |= 3 << 8;
#endif
	
	pxHeader->isrTailchainingThreshold = TRC_CFG_ISR_TAILCHAINING_THRESHOLD;

	/* Lowest bit used for TRC_IRQ_PRIORITY_ORDER */
	pxHeader->uiOptions = (((uint32_t)(TRC_IRQ_PRIORITY_ORDER)) << 0);

	/* 3rd bit used for TRC_CFG_TEST_MODE */
	pxHeader->uiOptions |= (((uint32_t)(TRC_CFG_TEST_MODE)) << 2);

	/* 4th bit used for 64-bit*/
	if (prvIs64bit()) /* Call helper function to avoid "unreachable code" */
	{
		pxHeader->uiOptions |= (1 << 3);
	}

	return TRC_SUCCESS;
}

traceResult xTraceEnable(uint32_t uiStartOption)
{
	TraceCommand_t xCommand = { 0 };
	int32_t iBytes;

	if (xTraceInitialize() == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	/*cstat !MISRAC2004-13.7_b !MISRAC2012-Rule-14.3_b Suppress always false check*/
	if (xTraceStreamPortOnEnable(uiStartOption) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	/*cstat !MISRAC2004-13.7_b !MISRAC2012-Rule-14.3_b Suppress always false check*/
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
				(void)xTraceWarning(TRC_WARNING_STREAM_PORT_READ);
			}

			if ((uint32_t)iBytes == sizeof(TraceCommand_t))
			{
				if (prvIsValidCommand(&xCommand) != 0)
				{
					prvProcessCommand(&xCommand);
				}
			}
		} while (pxTraceRecorderData->uiRecorderEnabled == 0u);
	}
	else if (uiStartOption == (uint32_t)(TRC_START))
	{
		/* We start streaming directly - this assumes that the host interface is ready! */
		xCommand.cmdCode = CMD_SET_ACTIVE;
		xCommand.param1 = 1u;
		prvProcessCommand(&xCommand);
	}
	else if (uiStartOption == TRC_START_FROM_HOST)
	{
		/* We prepare the system to receive commands from host, but let system resume execution until that happens */
	}
	else
	{
		return TRC_FAIL;
	}

	return TRC_SUCCESS;
}

traceResult xTraceDisable(void)
{
	prvSetRecorderDisabled();

	(void)xTraceStreamPortOnDisable();
	
	return TRC_SUCCESS;
}

#if (TRC_CFG_RECORDER_BUFFER_ALLOCATION == TRC_RECORDER_BUFFER_ALLOCATION_CUSTOM)
traceResult xTraceSetBuffer(TraceRecorderData_t* pxBuffer)
{
	if (pxBuffer == 0)
	{
		return TRC_FAIL;
	}
	
	pxTraceRecorderData = pxBuffer;

	return TRC_SUCCESS;
}
#endif

traceResult xTraceGetEventBuffer(void **ppvBuffer, TraceUnsignedBaseType_t *puiSize)
{
	if ((pxTraceRecorderData == (void*)0) || (ppvBuffer == (void*)0) || (puiSize == (void*)0))
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
	TraceCommand_t xCommand = { 0 };
	int32_t iRxBytes;
	
	do
	{
		/* Listen for new commands */
		iRxBytes = 0;
		if (xTraceStreamPortReadData(&xCommand, sizeof(TraceCommand_t), &iRxBytes) == TRC_FAIL)
		{
			/* The connection has failed, stop tracing */
			(void)xTraceDisable();

			return TRC_FAIL;
		}

		if ((uint32_t)iRxBytes == sizeof(TraceCommand_t))
		{
			if (prvIsValidCommand(&xCommand) != 0)
			{
				prvProcessCommand(&xCommand); /* Start or Stop currently... */
			}
		}

		if (xTraceIsRecorderEnabled())
		{
			(void)xTraceInternalEventBufferTransfer();
		}

		/* If there was data sent or received (bytes != 0), loop around and repeat, if there is more data to send or receive.
		Otherwise, step out of this loop and sleep for a while. */

	} while (iRxBytes > 0);

	if (xTraceIsRecorderEnabled())
	{
		(void)xTraceDiagnosticsCheckStatus();
		(void)xTraceStackMonitorReport();
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

static TraceUnsignedBaseType_t prvIs64bit(void)
{
	return sizeof(TraceUnsignedBaseType_t) == 8;
}

/* Internal function for starting/stopping the recorder. */
static void prvSetRecorderEnabled(void)
{
	TraceUnsignedBaseType_t uxTimestampFrequency = 0u;
	uint32_t uiTimestampPeriod = 0u;
	
	TRACE_ALLOC_CRITICAL_SECTION();
	
	if (pxTraceRecorderData->uiRecorderEnabled == 1u)
	{
		return;
	}

	(void)xTraceTimestampGetFrequency(&uxTimestampFrequency);
	/* If not overridden using xTraceTimestampSetFrequency(...), use default value */
	if (uxTimestampFrequency == 0u)
	{
		(void)xTraceTimestampSetFrequency((TraceUnsignedBaseType_t)(TRC_HWTC_FREQ_HZ));
	}

	(void)xTraceTimestampGetPeriod(&uiTimestampPeriod);
	/* If not overridden using xTraceTimestampSetPeriod(...), use default value */
	if (uiTimestampPeriod == 0u)
	{
		(void)xTraceTimestampSetPeriod((TraceUnsignedBaseType_t)(TRC_HWTC_PERIOD));
	}

	TRACE_ENTER_CRITICAL_SECTION();

	/* If the internal event buffer is used, we must clear it */
	(void)xTraceInternalEventBufferClear();
	
	(void)xTraceStreamPortOnTraceBegin();

	prvTraceStoreHeader();
	prvTraceStoreTimestampInfo();
	prvTraceStoreEntryTable();
	prvTraceStoreStartEvent();

	pxTraceRecorderData->uiSessionCounter++;

	pxTraceRecorderData->uiRecorderEnabled = 1u;

	TRACE_EXIT_CRITICAL_SECTION();
}

static void prvSetRecorderDisabled(void)
{
	TRACE_ALLOC_CRITICAL_SECTION();

	if (pxTraceRecorderData->uiRecorderEnabled == 0u)
	{
		return;
	}

	TRACE_ENTER_CRITICAL_SECTION();
	
	pxTraceRecorderData->uiRecorderEnabled = 0u;

	(void)xTraceStreamPortOnTraceEnd();

	TRACE_EXIT_CRITICAL_SECTION();
}

#if (TRC_EXTERNAL_BUFFERS == 0)
/* Stores the header information on Start */
static void prvTraceStoreHeader(void)
{
	xTraceEventCreateRawBlocking((TraceUnsignedBaseType_t*)pxHeader, sizeof(TraceHeader_t));
}

/* Store the Timestamp */
static void prvTraceStoreTimestampInfo(void)
{
	xTraceEventCreateRawBlocking((TraceUnsignedBaseType_t*)&pxTraceRecorderData->xTimestampBuffer,sizeof(TraceTimestampData_t));
}

/* Stores the entry table on Start */
static void prvTraceStoreEntryTable(void)
{
	uint32_t i = 0;
	TraceEntryHandle_t xEntryHandle;
	uint32_t uiEntryCount;
	TraceUnsignedBaseType_t xHeaderData[3];
	void *pvEntryAddress;

	(void)xTraceEntryGetCount(&uiEntryCount);

	xHeaderData[0] = (TraceUnsignedBaseType_t)uiEntryCount;
	xHeaderData[1] = TRC_ENTRY_TABLE_SLOT_SYMBOL_SIZE;
	xHeaderData[2] = TRC_ENTRY_TABLE_STATE_COUNT;

	xTraceEventCreateRawBlocking(xHeaderData, sizeof(xHeaderData));

	for (i = 0; i < (TRC_ENTRY_TABLE_SLOTS); i++)
	{
		(void)xTraceEntryGetAtIndex(i, &xEntryHandle);
		(void)xTraceEntryGetAddress(xEntryHandle, &pvEntryAddress);

		/* We only send used entry slots */
		if (pvEntryAddress != 0)
		{
			xTraceEventCreateRawBlocking((TraceUnsignedBaseType_t *) xEntryHandle, sizeof(TraceEntry_t));
		}
	}

}
#endif /* (TRC_EXTERNAL_BUFFERS == 0) */

static void prvTraceStoreStartEvent(void)
{
	void* pvCurrentTask = (void*)0;
	uint32_t i;

	TraceUnsignedBaseType_t xTraceTasks[TRC_CFG_CORE_COUNT];
	for (i = 0; i < (TRC_CFG_CORE_COUNT); i++)
	{
		(void)xTraceTaskGetCurrentOnCore(i, &pvCurrentTask);
		xTraceTasks[i] = (TraceUnsignedBaseType_t)pvCurrentTask;
	}

	(void)xTraceEventCreateDataOffline0(PSF_EVENT_TRACE_START, xTraceTasks, sizeof(xTraceTasks));
}

/* Checks if the provided command is a valid command */
static int32_t prvIsValidCommand(const TraceCommand_t* const cmd)
{
  	uint16_t checksum = (uint16_t)0xFFFFU - (uint16_t)(unsigned char)(cmd->cmdCode + /*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/
												cmd->param1 +
												cmd->param2 +
												cmd->param3 +
												cmd->param4 +
												cmd->param5);

	if (cmd->checksumMSB != (unsigned char)(checksum >> 8)) /*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/
	{
		return 0;
	}

	if (cmd->checksumLSB != (unsigned char)(checksum & 0xFFU)) /*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/
	{
		return 0;
	}

	if (cmd->cmdCode > (unsigned char)(CMD_LAST_COMMAND)) /*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/
	{
		return 0;
	}

	return 1;
}

/* Executed the received command (Start or Stop) */
static void prvProcessCommand(const TraceCommand_t* const cmd)
{
  	switch(cmd->cmdCode)
	{
		case CMD_SET_ACTIVE:
			if (cmd->param1 == 1u)
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

/* Do this in function to avoid unreachable code warnings */
static traceResult prvVerifySizeAlignment(uint32_t ulSize)
{
	return (ulSize % sizeof(TraceUnsignedBaseType_t)) == 0 ? TRC_SUCCESS : TRC_FAIL;
}

#endif
