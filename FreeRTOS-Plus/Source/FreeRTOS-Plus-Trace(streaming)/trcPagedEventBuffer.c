/*******************************************************************************
 * Trace Recorder Library for Tracealyzer v3.0.2
 * Percepio AB, www.percepio.com
 *
 * trcPagedEventBuffer.c
 *
 * Implements a paged buffer that can be used by TCP/IP or custom transfer
 * methods.
 *
 * Terms of Use
 * This software (the "Tracealyzer Recorder Library") is the intellectual
 * property of Percepio AB and may not be sold or in other ways commercially
 * redistributed without explicit written permission by Percepio AB.
 *
 * Separate conditions applies for the SEGGER branded source code included.
 *
 * The recorder library is free for use together with Percepio products.
 * You may distribute the recorder library in its original form, but public
 * distribution of modified versions require approval by Percepio AB.
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
 * Tabs are used for indent in this file (1 tab = 4 spaces)
 *
 * Copyright Percepio AB, 2015.
 * www.percepio.com
 ******************************************************************************/

#include <stdio.h>
#include <stdint.h>
#include <string.h>

#include "trcConfig.h"
#include "trcPagedEventBuffer.h"
#include "trcPagedEventBufferConfig.h"
#include "trcKernelPort.h"

uint32_t DroppedEventCounter = 0;	// Total number of dropped events (failed allocations)
uint32_t TotalBytesRemaining_LowWaterMark = TRC_PAGED_EVENT_BUFFER_PAGE_COUNT * TRC_PAGED_EVENT_BUFFER_PAGE_SIZE;

#if (USE_TRACEALYZER_RECORDER == 1)

#define PAGE_STATUS_FREE 0
#define PAGE_STATUS_WRITE 1
#define PAGE_STATUS_READ 2

uint32_t TotalBytesRemaining = TRC_PAGED_EVENT_BUFFER_PAGE_COUNT * TRC_PAGED_EVENT_BUFFER_PAGE_SIZE;

typedef struct{
	uint8_t Status;
	uint16_t BytesRemaining;
	char* WritePointer;
} PageType;

PageType PageInfo[TRC_PAGED_EVENT_BUFFER_PAGE_COUNT];

char* EventBuffer = NULL;

static void prvPageReadComplete(int pageIndex);
static int prvAllocateBufferPage(int prevPage);

static int prvAllocateBufferPage(int prevPage)
{
	int index;
	int count = 0;

	index = (prevPage + 1) % TRC_PAGED_EVENT_BUFFER_PAGE_COUNT;

	while((PageInfo[index].Status != PAGE_STATUS_FREE) && (count ++ < TRC_PAGED_EVENT_BUFFER_PAGE_COUNT))
	{
		index = (index + 1) % TRC_PAGED_EVENT_BUFFER_PAGE_COUNT;
	}

	if (PageInfo[index].Status == PAGE_STATUS_FREE)
	{
		return index;
	}

	return -1;
}

static void prvPageReadComplete(int pageIndex)
{
  	TRACE_ALLOC_CRITICAL_SECTION();

	TRACE_ENTER_CRITICAL_SECTION();
	PageInfo[pageIndex].BytesRemaining = TRC_PAGED_EVENT_BUFFER_PAGE_SIZE;
	PageInfo[pageIndex].WritePointer = &EventBuffer[pageIndex * TRC_PAGED_EVENT_BUFFER_PAGE_SIZE];
	PageInfo[pageIndex].Status = PAGE_STATUS_FREE;

	TotalBytesRemaining += TRC_PAGED_EVENT_BUFFER_PAGE_SIZE;

	TRACE_EXIT_CRITICAL_SECTION();
}

static int prvGetBufferPage(int32_t* bytesUsed)
{
	static int8_t lastPage = -1;
	int count = 0;
  	int8_t index = (lastPage + 1) % TRC_PAGED_EVENT_BUFFER_PAGE_COUNT;

	while((PageInfo[index].Status != PAGE_STATUS_READ) && (count++ < TRC_PAGED_EVENT_BUFFER_PAGE_COUNT))
	{
		index = (index + 1) % TRC_PAGED_EVENT_BUFFER_PAGE_COUNT;
	}

	if (PageInfo[index].Status == PAGE_STATUS_READ)
	{
		*bytesUsed = TRC_PAGED_EVENT_BUFFER_PAGE_SIZE - PageInfo[index].BytesRemaining;
		lastPage = index;
		return index;
	}

	*bytesUsed = 0;

	return -1;
}

/*******************************************************************************

int32_t vPagedEventBufferTransfer(int32_t (*writeFunc)(void* data,
                                                        uint32_t size),
                                            int32_t* nofBytes)

Transfers one block of trace data, if available for reading. Returns the number
of bytes transfered, or a negative error code. If data was transferred (return
value > 0), it can be good to call this function again until all data available
has been transfered.

This function is intended to be called by a periodic task with a suitable
delay (e.g. 10-100 ms).

Example:

	TickType_t lastWakeTime = xTaskGetTickCount();

	while(1)
	{

		do{
			// Transfer all available data
			status = vPagedEventBufferTransfer(MyWrite, ptrBytes);
		}while(status > 0);

		if (status < 0)
		{
			// A negative return value is an error code...
		}

		vTraceDelayUntil(lastWakeTime, 50); // 50 ms -> 20 times/sec
	}

Return value: returnvalue of writeFunc (0 == OK)

Parameters:

- writeFunc
Function pointer (example: int32_t write(void* data, uint32_t size))
The function passed as writeFunc should write "size" bytes from "data" to the
socket/file/channel, and return a status code where 0 means OK,
and any other non-zero value means an error.

- int32_t* nofBytes
Pointer to an integer assigned the number of bytes that was transfered.

*******************************************************************************/

int32_t vPagedEventBufferTransfer(int32_t (*writeFunc)(void* data, uint32_t size, int32_t* ptrBytesWritten), int32_t* nofBytes)
{
	static int firstTime = 1;
	int8_t pageToTransfer = -1;

	pageToTransfer = prvGetBufferPage(nofBytes);

	if (firstTime)
	{
		firstTime = 0;
	}

	if (pageToTransfer > -1)
	{
		if (writeFunc(&EventBuffer[pageToTransfer * TRC_PAGED_EVENT_BUFFER_PAGE_SIZE], *nofBytes, nofBytes) == 0)
		{
			prvPageReadComplete(pageToTransfer);
            
            return 0;
		}
        else
        {
            return 1;
        }
	}
	return 0;
}

/*******************************************************************************

void* vPagedEventBufferGetWritePointer(int sizeOfEvent)

Returns a pointer to an available location in the buffer able to store the
requested size.

Return value: The pointer.

Parameters:

- sizeOfEvent
The size of the event that is to be placed in the buffer.

*******************************************************************************/
void* vPagedEventBufferGetWritePointer(int sizeOfEvent)
{
	void* ret;
	static int currentWritePage = -1;

	if (currentWritePage == -1)
	{
	    currentWritePage = prvAllocateBufferPage(currentWritePage);
		if (currentWritePage == -1)
		{
		  	DroppedEventCounter++;
			return NULL;
		}
	}

    if (PageInfo[currentWritePage].BytesRemaining - sizeOfEvent < 0)
	{
		PageInfo[currentWritePage].Status = PAGE_STATUS_READ;

		TotalBytesRemaining -= PageInfo[currentWritePage].BytesRemaining; // Last trailing bytes

		if (TotalBytesRemaining < TotalBytesRemaining_LowWaterMark)
		  TotalBytesRemaining_LowWaterMark = TotalBytesRemaining;

		currentWritePage = prvAllocateBufferPage(currentWritePage);
		if (currentWritePage == -1)
		{
		  DroppedEventCounter++;
		  return NULL;
		}
	}
	ret = PageInfo[currentWritePage].WritePointer;
	PageInfo[currentWritePage].WritePointer += sizeOfEvent;
	PageInfo[currentWritePage].BytesRemaining -= sizeOfEvent;

	TotalBytesRemaining -= sizeOfEvent;

	if (TotalBytesRemaining < TotalBytesRemaining_LowWaterMark)
		TotalBytesRemaining_LowWaterMark = TotalBytesRemaining;

	return ret;
}

/*******************************************************************************

void vPagedEventBufferInit(char* buffer)

Assigns the buffer to use and initializes the PageInfo structure.

Return value: void

Parameters:

- buffer
Pointer to the buffer location that is dynamically or statically allocated by
the caller.

*******************************************************************************/
void vPagedEventBufferInit(char* buffer)
{
  	TRACE_ALLOC_CRITICAL_SECTION();
  	int i;
    
    EventBuffer = buffer;
    
	TRACE_ENTER_CRITICAL_SECTION();
	for (i = 0; i < TRC_PAGED_EVENT_BUFFER_PAGE_COUNT; i++)
	{
		PageInfo[i].BytesRemaining = TRC_PAGED_EVENT_BUFFER_PAGE_SIZE;
		PageInfo[i].WritePointer = &EventBuffer[i * TRC_PAGED_EVENT_BUFFER_PAGE_SIZE];
		PageInfo[i].Status = PAGE_STATUS_FREE;
	}
	TRACE_EXIT_CRITICAL_SECTION();
}

#endif



