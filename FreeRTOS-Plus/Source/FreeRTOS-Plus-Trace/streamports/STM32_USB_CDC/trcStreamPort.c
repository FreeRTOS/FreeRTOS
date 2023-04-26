/*
 * Trace Recorder for Tracealyzer v4.6.0
 * Copyright 2021 Percepio AB
 * www.percepio.com
 *
 * SPDX-License-Identifier: Apache-2.0
 *
 * Supporting functions for trace streaming ("stream ports").
 * This "stream port" sets up the recorder to use USB CDC as streaming channel.
 * The example is for STM32 using STM32Cube.
 */

#include <trcRecorder.h>

#include <usb_device.h>
#include <usbd_CDC_if.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1)
#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

static void prvCDCInit(void);

static int8_t CDC_Receive_FS_modified(uint8_t* pbuf, uint32_t *puiLength);

extern USBD_CDC_ItfTypeDef USBD_Interface_fops_FS;

static int8_t(*CDC_Receive_FS)(uint8_t* Buf, uint32_t* Len);

typedef struct TraceStreamPortUSBCommandBuffer {
	TraceUnsignedBaseType_t idx;
	uint8_t bufferUSB[TRC_STREAM_PORT_USB_BUFFER_SIZE];
	uint8_t bufferInternal[TRC_STREAM_PORT_INTERNAL_BUFFER_SIZE];
} TraceStreamPortUSBBuffers_t;

TraceStreamPortUSBBuffers_t* pxUSBBuffers;

static int8_t CDC_Receive_FS_modified(uint8_t* pBuffer, uint32_t *puiLength)
{
	for(uint32_t i = 0; i < *puiLength; i++)
	{
		pxUSBBuffers->bufferUSB[pxUSBBuffers->idx] = pBuffer[i];
		pxUSBBuffers->idx++;
	}

	CDC_Receive_FS(pBuffer, puiLength);

	return (USBD_OK);
}

static void prvCDCInit(void)
{
	/* Store the original "Receive" function, from the static initialization */
	CDC_Receive_FS = USBD_Interface_fops_FS.Receive;

	/* Update the function pointer with our modified variant */
	USBD_Interface_fops_FS.Receive = CDC_Receive_FS_modified;

	pxUSBBuffers->idx = 0;

	MX_USB_DEVICE_Init();
}

/* The READ function, used in trcStreamPort.h */
traceResult prvTraceCDCReceive(void *data, uint32_t uiSize, int32_t* piBytesReceived)
{
	uint32_t i, uiDiff;

	if(pxUSBBuffers->idx > 0)
	{
		if ((TraceUnsignedBaseType_t)uiSize >= pxUSBBuffers->idx) // More than what is stored, number of bytes will be .idx
		{
			TRC_MEMCPY(data, pxUSBBuffers->bufferUSB, pxUSBBuffers->idx);
			*piBytesReceived = (int32_t)pxUSBBuffers->idx;
			pxUSBBuffers->idx = 0; // Make the buffer ready for a new command
		}
		else  // If some data in the buffer is not read
		{
			uiDiff = pxUSBBuffers->idx - uiSize;
			TRC_MEMCPY(data, pxUSBBuffers->bufferUSB, uiSize);

			for(i = 0; i < uiDiff; i++)
			{
				pxUSBBuffers->bufferUSB[i] = pxUSBBuffers->bufferUSB[i + uiSize];
			}
			
			*piBytesReceived = uiSize;
			
			pxUSBBuffers->idx = uiDiff;
		}
	}
	else
	{
		*piBytesReceived = 0;
	}
	
	return TRC_SUCCESS;
}

/* The WRITE function, used in trcStreamPort.h */
traceResult prvTraceCDCTransmit(void* pvData, uint32_t uiSize, int32_t * piBytesSent )
{
	static int fail_counter = 0;

	int32_t result;

	*piBytesSent = 0;

	result = CDC_Transmit_FS(pvData, uiSize);
	
	if (result == USBD_OK)
	{
		fail_counter = 0;
		*piBytesSent = uiSize;
		return TRC_SUCCESS;
	}
	else
	{
		fail_counter++;

		/* We keep trying to send more pvData. If busy, we delay for a while. This function will be called again afterwards. */
		xTraceKernelPortDelay(TRC_CFG_STREAM_PORT_DELAY_ON_BUSY);

		if (fail_counter >= 100)
		{
			/* If many unsuccessful attempts in a row, something is very wrong. Returning -1 will stop the recorder. */
			return TRC_FAIL;
		}
	}

	return TRC_SUCCESS;
}

traceResult xTraceStreamPortInitialize(TraceStreamPortBuffer_t* pxBuffer)
{
	TRC_ASSERT_EQUAL_SIZE(TraceStreamPortBuffer_t, TraceStreamPortUSBBuffers_t);

	if (pxBuffer == 0)
	{
		return TRC_FAIL;
	}

	pxUSBBuffers = (TraceStreamPortUSBBuffers_t*)pxBuffer;

	prvCDCInit();

	return xTraceInternalEventBufferInitialize(pxUSBBuffers->bufferInternal, sizeof(pxUSBBuffers->bufferInternal));
}

#endif	/*(TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)*/
#endif  /*(TRC_USE_TRACEALYZER_RECORDER == 1)*/

