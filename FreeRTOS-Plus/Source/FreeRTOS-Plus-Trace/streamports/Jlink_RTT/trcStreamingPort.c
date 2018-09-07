
#include "trcRecorder.h"

#if (TRC_USE_TRACEALYZER_RECORDER == 1)
#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

int32_t readFromRTT(void* ptrData, uint32_t size, int32_t* ptrBytesRead)
{
	uint32_t bytesRead = 0; 
	
	if (SEGGER_RTT_HASDATA(TRC_CFG_RTT_DOWN_BUFFER_INDEX))
	{
		bytesRead = SEGGER_RTT_Read((TRC_CFG_RTT_DOWN_BUFFER_INDEX), (char*)ptrData, size);
	
		if (ptrBytesRead != NULL)
			*ptrBytesRead = (int32_t)bytesRead;
	
		if (bytesRead != size)
		{
			return -1;
		}

	}

	return 0;
}

int32_t writeToRTT(void* ptrData, uint32_t size, int32_t* ptrBytesWritten)
{
	uint32_t bytesWritten = SEGGER_RTT_Write((TRC_CFG_RTT_UP_BUFFER_INDEX), (const char*)ptrData, size);
	
	if (ptrBytesWritten != NULL)
		*ptrBytesWritten = (int32_t)bytesWritten;

	if (bytesWritten != size)
	{
		return -1;
	}

	return 0;
}

#endif
#endif
