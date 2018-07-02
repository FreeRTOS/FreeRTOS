
#include "trcRecorder.h"

#if (TRC_USE_TRACEALYZER_RECORDER == 1)
#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

static void itm_write_32(uint32_t data);

volatile int32_t tz_host_command_bytes_to_read = 0; // This is set by the Tracealyzer host application (to the number of bytes written), after having written to tz_host_commands. Set to zero by the read function after the message in tz_host_commands has been read.
volatile char tz_host_command_data[32];

/* This reads "command" data from a RAM buffer, written by a host macro in the debugger */
int32_t read_from_host(void* ptrData, uint32_t size, int32_t* ptrBytesRead)
{
	if ( tz_host_command_bytes_to_read > 0)
	{		
		int i;
		uint8_t * bytesBuffer = (uint8_t*) ptrData;

		if (ptrBytesRead != NULL)
			*ptrBytesRead = (int32_t)tz_host_command_bytes_to_read;
	
		if (tz_host_command_bytes_to_read != size)
		{
			return -1;
		}
			
		for (i=0; i < tz_host_command_bytes_to_read; i++)
		{
			bytesBuffer[i] = tz_host_command_data[i];
		}
		
		tz_host_command_bytes_to_read = 0;
	}

	return 0;
}

static void itm_write_32(uint32_t data)
{	
     if   ((CoreDebug->DEMCR & CoreDebug_DEMCR_TRCENA_Msk)  &&      // Trace enabled
           (ITM->TCR & ITM_TCR_ITMENA_Msk)                  &&      // ITM enabled
           (ITM->TER & (1UL << 0)))                                  // ITM Port #0 enabled
    {
        while (ITM->PORT[TRC_CFG_ITM_PORT].u32 == 0);     // Block until room in ITM FIFO - This stream port is always in "blocking mode", since intended for high-speed ITM!
        ITM->PORT[TRC_CFG_ITM_PORT].u32 = data;           // Write the data
	}	
}

/* This is assumed to execute from within the recorder, with interrupts disabled */
int32_t itm_write(void* ptrData, uint32_t size, int32_t* ptrBytesWritten)
{
	uint32_t bytesWritten = 0;
	uint32_t* ptr32 = (uint32_t*)ptrData;
	
	if (size % 4 != 0) return -2;
		
	while(bytesWritten < size)
	{
		itm_write_32(*ptr32);
		ptr32++;
		bytesWritten += 4;
	}

	*ptrBytesWritten = bytesWritten;
	
	return 0;
}

#endif
#endif
