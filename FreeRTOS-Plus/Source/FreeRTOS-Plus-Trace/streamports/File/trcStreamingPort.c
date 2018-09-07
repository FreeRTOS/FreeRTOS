/*******************************************************************************
 * Trace Recorder Library for Tracealyzer v4.1.5
 * Percepio AB, www.percepio.com
 *
 * trcStreamingPort.c
 *
 * Supporting functions for trace streaming, used by the "stream ports" 
 * for reading and writing data to the interface.
 * Existing ports can easily be modified to fit another setup, e.g., a 
 * different TCP/IP stack, or to define your own stream port.
 *
  * Terms of Use
 * This file is part of the trace recorder library (RECORDER), which is the 
 * intellectual property of Percepio AB (PERCEPIO) and provided under a
 * license as follows.
 * The RECORDER may be used free of charge for the purpose of recording data
 * intended for analysis in PERCEPIO products. It may not be used or modified
 * for other purposes without explicit permission from PERCEPIO.
 * You may distribute the RECORDER in its original source code form, assuming
 * this text (terms of use, disclaimer, copyright notice) is unchanged. You are
 * allowed to distribute the RECORDER with minor modifications intended for
 * configuration or porting of the RECORDER, e.g., to allow using it on a 
 * specific processor, processor family or with a specific communication
 * interface. Any such modifications should be documented directly below
 * this comment block.  
 *
 * Disclaimer
 * The RECORDER is being delivered to you AS IS and PERCEPIO makes no warranty
 * as to its use or performance. PERCEPIO does not and cannot warrant the 
 * performance or results you may obtain by using the RECORDER or documentation.
 * PERCEPIO make no warranties, express or implied, as to noninfringement of
 * third party rights, merchantability, or fitness for any particular purpose.
 * In no event will PERCEPIO, its technology partners, or distributors be liable
 * to you for any consequential, incidental or special damages, including any
 * lost profits or lost savings, even if a representative of PERCEPIO has been
 * advised of the possibility of such damages, or for any claim by any third
 * party. Some jurisdictions do not allow the exclusion or limitation of
 * incidental, consequential or special damages, or the exclusion of implied
 * warranties or limitations on how long an implied warranty may last, so the
 * above limitations may not apply to you.
 *
 * Tabs are used for indent in this file (1 tab = 4 spaces)
 *
 * Copyright Percepio AB, 2018.
 * www.percepio.com
 ******************************************************************************/

#include "trcRecorder.h"

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)  
#if (TRC_USE_TRACEALYZER_RECORDER == 1)

FILE* traceFile = NULL;

void openFile(char* fileName)
{
	if (traceFile == NULL)
	{
		errno_t err = fopen_s(&traceFile, fileName, "wb");
		if (err != 0)
		{
			printf("Could not open trace file, error code %d.\n", err);
			exit(-1);
		}
		else {
			printf("Trace file created.\n");
		}
	}
}

int32_t writeToFile(void* data, uint32_t size, int32_t *ptrBytesWritten)
{
	int32_t written = 0;
	if (traceFile != NULL)
	{
		written = fwrite(data, 1, size, traceFile);
	}
	else
	{
		written = 0;
	}

	if (ptrBytesWritten != 0)
		*ptrBytesWritten = written;

	if ((int32_t)size == written)
		return 0;
	else
		return -1;
}

void closeFile(void)
{
	if (traceFile != NULL)
	{
		fclose(traceFile);
		traceFile = NULL;
		printf("Trace file closed.\n");
	}
}

#endif /*(TRC_USE_TRACEALYZER_RECORDER == 1)*/
#endif /*(TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)*/
