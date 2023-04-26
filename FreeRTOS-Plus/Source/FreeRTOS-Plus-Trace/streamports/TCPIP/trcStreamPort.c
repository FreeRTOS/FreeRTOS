/*
 * Trace Recorder for Tracealyzer v4.6.0
 * Copyright 2021 Percepio AB
 * www.percepio.com
 *
 * SPDX-License-Identifier: Apache-2.0
 *
 * Supporting functions for trace streaming, used by the "stream ports" 
 * for reading and writing data to the interface.
 * Existing ports can easily be modified to fit another setup, e.g., a 
 * different TCP/IP stack, or to define your own stream port.
 */

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)  
	
/* TCP/IP includes - for lwIP in this case */
#include <lwip/tcpip.h>
#include <lwip/sockets.h>
#include <lwip/errno.h>

int sock = -1, new_sd = -1;
int flags = 0;
int remoteSize;
struct sockaddr_in address, remote;

typedef struct TraceStreamPortTCPIP
{
#if (TRC_USE_INTERNAL_BUFFER)
	uint8_t buffer[(TRC_STREAM_PORT_BUFFER_SIZE)];
#else
	TraceUnsignedBaseType_t buffer[1];
#endif
} TraceStreamPortTCPIP_t;

static TraceStreamPortTCPIP_t* pxStreamPortFile;

static int32_t prvSocketSend(void* pvData, uint32_t uiSize, int32_t* piBytesWritten);
static int32_t prvSocketReceive(void* pvData, uint32_t uiSize, int32_t* bytesRead);
static int32_t prvSocketInitializeListener();
static int32_t prvSocketAccept();
static void prvCloseAllSockets();

static int32_t prvSocketSend( void* pvData, uint32_t uiSize, int32_t* piBytesWritten )
{
  if (new_sd < 0)
    return -1;
  
  if (piBytesWritten == 0)
	return -1;
  
  *piBytesWritten = send( new_sd, pvData, uiSize, 0 );
  if (*piBytesWritten < 0)
  {
    /* EWOULDBLOCK may be expected when buffers are full */
    if ((errno != 0) && (errno != EWOULDBLOCK))
	{
		closesocket(new_sd);
		new_sd = -1;
		return -1;
	}
    else
        *piBytesWritten = 0;
  }
  
  return 0;
}

static int32_t prvSocketReceive( void* pvData, uint32_t uiSize, int32_t* bytesRead )
{
  if (new_sd < 0)
    return -1;

  *bytesRead = recv( new_sd, pvData, uiSize, 0 );
  /* EWOULDBLOCK may be expected when there is no pvData to receive */
  if (errno != 0 && errno != EWOULDBLOCK)
  {
    closesocket(new_sd);
    new_sd = -1;
    return -1;
  }

  return 0;
}

static int32_t prvSocketInitializeListener()
{
  if (sock >= 0)
	return 0;
  
  sock = lwip_socket(AF_INET, SOCK_STREAM, 0);
  
  if (sock < 0)
    return -1;

  address.sin_family = AF_INET;
  address.sin_port = htons(TRC_CFG_STREAM_PORT_TCPIP_PORT);
  address.sin_addr.s_addr = INADDR_ANY;

  if (bind(sock, (struct sockaddr *)&address, sizeof (address)) < 0)
  {
    closesocket(sock);
    sock = -1;
    return -1;
  }

  if (lwip_listen(sock, 5) < 0)
  {
    closesocket(sock);
    sock = -1;
    return -1;
  }

  return 0;
}

static int32_t prvSocketAccept()
{
  if (sock < 0)
      return -1;
  
  if (new_sd >= 0)
      return 0;
  
  remoteSize = sizeof( remote );
  new_sd = accept( sock, (struct sockaddr *)&remote, (socklen_t*)&remoteSize );

  if( new_sd < 0 )
  {
   	closesocket(new_sd);
    new_sd = -1;
   	closesocket(sock);
    sock = -1;
    return -1;
  }

  flags = fcntl( new_sd, F_GETFL, 0 );
  fcntl( new_sd, F_SETFL, flags | O_NONBLOCK );

  return 0;
}

static void prvCloseAllSockets()
{
	if (new_sd > 0)
	{
		closesocket(new_sd);
	}
	
	if (sock > 0)
	{
		closesocket(sock);
	}
}
/************** MODIFY THE ABOVE PART TO USE YOUR TPC/IP STACK ****************/

int32_t prvTraceTcpWrite(void* pvData, uint32_t uiSize, int32_t *piBytesWritten)
{
	prvSocketInitializeListener();

	prvSocketAccept();
	
    return prvSocketSend(pvData, uiSize, piBytesWritten);
}

int32_t prvTraceTcpRead(void* pvData, uint32_t uiSize, int32_t *piBytesRead)
{
    prvSocketInitializeListener();
        
    prvSocketAccept();
      
    return prvSocketReceive(pvData, uiSize, piBytesRead);
}

traceResult xTraceStreamPortInitialize(TraceStreamPortBuffer_t* pxBuffer)
{
	TRC_ASSERT_EQUAL_SIZE(TraceStreamPortBuffer_t, TraceStreamPortTCPIP_t);

	if (pxBuffer == 0)
	{
		return TRC_FAIL;
	}

	pxStreamPortFile = (TraceStreamPortTCPIP_t*)pxBuffer;

#if (TRC_USE_INTERNAL_BUFFER == 1)
	return xTraceInternalEventBufferInitialize(pxStreamPortFile->buffer, sizeof(pxStreamPortFile->buffer));
#else
	return TRC_SUCCESS;
#endif
}

traceResult xTraceStreamPortOnTraceEnd(void)
{
	prvCloseAllSockets();

	return TRC_SUCCESS;
}

#endif /*(TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)*/

#endif /*(TRC_USE_TRACEALYZER_RECORDER == 1)*/
