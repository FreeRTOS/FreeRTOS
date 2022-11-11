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

#include<stdio.h>
#include<winsock2.h>

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#pragma comment(lib,"ws2_32.lib") //Winsock Library

typedef struct TraceStreamPortTCPIP
{
#if (TRC_USE_INTERNAL_BUFFER)
	uint8_t buffer[(TRC_STREAM_PORT_BUFFER_SIZE)];
#else
	TraceUnsignedBaseType_t buffer[1];
#endif
} TraceStreamPortTCPIP_t;

static TraceStreamPortTCPIP_t* pxStreamPortFile;
static SOCKET server_socket = (UINT_PTR)0, trace_socket = (UINT_PTR)0;
struct sockaddr_in server, client;

static int prvInitServerSocketIfNeeded(void);
static int prvInitWinsockIfNeeded(void);
static int prvInitTraceSocketIfNeeded(void);
static void prvCloseAllSockets(void);

static int prvInitWinsockIfNeeded(void)
{
	WSADATA wsa;
	
	if (server_socket)
		return 0;

	if (WSAStartup(MAKEWORD(2, 2), &wsa) != 0)
	{
		return -1;
	}

	return 0;
}

static int prvInitServerSocketIfNeeded(void)
{
	if (prvInitWinsockIfNeeded() < 0)
	{
		return -1;
	}

	if (server_socket)
		return 0;

	if ((server_socket = socket(AF_INET, SOCK_STREAM, 0)) == INVALID_SOCKET)
	{
		return -1;
	}

	server.sin_family = AF_INET;
	server.sin_addr.s_addr = INADDR_ANY;
	server.sin_port = htons(TRC_CFG_STREAM_PORT_TCPIP_PORT);

	if (bind(server_socket, (struct sockaddr *)&server, sizeof(server)) == SOCKET_ERROR)
	{
		closesocket(server_socket);
		WSACleanup();
		server_socket = (UINT_PTR)0;
		return -1;
	}

	if (listen(server_socket, 3) < 0)
	{
		closesocket(server_socket);
		WSACleanup();
		server_socket = (UINT_PTR)0;
		return -1;
	}

	return 0;
}

static int prvInitTraceSocketIfNeeded(void)
{
	int c;

	if (!server_socket)
		return -1;

	if (trace_socket)
		return 0;

	c = sizeof(struct sockaddr_in);
	trace_socket = accept(server_socket, (struct sockaddr *)&client, &c);
	if (trace_socket == INVALID_SOCKET)
	{
		trace_socket = (UINT_PTR)0;
		
		closesocket(server_socket);
		WSACleanup();
		server_socket = (UINT_PTR)0;
		
		return -1;
	}

	return 0;
}

int32_t prvTraceWriteToSocket(void* data, uint32_t size, int32_t *ptrBytesWritten)
{
	int ret;

	if (prvInitServerSocketIfNeeded() < 0)
	{
		return -1;
	}

	if (prvInitTraceSocketIfNeeded() < 0)
	{
		return -1;
	}

	if (!trace_socket)
	{
		if (ptrBytesWritten != 0)
		{
			*ptrBytesWritten = 0;
		}
		return -1;
	}
	ret = send(trace_socket, data, size, 0);
	if (ret <= 0)
	{
		if (ptrBytesWritten != 0)
		{
			*ptrBytesWritten = 0;
		}

		closesocket(trace_socket);
		trace_socket = (UINT_PTR)0;
		return ret;
	}

	if (ptrBytesWritten != 0)
	{
		*ptrBytesWritten = ret;
	}
	
	return 0;
}

int32_t prvTraceReadFromSocket(void* data, uint32_t bufsize, int32_t *ptrBytesRead)
{
	unsigned long bytesAvailable = 0;

	if (prvInitServerSocketIfNeeded() < 0)
		return -1;
	
	if (prvInitTraceSocketIfNeeded() < 0)
		return -1;

	if (ioctlsocket(trace_socket, FIONREAD, &bytesAvailable) != NO_ERROR)
	{
		closesocket(trace_socket);
		trace_socket = (UINT_PTR)0;
		return -1;
	}

	if (bytesAvailable > 0)
	{
		*ptrBytesRead = recv(trace_socket, data, bufsize, 0);
		if (*ptrBytesRead == SOCKET_ERROR)
		{
			closesocket(trace_socket);
			trace_socket = (UINT_PTR)0;
			return -1;
		}
	}

	return 0;
}

static void prvCloseAllSockets(void)
{
	if (trace_socket != 0)
	{
		closesocket(trace_socket);
		trace_socket = 0;
	}

	if (server_socket != 0)
	{
		closesocket(server_socket);
		server_socket = 0;
	}
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
