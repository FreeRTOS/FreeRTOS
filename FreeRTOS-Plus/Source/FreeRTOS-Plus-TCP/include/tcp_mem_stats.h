/*
 * FreeRTOS+TCP V2.2.2
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/*
 * tcp_mem_stats.h
 */
 
 
#ifndef TCP_MEM_STATS_H

#define TCP_MEM_STATS_H

#ifdef __cplusplus
extern "C" {
#endif

typedef enum xTCP_MEMORY
{
	tcpSOCKET_TCP,
	tcpSOCKET_UDP,
	tcpSOCKET_SET,
	tcpSEMAPHORE,
	tcpRX_STREAM_BUFFER,
	tcpTX_STREAM_BUFFER,
	tcpNETWORK_BUFFER,
} TCP_MEMORY_t;

#if( ipconfigUSE_TCP_MEM_STATS != 0 )

	void vTCPMemStatCreate( TCP_MEMORY_t xMemType, void *pxObject, size_t uxSize );

	void vTCPMemStatDelete( void *pxObject );

	void vTCPMemStatClose( void );

	#define iptraceMEM_STATS_CREATE( xMemType, pxObject, uxSize ) \
		vTCPMemStatCreate( xMemType, pxObject, uxSize )

	#define iptraceMEM_STATS_DELETE( pxObject ) \
		vTCPMemStatDelete( pxObject )

	#define iptraceMEM_STATS_CLOSE() \
		vTCPMemStatClose()
#else

	/* The header file 'IPTraceMacroDefaults.h' will define the default empty macro's. */

#endif /* ipconfigUSE_TCP_MEM_STATS != 0 */

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif	/* TCP_MEM_STATS_H */

