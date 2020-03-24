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

	void vTCPMemStatRemove( void *pxObject );

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

