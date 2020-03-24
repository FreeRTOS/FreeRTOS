/*
 * dump_packets.c
 * Used in the PC/Win project to dump Ethernet packets, along with some description.
 */

#ifndef DUMP_PACKETS_H


#define DUMP_PACKETS_H

#ifndef dumpMAX_DUMP_ENTRIES
	#define	dumpMAX_DUMP_ENTRIES	16
#endif

#define flag_ICMP4            0x00000001uL
#define flag_ICMP6            0x00000002uL
#define flag_UDP              0x00000004uL
#define flag_TCP              0x00000008uL
#define flag_DNS              0x00000010uL
#define flag_REPLY            0x00000020uL
#define flag_REQUEST          0x00000040uL
#define flag_SYN              0x00000080uL
#define flag_FIN              0x00000100uL
#define flag_RST              0x00000200uL
#define flag_ACK              0x00000400uL
#define flag_IN               0x00000800uL
#define flag_OUT              0x00001000uL
#define flag_FRAME_ARP        0x00002000uL
#define flag_ARP              0x00004000uL
#define flag_UNKNOWN          0x00008000uL
#define flag_FRAME_4          0x00010000uL
#define flag_FRAME_6          0x00020000uL
#define flag_Unknown_FRAME    0x00040000uL

typedef struct xDumpEntry
{
	uint32_t ulMask;
	size_t uxMax;
	size_t uxCount;
} DumpEntry_t;

typedef struct xDumpEntries
{
	size_t uxEntryCount;
	DumpEntry_t xEntries[ dumpMAX_DUMP_ENTRIES ];
} DumpEntries_t;

/*

 */

#if( ipconfigUSE_DUMP_PACKETS != 0 )

	extern void dump_packet_init( const char *pcFileName, DumpEntries_t *pxEntries );
	extern void dump_packet( const uint8_t *pucBuffer, size_t uxLength, BaseType_t xIncoming );
	#define iptraceDUMP_PACKET( pucBuffer, uxLength, xIncoming ) \
		dump_packet( pucBuffer, uxLength, xIncoming )

#endif

#endif
