/*
 * dump_packets.c
 * Used in the PC/Win project to dump Ethernet packets, along with some description.
 */

#ifndef DUMP_PACKETS_H


#define DUMP_PACKETS_H

#ifndef dumpMAX_DUMP_ENTRIES
	#define	dumpMAX_DUMP_ENTRIES	16
#endif

#define flag_ICMP4            0x00000001UL
#define flag_ICMP6            0x00000002UL
#define flag_UDP              0x00000004UL
#define flag_TCP              0x00000008UL
#define flag_DNS              0x00000010UL
#define flag_REPLY            0x00000020UL
#define flag_REQUEST          0x00000040UL
#define flag_SYN              0x00000080UL
#define flag_FIN              0x00000100UL
#define flag_RST              0x00000200UL
#define flag_ACK              0x00000400UL
#define flag_IN               0x00000800UL
#define flag_OUT              0x00001000UL
#define flag_FRAME_ARP        0x00002000UL
#define flag_ARP              0x00004000UL
#define flag_UNKNOWN          0x00008000UL
#define flag_FRAME_4          0x00010000UL
#define flag_FRAME_6          0x00020000UL
#define flag_Unknown_FRAME    0x00040000UL

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
	#define iptraceDUMP_INIT( pcFileName, pxEntries ) \
		dump_packet_init( pcFileName, pxEntries )

	extern void dump_packet( const uint8_t *pucBuffer, size_t uxLength, BaseType_t xIncoming );
	#define iptraceDUMP_PACKET( pucBuffer, uxLength, xIncoming ) \
		dump_packet( pucBuffer, uxLength, xIncoming )

#endif

#endif
