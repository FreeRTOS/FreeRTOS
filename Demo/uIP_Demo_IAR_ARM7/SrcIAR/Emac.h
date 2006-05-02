//*----------------------------------------------------------------------------
//*         ATMEL Microcontroller Software Support  -  ROUSSET  -
//*----------------------------------------------------------------------------
//* The software is delivered "AS IS" without warranty or condition of any
//* kind, either express, implied or statutory. This includes without
//* limitation any warranty or condition with respect to merchantability or
//* fitness for any particular purpose, or against the infringements of
//* intellectual property rights of others.
//*----------------------------------------------------------------------------
//* File Name           : Emac.h
//* Object              : Emac header file
//* Creation            : Hi   11/18/2002
//*
//*----------------------------------------------------------------------------
#ifndef AT91C_EMAC_H
#define AT91C_EMAC_H


//* Allows to display all IP header in the main.c
//* If not defined, only ICMP packets are displayed
#define AT91C_DISPLAY_ALL_IPHEADER		0

#define NB_RX_BUFFERS			25			//* Number of receive buffers
#define ETH_RX_BUFFER_SIZE		128         //*

#define NB_TX_BUFFERS			2		//* Number of Transmit buffers
#define ETH_TX_BUFFER_SIZE		UIP_BUFSIZE       //*

#define AT91C_NO_IPPACKET		0
#define AT91C_IPPACKET	        1

#define ARP_REQUEST				0x0001
#define ARP_REPLY				0x0002
#define PROT_ARP				0x0806
#define PROT_IP					0x0800
#define PROT_ICMP				0x01
#define ICMP_ECHO_REQUEST		0x08
#define ICMP_ECHO_REPLY			0x00

#define AT91C_EMAC_CLKEN 0x2
#define SWAP16(x)	(((x & 0xff) << 8) | (x >> 8))

#if 0
//* Transfer descriptor structure
typedef struct _AT91S_TdDescriptor {
	unsigned int addr;
	unsigned int status;
}AT91S_TdDescriptor, *AT91PS_TdDescriptor;
#endif

//* Receive Transfer descriptor structure
typedef struct  _AT91S_RxTdDescriptor {
	unsigned int addr;
	union
	{
		unsigned int status;
		struct {
			unsigned int Length:11;
			unsigned int Res0:1;
			unsigned int Rxbuf_off:2;
			unsigned int StartOfFrame:1;
			unsigned int EndOfFrame:1;
			unsigned int Cfi:1;
			unsigned int VlanPriority:3;
			unsigned int PriorityTag:1;
			unsigned int VlanTag:1;
			unsigned int TypeID:1;
			unsigned int Sa4Match:1;
			unsigned int Sa3Match:1;
			unsigned int Sa2Match:1;
			unsigned int Sa1Match:1;
			unsigned int Res1:1;
			unsigned int ExternalAdd:1;
			unsigned int UniCast:1;
			unsigned int MultiCast:1;
			unsigned int BroadCast:1;
		}S_Status;		
	}U_Status;
}AT91S_RxTdDescriptor, *AT91PS_RxTdDescriptor;


//* Transmit Transfer descriptor structure
typedef struct _AT91S_TxTdDescriptor {
	unsigned int addr;
	union
	{
		unsigned int status;
		struct {
			unsigned int Length:11;
			unsigned int Res0:4;
			unsigned int LastBuff:1;
			unsigned int NoCrc:1;
			unsigned int Res1:10;
			unsigned int BufExhausted:1;
			unsigned int TransmitUnderrun:1;
			unsigned int TransmitError:1;
			unsigned int Wrap:1;
			unsigned int BuffUsed:1;
		}S_Status;		
	}U_Status;
}AT91S_TxTdDescriptor, *AT91PS_TxTdDescriptor;

#define AT91C_OWNERSHIP_BIT		0x00000001

/* Receive status defintion */
#define AT91C_BROADCAST_ADDR	((unsigned int) (1 << 31))	//* Broadcat address detected
#define AT91C_MULTICAST_HASH 	((unsigned int) (1 << 30))	//* MultiCast hash match
#define AT91C_UNICAST_HASH 	    ((unsigned int) (1 << 29))	//* UniCast hash match
#define AT91C_EXTERNAL_ADDR	    ((unsigned int) (1 << 28))	//* External Address match
#define AT91C_SA1_ADDR	    	((unsigned int) (1 << 26))	//* Specific address 1 match
#define AT91C_SA2_ADDR	    	((unsigned int) (1 << 25))	//* Specific address 2 match
#define AT91C_SA3_ADDR	    	((unsigned int) (1 << 24))	//* Specific address 3 match
#define AT91C_SA4_ADDR	    	((unsigned int) (1 << 23))	//* Specific address 4 match
#define AT91C_TYPE_ID	    	((unsigned int) (1 << 22))	//* Type ID match
#define AT91C_VLAN_TAG	    	((unsigned int) (1 << 21))	//* VLAN tag detected
#define AT91C_PRIORITY_TAG    	((unsigned int) (1 << 20))	//* PRIORITY tag detected
#define AT91C_VLAN_PRIORITY    	((unsigned int) (7 << 17))  //* PRIORITY Mask
#define AT91C_CFI_IND        	((unsigned int) (1 << 16))  //* CFI indicator
#define AT91C_EOF           	((unsigned int) (1 << 15))  //* EOF
#define AT91C_SOF           	((unsigned int) (1 << 14))  //* SOF
#define AT91C_RBF_OFFSET     	((unsigned int) (3 << 12))  //* Receive Buffer Offset Mask
#define AT91C_LENGTH_FRAME     	((unsigned int) 0x07FF)     //* Length of frame

/* Transmit Status definition */
#define AT91C_TRANSMIT_OK		((unsigned int) (1 << 31))	//*
#define AT91C_TRANSMIT_WRAP		((unsigned int) (1 << 30))	//* Wrap bit: mark the last descriptor
#define AT91C_TRANSMIT_ERR		((unsigned int) (1 << 29))	//* RLE:transmit error
#define AT91C_TRANSMIT_UND		((unsigned int) (1 << 28))	//* Transmit Underrun
#define AT91C_BUF_EX     		((unsigned int) (1 << 27))	//* Buffers exhausted in mid frame
#define AT91C_TRANSMIT_NO_CRC	((unsigned int) (1 << 16))	//* No CRC will be appended to the current frame
#define AT91C_LAST_BUFFER    	((unsigned int) (1 << 15))	//*

#define ARP_ETHER	 		1		/* Ethernet  hardware address	*/
#define ARPOP_REQUEST    	1		/* Request  to resolve  address	*/
#define ARPOP_REPLY	    	2		/* Response to previous request	*/
#define RARPOP_REQUEST   	3		/* Request  to resolve  address	*/
#define RARPOP_REPLY	    4		/* Response to previous request */


typedef struct _AT91S_EthHdr
{
	unsigned char		et_dest[6];	/* Destination node		*/
	unsigned char		et_src[6];	/* Source node			*/
	unsigned short		et_protlen;	/* Protocol or length		*/
} AT91S_EthHdr, *AT91PS_EthHdr;

typedef struct _AT91S_ArpHdr
{
	unsigned short		ar_hrd;		/* Format of hardware address	*/
	unsigned short		ar_pro;		/* Format of protocol address	*/
	unsigned char		ar_hln;		/* Length of hardware address	*/
	unsigned char		ar_pln;		/* Length of protocol address	*/
	unsigned short		ar_op;		/* Operation			*/
	unsigned char		ar_sha[6];	/* Sender hardware address	*/
	unsigned char		ar_spa[4];	/* Sender protocol address	*/
	unsigned char		ar_tha[6];	/* Target hardware address	*/
	unsigned char		ar_tpa[4];	/* Target protocol address	*/
} AT91S_ArpHdr, *AT91PS_ArpHdr;

//* IP Header structure
typedef struct _AT91S_IPheader {
	unsigned char	ip_hl_v;	/* header length and version	*/
	unsigned char	ip_tos;		/* type of service		*/
	unsigned short	ip_len;		/* total length			*/
	unsigned short	ip_id;		/* identification		*/
	unsigned short	ip_off;		/* fragment offset field	*/
	unsigned char	ip_ttl;		/* time to live			*/
	unsigned char	ip_p;		/* protocol			*/
	unsigned short	ip_sum;		/* checksum			*/
	unsigned char	ip_src[4];	/* Source IP address		*/
	unsigned char	ip_dst[4];	/* Destination IP address	*/
	unsigned short	udp_src;	/* UDP source port		*/
	unsigned short	udp_dst;	/* UDP destination port		*/
	unsigned short	udp_len;	/* Length of UDP packet		*/
	unsigned short	udp_xsum;	/* Checksum			*/
} AT91S_IPheader, *AT91PS_IPheader;

//* ICMP echo header structure
typedef struct _AT91S_IcmpEchoHdr {
    unsigned char   type;       /* type of message */
    unsigned char   code;       /* type subcode */
    unsigned short  cksum;      /* ones complement cksum of struct */
    unsigned short  id;         /* identifier */
    unsigned short  seq;        /* sequence number */
}AT91S_IcmpEchoHdr, *AT91PS_IcmpEchoHdr;


typedef struct _AT91S_EthPack
{
	AT91S_EthHdr	EthHdr;
	AT91S_ArpHdr	ArpHdr;
} AT91S_EthPack, *AT91PS_EthPack;


#endif //* AT91C_EMAC_H
