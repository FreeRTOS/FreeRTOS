/*******************************************************************************
 * (c) Copyright 2009 SLS Corporation,All Rights Reserved.
 *
 *	tcpip.h:header file for TCP/IP implementation.
 *  Version       Author         Comment
 *  1.0.0         SLS corp.		 First release
 */
/***************************************************************************//**
 * This header file contains the definition and datastructures for the TCP/IP 
 * stack implementation.
 */
#ifndef _NETTYPE_H_
#define _NETTYPE_H_

#define BUF_LEN 1500

/* IP header length in terms of 16-bit words */
#define IP_HDR_LEN 10
#define IP_HDR_CSUM_OFFSET 5
#define TCP_HDR_CSUM_OFFSET 8

#define ETH_ADDR_LEN 6
#define IP_ADDR_LEN 4
#define ETH_TYPE_LEN 2
#define ARP_HW_TYPE_LEN 2
#define ARP_PROTO_TYPE_LEN 2
#define ARP_OPCODE_LEN 2

#define ETH_TYPE_0     0x08	/* both IP and ARP have 08 as the first byte */
#define ETH_TYPE_ARP_1 0x06	/* 0806 is ARP */
#define ETH_TYPE_IP_1  0x00	/* 0800 is IP */

#define ARP_HW_TYPE_0  0x00	/* 0001 for ethernet */
#define ARP_HW_TYPE_1  0x01	/* 0001 for ethernet */

#define ARP_PROTO_TYPE_0 0x08	/* 0800 is IP */
#define ARP_PROTO_TYPE_1 0x00   

#define ARP_OPCODE_0 0x00	/* same for req and reply */
#define ARP_OPCODE_REQ_1 0x01	/* 0001 is Request */
#define ARP_OPCODE_REPLY_1 0x02	/* 0002 is Reply */

extern unsigned char my_IP_address[IP_ADDR_LEN];

typedef struct ether_hdr {
    unsigned char da[ETH_ADDR_LEN];	/* destination MAC address */
    unsigned char sa[ETH_ADDR_LEN];	/* source MAC address */
    unsigned char type_code[ETH_TYPE_LEN]; /* type code */
} ether_hdr_t;

typedef struct arp_pkt {
    unsigned char hw_type[ARP_HW_TYPE_LEN]; /* Hardware Type */
    unsigned char proto_type[ARP_PROTO_TYPE_LEN]; /* Protocol Type */
    unsigned char hw_addr_len;		/* Hardware Address Length */
    unsigned char proto_addr_len; 	/* Protocol Address Length */
    unsigned char opcode[ARP_OPCODE_LEN]; /* Opcode */
    unsigned char mac_sa[ETH_ADDR_LEN]; /* sender MAC address */
    unsigned char ip_sa[IP_ADDR_LEN];	/* sender IP address */
    unsigned char mac_ta[ETH_ADDR_LEN]; /* target MAC address */
    unsigned char ip_ta[IP_ADDR_LEN];	/* target IP address */
} arp_pkt_t;

#define ICMP_PROTO	0x01
#define	TCP_PROTO	0x06
#define	UDP_PROTO	0x11

#define IP_CSUM_LEN     2
#define IP_ID_LEN       2
#define IP_TLEN_LEN     2
#define IP_FRAG_OFF_LEN 2

typedef struct ip_hdr {
    unsigned char ver_hlen;		/* version - 4 bits;  IP hdr len - 4 bits */
    unsigned char tos;			/* Type of service */
    unsigned char tlen[IP_TLEN_LEN];	/* Size of datagram (header + data) */
    unsigned char id[IP_ID_LEN];	/* together with sa, uniequly identifies pkt */
    unsigned char frag_off[IP_FRAG_OFF_LEN]; /* flags - 3 bits; fragment offset - 13 bits */
    unsigned char ttl;			/* time to live */
    unsigned char proto;		/* protocol */
    unsigned char csum[IP_CSUM_LEN];	/* header checksum */
    unsigned char sa[IP_ADDR_LEN];	/* IP source address */
    unsigned char da[IP_ADDR_LEN];	/* IP dest address */
} ip_hdr_t;


#define ICMP_TYPE_ECHO_REQUEST  8
#define ICMP_TYPE_ECHO_REPLY    0

typedef struct icmp_hdr {
    unsigned char type;
    unsigned char icode;
    unsigned char csum[IP_CSUM_LEN];
} icmp_hdr_t;

#define TCP_PORT_LEN             2
#define TCP_SEQ_LEN              4
#define TCP_WSIZE_LEN            2
#define TCP_UPTR_LEN             2
#define TCP_CSUM_LEN             2
#define TCP_PLEN_LEN             2

typedef struct tcp_hdr {
    unsigned char sp[TCP_PORT_LEN];	/* Source port */
    unsigned char dp[TCP_PORT_LEN];	/* Destination port */
    unsigned char seqnum[TCP_SEQ_LEN];	/* Sequence number */
    unsigned char acknum[TCP_SEQ_LEN];	/* Acknowledgement number */
    unsigned char data_off;		/* Data Offset - 4 upper bits are valid */
    unsigned char urg_ack_psh_rst_syn_fin; /* 6 lower bits are valid */
    unsigned char wsize[TCP_WSIZE_LEN]; /* Window */
    unsigned char csum[TCP_CSUM_LEN];	/* Chekcsum */
    unsigned char uptr[TCP_UPTR_LEN];	/* Urgent pointer */
} tcp_hdr_t;		

#define UDP_LEN_LEN              2
#define UDP_CSUM_LEN             2

typedef struct udp_hdr {
    unsigned char sp[TCP_PORT_LEN];	/* Source port */
    unsigned char dp[TCP_PORT_LEN];	/* Destination port */
    unsigned char len[UDP_LEN_LEN];	/* length of packet */
    unsigned char csum[UDP_CSUM_LEN];	/* checksum */
} udp_hdr_t;

#define BOOTP_OPTCODE_DHCP_SUBNET     1  /* Subnet mask */
#define BOOTP_OPTCODE_DHCP_ROUTER     3  /* Router*/
#define BOOTP_OPTCODE_DHCP_DOMAIN     6  /* Domain */
#define BOOTP_OPTCODE_DHCP_LEASE      51 /* Lease time*/ 
#define BOOTP_OPTCODE_DHCP_TYPE       53 /* 53, 1, DHCP_TYPE_* */
#define BOOTP_OPTCODE_DHCP_SID	      54 /* 54, 4, a.b.c.d, Server ID */
#define BOOTP_OPTCODE_DHCP_RENEW      58 /* Renewal time */
#define BOOTP_OPTCODE_DHCP_REBIND     59 /* Rebinding time */

#define BOOTP_OPTCODE_END            255 /* last in options */

#define DHCP_TYPE_DISCOVER             1     
#define DHCP_TYPE_OFFER                2     
#define DHCP_TYPE_REQUEST              3     
#define DHCP_TYPE_DECLINE              4     
#define DHCP_TYPE_ACK                  5     
#define DHCP_TYPE_NAK                  6     
#define DHCP_TYPE_RELEASE              7     


#define BOOTP_OP_REQUEST         1
#define BOOTP_OP_REPLY           2
#define BOOTP_HWTYPE_ETH         1
#define BOOTP_XID_LEN            4
#define BOOTP_SEC_LEN		 2
#define BOOTP_CHLEN             16
#define BOOTP_SN_LEN            64
#define BOOTP_FL_LEN           128
#define BOOTP_VEN_LEN           64

#define BOOTP_CLIENT_PORT       68
#define BOOTP_SERVER_PORT       67

typedef struct bootp_pkt {
    unsigned char op;			/* packet op code */
    unsigned char hwtype;		/* hardware type */
    unsigned char hlen;		/* hardware address length */
    unsigned char hops;		/* client sets to zero */
    unsigned char xid[BOOTP_XID_LEN];	/* transaction ID, random */
    unsigned char secs[BOOTP_SEC_LEN]; /* seconds since boot */
    unsigned char flags[2];		/* flags */
    unsigned char ciaddr[IP_ADDR_LEN];	/* client IP ADDR */
    unsigned char yiaddr[IP_ADDR_LEN];	/* Your IP Addr */
    unsigned char siaddr[IP_ADDR_LEN];	/* Server IP ADDR */
    unsigned char giaddr[IP_ADDR_LEN];	/* Gateway IP ADDR */
    unsigned char chaddr[BOOTP_CHLEN];	/* Client Hardware Addr */
    unsigned char sname[BOOTP_SN_LEN];	/* Server Name */
    unsigned char file[BOOTP_FL_LEN];	/* File Path */
    unsigned char vend[BOOTP_VEN_LEN];	/* Vendor Data */
} bootp_pkt_t;

typedef struct tcp_pseudo_hdr {
    unsigned char sa[IP_ADDR_LEN];
    unsigned char da[IP_ADDR_LEN];
    unsigned char zero;
    unsigned char proto;
    unsigned char plen[TCP_PLEN_LEN];
} tcp_pseudo_hdr_t;

typedef enum tcp_state_e {
    TCP_STATE_LISTEN = 0,
    TCP_STATE_SYN_RECVD,
    TCP_STATE_ESTABLISHED,
    TCP_STATE_LAST_ACK,
    TCP_STATE_MY_LAST,
    TCP_STATE_CLOSED
} tcp_state_t;

typedef struct tcp_control_block {
    unsigned char local_port[TCP_PORT_LEN];
    unsigned char remote_port[TCP_PORT_LEN];
    unsigned char remote_addr[IP_ADDR_LEN];
    tcp_state_t state;
    unsigned int local_seq;
    unsigned int remote_seq;
    unsigned char remote_mac[ETH_ADDR_LEN]; /* this really doesn't belong here */
//<CJ>:    
    const uint8_t * tx_block_addr;
    unsigned short int tx_block_size;
    unsigned short int tx_block_idx;
    uint8_t * tcp_packet;
} tcp_control_block_t;


typedef enum tcp_cntrol_flags_e {
    TCP_CNTRL_FIN = 0x01,
    TCP_CNTRL_SYN = 0x02,
    TCP_CNTRL_RST = 0x04,
    TCP_CNTRL_PSH = 0x08,
    TCP_CNTRL_ACK = 0x10,
    TCP_CNTRL_URG = 0x20
} tcp_control_flags_t;


typedef struct arp_entry {
    unsigned char mac[ETH_ADDR_LEN];	/* MAC address */
    unsigned char ip[IP_ADDR_LEN];	/* IP address */
    unsigned char used; 		/* Is this entry used? */
} arp_entry_t;

typedef arp_pkt_t  *arp_pkt_xp;
typedef ether_hdr_t *eth_hdr_xp;
typedef ip_hdr_t  *ip_hdr_xp;
typedef icmp_hdr_t  *icmp_hdr_xp;
typedef udp_hdr_t  *udp_hdr_xp;
typedef tcp_hdr_t  *tcp_hdr_xp;
typedef tcp_pseudo_hdr_t  *tcp_pseudo_hdr_xp;
typedef bootp_pkt_t  *bootp_pkt_xp;

#endif /* _NETTYPE_H_ */
