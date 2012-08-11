/*
********************************************************************************
* TERN, Inc.
* (c) Copyright 2005, http://www.tern.com
*
* - Derived based on development version provided by Wiznet.
*
* Filename : socket.h
* Programmer(s):
* Created : 2002/06/20
* Modified :
*  2002/09/27 : - Renaming
*			       INT_STATUS --> INT_REG
*			       STATUS(i) --> INT_STATUS(i)
*			       C_STATUS(i) --> SOCK_STATUS(i)
*  2003/11/06 : Ported for use with TERN controller.  Note all byte access is at even addresses
*  2005/10/8  : Modified constants for easier initialization.
*
* Description : Header file of W3100A for TERN embedded controller
********************************************************************************
*/
#ifndef	__SOCKET_H__
#define	__SOCKET_H__

#include "types.h"
#include "i2chip_hw.h"
#include <dos.h>

/*******************************************************************/
#define	MAX_SOCK_NUM	4					// Concurrent maxmium number of socket

#define I2CHIP_C0_CR       0x00
#define I2CHIP_C1_CR       0x01
#define I2CHIP_C2_CR       0x02
#define I2CHIP_C3_CR       0x03
#define I2CHIP_C0_ISR      0x04
#define I2CHIP_C1_ISR      0x05
#define I2CHIP_C2_ISR      0x06
#define I2CHIP_C3_ISR      0x07
#define I2CHIP_IR          0x08
#define I2CHIP_IMR         0x09

#define I2CHIP_IDM_OR		0x0C
#define I2CHIP_IDM_AR0     0x0D
#define I2CHIP_IDM_AR1     0x0E
#define I2CHIP_IDM_DR      0x0F
#define I2CHIP_C0_RW_PR    0x10
#define I2CHIP_C0_RR_PR    0x14
#define I2CHIP_C0_TA_PR    0x18
#define I2CHIP_C1_RW_PR    0x1C
#define I2CHIP_C1_RR_PR    0x20
#define I2CHIP_C1_TA_PR    0x24
#define I2CHIP_C2_RW_PR    0x28
#define I2CHIP_C2_RR_PR    0x2C
#define I2CHIP_C2_TA_PR    0x30
#define I2CHIP_C3_RW_PR    0x34
#define I2CHIP_C3_RR_PR    0x38
#define I2CHIP_C3_TA_PR    0x3C
#define I2CHIP_C0_TW_PR    0x40
#define I2CHIP_C0_TR_PR    0x44
#define I2CHIP_C1_TW_PR    0x4C
#define I2CHIP_C1_TR_PR    0x50
#define I2CHIP_C2_TW_PR    0x58
#define I2CHIP_C2_TR_PR    0x5C
#define I2CHIP_C3_TW_PR    0x64
#define I2CHIP_C3_TR_PR    0x68
#define I2CHIP_GAR         0x80
#define I2CHIP_SMR         0x84
#define I2CHIP_SHAR     	0x88
#define I2CHIP_SIPR        0x8E
#define I2CHIP_IRTR        0x92
#define I2CHIP_RCR         0x94
#define I2CHIP_RMSR        0x95
#define I2CHIP_TMSR        0x96
#define I2CHIP_C0_SSR      0xA0
#define I2CHIP_C0_SOPR     0xA1
#define I2CHIP_C0_DIR      0xA8
#define I2CHIP_CO_DPR      0xAC
#define I2CHIP_C0_SPR      0xAE
#define I2CHIP_C0_IPR      0xB0
#define I2CHIP_C0_TOSR     0xB1
#define I2CHIP_C0_MSSR     0xB2

#define I2CHIP_C1_SSR      0xB8
#define I2CHIP_C1_SOPR     0xB9
#define I2CHIP_C1_DIR      0xC0
#define I2CHIP_C1_DPR      0xC4
#define I2CHIP_C1_SPR      0xC6
#define I2CHIP_C1_IPR      0xC8
#define I2CHIP_C1_TOSR     0xC9
#define I2CHIP_C1_MSSR     0xCA

#define I2CHIP_C2_SSR      0xD0
#define I2CHIP_C2_SOPR     0xD1
#define I2CHIP_C2_DIR      0xD8
#define I2CHIP_C2_DPR      0xDC
#define I2CHIP_C2_SPR      0xDE
#define I2CHIP_C2_IPR      0xE0
#define I2CHIP_C2_TOSR     0xE1
#define I2CHIP_C2_MSSR     0xE2

#define I2CHIP_C3_SSR      0xE8
#define I2CHIP_C3_SOPR     0xE9
#define I2CHIP_C3_DIR      0xF0
#define I2CHIP_C3_DPR      0xF4
#define I2CHIP_C3_SPR      0xF6
#define I2CHIP_C3_IPR      0xF8
#define I2CHIP_C3_TOSR     0xF9
#define I2CHIP_C3_MSSR     0xFA

#define MAX_SEGMENT_SIZE	1460			// Maximum TCP transmission packet size
#define MAX_BUF_SIZE1		0


/* SOCKET OPTION(Settting OPT_PROTOCOL REG.) */
#define SOCKOPT_BROADCAST	0x80		// Transmission, Reception of broadcasting data
#define SOCKOPT_NDTIMEOUT	0x40		// Setting timeout
#define SOCKOPT_NDACK		0x20		// Setting No Delayed Ack(TCP)
#define SOCKOPT_SWS			0x10		// Setting Silly Window Syndrome(TCP)

/* OPTION(Setting OPT_PROTOCOL REG.) for MAC LAYER RAW MODE */
#define MACLOPT_RXERR		0x80		// Setting reception of error packet
#define MACLOPT_BROADCAST	0x40		// Setting reception of broadcast packet
#define MACLOPT_PROMISC		0x20		// Setting reception of promiscuous packet

/* Distinguish TCP / UDP / IP RAW / MAC RAW (Setting OPT_PROTOCOL REG.) */
#define	SOCK_CLOSEDM	0x00			// unused socket
#define	SOCK_STREAM		0x01			// TCP
#define	SOCK_DGRAM		0x02			// UDP
#define	SOCK_IPL_RAW	0x03			// IP LAYER RAW SOCK
#define	SOCK_MACL_RAW	0x04			// MAC LAYER RAW SOCK

/* Setting IP PROTOCOL */
#define IPPROTO_IP              0               // dummy for IP
#define IPPROTO_ICMP            1               // control message protocol
#define IPPROTO_IGMP            2               // internet group management protocol
#define IPPROTO_GGP             3               // gateway^2 (deprecated)
#define IPPROTO_TCP             6               // tcp
#define IPPROTO_PUP             12              // pup
#define IPPROTO_UDP             17              // user datagram protocol
#define IPPROTO_IDP             22              // xns idp
#define IPPROTO_ND              77              // UNOFFICIAL net disk proto
#define IPPROTO_RAW             255             // raw IP packet

/* Select parameter to use */
#define SEL_CONTROL	0			//Confirm socket status
#define SEL_SEND		1			// Confirm Tx free buffer size
#define SEL_RECV		2			// Confirm Rx data size

/* Command variables */
#define CSYS_INIT		0x01	   // To set up network information(mac address, gateway address,
                              // subnet mask, source ip)
#define CSOCK_INIT	0x02		// To initialize socket
#define CCONNECT		0x04		// To establish connection as tcp client mode
#define CLISTEN		0x08		// To wait for connection request as tcp server mode
#define CCLOSE			0x10		// To terminate connection
#define CSEND			0x20		// To send data
#define CRECV			0x40		// To receive data
#define CSW_RESET		0x80		// To do software reset

#define CSET_MEMORY_TEST   0x80     // To set the memory test bit
#define CRESET_MEMORY_TEST 0x00     // To clear the memory test bit

/* Status Variables */
#define SSYS_INIT_OK		0x01	// Completion of CSYS_INIT command
#define SSOCK_INIT_OK	0x02	// Completion of CSOCK_INIT command
#define SESTABLISHED		0x04	// Completion of connection setup
#define SCLOSED			0x08	// Completion of CCLOSED command
#define SSEND_OK		   0x20	// Completion of sending data
#define SRECV_OK		   0x40	// Completion of receiving data

/* Socket Status Vabiables */
#define SOCK_CLOSED		   0x00	   // Status of connection closed
#define SOCK_ARP		      0x01		// Status of ARP
#define SOCK_LISTEN		   0x02		// Status of waiting for TCP connection setup
#define SOCK_SYNSENT		   0x03		// Status of setting up TCP connection
#define SOCK_SYNSENT_ACK	0x04		// Status of setting up TCP connection
#define SOCK_SYNRECV		   0x05		// Status of setting up TCP connection
#define SOCK_ESTABLISHED	0x06		// Status of TCP connection established
#define SOCK_CLOSE_WAIT		0x07		// Status of closing TCP connection
#define SOCK_LAST_ACK		0x08		// Status of closing TCP connection
#define SOCK_FIN_WAIT1		0x09		// Status of closing TCP connection
#define SOCK_FIN_WAIT2		0x0A		// Status of closing TCP connection
#define SOCK_CLOSING		   0x0B		// Status of closing TCP connection
#define SOCK_TIME_WAIT		0x0C		// Status of closing TCP connection
#define SOCK_RESET		   0x0D		// Status of closing TCP connection
#define SOCK_INIT		      0x0E		// Status of socket initialization
#define SOCK_UDP		      0x0F		// Status of UDP
#define SOCK_RAW		      0x10		// Status of IP RAW

/* TERN Behavior Parameters */
#define TERN_TDMA_THRES    10000      // Use DMA for transmits if data > thres bytes.
#define TERN_RDMA_THRES    10000      // Use DMA for receives if data > thres bytes.
                                      // High thres value effectively disables DMA
                                      
void far interrupt in4_isr_i2chip(void);

//void ISR_ESTABLISHED(SOCKET s);
//void ISR_CLOSED(SOCKET s);
//void ISR_RX(SOCKET s);

void initW3100A(void);
void sysinit(u_char sbufsize, u_char rbufsize);
void setsubmask(u_char * addr);
void setgateway(u_char * addr);
void setMACAddr(u_char * addr);
void setIP(u_char * addr);

char socket(SOCKET s, u_char protocol, u_int port, u_char flag);

void setIPprotocol(SOCKET s, u_char ipprotocol);

void setINTMask(u_char mask);
void settimeout(u_char * val);
void setTOS(SOCKET s, u_char tos);

void GetDestAddr(SOCKET s, u_char* addr);

//void setbroadcast(SOCKET s);

char connect(SOCKET s, u_char far * addr, u_int port);
char NBconnect(SOCKET s, u_char far * addr, u_int port);

//char listen(SOCKET s, u_char far * addr, u_int far * port);
char NBlisten(SOCKET s);

void initseqnum(SOCKET s);

int send(SOCKET s, u_char far * buf, u_int len);
int send_in(SOCKET s, u_char far * buf, u_int len);
int recv(SOCKET s, u_char far * buf, u_int len);

u_int sendto(SOCKET , u_char far * buf, u_int, u_char * addr, u_int);
u_int sendto_in(SOCKET , u_char far *, u_int);
u_int recvfrom(SOCKET , u_char far * buf, u_int, u_char * addr, u_int *);

u_int read_data(SOCKET s, u_int src_offset, u_char far * dst, u_int len);
u_int write_data(SOCKET s, u_char far * src, u_int dst_offset, u_int len);

void close(SOCKET s);
char reset_sock(SOCKET s);

u_int select(SOCKET s, u_char func);
void recv_clear(SOCKET s);
u_char tx_empty(SOCKET s);

#endif	// __SOCKET_H__
