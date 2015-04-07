/******************************************************************************
* DISCLAIMER
* Please refer to http://www.renesas.com/disclaimer
******************************************************************************
  Copyright (C) 2008. Renesas Technology Corp., All Rights Reserved.
*******************************************************************************
* File Name    : r_ether.h
* Version      : 1.02
* Description  : Ethernet module device driver
******************************************************************************
* History : DD.MM.YYYY Version Description
*         : 15.02.2010 1.00    First Release
*         : 03.03.2010 1.01    Buffer size is aligned on the 32-byte boundary.
*         : 04.06.2010 1.02    RX62N changes
******************************************************************************/

#ifndef	R_ETHER_H
#define	R_ETHER_H

/******************************************************************************
Includes   <System Includes> , "Project Includes"
******************************************************************************/


/******************************************************************************
Typedef definitions
******************************************************************************/
struct Descriptor
{
	 unsigned long	status;
#if __RX_LITTLE_ENDIAN__ == 1
/* Little endian */
	 unsigned short	size;
	 unsigned short	bufsize;
#else
/* Big endian */
	 unsigned short	bufsize;
	 unsigned short	size;

#endif
	char					*buf_p;
	struct Descriptor		*next;
};

typedef struct Descriptor ethfifo;

typedef enum _NETLNK
{
    PHY_NO_LINK = 0,
    PHY_LINK_10H,
    PHY_LINK_10F,
    PHY_LINK_100H,
    PHY_LINK_100F

} NETLNK;

/******************************************************************************
Macro definitions
******************************************************************************/
#define	BUFSIZE	  256                   /* Must be 32-bit aligned */
#define ENTRY     8                     /* Number of RX and TX buffers */

#define  ACT      0x80000000
#define  DL       0x40000000
#define  FP1      0x20000000
#define  FP0      0x10000000
#define  FE       0x08000000

#define  RFOVER   0x00000200
#define  RAD      0x00000100
#define  RMAF     0x00000080
#define  RRF      0x00000010
#define  RTLF     0x00000008
#define  RTSF     0x00000004
#define  PRE      0x00000002
#define  CERF     0x00000001

#define  TAD      0x00000100
#define  CND      0x00000008
#define  DLC      0x00000004
#define  CD       0x00000002
#define  TRO      0x00000001

/**
 * Renesas Ethernet API return defines
 **/
#define R_ETHER_OK          0
#define R_ETHER_ERROR       -1

/*	Ether Interface definitions	*/
#define ETH_RMII_MODE	0
#define ETH_MII_MODE	1
/*	Select Ether Interface Mode 	*/
#define ETH_MODE_SEL	ETH_MII_MODE

/******************************************************************************
Variable Externs
******************************************************************************/

/******************************************************************************
Functions Prototypes
******************************************************************************/
/**
 * Renesas Ethernet API prototypes
 **/
long R_Ether_Open(unsigned long ch, unsigned char mac_addr[]);
long R_Ether_Close(unsigned long ch);
long R_Ether_Write(unsigned long ch, void *buf, unsigned long len);
long R_Ether_Read(unsigned long ch, void *buf);

/**
 * FreeRTOS Ethernet API prototypes.
 */

/*
 * Configure all the ethernet components (MAC, DMA, PHY) ready for communication.
 */
void vInitEmac( void );

/*
 * Auto negotiate the link, returning pass or fail depending on whether a link
 * was established or not.
 */
long lEMACWaitForLink( void );

/*
 * Check the Rx status, and return the number of bytes received if any.
 */
unsigned long ulEMACRead( void );

/*
 * Send uip_len bytes from uip_buf to the Tx descriptors and initiate a Tx.
 */
void vEMACWrite( void );




/****************************************************/
/* Ethernet statistic collection data */
struct enet_stats
{
  unsigned long  rx_packets;      /* total packets received    */
  unsigned long  tx_packets;      /* total packets transmitted  */
  unsigned long  rx_errors;       /* bad packets received      */
  unsigned long  tx_errors;       /* packet transmit problems    */
  unsigned long  rx_dropped;      /* no space in buffers      */
  unsigned long  tx_dropped;      /* no space available      */
  unsigned long  multicast;       /* multicast packets received  */
  unsigned long  collisions;

  /* detailed rx_errors: */
  unsigned long  rx_length_errors;
  unsigned long  rx_over_errors;    /* receiver ring buffer overflow  */
  unsigned long  rx_crc_errors;     /* recved pkt with crc error  */
  unsigned long  rx_frame_errors;   /* recv'd frame alignment error  */
  unsigned long  rx_fifo_errors;    /* recv'r fifo overrun      */
  unsigned long  rx_missed_errors;  /* receiver missed packet    */

  /* detailed tx_errors */
  unsigned long  tx_aborted_errors;
  unsigned long  tx_carrier_errors;
  unsigned long  tx_fifo_errors;
  unsigned long  tx_heartbeat_errors;
  unsigned long  tx_window_errors;
};

struct ei_device
{
  const char      *name;
  unsigned char   open;
  unsigned char   Tx_act;
  unsigned char   Rx_act;
  unsigned char   txing;        /* Transmit Active */
  unsigned char   irqlock;      /* EDMAC's interrupt disabled when '1'. */
  unsigned char   dmaing;       /* EDMAC Active */
  ethfifo         *rxcurrent;   /* current receive discripter */
  ethfifo         *txcurrent;   /* current transmit discripter */
  unsigned char   save_irq;     /* Original dev->irq value. */
  struct enet_stats stat;
  unsigned char   mac_addr[6];
};

#endif /* R_ETHER_H */

