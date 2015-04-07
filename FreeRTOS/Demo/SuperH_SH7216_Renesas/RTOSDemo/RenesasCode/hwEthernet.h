/******************************************************************************
*   DISCLAIMER
*   Please refer to http://www.renesas.com/disclaimer
******************************************************************************
    Copyright   (C) 2008.   Renesas Technology Corp.,   All Rights Reserved.
*******************************************************************************
*   File Name        : hwEthernet.h
*   Version          : 1.00
*   Description  : Ethernet module device   driver
******************************************************************************
*   History :   DD.MM.YYYY Version Description
*                   :   06.10.2009 1.00      First Release
******************************************************************************/

#ifndef HWETHERNET_H_INCLUDED
#define HWETHERNET_H_INCLUDED

/******************************************************************************
Includes     <System Includes> , "Project   Includes"
******************************************************************************/

#include "typedefine.h"

/******************************************************************************
Typedef definitions
******************************************************************************/
typedef struct Discript
{
    uint32_t            status;
    ushort16_t          bufsize;
    ushort16_t          size;
    char8_t             *buf_p;
    struct Discript     *next;
}   ethfifo;

/******************************************************************************
Macro   definitions
******************************************************************************/
#define BUFSIZE         256
#define ENTRY           8

#define  ACT            0x80000000
#define  DL             0x40000000
#define  FP1            0x20000000
#define  FP0            0x10000000
#define  FE             0x08000000

#define  RFOVER         0x00000200
#define  RMAF           0x00000080
#define  RRF            0x00000010
#define  RTLF           0x00000008
#define  RTSF           0x00000004
#define  PRE            0x00000002
#define  CERF           0x00000001

#define  ITF            0x00000010
#define  CND            0x00000008
#define  DLC            0x00000004
#define  CD             0x00000002
#define  TRO            0x00000001

/** 
 * Renesas Ethernet API return defines
 **/
#define R_ETHER_OK      0
#define R_ETHER_ERROR   -1


/******************************************************************************
Variable Externs
******************************************************************************/

/******************************************************************************
Functions   Prototypes
******************************************************************************/
/** 
 * Renesas Ethernet API prototypes
 **/

#ifdef __cplusplus
extern "C" {
#endif

extern  int32_t R_Ether_Open(uint32_t   ch, uint8_t mac_addr[]);
extern  int32_t R_Ether_Close(uint32_t ch);
extern  int32_t R_Ether_Write(uint32_t ch, void *buf,   uint32_t len);
extern  int32_t R_Ether_Read(uint32_t   ch, void *buf);

/* Added for the FreeRTOS demo project. */
unsigned long ulEMACRead( void );
void vEMACWrite( void );
void vInitEmac( void );
long lEMACWaitForLink( void );

/* Extension of the API functions added to allow PnP link */

/* R_Ether_OpenEx opens irrispective of link status */
extern  int32_t R_Ether_OpenEx(uint32_t   ch, uint8_t mac_addr[]);
/* Enables/disables operation for the current link */
extern  int32_t R_Ether_EnableEx(uint32_t   ch, int iEnable);

#ifdef __cplusplus
}
#endif

/****************************************************/
/* Ethernet statistic   collection data */
struct enet_stats
{
    uint32_t    rx_packets;          /* total   packets received        */
    uint32_t    tx_packets;          /* total   packets transmitted  */
    uint32_t    rx_errors;           /* bad packets received            */
    uint32_t    tx_errors;           /* packet transmit problems        */
    uint32_t    rx_dropped;          /* no space in buffers          */
    uint32_t    tx_dropped;          /* no space available          */
    uint32_t    multicast;           /* multicast   packets received    */
    uint32_t    collisions;

    /* detailed rx_errors: */
    uint32_t    rx_length_errors;
    uint32_t    rx_over_errors;      /* receiver ring   buffer overflow  */
    uint32_t    rx_crc_errors;       /* recved pkt with crc error    */
    uint32_t    rx_frame_errors;     /* recv'd frame alignment error    */
    uint32_t    rx_fifo_errors;      /* recv'r fifo overrun          */
    uint32_t    rx_missed_errors;    /* receiver missed packet      */

    /* detailed tx_errors   */
    uint32_t    tx_aborted_errors;
    uint32_t    tx_carrier_errors;
    uint32_t    tx_fifo_errors;
    uint32_t    tx_heartbeat_errors;
    uint32_t    tx_window_errors;
};

struct ei_device
{
    const   char8_t             *name;
    uchar8_t                    open;
    uchar8_t                    Tx_act;
    uchar8_t                    Rx_act;
    uchar8_t                    txing;          /* Transmit Active */
    uchar8_t                    irqlock;        /* EDMAC's interrupt disabled   when '1'.   */
    uchar8_t                    dmaing;         /* EDMAC Active */
    ethfifo                     *rxcurrent;     /* current receive discriptor   */
    ethfifo                     *txcurrent;     /* current transmit discriptor */
    uchar8_t                    save_irq;       /* Original dev->irq value. */
    struct enet_stats   stat;
    uchar8_t                    mac_addr[6];
};

#endif /*   HWETHERNET_H_INCLUDED    */

