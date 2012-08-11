/*! 
 * \file    eth.h
 * \brief   Definitinos for Ethernet Frames
 * \version $Revision: 1.2 $
 * \author  Michael Norman
 */

#ifndef _ETH_H
#define _ETH_H

/*******************************************************************/

/* Ethernet standard lengths in bytes*/
#define ETH_ADDR_LEN    (6)
#define ETH_TYPE_LEN    (2)
#define ETH_CRC_LEN     (4)
#define ETH_MAX_DATA    (1500)
#define ETH_MIN_DATA    (46)
#define ETH_HDR_LEN     (ETH_ADDR_LEN * 2 + ETH_TYPE_LEN)

/* Defined Ethernet Frame Types */
#define ETH_FRM_IP      (0x0800)
#define ETH_FRM_ARP     (0x0806)
#define ETH_FRM_RARP    (0x8035)
#define ETH_FRM_TEST    (0xA5A5)

/* Maximum and Minimum Ethernet Frame Sizes */
#define ETH_MAX_FRM     (ETH_HDR_LEN + ETH_MAX_DATA + ETH_CRC_LEN)
#define ETH_MIN_FRM     (ETH_HDR_LEN + ETH_MIN_DATA + ETH_CRC_LEN)
#define ETH_MTU         (ETH_HDR_LEN + ETH_MAX_DATA)

/* Ethernet Addresses */
typedef uint8 ETH_ADDR[ETH_ADDR_LEN];

/* 16-bit Ethernet Frame Type, ie. Protocol */
typedef uint16 ETH_FRM_TYPE;

/* Ethernet Frame Header definition */
typedef struct
{
    ETH_ADDR     dest;
    ETH_ADDR     src;
    ETH_FRM_TYPE type;
} ETH_HDR;

/* Ethernet Frame definition */
typedef struct
{
    ETH_HDR head;
    uint8*  data;
} ETH_FRAME;

/*******************************************************************/

#endif  /* _ETH_H */
