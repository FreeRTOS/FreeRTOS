/*
 * File:    enet.h
 * Purpose: Driver for the ENET controller
 *
 * Notes:       
 */

#ifndef _ENET_H_
#define _ENET_H_

#include "nbuf.h"

/********INTERFACE**********/
typedef enum {
  mac_mii,
  mac_rmii,
} ENET_INTERFACE;
/********AUTONEG**********/
typedef enum {
  autoneg_on,
  autoneg_off
} ENET_AUTONEG;
/********SPEED**********/
typedef enum {
        MII_10BASET,
        MII_100BASET
} ENET_SPEED;
/********DUPLEX**********/
/* MII Duplex Settings */
typedef enum {
	MII_HDX,		/*!< half-duplex */
	MII_FDX			/*!< full-duplex */
} ENET_DUPLEX;
/********LOOPBACK**********/
typedef enum {
        INTERNAL_LOOPBACK,
        EXTERNAL_LOOPBACK,
        NO_LOOPBACK
} ENET_LOOPBACK;
/********EXTERNAL**********/
typedef enum {
        EXTERNAL_NONE,
        EXTERNAL_YES
} ENET_EXTERNAL_CONN;

/*
 * FEC Configuration Parameters
 */
typedef struct 
{
    uint8_t             ch;            /* FEC channel       */
    ENET_INTERFACE      interface;     /* Transceiver mode  */
    ENET_AUTONEG        neg;           /* FEC autoneg */
    ENET_SPEED          speed;         /* Ethernet Speed           */
    ENET_DUPLEX         duplex;        /* Ethernet Duplex          */
    ENET_LOOPBACK       loopback;      /* Loopback Mode */
    ENET_EXTERNAL_CONN  external;      /* outside test? */
    uint8_t             prom;     /* Promiscuous Mode?        */
    uint8_t             mac[6];   /* Ethernet Address         */
} ENET_CONFIG;

void
enet_mib_init(int);

void
enet_mib_dump(int);

void
enet_reg_dump(int);

void
enet_duplex (int, ENET_DUPLEX);

uint8_t
enet_hash_address(const uint8_t*);

void
enet_set_address (int, const uint8_t*);

void
enet_reset (int);

void
enet_init (ENET_CONFIG *config);

void
enet_start (int ch);

int 
enet_wait_for_frame_receive(int,int);


/********************************************************************/

#endif /* _ENET_H_ */
