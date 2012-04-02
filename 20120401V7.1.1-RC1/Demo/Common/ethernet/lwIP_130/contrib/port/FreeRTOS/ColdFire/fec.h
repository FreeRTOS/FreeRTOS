/*
 * File:    fec.h
 * Purpose: Driver for the Fast Ethernet Controller (FEC)
 *
 * Notes:       
 */

#ifndef _FEC_H_
#define _FEC_H_

#include "eth.h"
#include "fecbd.h"
#include "mii.h"
#include "eth_phy.h"

/********************************************************************/

/* External Interface Modes */
#define FEC_MODE_7WIRE          0   /* Old 7-wire (AMD) mode */
#define FEC_MODE_MII            1   /* Media Independent Interface */
#define FEC_MODE_RMII           2   /* Reduced MII */
#define FEC_MODE_LOOPBACK       3   /* Internal Loopback */

#define INTC_LVL_FEC			3
/*
 * FEC Configuration Parameters
 */
typedef struct 
{
    uint8      ch;       /* FEC channel              */
    uint8      mode;     /* Transceiver mode         */
    MII_SPEED  speed;    /* Ethernet Speed           */
    MII_DUPLEX duplex;   /* Ethernet Duplex          */
    uint8      prom;     /* Promiscuous Mode?        */
    uint8      mac[6];   /* Ethernet Address         */
    uint8      phyaddr;  /* PHY address              */
    uint8      initphy;  /* Init PHY?                */
    int        nrxbd;    /* Number of RxBDs          */
    int        ntxbd;    /* Number of TxBDs          */
} FEC_CONFIG;
#define YES 1
#define NO 0
/*
 * FEC Event Log
 */
typedef struct {
    int errors;     /* total count of errors   */
    int hberr;      /* heartbeat error         */
    int babr;       /* babbling receiver       */
    int babt;       /* babbling transmitter    */
    int gra;        /* graceful stop complete  */
    int txf;        /* transmit frame          */
    int txb;        /* transmit buffer         */
    int rxf;        /* receive frame           */
    int rxb;        /* received buffer         */
    int mii;        /* MII                     */
    int eberr;      /* FEC/DMA fatal bus error */
    int lc;         /* late collision          */
    int rl;         /* collision retry limit   */
    int un;         /* Tx FIFO underflow       */
    int rfsw_inv;   /* Invalid bit in RFSW     */
    int rfsw_l;     /* RFSW Last in Frame      */
    int rfsw_m;     /* RFSW Miss               */
    int rfsw_bc;    /* RFSW Broadcast          */
    int rfsw_mc;    /* RFSW Multicast          */
    int rfsw_lg;    /* RFSW Length Violation   */
    int rfsw_no;    /* RFSW Non-octet          */
    int rfsw_cr;    /* RFSW Bad CRC            */
    int rfsw_ov;    /* RFSW Overflow           */
    int rfsw_tr;    /* RFSW Truncated          */
} FEC_EVENT_LOG;

#if 0

int 
fec_mii_write( int, int, int);

int 
fec_mii_read(int, int, uint16*);

void
fec_mii_init(int, int);

void
fec_mib_init(void);

void
fec_mib_dump(void);

void
fec_log_init(int);

void
fec_log_dump(int);

void
fec_reg_dump(int);

void
fec_duplex (int, MII_DUPLEX);

void
fec_rmii_speed (int, MII_SPEED);

uint8
fec_hash_address(const uint8*);

void
fec_set_address (const uint8*);

void
fec_reset ( void );

void
fec_init (int, const uint8*);

void
fec_rx_start(int, uint8*, int);

void
fec_rx_continue( void );

void
fec_rx_handler(void);

void
fec0_rx_handler(void);

void
fec1_rx_handler(void);

void
fec_tx_continue( void );

void
fec_tx_stop (int);

void
fec_tx_handler(NIF*, int);

int
fec_send (uint8*, uint8*, uint16 , NBUF*);

int
fec0_send(uint8*, uint8*, uint16 , NBUF*);

int
fec1_send(uint8*, uint8*, uint16 , NBUF*);

void
fec_irq_enable( void );

void
fec_irq_disable(int);

int
fec_eth_start(FEC_CONFIG*, int);

void
fec_eth_stop(int);

#endif

/********************************************************************/

#endif /* _FEC_H_ */
