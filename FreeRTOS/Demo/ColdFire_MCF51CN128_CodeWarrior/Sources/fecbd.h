/*
 * File:    fecbd.h
 * Purpose:     
 *
 * Purpose: Provide a simple buffer management driver
 */

#ifndef _FECBD_H_
#define _FECBD_H_

/********************************************************************/

#define Rx  1
#define Tx  0

/*
 * Buffer sizes in bytes 
 */
#ifndef RX_BUF_SZ
#define RX_BUF_SZ  1520 //2048 
#endif
#ifndef TX_BUF_SZ
#define TX_BUF_SZ  1520
#endif

/* 
 * Buffer Descriptor Format 
 */
#pragma options align= packed
typedef struct
{
    unsigned short status;  /* control and status */
    unsigned short length;  /* transfer length */
    unsigned char  *data;   /* buffer address */
} FECBD;

/*
 * Bit level definitions for status field of buffer descriptors
 */
#define TX_BD_R         0x8000
#define TX_BD_TO1       0x4000
#define TX_BD_W         0x2000
#define TX_BD_TO2       0x1000
#define TX_BD_INTERRUPT 0x1000  /* MCF547x/8x Only */
#define TX_BD_L         0x0800
#define TX_BD_TC        0x0400
#define TX_BD_DEF       0x0200  /* MCF5272 Only */
#define TX_BD_ABC       0x0200
#define TX_BD_HB        0x0100  /* MCF5272 Only */
#define TX_BD_LC        0x0080  /* MCF5272 Only */
#define TX_BD_RL        0x0040  /* MCF5272 Only */
#define TX_BD_UN        0x0002  /* MCF5272 Only */
#define TX_BD_CSL       0x0001  /* MCF5272 Only */

#define RX_BD_E         0x8000
#define RX_BD_R01       0x4000
#define RX_BD_W         0x2000
#define RX_BD_R02       0x1000
#define RX_BD_INTERRUPT 0x1000  /* MCF547x/8x Only */
#define RX_BD_L         0x0800
#define RX_BD_M         0x0100
#define RX_BD_BC        0x0080
#define RX_BD_MC        0x0040
#define RX_BD_LG        0x0020
#define RX_BD_NO        0x0010
#define RX_BD_CR        0x0004
#define RX_BD_OV        0x0002
#define RX_BD_TR        0x0001
#define RX_BD_ERROR     (RX_BD_NO | RX_BD_CR | RX_BD_OV | RX_BD_TR)

/*
 * The following defines are provided by the MCF547x/8x 
 * DMA API.  These are shown here to show their correlation
 * to the other FEC buffer descriptor status bits
 * 
 * #define MCD_FEC_BUF_READY   0x8000
 * #define MCD_FEC_WRAP        0x2000
 * #define MCD_FEC_INTERRUPT   0x1000
 * #define MCD_FEC_END_FRAME   0x0800
 */

/* 
 * Functions provided in fec_bd.c 
 */
int     fecbd_init(int, int, int);
void    fecbd_flush(int);
void    fecbd_dump( void );
unsigned long  fecbd_get_start(int, int);
FECBD*  fecbd_rx_alloc(int);
FECBD*  fecbd_tx_alloc(int);
FECBD*  fecbd_tx_free(int);

/*
 * Error codes
 */
#define ERR_MALLOC      (-1)
#define ERR_NBUFALLOC   (-2)

/*******************************************************************/

#endif /* _FECBD_H_ */
