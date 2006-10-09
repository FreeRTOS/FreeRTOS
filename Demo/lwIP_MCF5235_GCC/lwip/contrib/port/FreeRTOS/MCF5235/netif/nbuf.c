/*
 * Network buffer code based on the MCF523x examples from Freescale.
 *
 * File: $Id: nbuf.c,v 1.2 2006/08/31 22:28:21 wolti Exp $
 */

/* ------------------------ Platform includes ----------------------------- */
#include "mcf5xxx.h"
#include "mcf523x.h"

#include "nbuf.h"

/* ------------------------ Static variables ------------------------------ */

/* Buffer descriptor indexes */
static uint8    tx_bd_idx;
static uint8    rx_bd_idx;

/* Buffer Descriptors -- must be aligned on a 4-byte boundary but a
 * 16-byte boundary is recommended. */
static nbuf_t   tx_nbuf[sizeof( nbuf_t ) * NUM_TXBDS] ATTR_FECMEM;
static nbuf_t   rx_nbuf[sizeof( nbuf_t ) * NUM_RXBDS] ATTR_FECMEM;

/* Data Buffers -- must be aligned on a 16-byte boundary. */
static uint8    tx_buf[TX_BUFFER_SIZE * NUM_TXBDS] ATTR_FECMEM;
static uint8    rx_buf[RX_BUFFER_SIZE * NUM_RXBDS] ATTR_FECMEM;

/* ------------------------ Start implementation -------------------------- */
void
nbuf_init(  )
{

    uint8           i;

    /* Initialize receive descriptor ring */
    for( i = 0; i < NUM_RXBDS; i++ )
    {
        rx_nbuf[i].status = RX_BD_E;
        rx_nbuf[i].length = 0;
        rx_nbuf[i].data = &rx_buf[i * RX_BUFFER_SIZE];
    }

    /* Set the Wrap bit on the last one in the ring */
    rx_nbuf[NUM_RXBDS - 1].status |= RX_BD_W;

    /* Initialize transmit descriptor ring */
    for( i = 0; i < NUM_TXBDS; i++ )
    {
        tx_nbuf[i].status = TX_BD_L | TX_BD_TC;
        tx_nbuf[i].length = 0;
        tx_nbuf[i].data = &tx_buf[i * TX_BUFFER_SIZE];
    }

    /* Set the Wrap bit on the last one in the ring */
    tx_nbuf[NUM_TXBDS - 1].status |= TX_BD_W;

    /* Initialize the buffer descriptor indexes */
    tx_bd_idx = rx_bd_idx = 0;

    return;
}


/********************************************************************/
uint32
nbuf_get_start( uint8 direction )
{
    /*
     * Return the address of the first buffer descriptor in the ring.
     * This routine is needed by the FEC of the MPC860T , MCF5282, and MCF523x
     * in order to write the Rx/Tx descriptor ring start registers
     */
    switch ( direction )
    {
    case NBUF_RX:
        return ( uint32 ) rx_nbuf;
    case NBUF_TX:
    default:
        return ( uint32 ) tx_nbuf;
    }
}


/********************************************************************/
nbuf_t         *
nbuf_rx_allocate(  )
{
    /* This routine alters shared data. Disable interrupts! */
    int             old_ipl = asm_set_ipl( 6 );

    /* Return a pointer to the next empty Rx Buffer Descriptor */
    int             i = rx_bd_idx;


    /* Check to see if the ring of BDs is full */
    if( rx_nbuf[i].status & RX_BD_INUSE )
        return NULL;

    /* Mark the buffer as in use */
    rx_nbuf[i].status |= RX_BD_INUSE;

    /* increment the circular index */
    rx_bd_idx = ( uint8 ) ( ( rx_bd_idx + 1 ) % NUM_RXBDS );

    /* Restore previous IPL */
    asm_set_ipl( old_ipl );

    return &rx_nbuf[i];
}


/********************************************************************/
nbuf_t         *
nbuf_tx_allocate(  )
{
    /* This routine alters shared data. Disable interrupts! */
    int             old_ipl = asm_set_ipl( 6 );

    /* Return a pointer to the next empty Tx Buffer Descriptor */
    int             i = tx_bd_idx;

    /* Check to see if ring of BDs is full */
    if( ( tx_nbuf[i].status & TX_BD_INUSE ) || ( tx_nbuf[i].status & TX_BD_R ) )
        return NULL;

    /* Mark the buffer as Ready (in use) */
    /* FEC must set R bit in transmit routine */
    tx_nbuf[i].status |= TX_BD_INUSE;

    /* increment the circular index */
    tx_bd_idx = ( uint8 ) ( ( tx_bd_idx + 1 ) % NUM_TXBDS );

    /* Restore previous IPL */
    asm_set_ipl( old_ipl );

    return &tx_nbuf[i];
}


/********************************************************************/
void
nbuf_rx_release( nbuf_t * pNbuf )
{
    /* This routine alters shared data. Disable interrupts! */
    int             old_ipl = asm_set_ipl( 6 );

    /* Mark the buffer as empty and not in use */
    pNbuf->status |= RX_BD_E;
    pNbuf->status &= ~RX_BD_INUSE;

    /* Restore previous IPL */
    asm_set_ipl( old_ipl );
}

/********************************************************************/
void
nbuf_tx_release( nbuf_t * pNbuf )
{
    /* This routine alters shared data. Disable interrupts! */
    int             old_ipl = asm_set_ipl( 6 );

    /* Mark the buffer as not in use */
    pNbuf->status &= ~TX_BD_INUSE;

    /* Restore previous IPL */
    asm_set_ipl( old_ipl );
}

/********************************************************************/
int
nbuf_rx_next_ready(  )
{
    /****************************************************************
 This function checks the EMPTY bit of the next Rx buffer to be
 allocated. If the EMPTY bit is cleared, then the next buffer in
 the ring has been filled by the FEC and has not already been
 allocated and passed up the stack. In this case, the next buffer
 in the ring is ready to be allocated. Otherwise, the  buffer is
 either empty or not empty but still in use by a higher level
 protocol. The FEC receive routine uses this function to determine
 if multiple buffers where filled by the FEC during a single
 interrupt event.
 ****************************************************************/

    return ( !( rx_nbuf[rx_bd_idx].status & RX_BD_E ) );
}
