/*
 * Copyright (c) 2006 Christian Walter
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without modification,
 * are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 * 3. The name of the author may not be used to endorse or promote products
 *    derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT
 * SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT
 * OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING
 * IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY
 * OF SUCH DAMAGE.
 *
 * Author: Christian Walter <wolti@sil.at>
 *
 * TODO:
 *  - Introduce another task create function in the sys_arch layer which allows
 *    for passing the stack size.
 *  - Avoid copying the buffers - this requires changeing the nbuf driver code
 *    to use the lwIP pbuf buffer implementation.
 *
 * File: $Id: fec.c,v 1.3 2006/08/29 18:53:46 wolti Exp $
 */

/* ------------------------ System includes ------------------------------- */
#include <stdlib.h>

/* ------------------------ Platform includes ----------------------------- */
#include "mcf5xxx.h"
#include "mcf523x.h"

#include "nbuf.h"

/* ------------------------ lwIP includes --------------------------------- */
#include "lwip/opt.h"
#include "lwip/def.h"
#include "lwip/mem.h"
#include "lwip/pbuf.h"
#include "lwip/sys.h"
#include "lwip/stats.h"
#include "lwip/debug.h"
#include "netif/etharp.h"

/* ------------------------ Defines --------------------------------------- */
#ifdef FEC_DEBUG
#define FEC_DEBUG_INIT \
    do \
    { \
        MCF_GPIO_PDDR_FECI2C = ( MCF_GPIO_PDDR_FECI2C_PDDR_FECI2C0 | \
                                 MCF_GPIO_PDDR_FECI2C_PDDR_FECI2C1 ); \
    } while( 0 )

#define FEC_DEBUG_RX_TIMING( x ) \
    do \
    { \
        if( x ) \
            MCF_GPIO_PPDSDR_FECI2C = MCF_GPIO_PDDR_FECI2C_PDDR_FECI2C0; \
        else \
            MCF_GPIO_PCLRR_FECI2C = ~( MCF_GPIO_PDDR_FECI2C_PDDR_FECI2C0 ); \
    } while( 0 )

#define FEC_DEBUG_TX_TIMING( x ) \
    do \
    { \
        if( x ) \
            MCF_GPIO_PPDSDR_FECI2C = MCF_GPIO_PDDR_FECI2C_PDDR_FECI2C1; \
        else \
            MCF_GPIO_PCLRR_FECI2C = ~( MCF_GPIO_PDDR_FECI2C_PDDR_FECI2C1 ); \
    } while( 0 )

#else
#define FEC_DEBUG               DBG_OFF
#define FEC_DEBUG_INIT
#define FEC_DEBUG_RX_TIMING( x )
#define FEC_DEBUG_TX_TIMING( x )
#endif

#define MCF_FEC_INT_LEVEL       ( 6 )
#define MCF_FEC_INT_PRIORITY    ( 0 )
#define MCF_FEC_VEC_RXF         ( 64 + 27 )
#define MCF_FEC_MTU             ( 1518 )

#define ETH_ADDR_LEN            ( 6 )

#define TASK_PRIORITY           ( configMAX_PRIORITIES - 1 )

/* ------------------------ Type definitions ------------------------------ */
typedef struct
{
    struct netif   *netif;      /* lwIP network interface. */
    struct eth_addr *self;      /* MAC address of FEC interface. */
    sys_sem_t       tx_sem;     /* Control access to transmitter. */
    sys_sem_t       rx_sem;     /* Semaphore to signal receive thread. */
} mcf523xfec_if_t;

/* ------------------------ Static variables ------------------------------ */
static mcf523xfec_if_t *fecif_g;

/* ------------------------ Static functions ------------------------------ */
static err_t    mcf523xfec_output( struct netif *, struct pbuf *, struct ip_addr * );
static err_t    mcf523xfec_output_raw( struct netif *, struct pbuf * );

static void     mcf523xfec_reset( mcf523xfec_if_t * fecif );
static void     mcf523xfec_enable( mcf523xfec_if_t * fecif );
static void     mcf523xfec_disable( mcf523xfec_if_t * fecif );
static void     mcf523xfec_get_mac( mcf523xfec_if_t * fecif, struct eth_addr *mac );
static void     mcf523xfec_rx_irq( void );
static void     mcf523xfec_rx_task( void *arg );

static void     arp_timer( void *arg );
static void     eth_input( struct netif *netif, struct pbuf *p );

/* ------------------------ Start implementation -------------------------- */

static void
arp_timer( void *arg )
{
    ( void )arg;
    etharp_tmr(  );
    sys_timeout( ARP_TMR_INTERVAL, arp_timer, NULL );
}

err_t
mcf523xfec_output_raw( struct netif *netif, struct pbuf *p )
{
    err_t           res;
    nbuf_t         *pNBuf;
    mcf523xfec_if_t *fecif = netif->state;
    int             i;
    struct pbuf    *q;

#if ETH_PAD_SIZE
    pbuf_header( p, -ETH_PAD_SIZE );    /* drop the padding word */
#endif


    /* Test if we can handle such big frames. If not drop it. */
    if( p->tot_len > MCF_FEC_MTU )
    {
#if LINK_STATS
        lwip_stats.link.lenerr++;
#endif
        res = ERR_BUF;
    }
    /* Test if our network buffer scheme can handle a packet of this size. If
     * not drop it and return a memory error. */
    else if( p->tot_len > TX_BUFFER_SIZE )
    {
#ifdef LINK_STATS
        lwip_stats.link.memerr++;
#endif
        res = ERR_MEM;
    }
    /* Allocate a transmit buffer. If no buffer is available drop the frame. */
    else if( ( pNBuf = nbuf_tx_allocate(  ) ) == NULL )
    {
        LWIP_ASSERT( "mcf523xfec_output_raw: pNBuf != NULL\n", pNBuf != NULL );
#ifdef LINK_STATS
        lwip_stats.link.memerr++;
#endif
        res = ERR_MEM;
    }
    else
    {
        q = p;
        i = 0;
        do
        {
            memcpy( &pNBuf->data[i], q->payload, q->len );
            i += q->len;
        }
        while( ( q = q->next ) != NULL );
        pNBuf->length = p->tot_len;

        /* Set Frame ready for transmission. */
        pNBuf->status |= TX_BD_R;
        /* Mark the buffer as not in use so the FEC can take it. */
        nbuf_tx_release( pNBuf );
        /* Indicate that a new transmit buffer has been produced. */
        MCF_FEC_TDAR = 1;
#if LINK_STATS
        lwip_stats.link.xmit++;
#endif
        res = ERR_OK;
    }

    sys_sem_signal( fecif->tx_sem );
#if ETH_PAD_SIZE
    buf_header( p, ETH_PAD_SIZE );
#endif

    return res;
}

/* This function is called by the TCP/IP stack when an IP packet should be
 * sent. It uses the ethernet ARP module provided by lwIP to resolve the
 * destination MAC address. The ARP module will later call our low level
 * output function mcf523xfec_output_raw.
 */
err_t
mcf523xfec_output( struct netif * netif, struct pbuf * p, struct ip_addr * ipaddr )
{
    err_t           res;
    mcf523xfec_if_t *fecif = netif->state;

    FEC_DEBUG_TX_TIMING( 1 );
    /* Make sure only one thread is in this function. */
    sys_sem_wait( fecif->tx_sem );
    res = etharp_output( netif, ipaddr, p );
    FEC_DEBUG_TX_TIMING( 0 );
    return res;
}

void
mcf523xfec_rx_task( void *arg )
{
    mcf523xfec_if_t *fecif = arg;
    struct pbuf    *p, *q;
    nbuf_t         *pNBuf;
    uint8          *pPayLoad;

    do
    {
        sys_sem_wait( fecif->rx_sem );
        while( nbuf_rx_next_ready(  ) )
        {
            pNBuf = nbuf_rx_allocate(  );
            if( pNBuf != NULL )
            {
                LWIP_ASSERT( "mcf523xfec_rx_task: pNBuf->status & RX_BD_L ",
                             pNBuf->status & RX_BD_L );

                /* This flags indicate that the frame has been damaged. In
                 * this case we must update the link stats if enabled and
                 * remove the frame from the FEC. */
                if ( pNBuf->status & ( RX_BD_LG | RX_BD_NO |
                                       RX_BD_CR | RX_BD_OV ) )
                {
#ifdef LINK_STATS
                    lwip_stats.link.drop++;
                    if ( pNBuf->status & RX_BD_LG)
                    {
                        lwip_stats.link.lenerr++;
                    }
                    else if ( pNBuf->status & ( RX_BD_NO | RX_BD_OV ) )
                    {
                        lwip_stats.link.err++;
                    }
                    else
                    {
                        lwip_stats.link.chkerr++;
                    }
#endif
                }
                else
                {
                    /* The frame must no be valid. Perform some checks to see if the FEC
                     * driver is working correctly.
                     */
                    LWIP_ASSERT( "mcf523xfec_rx_task: pNBuf->length != 0", pNBuf->length != 0 );
                    p = pbuf_alloc( PBUF_RAW, pNBuf->length, PBUF_POOL );
                    if( p != NULL )
                    {
#if ETH_PAD_SIZE
                        pbuf_header( p, -ETH_PAD_SIZE );
#endif
                        pPayLoad = pNBuf->data;
                        for( q = p; q != NULL; q = q->next )
                        {
                            memcpy( q->payload, pPayLoad, q->len );
                            pPayLoad += q->len;
                        }
#if ETH_PAD_SIZE
                        pbuf_header( p, ETH_PAD_SIZE );
#endif

                        /* Ethernet frame received. Handling it is not device
                         * dependent and therefore done in another function.
                         */
                        eth_input( fecif->netif, p );
                    }
                }
                nbuf_rx_release( pNBuf );

                /* Tell the HW that there are new free RX buffers. */
                MCF_FEC_RDAR = 1;
            }
            else
            {
#if LINK_STATS
                lwip_stats.link.memerr++;
                lwip_stats.link.drop++;
#endif
            }
        }
        /* Set RX Debug PIN to low since handling of next frame is possible. */
        FEC_DEBUG_RX_TIMING( 0 );
    }
    while( 1 );
}

void
eth_input( struct netif *netif, struct pbuf *p )
{
    struct eth_hdr *eth_hdr = p->payload;

    LWIP_ASSERT( "eth_input: p != NULL ", p != NULL );

    switch ( htons( eth_hdr->type ) )
    {
    case ETHTYPE_IP:
        /* Pass to ARP layer. */
        etharp_ip_input( netif, p );

        /* Skip Ethernet header. */
        pbuf_header( p, ( s16_t ) - sizeof( struct eth_hdr ) );

        /* Pass to network layer. */
        netif->input( p, netif );
        break;

    case ETHTYPE_ARP:
        /* Pass to ARP layer. */
        etharp_arp_input( netif, ( struct eth_addr * )netif->hwaddr, p );
        break;

    default:
        pbuf_free( p );
        break;
    }
}

void
mcf523xfec_rx_irq( void )
{
    static portBASE_TYPE xNeedSwitch = pdFALSE;

    /* Workaround GCC if frame pointers are enabled. This is an ISR and
     * we must not modify the stack before portENTER_SWITCHING_ISR( )
     * has been called. */
#if _GCC_USES_FP == 1
    asm volatile    ( "unlk %fp\n\t" );
#endif

    /* This ISR can cause a context switch, so the first statement must be
     * a call to the portENTER_SWITCHING_ISR() macro.
     */
    portENTER_SWITCHING_ISR(  );

    /* Set Debug PIN to high to measure RX latency. */
    FEC_DEBUG_RX_TIMING( 1 );

    /* Clear FEC RX Event from the Event Register (by writing 1) */
    if( MCF_FEC_EIR & ( MCF_FEC_EIR_RXB | MCF_FEC_EIR_RXF ) )
    {
        /* Clear interrupt from EIR register immediately */
        MCF_FEC_EIR = ( MCF_FEC_EIR_RXB | MCF_FEC_EIR_RXF );
        xNeedSwitch = xSemaphoreGiveFromISR( fecif_g->rx_sem, pdFALSE );
    }
    portEXIT_SWITCHING_ISR( xNeedSwitch );
}

void
mcf523xfec_reset( mcf523xfec_if_t * fecif )
{
    extern void     ( *__RAMVEC[] ) (  );

    int             old_ipl = asm_set_ipl( 7 );

    /* Reset the FEC - equivalent to a hard reset */
    MCF_FEC_ECR = MCF_FEC_ECR_RESET;

    /* Wait for the reset sequence to complete */
    while( MCF_FEC_ECR & MCF_FEC_ECR_RESET );

    /* Disable all FEC interrupts by clearing the EIMR register */
    MCF_FEC_EIMR = 0;

    /* Clear any interrupts by setting all bits in the EIR register */
    MCF_FEC_EIR = 0xFFFFFFFFUL;

    /* Configure Interrupt vectors. */
    __RAMVEC[MCF_FEC_VEC_RXF] = mcf523xfec_rx_irq;

    /* Set the source address for the controller */
    MCF_FEC_PALR =
        ( fecif->self->addr[0] << 24U ) | ( fecif->self->addr[1] << 16U ) |
        ( fecif->self->addr[2] << 8U ) | ( fecif->self->addr[3] << 0U );
    MCF_FEC_PAUR = ( fecif->self->addr[4] << 24U ) | ( fecif->self->addr[5] << 16U );

    /* Initialize the hash table registers */
    MCF_FEC_IAUR = 0;
    MCF_FEC_IALR = 0;

    /* Set Receive Buffer Size */
#if RX_BUFFER_SIZE != 2048
#error "RX_BUFFER_SIZE must be set to 2048 for safe FEC operation."
#endif
    MCF_FEC_EMRBR = RX_BUFFER_SIZE - 1;

    /* Point to the start of the circular Rx buffer descriptor queue */
    MCF_FEC_ERDSR = nbuf_get_start( NBUF_RX );

    /* Point to the start of the circular Tx buffer descriptor queue */
    MCF_FEC_ETDSR = nbuf_get_start( NBUF_TX );

    /* Set the tranceiver interface to MII mode */
    MCF_FEC_RCR = MCF_FEC_RCR_MAX_FL( MCF_FEC_MTU ) | MCF_FEC_RCR_MII_MODE;

    /* Set MII Speed Control Register for 2.5Mhz */
    MCF_FEC_MSCR = MCF_FEC_MSCR_MII_SPEED( FSYS_2 / ( 2UL * 2500000UL ) );

    /* Only operate in half-duplex, no heart beat control */
    MCF_FEC_TCR = 0;

    /* Enable Debug support */
    FEC_DEBUG_INIT;
    FEC_DEBUG_RX_TIMING( 0 );
    FEC_DEBUG_TX_TIMING( 0 );
    ( void )asm_set_ipl( old_ipl );
}

void
mcf523xfec_get_mac( mcf523xfec_if_t * hw, struct eth_addr *mac )
{
    int             i;
    static const struct eth_addr mac_default = {
        {0x00, 0xCF, 0x52, 0x35, 0x00, 0x01}
    };

    ( void )hw;

    for( i = 0; i < ETH_ADDR_LEN; i++ )
    {
        mac->addr[i] = mac_default.addr[i];
    }
}

void
mcf523xfec_enable( mcf523xfec_if_t * fecif )
{
    ( void )fecif;

    int             old_ipl = asm_set_ipl( 7 );

    /* Configure I/O pins for the FEC. */
    MCF_GPIO_PAR_FECI2C = ( MCF_GPIO_PAR_FECI2C_PAR_EMDC_FEC | MCF_GPIO_PAR_FECI2C_PAR_EMDIO_FEC );

    /* Allow interrupts by setting IMR register */
    MCF_FEC_EIMR = MCF_FEC_EIMR_RXF;

    /* Configure the interrupt controller. */
    MCF_INTC0_ICR27 = ( MCF_INTC0_ICRn_IL( MCF_FEC_INT_LEVEL ) |
                        MCF_INTC0_ICRn_IP( MCF_FEC_INT_PRIORITY ) );
    MCF_INTC0_IMRL &= ~( MCF_INTC0_IMRL_INT_MASK27 | MCF_INTC0_IMRL_MASKALL );

    /* Enable FEC */
    MCF_FEC_ECR = MCF_FEC_ECR_ETHER_EN;

    /* Indicate that there have been empty receive buffers produced */
    MCF_FEC_RDAR = 1;
    ( void )asm_set_ipl( old_ipl );
}

void
mcf523xfec_disable( mcf523xfec_if_t * fecif )
{
    ( void )fecif;

    int             old_ipl = asm_set_ipl( 7 );

    /* Set the Graceful Transmit Stop bit */
    MCF_FEC_TCR = ( MCF_FEC_TCR | MCF_FEC_TCR_GTS );

    /* Wait for the current transmission to complete */
    while( !( MCF_FEC_EIR & MCF_FEC_EIR_GRA ) );

    /* Clear the GRA event */
    MCF_FEC_EIR = MCF_FEC_EIR_GRA;

    /* Disable the FEC */
    MCF_FEC_ECR = 0;

    /* Disable all FEC interrupts by clearing the IMR register */
    MCF_FEC_EIMR = 0;

    /* Unconfigure the interrupt controller. */
    MCF_INTC0_ICR27 = MCF_INTC0_ICRn_IL( 0 ) | MCF_INTC0_ICRn_IP( 0 );
    MCF_INTC0_IMRL |= MCF_INTC0_IMRL_INT_MASK27;

    /* Clear the GTS bit so frames can be tranmitted when restarted */
    MCF_FEC_TCR = ( MCF_FEC_TCR & ~MCF_FEC_TCR_GTS );

    /* Disable I/O pins used by the FEC. */
    MCF_GPIO_PAR_FECI2C &= ~( MCF_GPIO_PAR_FECI2C_PAR_EMDC_FEC |
                              MCF_GPIO_PAR_FECI2C_PAR_EMDIO_FEC );
    ( void )asm_set_ipl( old_ipl );
}

err_t
mcf523xfec_init( struct netif *netif )
{
    err_t           res;

    mcf523xfec_if_t *fecif = mem_malloc( sizeof( mcf523xfec_if_t ) );

    if( fecif != NULL )
    {
        /* Global copy used in ISR. */
        fecif_g = fecif;
        fecif->self = ( struct eth_addr * )&netif->hwaddr[0];
        fecif->netif = netif;
        fecif->tx_sem = NULL;
        fecif->rx_sem = NULL;

        if( ( fecif->tx_sem = sys_sem_new( 1 ) ) == NULL )
        {
            res = ERR_MEM;
        }
        else if( ( fecif->rx_sem = sys_sem_new( 0 ) ) == NULL )
        {
            res = ERR_MEM;
        }
        else if( sys_thread_new( mcf523xfec_rx_task, fecif, TASK_PRIORITY ) == NULL )
        {
            res = ERR_MEM;
        }
        else
        {
            netif->state = fecif;
            netif->name[0] = 'C';
            netif->name[1] = 'F';
            netif->hwaddr_len = ETH_ADDR_LEN;
            netif->mtu = MCF_FEC_MTU;
            netif->flags = NETIF_FLAG_BROADCAST;
            netif->output = mcf523xfec_output;
            netif->linkoutput = mcf523xfec_output_raw;

            nbuf_init(  );
            mcf523xfec_get_mac( fecif, fecif->self );
            mcf523xfec_reset( fecif );
            mcf523xfec_enable( fecif );

            etharp_init(  );
            sys_timeout( ARP_TMR_INTERVAL, arp_timer, NULL );

            res = ERR_OK;
        }

        if( res != ERR_OK )
        {
            free( fecif );
            if( fecif->tx_sem != NULL )
            {
                mem_free( fecif->tx_sem );
            }
            if( fecif->rx_sem != NULL )
            {
                mem_free( fecif->rx_sem );
            }
        }
    }
    else
    {
        res = ERR_MEM;
    }

    return res;
}
