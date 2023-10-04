/******************************************************************************
*
* Copyright (C) 2007 - 2014 Xilinx, Inc.  All rights reserved.
*
* Permission is hereby granted, free of charge, to any person obtaining a copy
* of this software and associated documentation files (the "Software"), to deal
* in the Software without restriction, including without limitation the rights
* to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
* copies of the Software, and to permit persons to whom the Software is
* furnished to do so, subject to the following conditions:
*
* The above copyright notice and this permission notice shall be included in
* all copies or substantial portions of the Software.
*
* Use of the Software is limited solely to applications:
* (a) running on a Xilinx device, or
* (b) that interact with a Xilinx device through a bus or interconnect.
*
* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
* XILINX CONSORTIUM BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
* WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
* OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
* SOFTWARE.
*
* Except as contained in this notice, the name of the Xilinx shall not be used
* in advertising or otherwise to promote the sale, use or other dealings in
* this Software without prior written authorization from Xilinx.
*
******************************************************************************/

#include "lwipopts.h"
#include "xlwipconfig.h"

#if !NO_SYS
    #ifdef OS_IS_XILKERNEL
        #include "xmk.h"
        #include "sys/process.h"
    #endif
#endif

#include "lwip/mem.h"
#include "lwip/stats.h"
#include "lwip/sys.h"
#include "lwip/ip.h"
#include "lwip/tcp.h"
#include "lwip/udp.h"
#include "lwip/tcp_impl.h"

#include "netif/etharp.h"
#include "netif/xadapter.h"

#ifdef XLWIP_CONFIG_INCLUDE_EMACLITE
    #include "netif/xemacliteif.h"
#endif

#ifdef XLWIP_CONFIG_INCLUDE_TEMAC
    #include "netif/xlltemacif.h"
#endif

#ifdef XLWIP_CONFIG_INCLUDE_AXI_ETHERNET
    #include "netif/xaxiemacif.h"
#endif

#ifdef XLWIP_CONFIG_INCLUDE_GEM
    #include "netif/xemacpsif.h"
#endif

#if !NO_SYS
    #include "lwip/tcpip.h"
#endif


/* global lwip debug variable used for debugging */
int lwip_runtime_debug = 0;

void lwip_raw_init()
{
    ip_init();      /* Doesn't do much, it should be called to handle future changes. */
    #if LWIP_UDP
        udp_init(); /* Clears the UDP PCB list. */
    #endif
    #if LWIP_TCP
        tcp_init(); /* Clears the TCP PCB list and clears some internal TCP timers. */
        /* Note: you must call tcp_fasttmr() and tcp_slowtmr() at the */
        /* predefined regular intervals after this initialization. */
    #endif
}

static enum xemac_types find_mac_type( unsigned base )
{
    int i;

    for( i = 0; i < xtopology_n_emacs; i++ )
    {
        if( xtopology[ i ].emac_baseaddr == base )
        {
            return xtopology[ i ].emac_type;
        }
    }

    return xemac_type_unknown;
}

int xtopology_find_index( unsigned base )
{
    int i;

    for( i = 0; i < xtopology_n_emacs; i++ )
    {
        if( xtopology[ i ].emac_baseaddr == base )
        {
            return i;
        }
    }

    return -1;
}

/*
 * xemac_add: this is a wrapper around lwIP's netif_add function.
 * The objective is to provide portability between the different Xilinx MAC's
 * This function can be used to add both xps_ethernetlite and xps_ll_temac
 * based interfaces
 */
struct netif * xemac_add( struct netif * netif,
                          struct ip_addr * ipaddr,
                          struct ip_addr * netmask,
                          struct ip_addr * gw,
                          unsigned char * mac_ethernet_address,
                          unsigned mac_baseaddr )
{
    int i;

    /* set mac address */
    netif->hwaddr_len = 6;

    for( i = 0; i < 6; i++ )
    {
        netif->hwaddr[ i ] = mac_ethernet_address[ i ];
    }

    /* initialize based on MAC type */
    switch( find_mac_type( mac_baseaddr ) )
    {
        case xemac_type_xps_emaclite:
            #ifdef XLWIP_CONFIG_INCLUDE_EMACLITE
                return netif_add( netif, ipaddr, netmask, gw,
                                  ( void * ) mac_baseaddr,
                                  xemacliteif_init,
                                  #if NO_SYS
                                      ethernet_input
                                  #else
                                      tcpip_input
                                  #endif
                                  );
            #else
                return NULL;
            #endif /* ifdef XLWIP_CONFIG_INCLUDE_EMACLITE */
        case xemac_type_xps_ll_temac:
            #ifdef XLWIP_CONFIG_INCLUDE_TEMAC
                return netif_add( netif, ipaddr, netmask, gw,
                                  ( void * ) mac_baseaddr,
                                  xlltemacif_init,
                                  #if NO_SYS
                                      ethernet_input
                                  #else
                                      tcpip_input
                                  #endif
                                  );
            #else
                return NULL;
            #endif /* ifdef XLWIP_CONFIG_INCLUDE_TEMAC */
        case xemac_type_axi_ethernet:
            #ifdef XLWIP_CONFIG_INCLUDE_AXI_ETHERNET
                return netif_add( netif, ipaddr, netmask, gw,
                                  ( void * ) mac_baseaddr,
                                  xaxiemacif_init,
                                  #if NO_SYS
                                      ethernet_input
                                  #else
                                      tcpip_input
                                  #endif
                                  );
            #else
                return NULL;
            #endif /* ifdef XLWIP_CONFIG_INCLUDE_AXI_ETHERNET */
            #ifdef __arm__
                case xemac_type_emacps:
                    #ifdef XLWIP_CONFIG_INCLUDE_GEM
                        return netif_add( netif, ipaddr, netmask, gw,
                                          ( void * ) mac_baseaddr,
                                          xemacpsif_init,
                                          #if NO_SYS
                                              ethernet_input
                                          #else
                                              tcpip_input
                                          #endif

                                          );
                    #endif /* ifdef XLWIP_CONFIG_INCLUDE_GEM */
            #endif /* ifdef __arm__ */
        default:
            printf( "unable to determine type of EMAC with baseaddress 0x%08x\r\n",
                    mac_baseaddr );
            return NULL;
    }
}

#if !NO_SYS

/*
 * The input thread calls lwIP to process any received packets.
 * This thread waits until a packet is received (sem_rx_data_available),
 * and then calls xemacif_input which processes 1 packet at a time.
 */
    void xemacif_input_thread( struct netif * netif )
    {
        struct xemac_s * emac = ( struct xemac_s * ) netif->state;

        while( 1 )
        {
            /* sleep until there are packets to process
             * This semaphore is set by the packet receive interrupt
             * routine.
             */
            sys_arch_sem_wait( &emac->sem_rx_data_available, pdMS_TO_TICKS( 250 ) );

            /* move all received packets to lwIP */
            xemacif_input( netif );
        }
    }
#endif /* if !NO_SYS */

int xemacif_input( struct netif * netif )
{
    struct xemac_s * emac = ( struct xemac_s * ) netif->state;

    SYS_ARCH_DECL_PROTECT( lev );

    int n_packets = 0;

    switch( emac->type )
    {
        case xemac_type_xps_emaclite:
            #ifdef XLWIP_CONFIG_INCLUDE_EMACLITE
                SYS_ARCH_PROTECT( lev );
                n_packets = xemacliteif_input( netif );
                SYS_ARCH_UNPROTECT( lev );
                break;
            #else
                print( "incorrect configuration: xps_ethernetlite drivers not present?" );

                while( 1 )
                {
                }
                return 0;
            #endif /* ifdef XLWIP_CONFIG_INCLUDE_EMACLITE */
        case xemac_type_xps_ll_temac:
            #ifdef XLWIP_CONFIG_INCLUDE_TEMAC
                SYS_ARCH_PROTECT( lev );
                n_packets = xlltemacif_input( netif );
                SYS_ARCH_UNPROTECT( lev );
                break;
            #else
                print( "incorrect configuration: xps_ll_temac drivers not present?" );

                while( 1 )
                {
                }
                return 0;
            #endif /* ifdef XLWIP_CONFIG_INCLUDE_TEMAC */
        case xemac_type_axi_ethernet:
            #ifdef XLWIP_CONFIG_INCLUDE_AXI_ETHERNET
                SYS_ARCH_PROTECT( lev );
                n_packets = xaxiemacif_input( netif );
                SYS_ARCH_UNPROTECT( lev );
                break;
            #else
                print( "incorrect configuration: axi_ethernet drivers not present?" );

                while( 1 )
                {
                }
                return 0;
            #endif /* ifdef XLWIP_CONFIG_INCLUDE_AXI_ETHERNET */
            #ifdef __arm__
                case xemac_type_emacps:
                    #ifdef XLWIP_CONFIG_INCLUDE_GEM
                        SYS_ARCH_PROTECT( lev );
                        n_packets = xemacpsif_input( netif );
                        SYS_ARCH_UNPROTECT( lev );
                        break;
                    #else
                        xil_printf( "incorrect configuration: ps7_ethernet drivers not present?\r\n" );

                        while( 1 )
                        {
                        }
                        return 0;
                    #endif /* ifdef XLWIP_CONFIG_INCLUDE_GEM */
            #endif /* ifdef __arm__ */
        default:
            print( "incorrect configuration: unknown temac type" );

            while( 1 )
            {
            }

            return 0;
    }

    return n_packets;
}
