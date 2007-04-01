/* This source file is part of the ATMEL FREERTOS-0.9.0 Release */

/*This file has been prepared for Doxygen automatic documentation generation.*/
/*! \file *********************************************************************
 *
 * \brief ethernet management for AVR32 UC3.
 *
 * - Compiler:           IAR EWAVR32 and GNU GCC for AVR32
 * - Supported devices:  All AVR32 devices can be used.
 * - AppNote:
 *
 * \author               Atmel Corporation: http://www.atmel.com \n
 *                       Support email: avr32@atmel.com
 *
 *****************************************************************************/

/* Copyright (c) 2007, Atmel Corporation All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * 3. The name of ATMEL may not be used to endorse or promote products derived
 * from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL ``AS IS'' AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE EXPRESSLY AND
 * SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */



#include <string.h>

#include "conf_eth.h"

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo program include files. */
#include "partest.h"
#include "serial.h"


/* ethernet includes */
#include "ethernet.h"
#include "AVR32_EMAC.h"

#if (HTTP_USED == 1)
  #include "BasicWEB.h"
#endif

#if (TFTP_USED == 1)
  #include "BasicTFTP.h"
#endif

#if (SMTP_USED == 1)
  #include "BasicSMTP.h"
#endif

/* lwIP includes */
#include "lwip/sys.h"
#include "lwip/api.h" 
#include "lwip/tcpip.h"
#include "lwip/memp.h" 
#include "lwip/stats.h"
#include "netif/loopif.h"


//_____ M A C R O S ________________________________________________________


//_____ D E F I N I T I O N S ______________________________________________

/* global variable containing MAC Config (hw addr, IP, GW, ...) */
struct netif EMAC_if;

//_____ D E C L A R A T I O N S ____________________________________________

/* Initialisation required by lwIP. */
static void prvlwIPInit( void );

/* Initialisation of ethernet interfaces by reading config file */
static void prvEthernetConfigureInterface(void * param);


/*! \brief create ethernet task, for ethernet management.
 *
 *  \param uxPriority   Input. priority for the task, it should be low
 *
 */
void vStartEthernetTask( unsigned portBASE_TYPE uxPriority )
{
  /* Setup lwIP. */
  prvlwIPInit();

#if (HTTP_USED == 1)
  /* Create the WEB server task.  This uses the lwIP RTOS abstraction layer.*/
  sys_thread_new( vBasicWEBServer, ( void * ) NULL, ethWEBSERVER_PRIORITY );
#endif

#if (TFTP_USED == 1)
  /* Create the TFTP server task.  This uses the lwIP RTOS abstraction layer.*/
  sys_thread_new( vBasicTFTPServer, ( void * ) NULL, ethTFTPSERVER_PRIORITY );
#endif

#if (SMTP_USED == 1)
  /* Create the SMTP Host task.  This uses the lwIP RTOS abstraction layer.*/
  sys_thread_new( vBasicSMTPHost, ( void * ) NULL, ethSMTPHOST_PRIORITY );
#endif

}


/*!
 *  \brief start lwIP layer.
 */
static void prvlwIPInit( void )
{
	/* Initialize lwIP and its interface layer. */
	#if LWIP_STATS
		stats_init();
	#endif

	sys_init();
	mem_init();
	memp_init();
	pbuf_init();
	netif_init();
	
	/* once TCP stack has been initalized, set hw and IP parameters, initialize MACB too */
	tcpip_init( prvEthernetConfigureInterface, NULL );
}

/*!
 *  \brief set ethernet config 
 */
static void prvEthernetConfigureInterface(void * param)
{
struct ip_addr xIpAddr, xNetMask, xGateway;
extern err_t ethernetif_init( struct netif *netif );
portCHAR MacAddress[6];

   /* Default MAC addr. */
   MacAddress[0] = emacETHADDR0;
   MacAddress[1] = emacETHADDR1;
   MacAddress[2] = emacETHADDR2;
   MacAddress[3] = emacETHADDR3;
   MacAddress[4] = emacETHADDR4;
   MacAddress[5] = emacETHADDR5;
   
   /* pass the EMAC address to AVR32_EMAC module */
   vEMACSetMACAddress( MacAddress );
   
   /* set MAC hardware address length to be used by lwIP */
   EMAC_if.hwaddr_len = 6;
   
   /* set MAC hardware address to be used by lwIP */
   memcpy( EMAC_if.hwaddr, MacAddress, EMAC_if.hwaddr_len );
   
   /* Default ip addr. */
   IP4_ADDR( &xIpAddr,emacIPADDR0,emacIPADDR1,emacIPADDR2,emacIPADDR3 );
   
   /* Default Subnet mask. */
   IP4_ADDR( &xNetMask,emacNET_MASK0,emacNET_MASK1,emacNET_MASK2,emacNET_MASK3 );
   
   /* Default Gw addr. */
   IP4_ADDR( &xGateway,emacGATEWAY_ADDR0,emacGATEWAY_ADDR1,emacGATEWAY_ADDR2,emacGATEWAY_ADDR3 );
   
   /* add data to netif */
   netif_add( &EMAC_if, &xIpAddr, &xNetMask, &xGateway, NULL, ethernetif_init, tcpip_input );
   
   /* make it the default interface */
   netif_set_default( &EMAC_if );
   
   /* bring it up */
   netif_set_up( &EMAC_if );
}



