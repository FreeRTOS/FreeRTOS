/* This header file is part of the ATMEL FREERTOS-0.9.0 Release */

/*This file is prepared for Doxygen automatic documentation generation.*/
/*! \file ******************************************************************
 *
 * \brief Ethernet module configuration file.
 *
 * This file contains the possible external configuration of the Ethernet module.
 *
 * - Compiler:           IAR EWAVR32 and GNU GCC for AVR32
 * - Supported devices:  All AVR32 devices can be used.
 * - AppNote:
 *
 * \author               Atmel Corporation: http://www.atmel.com \n
 *                       Support email: avr32@atmel.com
 *
 ***************************************************************************/

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


#ifndef _CONF_ETH_H_
#define _CONF_ETH_H_

/*! define stack size for WEB server task */
#define lwipBASIC_WEB_SERVER_STACK_SIZE   256

/*! define stack size for TFTP server task */
#define lwipBASIC_TFTP_SERVER_STACK_SIZE  1024

/*! define stack size for SMTP host task */
#define lwipBASIC_SMTP_HOST_STACK_SIZE    256

/*! define stack size for lwIP task */
#define lwipINTERFACE_STACK_SIZE          512

/*! define stack size for netif task */
#define netifINTERFACE_TASK_STACK_SIZE    256

/*! define WEB server priority */
#define ethWEBSERVER_PRIORITY             ( tskIDLE_PRIORITY + 2 )

/*! define TFTP server priority */
#define ethTFTPSERVER_PRIORITY            ( tskIDLE_PRIORITY + 3 )

/*! define SMTP host priority */
#define ethSMTPHOST_PRIORITY              ( tskIDLE_PRIORITY + 5 )

/*! define lwIP task priority */
#define lwipINTERFACE_TASK_PRIORITY       ( configMAX_PRIORITIES - 1 )

/*! define netif task priority */
#define netifINTERFACE_TASK_PRIORITY      ( configMAX_PRIORITIES - 1 )

/*! Number of threads that can be started with sys_thread_new() */
#define SYS_THREAD_MAX                      6

/*! LED used by the ethernet task, toggled on each activation */
#define webCONN_LED                         7

/*! Use Auto Negociation to get speed and duplex */
#define ETHERNET_CONF_AN_ENABLE                      1

/*! Do not use auto cross capability */
#define ETHERNET_CONF_AUTO_CROSS_ENABLE              0
/*! use direct cable */
#define ETHERNET_CONF_CROSSED_LINK                   0


/* ethernet default parameters */
/*! MAC address definition.  The MAC address must be unique on the network. */
#define emacETHADDR0                        0x00
#define emacETHADDR1                        0x04
#define emacETHADDR2                        0x25
#define emacETHADDR3                        0x40
#define emacETHADDR4                        0x40
#define emacETHADDR5                        0x40

#if 0
/*! The IP address being used. */
#define emacIPADDR0           10
#define emacIPADDR1           172
#define emacIPADDR2           214
#define emacIPADDR3           40

/*! The gateway address being used. */
#define emacGATEWAY_ADDR0     10
#define emacGATEWAY_ADDR1     172
#define emacGATEWAY_ADDR2     250
#define emacGATEWAY_ADDR3     1

/*! The network mask being used. */
#define emacNET_MASK0         255
#define emacNET_MASK1         255
#define emacNET_MASK2         0
#define emacNET_MASK3         0

#else
/*! The IP address being used. */
#define emacIPADDR0                         192
#define emacIPADDR1                         168
#define emacIPADDR2                         0
#define emacIPADDR3                         2

/*! The gateway address being used. */
#define emacGATEWAY_ADDR0                   192
#define emacGATEWAY_ADDR1                   168
#define emacGATEWAY_ADDR2                   0
#define emacGATEWAY_ADDR3                   1

/*! The network mask being used. */
#define emacNET_MASK0                       255
#define emacNET_MASK1                       255
#define emacNET_MASK2                       255
#define emacNET_MASK3                       0
#endif

#endif
