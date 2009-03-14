/*
	FreeRTOS.org V5.2.0 - Copyright (C) 2003-2009 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify it 
	under the terms of the GNU General Public License (version 2) as published
	by the Free Software Foundation and modified by the FreeRTOS exception.

	FreeRTOS.org is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or 
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for 
	more details.

	You should have received a copy of the GNU General Public License along 
	with FreeRTOS.org; if not, write to the Free Software Foundation, Inc., 59 
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.

	A special exception to the GPL is included to allow you to distribute a 
	combined work that includes FreeRTOS.org without being obliged to provide
	the source code for any proprietary components.  See the licensing section
	of http://www.FreeRTOS.org for full details.


	***************************************************************************
	*                                                                         *
	* Get the FreeRTOS eBook!  See http://www.FreeRTOS.org/Documentation      *
	*                                                                         *
	* This is a concise, step by step, 'hands on' guide that describes both   *
	* general multitasking concepts and FreeRTOS specifics. It presents and   *
	* explains numerous examples that are written using the FreeRTOS API.     *
	* Full source code for all the examples is provided in an accompanying    *
	* .zip file.                                                              *
	*                                                                         *
	***************************************************************************

	1 tab == 4 spaces!

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting,
	licensing and training services.
*/

#ifndef BASIC_WEB_SERVER_H
#define BASIC_WEB_SERVER_H

#include <91x_type.h>

/*------------------------------------------------------------------------------*/
/*                            MACROS                                             */
/*------------------------------------------------------------------------------*/
#define basicwebWEBSERVER_PRIORITY      ( tskIDLE_PRIORITY + 2 )

/* The port on which we listen. */
#define webHTTP_PORT		( 80 )

/* Delay on close error. */
#define webSHORT_DELAY		( 10 / portTICK_RATE_MS )

/* The IP address being used. */
#define emacIPADDR0			172
#define emacIPADDR1 		25
#define emacIPADDR2   		218
#define emacIPADDR3   		17

/* The gateway address being used. */
#define emacGATEWAY_ADDR0   10
#define emacGATEWAY_ADDR1   52
#define emacGATEWAY_ADDR2   156
#define emacGATEWAY_ADDR3   254

/* The network mask being used. */
#define emacNET_MASK0 		255
#define emacNET_MASK1 		255
#define emacNET_MASK2 		255
#define emacNET_MASK3 		0

#define STATIC_IP   1
#define DHCP_IP     2

#define lwipBASIC_SERVER_STACK_SIZE	250

/*------------------------------------------------------------------------------*/
/*                            PROTOTYPES                                        */
/*------------------------------------------------------------------------------*/
/* The function that implements the WEB server task. */
void vBasicWEBServer( void *pvParameters );

/* Initialisation required by lwIP. */
void vlwIPInit( void );

void  PrintIPOnLCD(unsigned int ipAddr);

void ToDoAfterGettingIP(bool dhcpStaticFlag);

void InitializeStaticIP(void);

void DelayForDHCPToCome(void);

#endif

