/*
	FreeRTOS V5.4.1 - Copyright (C) 2009 Real Time Engineers Ltd.

	This file is part of the FreeRTOS distribution.

	FreeRTOS is free software; you can redistribute it and/or modify it	under 
	the terms of the GNU General Public License (version 2) as published by the 
	Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS without being obliged to provide the 
	source code for proprietary components outside of the FreeRTOS kernel.  
	Alternative commercial license and support terms are also available upon 
	request.  See the licensing section of http://www.FreeRTOS.org for full 
	license details.

	FreeRTOS is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


	***************************************************************************
	*                                                                         *
	* Looking for a quick start?  Then check out the FreeRTOS eBook!          *
	* See http://www.FreeRTOS.org/Documentation for details                   *
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

