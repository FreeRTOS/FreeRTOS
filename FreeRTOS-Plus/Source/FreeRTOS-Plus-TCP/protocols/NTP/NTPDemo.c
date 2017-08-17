/*
 * FreeRTOS+TCP Labs Build 160919 (C) 2016 Real Time Engineers ltd.
 * Authors include Hein Tibosch and Richard Barry
 *
 *******************************************************************************
 ***** NOTE ******* NOTE ******* NOTE ******* NOTE ******* NOTE ******* NOTE ***
 ***                                                                         ***
 ***                                                                         ***
 ***   FREERTOS+TCP IS STILL IN THE LAB (mainly because the FTP and HTTP     ***
 ***   demos have a dependency on FreeRTOS+FAT, which is only in the Labs    ***
 ***   download):                                                            ***
 ***                                                                         ***
 ***   FreeRTOS+TCP is functional and has been used in commercial products   ***
 ***   for some time.  Be aware however that we are still refining its       ***
 ***   design, the source code does not yet quite conform to the strict      ***
 ***   coding and style standards mandated by Real Time Engineers ltd., and  ***
 ***   the documentation and testing is not necessarily complete.            ***
 ***                                                                         ***
 ***   PLEASE REPORT EXPERIENCES USING THE SUPPORT RESOURCES FOUND ON THE    ***
 ***   URL: http://www.FreeRTOS.org/contact  Active early adopters may, at   ***
 ***   the sole discretion of Real Time Engineers Ltd., be offered versions  ***
 ***   under a license other than that described below.                      ***
 ***                                                                         ***
 ***                                                                         ***
 ***** NOTE ******* NOTE ******* NOTE ******* NOTE ******* NOTE ******* NOTE ***
 *******************************************************************************
 *
 * FreeRTOS+TCP can be used under two different free open source licenses.  The
 * license that applies is dependent on the processor on which FreeRTOS+TCP is
 * executed, as follows:
 *
 * If FreeRTOS+TCP is executed on one of the processors listed under the Special
 * License Arrangements heading of the FreeRTOS+TCP license information web
 * page, then it can be used under the terms of the FreeRTOS Open Source
 * License.  If FreeRTOS+TCP is used on any other processor, then it can be used
 * under the terms of the GNU General Public License V2.  Links to the relevant
 * licenses follow:
 *
 * The FreeRTOS+TCP License Information Page: http://www.FreeRTOS.org/tcp_license
 * The FreeRTOS Open Source License: http://www.FreeRTOS.org/license
 * The GNU General Public License Version 2: http://www.FreeRTOS.org/gpl-2.0.txt
 *
 * FreeRTOS+TCP is distributed in the hope that it will be useful.  You cannot
 * use FreeRTOS+TCP unless you agree that you use the software 'as is'.
 * FreeRTOS+TCP is provided WITHOUT ANY WARRANTY; without even the implied
 * warranties of NON-INFRINGEMENT, MERCHANTABILITY or FITNESS FOR A PARTICULAR
 * PURPOSE. Real Time Engineers Ltd. disclaims all conditions and terms, be they
 * implied, expressed, or statutory.
 *
 * 1 tab == 4 spaces!
 *
 * http://www.FreeRTOS.org
 * http://www.FreeRTOS.org/plus
 * http://www.FreeRTOS.org/labs
 *
 */

/*
 * NTPDemo.c
 *
 * An example of how to lookup a domain using DNS
 * And also how to send and receive UDP messages to get the NTP time
 *
 */

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_DNS.h"
#include "FreeRTOS_Stream_Buffer.h"

/* Use the date & time functions from +FAT. */
#include "ff_time.h"

#include "NTPDemo.h"
#include "ntpClient.h"

#include "date_and_time.h"

enum EStatus {
	EStatusLookup,
	EStatusAsking,
	EStatusPause,
	EStatusFailed,
};

static struct SNtpPacket xNTPPacket;

#if( ipconfigUSE_CALLBACKS == 0 )
	static char cRecvBuffer[ sizeof( struct SNtpPacket ) + 64 ];
#endif

static enum EStatus xStatus = EStatusLookup;

static const char *pcTimeServers[] = {
	"0.asia.pool.ntp.org",
	"0.europe.pool.ntp.org",
	"0.id.pool.ntp.org",
	"0.south-america.pool.ntp.org",
	"0.oceania.pool.ntp.org",
	"0.north-america.pool.ntp.org"
};

static SemaphoreHandle_t xNTPWakeupSem = NULL;
static uint32_t ulIPAddressFound;
static Socket_t xUDPSocket = NULL;
static TaskHandle_t xNTPTaskhandle = NULL;
static TickType_t uxSendTime;

static void prvNTPTask( void *pvParameters );

static void vSignalTask( void )
{
	#if( ipconfigUSE_CALLBACKS == 0 )
	if( xUDPSocket != NULL )
	{
		/* Send a signal to the socket so that the
		FreeRTOS_recvfrom will get interrupted. */
		FreeRTOS_SignalSocket( xUDPSocket );
	}
	else
	#endif
	if( xNTPWakeupSem != NULL )
	{
		xSemaphoreGive( xNTPWakeupSem );
	}
}

void vStartNTPTask( uint16_t usTaskStackSize, UBaseType_t uxTaskPriority )
{
	/* The only public function in this module: start a task to contact
	some NTP server. */

	if( xNTPTaskhandle != NULL )
	{
		switch( xStatus )
		{
		case EStatusPause:
			xStatus = EStatusAsking;
			vSignalTask();
			break;
		case EStatusLookup:
			FreeRTOS_printf( ( "NTP looking up server\n" ) );
			break;
		case EStatusAsking:
			FreeRTOS_printf( ( "NTP still asking\n" ) );
			break;
		case EStatusFailed:
			FreeRTOS_printf( ( "NTP failed somehow\n" ) );
			ulIPAddressFound = 0ul;
			xStatus = EStatusLookup;
			vSignalTask();
			break;
		}
	}
	else
	{
		xUDPSocket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP );
		if( xUDPSocket != NULL )
		{
		struct freertos_sockaddr xAddress;
		#if( ipconfigUSE_CALLBACKS != 0 )
			BaseType_t xReceiveTimeOut = pdMS_TO_TICKS( 0 );
		#else
			BaseType_t xReceiveTimeOut = pdMS_TO_TICKS( 5000 );
		#endif

			xAddress.sin_addr = 0ul;
			xAddress.sin_port = FreeRTOS_htons( NTP_PORT );

			FreeRTOS_bind( xUDPSocket, &xAddress, sizeof( xAddress ) );
			FreeRTOS_setsockopt( xUDPSocket, 0, FREERTOS_SO_RCVTIMEO, &xReceiveTimeOut, sizeof( xReceiveTimeOut ) );
			xTaskCreate( 	prvNTPTask,						/* The function that implements the task. */
							( const char * ) "NTP client",	/* Just a text name for the task to aid debugging. */
							usTaskStackSize,				/* The stack size is defined in FreeRTOSIPConfig.h. */
							NULL,							/* The task parameter, not used in this case. */
							uxTaskPriority,					/* The priority assigned to the task is defined in FreeRTOSConfig.h. */
							&xNTPTaskhandle );				/* The task handle. */
		}
		else
		{
			FreeRTOS_printf( ( "Creating socket failed\n" ) );
		}
	}
}
/*-----------------------------------------------------------*/

static void vDNS_callback( const char *pcName, void *pvSearchID, uint32_t ulIPAddress )
{
char pcBuf[16];

	/* The DNS lookup has a result, or it has reached the time-out. */
	FreeRTOS_inet_ntoa( ulIPAddress, pcBuf );
	FreeRTOS_printf( ( "IP address of %s found: %s\n", pcName, pcBuf ) );
	if( ulIPAddressFound == 0ul )
	{
		ulIPAddressFound = ulIPAddress;
	}
	/* For testing: in case DNS doen't respond, still try some NTP server
	with a known IP-address. */
	if( ulIPAddressFound == 0ul )
	{
		ulIPAddressFound = FreeRTOS_inet_addr_quick( 184, 105, 182, 7 );
/*		ulIPAddressFound = FreeRTOS_inet_addr_quick( 103, 242,  70, 4 );	*/
	}
	xStatus = EStatusAsking;

	vSignalTask();
}
/*-----------------------------------------------------------*/

static void prvSwapFields( struct SNtpPacket *pxPacket)
{
	/* NTP messages are big-endian */
	pxPacket->rootDelay = FreeRTOS_htonl( pxPacket->rootDelay );
	pxPacket->rootDispersion = FreeRTOS_htonl( pxPacket->rootDispersion );

	pxPacket->referenceTimestamp.seconds = FreeRTOS_htonl( pxPacket->referenceTimestamp.seconds );
	pxPacket->referenceTimestamp.fraction = FreeRTOS_htonl( pxPacket->referenceTimestamp.fraction );

	pxPacket->originateTimestamp.seconds = FreeRTOS_htonl( pxPacket->originateTimestamp.seconds );
	pxPacket->originateTimestamp.fraction = FreeRTOS_htonl( pxPacket->originateTimestamp.fraction );

	pxPacket->receiveTimestamp.seconds = FreeRTOS_htonl( pxPacket->receiveTimestamp.seconds );
	pxPacket->receiveTimestamp.fraction = FreeRTOS_htonl( pxPacket->receiveTimestamp.fraction );

	pxPacket->transmitTimestamp.seconds = FreeRTOS_htonl( pxPacket->transmitTimestamp.seconds );
	pxPacket->transmitTimestamp.fraction = FreeRTOS_htonl( pxPacket->transmitTimestamp.fraction );
}
/*-----------------------------------------------------------*/

static void prvNTPPacketInit( )
{
	memset (&xNTPPacket, '\0', sizeof( xNTPPacket ) );

	xNTPPacket.flags = 0xDB;				/* value 0xDB : mode 3 (client), version 3, leap indicator unknown 3 */
	xNTPPacket.poll = 10;					/* 10 means 1 << 10 = 1024 seconds */
	xNTPPacket.precision = 0xFA;			/* = 250 = 0.015625 seconds */
	xNTPPacket.rootDelay = 0x5D2E;			/* 0x5D2E = 23854 or (23854/65535)= 0.3640 sec */
	xNTPPacket.rootDispersion = 0x0008CAC8;	/* 0x0008CAC8 = 8.7912  seconds */

	/* use the recorded NTP time */
	time_t uxSecs = FreeRTOS_time( NULL );/* apTime may be NULL, returns seconds */

	xNTPPacket.referenceTimestamp.seconds = uxSecs;	/* Current time */
	xNTPPacket.transmitTimestamp.seconds = uxSecs + 3;

	/* Transform the contents of the fields from native to big endian. */
	prvSwapFields( &xNTPPacket );
}
/*-----------------------------------------------------------*/

static void prvReadTime( struct SNtpPacket * pxPacket )
{
	FF_TimeStruct_t xTimeStruct;
	time_t uxPreviousSeconds;
	time_t uxPreviousMS;

	time_t uxCurrentSeconds;
	time_t uxCurrentMS;

	const char *pcTimeUnit;
	int32_t ilDiff;
	TickType_t uxTravelTime;

	uxTravelTime = xTaskGetTickCount() - uxSendTime;

	/* Transform the contents of the fields from big to native endian. */
	prvSwapFields( pxPacket );

	uxCurrentSeconds = pxPacket->receiveTimestamp.seconds - TIME1970;
	uxCurrentMS = pxPacket->receiveTimestamp.fraction / 4294967;
	uxCurrentSeconds += uxCurrentMS / 1000;
	uxCurrentMS = uxCurrentMS % 1000;

	// Get the last time recorded
	uxPreviousSeconds = FreeRTOS_get_secs_msec( &uxPreviousMS );

	// Set the new time with precision in msec. */
	FreeRTOS_set_secs_msec( &uxCurrentSeconds, &uxCurrentMS );

	if( uxCurrentSeconds >= uxPreviousSeconds )
	{
		ilDiff = ( int32_t ) ( uxCurrentSeconds - uxPreviousSeconds );
	}
	else
	{
		ilDiff = 0 - ( int32_t ) ( uxPreviousSeconds - uxCurrentSeconds );
	}

	if( ( ilDiff < -5 ) || ( ilDiff > 5 ) )
	{
		/* More than 5 seconds difference. */
		pcTimeUnit = "sec";
	}
	else
	{
		/* Less than or equal to 5 second difference. */
		pcTimeUnit = "ms";
		uint32_t ulLowest = ( uxCurrentSeconds <= uxPreviousSeconds ) ? uxCurrentSeconds : uxPreviousSeconds;
		int32_t iCurMS = 1000 * ( uxCurrentSeconds - ulLowest ) + uxCurrentMS;
		int32_t iPrevMS = 1000 * ( uxPreviousSeconds - ulLowest ) + uxPreviousMS;
		ilDiff = iCurMS - iPrevMS;
	}
	uxCurrentSeconds -= iTimeZone;

	FreeRTOS_gmtime_r( &uxCurrentSeconds, &xTimeStruct );

	/*
		378.067 [NTP client] NTP time: 9/11/2015 16:11:19.559 Diff -20 ms (289 ms)
		379.441 [NTP client] NTP time: 9/11/2015 16:11:20.933 Diff 0 ms (263 ms)
	*/

	FreeRTOS_printf( ("NTP time: %d/%d/%02d %2d:%02d:%02d.%03u Diff %d %s (%lu ms)\n",
		xTimeStruct.tm_mday,
		xTimeStruct.tm_mon + 1,
		xTimeStruct.tm_year + 1900,
		xTimeStruct.tm_hour,
		xTimeStruct.tm_min,
		xTimeStruct.tm_sec,
		( unsigned )uxCurrentMS,
		( unsigned )ilDiff,
		pcTimeUnit,
		uxTravelTime ) );

	/* Remove compiler warnings in case FreeRTOS_printf() is not used. */
	( void ) pcTimeUnit;
	( void ) uxTravelTime;
}
/*-----------------------------------------------------------*/

#if( ipconfigUSE_CALLBACKS != 0 )

	static BaseType_t xOnUDPReceive( Socket_t xSocket, void * pvData, size_t xLength,
		const struct freertos_sockaddr *pxFrom, const struct freertos_sockaddr *pxDest )
	{
		if( xLength >= sizeof( xNTPPacket ) )
		{
			prvReadTime( ( struct SNtpPacket *)pvData );
			if( xStatus != EStatusPause )
			{
				xStatus = EStatusPause;
			}
		}
		vSignalTask();
		/* Tell the driver not to store the RX data */
		return 1;
	}
	/*-----------------------------------------------------------*/

#endif	/* ipconfigUSE_CALLBACKS != 0 */

static void prvNTPTask( void *pvParameters )
{
BaseType_t xServerIndex = 3;
struct freertos_sockaddr xAddress;
#if( ipconfigUSE_CALLBACKS != 0 )
	F_TCP_UDP_Handler_t xHandler;
#endif /* ipconfigUSE_CALLBACKS != 0 */

	xStatus = EStatusLookup;
	#if( ipconfigSOCKET_HAS_USER_SEMAPHORE != 0 ) || ( ipconfigUSE_CALLBACKS != 0 )
	{
		xNTPWakeupSem = xSemaphoreCreateBinary();
	}
	#endif

	#if( ipconfigUSE_CALLBACKS != 0 )
	{
		memset( &xHandler, '\0', sizeof( xHandler ) );
		xHandler.pxOnUDPReceive = xOnUDPReceive;
		FreeRTOS_setsockopt( xUDPSocket, 0, FREERTOS_SO_UDP_RECV_HANDLER, ( void * ) &xHandler, sizeof( xHandler ) );
	}
	#endif
	#if( ipconfigSOCKET_HAS_USER_SEMAPHORE != 0 )
	{
		FreeRTOS_setsockopt( xUDPSocket, 0, FREERTOS_SO_SET_SEMAPHORE, ( void * ) &xNTPWakeupSem, sizeof( xNTPWakeupSem ) );
	}
	#endif
	for( ; ; )
	{
		switch( xStatus )
		{
		case EStatusLookup:
			if( ( ulIPAddressFound == 0ul ) || ( ulIPAddressFound == ~0ul ) )
			{
				if( ++xServerIndex == sizeof( pcTimeServers ) / sizeof( pcTimeServers[ 0 ] ) )
				{
					xServerIndex = 0;
				}
				FreeRTOS_printf( ( "Looking up server '%s'\n", pcTimeServers[ xServerIndex ] ) );
				FreeRTOS_gethostbyname_a( pcTimeServers[ xServerIndex ], vDNS_callback, (void *)NULL, 1200 );
			}
			else
			{
				xStatus = EStatusAsking;
			}
			break;

		case EStatusAsking:
			{
			char pcBuf[16];

				prvNTPPacketInit( );
				xAddress.sin_addr = ulIPAddressFound;
				xAddress.sin_port = FreeRTOS_htons( NTP_PORT );

				FreeRTOS_inet_ntoa( xAddress.sin_addr, pcBuf );
				FreeRTOS_printf( ( "Sending UDP message to %s:%u\n",
					pcBuf,
					FreeRTOS_ntohs( xAddress.sin_port ) ) );

				uxSendTime = xTaskGetTickCount( );
				FreeRTOS_sendto( xUDPSocket, ( void * )&xNTPPacket, sizeof( xNTPPacket ), 0, &xAddress, sizeof( xAddress ) );
			}
			break;

		case EStatusPause:
			break;

		case EStatusFailed:
			break;
		}

		#if( ipconfigUSE_CALLBACKS != 0 )
		{
			xSemaphoreTake( xNTPWakeupSem, 5000 );
		}
		#else
		{
		uint32_t xAddressSize;
		BaseType_t xReturned;

			xAddressSize = sizeof( xAddress );
			xReturned = FreeRTOS_recvfrom( xUDPSocket, ( void * ) cRecvBuffer, sizeof( cRecvBuffer ), 0, &xAddress, &xAddressSize );
			switch( xReturned )
			{
			case 0:
			case -pdFREERTOS_ERRNO_EAGAIN:
			case -pdFREERTOS_ERRNO_EINTR:
				break;
			default:
				if( xReturned < sizeof( xNTPPacket ) )
				{
					FreeRTOS_printf( ( "FreeRTOS_recvfrom: returns %ld\n", xReturned ) );
				}
				else
				{
					prvReadTime( ( struct SNtpPacket *)cRecvBuffer );
					if( xStatus != EStatusPause )
					{
						xStatus = EStatusPause;
					}
				}
				break;
			}
		}
		#endif
	}
}
/*-----------------------------------------------------------*/
