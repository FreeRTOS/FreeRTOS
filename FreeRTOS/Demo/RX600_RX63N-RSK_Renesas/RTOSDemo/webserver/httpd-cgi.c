/**
 * \addtogroup httpd
 * @{
 */

/**
 * \file
 *         Web server script interface
 * \author
 *         Adam Dunkels <adam@sics.se>
 *
 */

/*
 * Copyright (c) 2001-2006, Adam Dunkels.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. The name of the author may not be used to endorse or promote
 *    products derived from this software without specific prior
 *    written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS
 * OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE
 * GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * This file is part of the uIP TCP/IP stack.
 *
 * $Id: httpd-cgi.c,v 1.2 2006/06/11 21:46:37 adam Exp $
 *
 */
#include "net/uip.h"
#include "net/psock.h"
#include "apps/httpd/httpd.h"
#include "apps/httpd/httpd-cgi.h"
#include "apps/httpd/httpd-fs.h"

#include <stdio.h>
#include <string.h>

#include "FreeRTOS.h"
#include "task.h"

HTTPD_CGI_CALL( file, "file-stats", file_stats );
HTTPD_CGI_CALL( tcp, "tcp-connections", tcp_stats );
HTTPD_CGI_CALL( net, "net-stats", net_stats );
HTTPD_CGI_CALL( rtos, "rtos-stats", rtos_stats );
HTTPD_CGI_CALL( run, "run-time", run_time );
HTTPD_CGI_CALL( io, "led-io", led_io );

static const struct httpd_cgi_call	*calls[] = { &file, &tcp, &net, &rtos, &run, &io, NULL };

/*---------------------------------------------------------------------------*/
static PT_THREAD( nullfunction ( struct httpd_state *s, char *ptr ) )
{
	PSOCK_BEGIN( &s->sout );
	( void ) ptr;
	( void ) PT_YIELD_FLAG;
	PSOCK_END( &s->sout );
}

/*---------------------------------------------------------------------------*/
httpd_cgifunction httpd_cgi( char *name )
{
	const struct httpd_cgi_call **f;

	/* Find the matching name in the table, return the function. */
	for( f = calls; *f != NULL; ++f )
	{
		if( strncmp((*f)->name, name, strlen((*f)->name)) == 0 )
		{
			return( *f )->function;
		}
	}

	return nullfunction;
}

/*---------------------------------------------------------------------------*/
static unsigned short generate_file_stats( void *arg )
{
	char	*f = ( char * ) arg;
	return sprintf( ( char * ) uip_appdata, "%5u", httpd_fs_count(f) );
}

/*---------------------------------------------------------------------------*/
static PT_THREAD( file_stats ( struct httpd_state *s, char *ptr ) )
{
	PSOCK_BEGIN( &s->sout );

	( void ) PT_YIELD_FLAG;

	PSOCK_GENERATOR_SEND( &s->sout, generate_file_stats, strchr(ptr, ' ') + 1 );

	PSOCK_END( &s->sout );
}

/*---------------------------------------------------------------------------*/
static const char	closed[] = /*  "CLOSED",*/ { 0x43, 0x4c, 0x4f, 0x53, 0x45, 0x44, 0 };
static const char	syn_rcvd[] = /*  "SYN-RCVD",*/ { 0x53, 0x59, 0x4e, 0x2d, 0x52, 0x43, 0x56, 0x44, 0 };
static const char	syn_sent[] = /*  "SYN-SENT",*/ { 0x53, 0x59, 0x4e, 0x2d, 0x53, 0x45, 0x4e, 0x54, 0 };
static const char	established[] = /*  "ESTABLISHED",*/ { 0x45, 0x53, 0x54, 0x41, 0x42, 0x4c, 0x49, 0x53, 0x48, 0x45, 0x44, 0 };
static const char	fin_wait_1[] = /*  "FIN-WAIT-1",*/ { 0x46, 0x49, 0x4e, 0x2d, 0x57, 0x41, 0x49, 0x54, 0x2d, 0x31, 0 };
static const char	fin_wait_2[] = /*  "FIN-WAIT-2",*/ { 0x46, 0x49, 0x4e, 0x2d, 0x57, 0x41, 0x49, 0x54, 0x2d, 0x32, 0 };
static const char	closing[] = /*  "CLOSING",*/ { 0x43, 0x4c, 0x4f, 0x53, 0x49, 0x4e, 0x47, 0 };
static const char	time_wait[] = /*  "TIME-WAIT,"*/ { 0x54, 0x49, 0x4d, 0x45, 0x2d, 0x57, 0x41, 0x49, 0x54, 0 };
static const char	last_ack[] = /*  "LAST-ACK"*/ { 0x4c, 0x41, 0x53, 0x54, 0x2d, 0x41, 0x43, 0x4b, 0 };

static const char	*states[] = { closed, syn_rcvd, syn_sent, established, fin_wait_1, fin_wait_2, closing, time_wait, last_ack };

static unsigned short generate_tcp_stats( void *arg )
{
	struct uip_conn		*conn;
	struct httpd_state	*s = ( struct httpd_state * ) arg;

	conn = &uip_conns[s->count];
	return sprintf( ( char * ) uip_appdata,
					 "<tr><td>%d</td><td>%u.%u.%u.%u:%u</td><td>%s</td><td>%u</td><td>%u</td><td>%c %c</td></tr>\r\n", htons(conn->lport),
					 htons(conn->ripaddr.u16[0]) >> 8, htons(conn->ripaddr.u16[0]) & 0xff, htons(conn->ripaddr.u16[1]) >> 8,
					 htons(conn->ripaddr.u16[1]) & 0xff, htons(conn->rport), states[conn->tcpstateflags & UIP_TS_MASK], conn->nrtx, conn->timer,
					 (uip_outstanding(conn)) ? '*' : ' ', (uip_stopped(conn)) ? '!' : ' ' );
}

/*---------------------------------------------------------------------------*/
static PT_THREAD( tcp_stats ( struct httpd_state *s, char *ptr ) )
{
	PSOCK_BEGIN( &s->sout );
	( void ) ptr;
	( void ) PT_YIELD_FLAG;
	for( s->count = 0; s->count < UIP_CONNS; ++s->count )
	{
		if( (uip_conns[s->count].tcpstateflags & UIP_TS_MASK) != UIP_CLOSED )
		{
			PSOCK_GENERATOR_SEND( &s->sout, generate_tcp_stats, s );
		}
	}

	PSOCK_END( &s->sout );
}

/*---------------------------------------------------------------------------*/
static unsigned short generate_net_stats( void *arg )
{
	struct httpd_state	*s = ( struct httpd_state * ) arg;
	return sprintf( ( char * ) uip_appdata, "%5u\n", (( uip_stats_t * ) &uip_stat)[s->count] );
}

static PT_THREAD( net_stats ( struct httpd_state *s, char *ptr ) )
{
	PSOCK_BEGIN( &s->sout );
	( void ) ptr;
	( void ) PT_YIELD_FLAG;
#if UIP_STATISTICS
	for( s->count = 0; s->count < sizeof(uip_stat) / sizeof(uip_stats_t); ++s->count )
	{
		PSOCK_GENERATOR_SEND( &s->sout, generate_net_stats, s );
	}

#endif /* UIP_STATISTICS */

	PSOCK_END( &s->sout );
}

/*---------------------------------------------------------------------------*/
extern void vTaskList( char *pcWriteBuffer );
extern char *pcGetTaskStatusMessage( void );
static char cCountBuf[128];
long		lRefreshCount = 0;
static unsigned short generate_rtos_stats( void *arg )
{
	( void ) arg;
	lRefreshCount++;
	sprintf( cCountBuf, "<p><br>Refresh count = %d<p><br>%s", ( int ) lRefreshCount, pcGetTaskStatusMessage() );
	vTaskList( ( char * ) uip_appdata );
	strcat( uip_appdata, cCountBuf );

	return strlen( uip_appdata );
}

/*---------------------------------------------------------------------------*/
static PT_THREAD( rtos_stats ( struct httpd_state *s, char *ptr ) )
{
	PSOCK_BEGIN( &s->sout );
	( void ) ptr;
	( void ) PT_YIELD_FLAG;
	PSOCK_GENERATOR_SEND( &s->sout, generate_rtos_stats, NULL );
	PSOCK_END( &s->sout );
}

/*---------------------------------------------------------------------------*/
char			*pcStatus;
unsigned long	ulString;

static unsigned short generate_io_state( void *arg )
{
	extern long lParTestGetLEDState( unsigned long ulLED );
	( void ) arg;

	/* Are the dynamically setable LEDs currently on or off? */
	if( lParTestGetLEDState( 3 ) )
	{
		pcStatus = "checked";
	}
	else
	{
		pcStatus = "";
	}

	sprintf( uip_appdata, "<input type=\"checkbox\" name=\"LED0\" value=\"1\" %s>LED<p><p>", pcStatus );

	return strlen( uip_appdata );
}

/*---------------------------------------------------------------------------*/
extern void vTaskGetRunTimeStats( char *pcWriteBuffer );
extern unsigned short usMaxJitter;
static char cJitterBuffer[ 200 ];
static unsigned short generate_runtime_stats( void *arg )
{
	( void ) arg;
	lRefreshCount++;
	sprintf( cCountBuf, "<p><br>Refresh count = %d", ( int ) lRefreshCount );

	#ifdef INCLUDE_HIGH_FREQUENCY_TIMER_TEST
	{
		sprintf( cJitterBuffer, "<p><br>Max high frequency timer jitter = %d peripheral clock periods.<p><br>", ( int ) usMaxJitter );
		vTaskGetRunTimeStats( ( char * ) uip_appdata );
		strcat( uip_appdata, cJitterBuffer );
	}
	#else
	{
		( void ) cJitterBuffer;
		strcpy( uip_appdata, "<p>Run time stats are only available in the debug_with_optimisation build configuration.<p>" );
	}
	#endif

	strcat( uip_appdata, cCountBuf );

	return strlen( uip_appdata );
}

/*---------------------------------------------------------------------------*/
static PT_THREAD( run_time ( struct httpd_state *s, char *ptr ) )
{
	PSOCK_BEGIN( &s->sout );
	( void ) ptr;
	( void ) PT_YIELD_FLAG;
	PSOCK_GENERATOR_SEND( &s->sout, generate_runtime_stats, NULL );
	PSOCK_END( &s->sout );
}

/*---------------------------------------------------------------------------*/
static PT_THREAD( led_io ( struct httpd_state *s, char *ptr ) )
{
	PSOCK_BEGIN( &s->sout );
	( void ) ptr;
	( void ) PT_YIELD_FLAG;
	PSOCK_GENERATOR_SEND( &s->sout, generate_io_state, NULL );
	PSOCK_END( &s->sout );
}

/** @} */
