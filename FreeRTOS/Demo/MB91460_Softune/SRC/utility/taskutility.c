/* THIS SAMPLE CODE IS PROVIDED AS IS AND IS SUBJECT TO ALTERATIONS. FUJITSU */
/* MICROELECTRONICS ACCEPTS NO RESPONSIBILITY OR LIABILITY FOR ANY ERRORS OR */
/* ELIGIBILITY FOR ANY PURPOSES.											 */
/*				 (C) Fujitsu Microelectronics Europe GmbH					 */
/*------------------------------------------------------------------------
  taskutility.C
  -
-------------------------------------------------------------------------*/
#include "mb91467d.h"
#include "vectors.h"
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

static void vUART5Task( void *pvParameters );

const char			ASCII[] = "0123456789ABCDEF";

void				vInitUart5( void );


static QueueHandle_t xQueue;

void vInitUart5( void )
{
	//Initialize UART asynchronous mode
	BGR05 = 1666;	//  9600 Baud @ 16MHz
	SCR05 = 0x17;	// 7N2
	SMR05 = 0x0d;	// enable SOT3, Reset, normal mode
	SSR05 = 0x00;	// LSB first
	PFR19_D4 = 1;	// enable UART
	PFR19_D5 = 1;	// enable UART

	//EPFR19 = 0x00;   // enable UART
	SSR05_RIE = 1;
}

void Putch5( char ch )	/* sends a char */
{
	while( SSR05_TDRE == 0 );

	/* wait for transmit buffer empty */
	TDR05 = ch; /* put ch into buffer */
}

char Getch5( void ) /* waits for and returns incomming char */
{
	volatile unsigned	ch;

	while( SSR05_RDRF == 0 );

	/* wait for data received */
	if( SSR05_ORE )			/* overrun error */
	{
		ch = RDR05;			/* reset error flags */
		return ( char ) ( -1 );
	}
	else
	{
		return( RDR05 );	/* return char */
	}
}

void Puts5( const char *Name5 ) /* Puts a String to UART */
{
	volatile short	i, len;
	len = strlen( Name5 );

	for( i = 0; i < len; i++ )	/* go through string */
	{
		if( Name5[i] == 10 )
		{
			Putch5( 13 );
		}

		Putch5( Name5[i] );					/* send it out */
	}
}

void Puthex5( unsigned long n, unsigned char digits )
{
	unsigned char	digit = 0, div = 0, i;

	div = ( 4 * (digits - 1) );				/* init shift divisor */
	for( i = 0; i < digits; i++ )
	{
		digit = ( (n >> div) & 0xF );		/* get hex-digit value */
		Putch5( digit + ((digit < 0xA) ? '0' : 'A' - 0xA) );
		div -= 4;		/* next digit shift */
	}
}

void Putdec5( unsigned long x, int digits )
{
	short	i;
	char	buf[10], sign = 1;

	if( digits < 0 )
	{					/* should be print of zero? */
		digits *= ( -1 );
		sign = 1;
	}

	buf[digits] = '\0'; /* end sign of string */

	for( i = digits; i > 0; i-- )
	{
		buf[i - 1] = ASCII[x % 10];
		x = x / 10;
	}

	if( sign )
	{
		for( i = 0; buf[i] == '0'; i++ )
		{				/* no print of zero */
			if( i < digits - 1 )
			{
				buf[i] = ' ';
			}
		}
	}

	Puts5( buf );		/* send string */
}

void vUtilityStartTraceTask( unsigned portBASE_TYPE uxPriority )
{
	xQueue = xQueueCreate( 5, sizeof( char ) );

	if( xQueue != NULL )
	{
		portENTER_CRITICAL();
		vInitUart5();
		portENTER_CRITICAL();

		xTaskCreate( vUART5Task, "UART5", configMINIMAL_STACK_SIZE * 2, ( void * ) NULL, uxPriority, NULL );
	}
}

static void vUART5Task( void *pvParameters )
{
	static char	buff[ 900 ] = { 0 };
	unsigned long	trace_len, j;

	unsigned char	ch;

	SSR05_RIE = 1;
	Puts5( "\n -------------MB91467D FreeRTOS DEMO Task List and Trace Utility----------- \n" );

	for( ;; )
	{
		Puts5( "\n\rPress any of the following keys for the corresponding functionality: " );

		Puts5( "\n\r1: To call vTaskList() and display current task status " );

		/* The legacy trace is no longer supported.  Use FreeRTOS+Trace instead.
		Puts5( "\n\r2: To call vTaskStartTrace() and to display trace results once the trace ends" ); */

		/* Block on the semaphore.  The UART interrupt will use the semaphore to
		wake this task when required. */
		xQueueReceive( xQueue, &ch, portMAX_DELAY );

		switch( ch )
		{
			case '1':
				vTaskList( buff );
				Puts5( "\n\rThe current task list is as follows...." );
				Puts5( "\n\r----------------------------------------------" );
				Puts5( "\n\rName		  State  Priority  Stack   Number" );
				Puts5( "\n\r----------------------------------------------" );
				Puts5( buff );
				Puts5( "\r----------------------------------------------" );
				break;

			/* The legacy trace is no longer supported.  Use FreeRTOS+Trace instead.
			case '2':
				vTaskStartTrace( (signed char *) buff, sizeof( buff ) );
				Puts5( "\n\rThe trace started!!" );
				vTaskDelay( (TickType_t) 450 );
				trace_len = ulTaskEndTrace();
				Puts5( "\n\rThe trace ended!!" );
				Puts5( "\n\rThe trace is as follows...." );
				Puts5( "\n\r--------------------------------------------------------" );
				Puts5( "\n\r  Tick	 | Task Number  |	 Tick	 | Task Number  |" );
				Puts5( "\n\r--------------------------------------------------------\n\r" );
				for( j = 0; j < trace_len; j++ )
				{
					Puthex5( buff[j], 2 );
					if( j % 4 == 3 )
					{
						Puts5( "   |   " );
					}

					if( j % 16 == 15 )
					{
						Puts5( "\n" );
					}
				}

				Puts5( "\r--------------------------------------------------------" );
				break;*/

			default:
				break;
		}

		Puts5( "\n" );
	}
}

__interrupt void UART5_RxISR( void )
{
unsigned char ch;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	ch = RDR05;
	xQueueSendFromISR( xQueue, &ch, &xHigherPriorityTaskWoken );
}
