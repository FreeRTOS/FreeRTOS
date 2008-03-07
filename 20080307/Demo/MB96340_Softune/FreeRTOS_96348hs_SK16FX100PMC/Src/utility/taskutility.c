/* THIS SAMPLE CODE IS PROVIDED AS IS AND IS SUBJECT TO ALTERATIONS. FUJITSU */

/* MICROELECTRONICS ACCEPTS NO RESPONSIBILITY OR LIABILITY FOR ANY ERRORS OR */

/* ELIGIBILITY FOR ANY PURPOSES.                                             */

/*                 (C) Fujitsu Microelectronics Europe GmbH                  */

/*------------------------------------------------------------------------
  taskutility.C
  - 
-------------------------------------------------------------------------*/

/*************************@INCLUDE_START************************/
#include "mb96348hs.h"
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

static void vUART0Task( void *pvParameters );

/**************************@INCLUDE_END*************************/

/*********************@GLOBAL_VARIABLES_START*******************/
const char	ASCII[] = "0123456789ABCDEF";

xTaskHandle UART_TaskHandle;

static xQueueHandle xQueue;
void InitUart0( void )
{
	/* Initialize UART asynchronous mode */
	BGR0 = configCLKP1_CLOCK_HZ / 9600; /* 9600 Baud @ CLKP1 - 56 MHz */

	SCR0 = 0x17;						/* 8N1 */
	SMR0 = 0x0d;						/* enable SOT3, Reset, normal mode */
	SSR0 = 0x02;						/* LSB first, enable receive interrupts */

	PIER08_IE2 = 1; /* enable input */
	DDR08_D2 = 0;	/* switch P08_2 to input */
	DDR08_D3 = 1;	/* switch P08_3 to output */
}

void Putch0( char ch )	/* sends a char */
{
	while( SSR0_TDRE == 0 );

	/* wait for transmit buffer empty 	*/
	TDR0 = ch;	/* put ch into buffer			*/
}

char Getch0( void ) /* waits for and returns incomming char 	*/
{
	volatile unsigned	ch;

	while( SSR0_RDRF == 0 );

	/* wait for data received  	*/
	if( SSR0_ORE )		/* overrun error 		*/
	{
		ch = RDR0;		/* reset error flags 		*/
		return ( char ) ( -1 );
	}
	else
	{
		return( RDR0 ); /* return char 			*/
	}
}

void Puts0( const char *Name1 ) /* Puts a String to UART */
{
	volatile portSHORT	i, len;
	len = strlen( Name1 );

	for( i = 0; i < len; i++ )	/* go through string */
	{
		if( Name1[i] == 10 )
		{
			Putch0( 13 );
		}

		Putch0( Name1[i] );					/* send it out                           */
	}
}

void Puthex0( unsigned long n, unsigned char digits )
{
	unsigned portCHAR	digit = 0, div = 0, i;

	div = ( 4 * (digits - 1) );				/* init shift divisor */
	for( i = 0; i < digits; i++ )
	{
		digit = ( (n >> div) & 0xF );		/* get hex-digit value */
		Putch0( digit + ((digit < 0xA) ? '0' : 'A' - 0xA) );
		div -= 4;		/* next digit shift */
	}
}

void Putdec0( unsigned long x, int digits )
{
	portSHORT	i;
	portCHAR	buf[10], sign = 1;

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

	Puts0( buf );		/* send string */
}

void vUtilityStartTraceTask( unsigned portBASE_TYPE uxPriority )
{
	xQueue = xQueueCreate( 5, sizeof( char ) );

	if( xQueue != NULL )
	{
		portENTER_CRITICAL();
		InitUart0();
		portENTER_CRITICAL();
		xTaskCreate( vUART0Task, (signed portCHAR *) "UART1", configMINIMAL_STACK_SIZE * 3, ( void * ) NULL, uxPriority, &UART_TaskHandle );
	}
}

static void vUART0Task( void *pvParameters )
{
	static portCHAR	buff[ 800 ] = { 0 };
	unsigned portLONG	trace_len;
	signed portLONG		i, j, l = 0;

	unsigned portCHAR	ch;
	( void ) pvParameters;

	SSR0_RIE = 1;

	Puts0( "\n -------------MB96348 FreeRTOS DEMO Task List and Trace Utility----------- \n" );

	for( ;; )
	{
		Puts0( "\n\rPress any of the following keys for the corresponding functionality: " );

		Puts0( "\n\r1: To call vTaskList() and display current task status " );

		Puts0( "\n\r2: To call vTaskStartTrace() and to display trace results once the trace ends" );

		/* Block on the semaphore.  The UART interrupt will use the semaphore to
		wake this task when required. */
		xQueueReceive( xQueue, &ch, portMAX_DELAY );

		switch( ch )
		{
			case '1':
				vTaskList( (signed char *) buff );
				Puts0( "\n\rThe current task list is as follows...." );
				Puts0( "\n\r----------------------------------------------" );
				Puts0( "\n\rName          State  Priority  Stack   Number" );
				Puts0( "\n\r----------------------------------------------" );
				Puts0( buff );
				Puts0( "\r----------------------------------------------" );
				break;

			case '2':
				vTaskStartTrace( (signed char *) buff, sizeof( buff ) );
				Puts0( "\n\rThe trace started!!" );
				vTaskDelay( (portTickType) 500 );
				trace_len = ulTaskEndTrace();
				Puts0( "\n\rThe trace ended!!" );
				Puts0( "\n\rThe trace is as follows...." );
				Puts0( "\n\r--------------------------------------------------------" );
				Puts0( "\n\r  Tick     | Task Number  |     Tick     | Task Number  |" );
				Puts0( "\n\r--------------------------------------------------------\n\r" );

				for( i = 0; i < trace_len; i += 4 )
				{
					for( j = i + 3; j >= i; j-- )
					{
						Puthex0( buff[j], 2 );
					}

					Puts0( "   |   " );
					l++;
					if( l == 4 )
					{
						Puts0( "\n" );
						l = 0;
					}
				}

				Puts0( "\r--------------------------------------------------------" );
				break;

			default:
				break;
		}

		Puts0( "\n" );
	}
}

__interrupt void UART0_TraceRxISR( void )
{
unsigned portCHAR ch;

	ch = RDR0;
	xQueueSendFromISR( xQueue, &ch, pdFALSE );
}
