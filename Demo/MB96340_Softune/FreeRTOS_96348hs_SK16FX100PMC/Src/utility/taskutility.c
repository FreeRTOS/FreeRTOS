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


static void vUART1Task( void *pvParameters );

/**************************@INCLUDE_END*************************/
/*********************@GLOBAL_VARIABLES_START*******************/
const char ASCII[] = "0123456789ABCDEF";

xTaskHandle UART_TaskHandle;

void InitUart1(void)
{
	/* Initialize UART asynchronous mode */
	BGR1 = configCLKP1_CLOCK_HZ / 9600;	/* 9600 Baud @ CLKP1 - 56 MHz */
		  
	SCR1 = 0x17;    /* 8N1 */
	SMR1 = 0x0d;    /* enable SOT3, Reset, normal mode */
	SSR1 = 0x02;    /* LSB first, enable receive interrupts */
  
	PIER08_IE5 = 1;  /* enable input */
	DDR08_D5 = 0;    /* switch P08_5 to input */
	DDR08_D6 = 1;    /* switch P08_6 to output */
}

void Putch1(char ch)         /* sends a char */
{
  while (SSR1_TDRE == 0);    /* wait for transmit buffer empty 	*/
  TDR1 = ch;                 /* put ch into buffer			*/
}

char Getch1(void)            /* waits for and returns incomming char 	*/
{
  volatile unsigned ch;
  
  while(SSR1_RDRF == 0);	 /* wait for data received  	*/
  if (SSR1_ORE)              /* overrun error 		*/
  {
    ch = RDR1;              /* reset error flags 		*/
    return (char)(-1);
  }
  else
  return (RDR1);            /* return char 			*/
}

void Puts1(const char *Name1)  /* Puts a String to UART */
{
  volatile portSHORT i,len;
  len = strlen(Name1);
	
  for (i=0; i<strlen(Name1); i++)   /* go through string                     */
  {
    if (Name1[i] == 10)
      Putch1(13);
    Putch1(Name1[i]);              /* send it out                           */
  }
}

void Puthex1(unsigned long n, unsigned char digits)
{
   unsigned portCHAR digit=0,div=0,i;

   div=(4*(digits-1));	/* init shift divisor */
   for (i=0;i<digits;i++)
   {
     digit = ((n >> div)&0xF); /* get hex-digit value */
	 Putch1(digit + ((digit < 0xA) ? '0' : 'A' - 0xA));
     div-=4;     		/* next digit shift */
   }
}

void Putdec1(unsigned long x, int digits)
{
	portSHORT i;
	portCHAR buf[10],sign=1;
	
	if (digits < 0) {     /* should be print of zero? */
	  digits *= (-1);
	  sign =1;
	}  
	buf[digits]='\0';			/* end sign of string */
	
	for (i=digits; i>0; i--) {
		buf[i-1] = ASCII[x % 10];
		x = x/10;
	}

    if ( sign )
    {
	  for (i=0; buf[i]=='0'; i++) { /* no print of zero */
		if ( i<digits-1)
			buf[i] = ' ';
	  }		
    }
    
	Puts1(buf);					/* send string */
}

void vTraceListTasks( unsigned portBASE_TYPE uxPriority )
{
	portENTER_CRITICAL();
	InitUart1();
	portENTER_CRITICAL();
	xTaskCreate( vUART1Task , ( signed portCHAR * ) "UART1",  ( unsigned portSHORT ) 2048, ( void * ) NULL, uxPriority, &UART_TaskHandle );
}

static void vUART1Task( void *pvParameters )
{
	portCHAR tasklist_buff[512];
	portCHAR trace_buff[512];
	unsigned portLONG trace_len;
	signed portLONG i, j, l=0;
	
	unsigned portCHAR ch;	
	
	( void ) pvParameters;
	
	Puts1("\n -------------MB96348 FreeRTOS DEMO Task List and Trace Utility----------- \n");

	for(;;)
	{
		Puts1("\n\rPress any of the following keys for the corresponding functionality: ");

		Puts1("\n\r1: To call vTaskList() and display current task status ");

		Puts1("\n\r2: To call vTaskStartTrace() and to display trace results once the trace ends");

		SSR1_RIE=1;

		vTaskSuspend(NULL);

	 	ch=Getch1();

		switch ( ch ) 
		{
			case '1':
				vTaskList( ( signed char * ) tasklist_buff );
				Puts1("\n\rThe current task list is as follows....");
				Puts1("\n\r----------------------------------------------");
				Puts1("\n\rName          State  Priority  Stack   Number");
				Puts1("\n\r----------------------------------------------");
				Puts1(tasklist_buff);
				Puts1("\r----------------------------------------------");
				break;

			case '2':
				vTaskStartTrace(( signed char * ) trace_buff, 512);
				Puts1("\n\rThe trace started!!");
				vTaskDelay( ( portTickType ) 500);
				trace_len = ulTaskEndTrace();
				Puts1("\n\rThe trace ended!!");
				Puts1("\n\rThe trace is as follows....");
				Puts1("\n\r--------------------------------------------------------");
				Puts1("\n\r  Tick     | Task Number  |     Tick     | Task Number  |");
				Puts1("\n\r--------------------------------------------------------\n\r");
				
				for( i = 0 ; i < trace_len ; i+=4 )
				{
					for( j = i+3 ; j >= i ; j-- )
					{
						Puthex1(trace_buff[j],2);
					}
					Puts1("   |   ");
					l++;
					if ( l == 4)
					{
						Puts1("\n");
						l = 0;
					}	
				}
				Puts1("\r--------------------------------------------------------");
				break;
				
			default:
				break;
		}
		Puts1("\n");
	}
}

__interrupt void UART1_RxISR ( void )
{
	SSR1_RIE=0;
	vTaskResume( UART_TaskHandle );
}
