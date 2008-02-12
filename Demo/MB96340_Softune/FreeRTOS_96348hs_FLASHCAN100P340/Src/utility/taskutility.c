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


static void vUART2Task( void *pvParameters );

/**************************@INCLUDE_END*************************/
/*********************@GLOBAL_VARIABLES_START*******************/
const char ASCII[] = "0123456789ABCDEF";

xTaskHandle UART_TaskHandle;

void InitUart2(void)
{
	/* Initialize UART asynchronous mode */
	BGR2 = configCLKP1_CLOCK_HZ / 9600;	/* 9600 Baud @ CLKP1 - 56 MHz */
		  
	SCR2 = 0x17;    /* 8N1 */
	SMR2 = 0x0d;    /* enable SOT3, Reset, normal mode */
	SSR2 = 0x02;    /* LSB first, enable receive interrupts */
  
	PIER05_IE0 = 1;  /* enable input */
	DDR05_D0 = 0;    /* switch P05_0 to input */
	DDR05_D1 = 1;    /* switch P05_1 to output */
	
}

void Putch2(char ch)         /* sends a char */
{
  while (SSR2_TDRE == 0);    /* wait for transmit buffer empty 	*/
  TDR2 = ch;                 /* put ch into buffer			*/
}

char Getch2(void)            /* waits for and returns incomming char 	*/
{
  volatile unsigned ch;
  
  while(SSR2_RDRF == 0);	 /* wait for data received  	*/
  if (SSR2_ORE)              /* overrun error 		*/
  {
    ch = RDR2;              /* reset error flags 		*/
    return (char)(-1);
  }
  else
  return (RDR2);            /* return char 			*/
}

void Puts2(const char *Name2)  /* Puts a String to UART */
{
  volatile portSHORT i,len;
  len = strlen(Name2);
	
  for (i=0; i<strlen(Name2); i++)   /* go through string                     */
  {
    if (Name2[i] == 10)
      Putch2(13);
    Putch2(Name2[i]);              /* send it out                           */
  }
}

void Puthex2(unsigned long n, unsigned char digits)
{
   unsigned portCHAR digit=0,div=0,i;

   div=(4*(digits-1));	/* init shift divisor */
   for (i=0;i<digits;i++)
   {
     digit = ((n >> div)&0xF); /* get hex-digit value */
	 Putch2(digit + ((digit < 0xA) ? '0' : 'A' - 0xA));
     div-=4;     		/* next digit shift */
   }
}

void Putdec2(unsigned long x, int digits)
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
    
	Puts2(buf);					/* send string */
}

void vTraceListTasks( unsigned portBASE_TYPE uxPriority )
{
	portENTER_CRITICAL();
	InitUart2();
	portENTER_CRITICAL();
	xTaskCreate( vUART2Task , ( signed portCHAR * ) "UART2",  ( unsigned portSHORT ) 2048, ( void * ) NULL, uxPriority, &UART_TaskHandle );
}

static void vUART2Task( void *pvParameters )
{
	portCHAR tasklist_buff[512];
	portCHAR trace_buff[512];
	unsigned portLONG trace_len;
	signed portLONG i, j, l=0;
	
	unsigned portCHAR ch;	
	
	( void ) pvParameters;
	
	Puts2("\n -------------MB96348 FreeRTOS DEMO Task List and Trace Utility----------- \n");

	for(;;)
	{
		Puts2("\n\rPress any of the following keys for the corresponding functionality: ");

		Puts2("\n\r1: To call vTaskList() and display current task status ");

		Puts2("\n\r2: To call vTaskStartTrace() and to display trace results once the trace ends");

		SSR2_RIE=1;

		vTaskSuspend(NULL);

	 	ch=Getch2();

		switch ( ch ) 
		{
			case '1':
				vTaskList( ( signed char * ) tasklist_buff );
				Puts2("\n\rThe current task list is as follows....");
				Puts2("\n\r----------------------------------------------");
				Puts2("\n\rName          State  Priority  Stack   Number");
				Puts2("\n\r----------------------------------------------");
				Puts2(tasklist_buff);
				Puts2("\r----------------------------------------------");
				break;

			case '2':
				vTaskStartTrace(( signed char * ) trace_buff, 512);
				Puts2("\n\rThe trace started!!");
				vTaskDelay( ( portTickType ) 500);
				trace_len = ulTaskEndTrace();
				Puts2("\n\rThe trace ended!!");
				Puts2("\n\rThe trace is as follows....");
				Puts2("\n\r--------------------------------------------------------");
				Puts2("\n\r  Tick     | Task Number  |     Tick     | Task Number  |");
				Puts2("\n\r--------------------------------------------------------\n\r");
				
				for( i = 0 ; i < trace_len ; i+=4 )
				{
					for( j = i+3 ; j >= i ; j-- )
					{
						Puthex2(trace_buff[j],2);
					}
					Puts2("   |   ");
					l++;
					if ( l == 4)
					{
						Puts2("\n");
						l = 0;
					}	
				}
				Puts2("\r--------------------------------------------------------");
				break;
				
			default:
				break;
		}
		Puts2("\n");
	}
}

__interrupt void UART2_RxISR ( void )
{
	SSR2_RIE=0;
	vTaskResume( UART_TaskHandle );
}
