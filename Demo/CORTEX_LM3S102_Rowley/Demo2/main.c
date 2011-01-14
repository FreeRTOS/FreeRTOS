/*
    FreeRTOS V6.1.1 - Copyright (C) 2011 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS books - available as PDF or paperback  *
    *                                                                         *
    *        "Using the FreeRTOS Real Time Kernel - a Practical Guide"        *
    *                  http://www.FreeRTOS.org/Documentation                  *
    *                                                                         *
    * A pdf reference manual is also available.  Both are usually delivered   *
    * to your inbox within 20 minutes to two hours when purchased between 8am *
    * and 8pm GMT (although please allow up to 24 hours in case of            *
    * exceptional circumstances).  Thank you for your support!                *
    *                                                                         *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    ***NOTE*** The exception to the GPL is included to allow you to distribute
    a combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public 
    License and the FreeRTOS license exception along with FreeRTOS; if not it 
    can be viewed here: http://www.freertos.org/a00114.html and also obtained 
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!

    http://www.FreeRTOS.org - Documentation, latest information, license and
    contact details.

    http://www.SafeRTOS.com - A version that is certified for use in safety
    critical systems.

    http://www.OpenRTOS.com - Commercial support, development, porting,
    licensing and training services.
*/

/* 
 * This demo application creates seven co-routines and one task (two including 
 * the idle task).  The co-routines execute as part of the idle task hook.
 *
 * Five of the created co-routines are the standard 'co-routine flash' 
 * co-routines contained within the Demo/Common/Minimal/crflash.c file and 
 * documented on the FreeRTOS.org WEB site.  
 *
 * The 'LCD Task' rotates a string on the LCD, delaying between each character
 * as necessitated by the slow interface, and delaying between each string just
 * long enough to enable the text to be read.
 *
 * The sixth co-routine controls the transmission of a string to UART 0.  The 
 * co-routine periodically sends the first character of the string to the UART, 
 * with the UART's TxEnd interrupt being used to transmit the remaining 
 * characters.  The UART's RxEnd interrupt receives the characters and places 
 * them on a queue to be processed by the seventh and final co-routine.  An 
 * error is latched should an unexpected character be received, or any 
 * character be received out of sequence.  
 *
 * A loopback connector is required to ensure that each character transmitted 
 * on the UART is also received on the same UART.  For test purposes the UART
 * FIFO's are not utalised in order to maximise the interrupt overhead.  Also
 * a pseudo random interval is used between the start of each transmission in 
 * order that the resultant interrupts are more randomly distributed and 
 * therefore more likely to highlight any problems.
 *
 * The flash co-routines control LED's zero to four.  LED five is toggled each
 * time the string is transmitted on the UART.  LED six is toggled each time
 * the string is CORRECTLY received on the UART.  LED seven is latched on should
 * an error be detected in any task or co-routine.
 *
 * In addition the idle task makes repetative calls to 
 * prvSetAndCheckRegisters().  This simply loads the general purpose registers 
 * with a known value, then checks each register to ensure the held value is 
 * still correct.  As a low priority task this checking routine is likely to 
 * get repeatedly swapped in and out.  A register being found to contain an 
 * incorrect value is therefore indicative of an error in the task switching 
 * mechansim.
 *
 */

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "croutine.h"

/* Demo application include files. */
#include "partest.h"
#include "crflash.h"

/* Library include files. */
#include "DriverLib.h"

/* The time to delay between writing each character to the LCD. */
#define mainCHAR_WRITE_DELAY		( 2 / portTICK_RATE_MS )

/* The time to delay between writing each string to the LCD. */
#define mainSTRING_WRITE_DELAY		( 400 / portTICK_RATE_MS )

/* The number of flash co-routines to create. */
#define mainNUM_FLASH_CO_ROUTINES	( 5 )

/* The length of the queue used to pass received characters to the Comms Rx
task. */
#define mainRX_QUEUE_LEN			( 5 )

/* The priority of the co-routine used to initiate the transmission of the 
string on UART 0. */
#define mainTX_CO_ROUTINE_PRIORITY	( 1 )

/* The priority of the co-routine used to receive characters from the UART. */
#define mainRX_CO_ROUTINE_PRIORITY	( 2 )

/* Only one co-routine is created so its index is not important. */
#define mainTX_CO_ROUTINE_INDEX		( 0 )
#define mainRX_CO_ROUTINE_INDEX		( 0 )

/* The time between transmissions of the string on UART 0.   This is pseudo
random in order to generate a bit or randomness to when the interrupts occur.*/
#define mainMIN_TX_DELAY			( 40 / portTICK_RATE_MS )
#define mainMAX_TX_DELAY			( ( portTickType ) 0x7f )
#define mainOFFSET_TIME				( ( portTickType ) 3 )

/* The time the Comms Rx task should wait to receive a character.  This should
be slightly longer than the time between transmissions.  If we do not receive
a character after this time then there must be an error in the transmission or
the timing of the transmission. */
#define mainCOMMS_RX_DELAY			( mainMAX_TX_DELAY + 20 )

/* The task priorites. */
#define mainLCD_TASK_PRIORITY		( tskIDLE_PRIORITY )
#define mainCOMMS_RX_TASK_PRIORITY	( tskIDLE_PRIORITY + 1 )

/* The LED's toggled by the various tasks. */
#define mainCOMMS_FAIL_LED			( 7 )
#define mainCOMMS_RX_LED			( 6 )
#define mainCOMMS_TX_LED			( 5 )

/* The baud rate used by the UART comms tasks/co-routine. */
#define mainBAUD_RATE				( 57600 )

/* FIFO setting for the UART.  The FIFO is not used to create a better test. */
#define mainFIFO_SET				( 0x10 )

/* The string that is transmitted on the UART contains sequentially the 
characters from mainFIRST_TX_CHAR to mainLAST_TX_CHAR. */
#define mainFIRST_TX_CHAR '0'
#define mainLAST_TX_CHAR 'z'

/* Just used to walk through the program memory in order that some random data
can be generated. */
#define mainTOTAL_PROGRAM_MEMORY ( ( unsigned long * ) ( 8 * 1024 ) )
#define mainFIRST_PROGRAM_BYTES ( ( unsigned long * ) 4 )

/* The error routine that is called if the driver library encounters an error. */
#ifdef DEBUG
void
__error__(char *pcFilename, unsigned long ulLine)
{
}
#endif

/*-----------------------------------------------------------*/

/*
 * The task that rotates text on the LCD.
 */
static void vLCDTask( void * pvParameters );

/*
 * The task that receives the characters from UART 0.
 */
static void vCommsRxCoRoutine( xCoRoutineHandle xHandle, unsigned portBASE_TYPE uxIndex );

/*
 * The co-routine that periodically initiates the transmission of the string on
 * the UART.
 */
static void vSerialTxCoRoutine( xCoRoutineHandle xHandle, unsigned portBASE_TYPE uxIndex );

/* 
 * Writes a string the the LCD.
 */
static void prvWriteString( const char *pcString );

/*
 * Initialisation routine for the UART.
 */
static void vSerialInit( void );

/*
 * Thread safe write to the PDC.
 */
static void prvPDCWrite( char cAddress, char cData );

/*
 * Function to simply set a known value into the general purpose registers
 * then read them back to ensure they remain set correctly.  An incorrect value
 * being indicative of an error in the task switching mechanism.
 */
void prvSetAndCheckRegisters( void );

/*
 * Latch the LED that indicates that an error has occurred. 
 */
void vSetErrorLED( void );

/*
 * Sets up the PLL and ports used by the demo.
 */
static void prvSetupHardware( void );

/*-----------------------------------------------------------*/

/* Error flag set to pdFAIL if an error is encountered in the tasks/co-routines
defined within this file. */
unsigned portBASE_TYPE uxErrorStatus = pdPASS;

/* The next character to transmit. */
static char cNextChar;

/* The queue used to transmit characters from the interrupt to the Comms Rx
task. */
static xQueueHandle xCommsQueue;

/*-----------------------------------------------------------*/

int main( void )
{
	/* Create the queue used to communicate between the UART ISR and the Comms
	Rx task. */
	xCommsQueue = xQueueCreate( mainRX_QUEUE_LEN, sizeof( char ) );

	/* Setup the ports used by the demo and the clock. */
	prvSetupHardware();

	/* Create the co-routines that flash the LED's. */
	vStartFlashCoRoutines( mainNUM_FLASH_CO_ROUTINES );

	/* Create the co-routine that initiates the transmission of characters
	on the UART. */
	xCoRoutineCreate( vSerialTxCoRoutine, mainTX_CO_ROUTINE_PRIORITY, mainTX_CO_ROUTINE_INDEX );

	/* Create the co-routine that receives characters from the UART. */
	xCoRoutineCreate( vCommsRxCoRoutine, mainRX_CO_ROUTINE_PRIORITY, mainRX_CO_ROUTINE_INDEX );

	/* Create the LCD task. */
	xTaskCreate( vLCDTask, "LCD", configMINIMAL_STACK_SIZE, NULL, mainLCD_TASK_PRIORITY, NULL );

	/* Start the scheduler running the tasks and co-routines just created. */
	vTaskStartScheduler();

	/* Should not get here unless we did not have enough memory to start the
	scheduler. */
	for( ;; );
	return 0;
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	/* Setup the PLL. */
	SysCtlClockSet( SYSCTL_SYSDIV_10 | SYSCTL_USE_PLL | SYSCTL_OSC_MAIN | SYSCTL_XTAL_6MHZ );

	/* Initialise the hardware used to talk to the LCD, LED's and UART. */
	PDCInit();
	vParTestInitialise();
	vSerialInit();
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
	/* The co-routines are executed in the idle task using the idle task 
	hook. */
	for( ;; )
	{
		/* Schedule the co-routines. */
		vCoRoutineSchedule();

		/* Run the register check function between each co-routine. */
		prvSetAndCheckRegisters();
	}
}
/*-----------------------------------------------------------*/

static void prvWriteString( const char *pcString )
{
	/* Write pcString to the LED, pausing between each character. */
	prvPDCWrite(PDC_LCD_CSR, LCD_CLEAR);        
	while( *pcString )
	{
		vTaskDelay( mainCHAR_WRITE_DELAY );
		prvPDCWrite( PDC_LCD_RAM, *pcString );
		pcString++;
	}
}
/*-----------------------------------------------------------*/

void vLCDTask( void * pvParameters )
{
unsigned portBASE_TYPE uxIndex;
const unsigned char ucCFGData[] = {	
											0x30,   /* Set data bus to 8-bits. */
											0x30,
											0x30,
											0x3C,   /* Number of lines/font. */
											0x08,   /* Display off. */
											0x01,   /* Display clear. */
											0x06,   /* Entry mode [cursor dir][shift]. */
											0x0C	/* Display on [display on][curson on][blinking on]. */
									  };  

/* The strings that are written to the LCD. */
const char *pcStringsToDisplay[] = {										
											"Stellaris",
											"Demo",
											"Two",
											"www.FreeRTOS.org",
											""
									   };

	/* Configure the LCD. */
	uxIndex = 0;
	while( uxIndex < sizeof( ucCFGData ) )
	{
		prvPDCWrite( PDC_LCD_CSR, ucCFGData[ uxIndex ] );
		uxIndex++;
		vTaskDelay( mainCHAR_WRITE_DELAY );
	}

	/* Turn the LCD Backlight on. */
	prvPDCWrite( PDC_CSR, 0x01 );

	/* Clear display. */
	vTaskDelay( mainCHAR_WRITE_DELAY );
	prvPDCWrite( PDC_LCD_CSR, LCD_CLEAR ); 

	uxIndex = 0;
	for( ;; )    
	{
		/* Display the string on the LCD. */
		prvWriteString( pcStringsToDisplay[ uxIndex ] );
		
		/* Move on to the next string - wrapping if necessary. */
		uxIndex++;
		if( *( pcStringsToDisplay[ uxIndex ] ) == 0x00 )
		{
			uxIndex = 0;
			/* Longer pause on the last string to be sent. */
			vTaskDelay( mainSTRING_WRITE_DELAY * 2 );
		}

		/* Wait until it is time to move onto the next string. */
		vTaskDelay( mainSTRING_WRITE_DELAY );
	}
}
/*-----------------------------------------------------------*/

static void vCommsRxCoRoutine( xCoRoutineHandle xHandle, unsigned portBASE_TYPE uxIndex )
{
static char cRxedChar, cExpectedChar = mainFIRST_TX_CHAR;
portBASE_TYPE xResult;

	crSTART( xHandle );

	for( ;; )
	{
		/* Wait for a character to be received. */
		crQUEUE_RECEIVE( xHandle, xCommsQueue, ( void * ) &cRxedChar, mainCOMMS_RX_DELAY, &xResult );

		/* Was the character recived (if any) the expected character. */
		if( ( cRxedChar != cExpectedChar ) || ( xResult != pdPASS ) )
		{
			/* Got an unexpected character.  This can sometimes occur when
			reseting the system using the debugger leaving characters already
			in the UART regsters. */
			uxErrorStatus = pdFAIL;

			/* Resync by waiting for the end of the current string. */
			while( cRxedChar != mainLAST_TX_CHAR )
			{
				crQUEUE_RECEIVE( xHandle, xCommsQueue, ( void * ) &cRxedChar, mainCOMMS_RX_DELAY, &xResult );
			}

			/* The next expected character is the start of the string again. */
			cExpectedChar = mainFIRST_TX_CHAR;
		}
		else
		{
			if( cExpectedChar == mainLAST_TX_CHAR )
			{
				/* We have reached the end of the string - we now expect to 
				receive the first character in the string again.   The LED is 
				toggled to indicate that the entire string was received without
				error. */
				vParTestToggleLED( mainCOMMS_RX_LED );
				cExpectedChar = mainFIRST_TX_CHAR;
			}
			else
			{
				/* We got the expected character, we now expect to receive the
				next character in the string. */
				cExpectedChar++;
			}
		}
	}

	crEND();
}
/*-----------------------------------------------------------*/

static void vSerialTxCoRoutine( xCoRoutineHandle xHandle, unsigned portBASE_TYPE uxIndex )
{
portTickType xDelayPeriod;
static unsigned long *pulRandomBytes = mainFIRST_PROGRAM_BYTES;

	/* Co-routine MUST start with a call to crSTART. */
	crSTART( xHandle );

	for(;;)
    {	
		/* Was the previously transmitted string received correctly? */
		if( uxErrorStatus != pdPASS )
		{
			/* An error was encountered so set the error LED. */
			vSetErrorLED();
		}

		/* The next character to Tx is the first in the string. */
		cNextChar = mainFIRST_TX_CHAR;

		UARTIntDisable( UART0_BASE, UART_INT_TX );
		{
			/* Send the first character. */
			if( !( HWREG( UART0_BASE + UART_O_FR ) & UART_FR_TXFF ) )
			{
				HWREG( UART0_BASE + UART_O_DR ) = cNextChar;
			}

			/* Move the variable to the char to Tx on so the ISR transmits
			the next character in the string once this one has completed. */
			cNextChar++;
		}
		UARTIntEnable(UART0_BASE, UART_INT_TX);

		/* Toggle the LED to show a new string is being transmitted. */
        vParTestToggleLED( mainCOMMS_TX_LED );

		/* Delay before we start the string off again.  A pseudo-random delay
		is used as this will provide a better test. */
		xDelayPeriod = xTaskGetTickCount() + ( *pulRandomBytes );

		pulRandomBytes++;
		if( pulRandomBytes > mainTOTAL_PROGRAM_MEMORY )
		{
			pulRandomBytes = mainFIRST_PROGRAM_BYTES;
		}

		/* Make sure we don't wait too long... */
		xDelayPeriod &= mainMAX_TX_DELAY;

		/* ...but we do want to wait. */
		if( xDelayPeriod < mainMIN_TX_DELAY )
		{
			xDelayPeriod = mainMIN_TX_DELAY;
		}

		/* Block for the random(ish) time. */
		crDELAY( xHandle, xDelayPeriod );
    }

	/* Co-routine MUST end with a call to crEND. */
	crEND();
}
/*-----------------------------------------------------------*/

static void vSerialInit( void )
{
	/* Enable the UART.  GPIOA has already been initialised. */
	SysCtlPeripheralEnable(SYSCTL_PERIPH_UART0);

	/* Set GPIO A0 and A1 as peripheral function.  They are used to output the
	UART signals. */
	GPIODirModeSet( GPIO_PORTA_BASE, GPIO_PIN_0 | GPIO_PIN_1, GPIO_DIR_MODE_HW );

	/* Configure the UART for 8-N-1 operation. */
	UARTConfigSet( UART0_BASE, mainBAUD_RATE, UART_CONFIG_WLEN_8 | UART_CONFIG_PAR_NONE | UART_CONFIG_STOP_ONE );

	/* We dont want to use the fifo.  This is for test purposes to generate
	as many interrupts as possible. */
	HWREG( UART0_BASE + UART_O_LCR_H ) &= ~mainFIFO_SET;

	/* Enable both Rx and Tx interrupts. */
	HWREG( UART0_BASE + UART_O_IM ) |= ( UART_INT_TX | UART_INT_RX );
	IntEnable( INT_UART0 );
}
/*-----------------------------------------------------------*/

void vUART_ISR(void)
{
unsigned long ulStatus;
char cRxedChar;
portBASE_TYPE xTaskWokenByPost = pdFALSE;

	/* What caused the interrupt. */
	ulStatus = UARTIntStatus( UART0_BASE, pdTRUE );

	/* Clear the interrupt. */
	UARTIntClear( UART0_BASE, ulStatus );

	/* Was an Rx interrpt pending? */
	if( ulStatus & UART_INT_RX )
	{
		if( ( HWREG(UART0_BASE + UART_O_FR ) & UART_FR_RXFF ) )
		{
			/* Get the char from the buffer and post it onto the queue of
			Rxed chars.  Posting the character should wake the task that is 
			blocked on the queue waiting for characters. */
			cRxedChar = ( char ) HWREG( UART0_BASE + UART_O_DR );
			xTaskWokenByPost = crQUEUE_SEND_FROM_ISR( xCommsQueue, &cRxedChar, xTaskWokenByPost );
		}		
	}

	/* Was a Tx interrupt pending? */
	if( ulStatus & UART_INT_TX )
	{
		/* Send the next character in the string.  We are not using the FIFO. */
		if( cNextChar <= mainLAST_TX_CHAR )
		{
			if( !( HWREG( UART0_BASE + UART_O_FR ) & UART_FR_TXFF ) )
			{
				HWREG( UART0_BASE + UART_O_DR ) = cNextChar;
			}
			cNextChar++;
		}
	}
	
	if( xTaskWokenByPost )
	{
		/* We are posting to a co-routine rather than a task so don't bother
		causing a task switch. */
	}
}
/*-----------------------------------------------------------*/

static void prvPDCWrite( char cAddress, char cData )
{
	vTaskSuspendAll();
	{
		PDCWrite( cAddress, cData );
	}
	xTaskResumeAll();
}
/*-----------------------------------------------------------*/

void vSetErrorLED( void )
{
	vParTestSetLED( mainCOMMS_FAIL_LED, pdTRUE );
}
/*-----------------------------------------------------------*/

void prvSetAndCheckRegisters( void )
{
	/* Fill the general purpose registers with known values. */
	__asm volatile
	( 
	"	mov r11, #10		\n"
	"	add r0, r11, #1		\n"
	"	add r1, r11, #2		\n"
	"	add r2, r11, #3		\n"
	"	add r3, r11, #4		\n"
	"	add r4, r11, #5		\n"
	"	add r5, r11, #6		\n"
	"	add r6, r11, #7		\n"
	"	add r7, r11, #8		\n"
	"	add r8, r11, #9		\n"
	"	add r9, r11, #10	\n"
	"	add r10, r11, #11	\n"
	"	add r12, r11, #12" 
	);

	/* Check the values are as expected. */
	__asm volatile
	( 
	"	cmp r11, #10		\n"
	"	bne set_error_led	\n"
	"	cmp r0, #11			\n"
	"	bne set_error_led	\n"
	"	cmp r1, #12			\n"
	"	bne set_error_led	\n"
	"	cmp r2, #13			\n"
	"	bne set_error_led	\n"
	"	cmp r3, #14			\n"
	"	bne set_error_led	\n"
	"	cmp r4, #15			\n"
	"	bne set_error_led	\n"
	"	cmp r5, #16			\n"
	"	bne set_error_led	\n"
	"	cmp r6, #17			\n"
	"	bne set_error_led	\n"
	"	cmp r7, #18			\n"
	"	bne set_error_led	\n"
	"	cmp r8, #19			\n"
	"	bne set_error_led	\n"
	"	cmp r9, #20			\n"
	"	bne set_error_led	\n"
	"	cmp r10, #21		\n"
	"	bne set_error_led	\n"
	"	cmp r12, #22		\n"
	"	bne set_error_led	\n"
	"	bx lr" 
	);

	__asm volatile
	(
	"set_error_led:			\n"
	"	push {r14}			\n"
	"	ldr r1, vSetErrorLEDConst\n"
	"	blx r1				\n"
	"	pop {r14}			\n"
	"	bx lr				\n"
	"						\n"
	"	.align 2			\n"
	"vSetErrorLEDConst: .word vSetErrorLED"
	);
}
/*-----------------------------------------------------------*/
