/*
	FreeRTOS.org V5.4.0 - Copyright (C) 2003-2009 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify it
	under the terms of the GNU General Public License (version 2) as published
	by the Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS.org without being obliged to provide
	the source code for any proprietary components.  Alternative commercial
	license and support terms are also available upon request.  See the
	licensing section of http://www.FreeRTOS.org for full details.

	FreeRTOS.org is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS.org; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


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


/*
 * Creates all the demo application tasks, then starts the scheduler.  The WEB
 * documentation provides more details of the standard demo application tasks
 * (which just exist to test the kernel port and provide an example of how to use
 * each FreeRTOS API function).
 *
 * In addition to the standard demo tasks, the following tasks and tests are
 * defined and/or created within this file:
 *
 * "LCD" task - the LCD task is a 'gatekeeper' task.  It is the only task that
 * is permitted to access the display directly.  Other tasks wishing to write a
 * message to the LCD send the message on a queue to the LCD task instead of
 * accessing the LCD themselves.  The LCD task just blocks on the queue waiting
 * for messages - waking and displaying the messages as they arrive.  The use
 * of a gatekeeper in this manner permits both tasks and interrupts to write to
 * the LCD without worrying about mutual exclusion.  This is demonstrated by the
 * check hook (see below) which sends messages to the display even though it
 * executes from an interrupt context.
 *
 * "Check" hook -  This only executes fully every five seconds from the tick
 * hook.  Its main function is to check that all the standard demo tasks are
 * still operational.  Should any unexpected behaviour be discovered within a
 * demo task then the tick hook will write an error to the LCD (via the LCD task).
 * If all the demo tasks are executing with their expected behaviour then the
 * check hook writes PASS to the LCD (again via the LCD task), as described above.
 * The check hook also toggles LED 4 each time it executes.
 *
 * LED tasks - These just demonstrate how multiple instances of a single task
 * definition can be created.  Each LED task simply toggles an LED.  The task
 * parameter is used to pass the number of the LED to be toggled into the task.
 *
 * "uIP" task -  This is the task that handles the uIP stack.  All TCP/IP
 * processing is performed in this task.
 */

/* Standard includes. */
#include <stdio.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* Hardware library includes. */
#include "LPC17xx_defs.h"

/* Demo app includes. */
#include "BlockQ.h"
#include "integer.h"
#include "blocktim.h"
#include "flash.h"
#include "partest.h"
#include "semtest.h"
#include "PollQ.h"
#include "GenQTest.h"
#include "QPeek.h"
#include "recmutex.h"


#if 0





/*-----------------------------------------------------------*/

/* The number of LED tasks that will be created. */
#define mainNUM_LED_TASKS					( 6 )

/* The time between cycles of the 'check' functionality (defined within the
tick hook. */
#define mainCHECK_DELAY						( ( portTickType ) 5000 / portTICK_RATE_MS )

/* Task priorities. */
#define mainQUEUE_POLL_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainSEM_TEST_PRIORITY				( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainUIP_TASK_PRIORITY				( tskIDLE_PRIORITY + 3 )
#define mainLCD_TASK_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainINTEGER_TASK_PRIORITY           ( tskIDLE_PRIORITY )
#define mainGEN_QUEUE_TASK_PRIORITY			( tskIDLE_PRIORITY )
#define mainFLASH_TASK_PRIORITY				( tskIDLE_PRIORITY + 2 )

/* The WEB server has a larger stack as it utilises stack hungry string
handling library calls. */
#define mainBASIC_WEB_STACK_SIZE            ( configMINIMAL_STACK_SIZE * 4 )

/* The length of the queue used to send messages to the LCD task. */
#define mainQUEUE_SIZE						( 3 )

/* The task that is toggled by the check task. */
#define mainCHECK_TASK_LED					( 4 )
/*-----------------------------------------------------------*/

/*
 * Configure the hardware for the demo.
 */
static void prvSetupHardware( void );

/*
 * Very simple task that toggles an LED.
 */
static void vLEDTask( void *pvParameters );

/*
 * The task that handles the uIP stack.  All TCP/IP processing is performed in
 * this task.
 */
extern void vuIP_Task( void *pvParameters );

/*
 * The LCD gatekeeper task as described in the comments at the top of this file.
 * */
static void vLCDTask( void *pvParameters );

/*-----------------------------------------------------------*/

/* The queue used to send messages to the LCD task. */
xQueueHandle xLCDQueue;

/*-----------------------------------------------------------*/

int main( void )
{
long l;

	/* Configure the hardware for use by this demo. */
	prvSetupHardware();

	/* Start the standard demo tasks.  These are just here to exercise the
	kernel port and provide examples of how the FreeRTOS API can be used. */
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
    vCreateBlockTimeTasks();
    vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
    vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
    vStartIntegerMathTasks( mainINTEGER_TASK_PRIORITY );
    vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );
    vStartQueuePeekTasks();
    vStartRecursiveMutexTasks();
	vStartLEDFlashTasks( mainFLASH_TASK_PRIORITY );

	/* Create the uIP task.  The WEB server runs in this task. */
    xTaskCreate( vuIP_Task, ( signed char * ) "uIP", mainBASIC_WEB_STACK_SIZE, ( void * ) NULL, mainUIP_TASK_PRIORITY, NULL );

	/* Create the queue used by the LCD task.  Messages for display on the LCD
	are received via this queue. */
	xLCDQueue = xQueueCreate( mainQUEUE_SIZE, sizeof( xLCDMessage ) );

	/* Start the LCD gatekeeper task - as described in the comments at the top
	of this file. */
	xTaskCreate( vLCDTask, ( signed portCHAR * ) "LCD", configMINIMAL_STACK_SIZE * 2, NULL, mainLCD_TASK_PRIORITY, NULL );

    /* Start the scheduler. */
	vTaskStartScheduler();

    /* Will only get here if there was insufficient memory to create the idle
    task.  The idle task is created within vTaskStartScheduler(). */
	for( ;; );
}
/*-----------------------------------------------------------*/

void vLCDTask( void *pvParameters )
{
xLCDMessage xMessage;
unsigned long ulRow = 0;
char cIPAddr[ 17 ]; /* To fit max IP address length of xxx.xxx.xxx.xxx\0 */

	( void ) pvParameters;

	/* The LCD gatekeeper task as described in the comments at the top of this
	file. */

	/* Initialise the LCD and display a startup message that includes the
	configured IP address. */
    sprintf( cIPAddr, "%d.%d.%d.%d", configIP_ADDR0, configIP_ADDR1, configIP_ADDR2, configIP_ADDR3 );

	for( ;; )
	{
		/* Wait for a message to arrive to be displayed. */
		while( xQueueReceive( xLCDQueue, &xMessage, portMAX_DELAY ) != pdPASS );

	}
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
static xLCDMessage xMessage = { "PASS" };
static unsigned portLONG ulTicksSinceLastDisplay = 0;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	/* Called from every tick interrupt as described in the comments at the top
	of this file.

	Have enough ticks passed to make it	time to perform our health status
	check again? */
	ulTicksSinceLastDisplay++;
	if( ulTicksSinceLastDisplay >= mainCHECK_DELAY )
	{
		/* Reset the counter so these checks run again in mainCHECK_DELAY
		ticks time. */
		ulTicksSinceLastDisplay = 0;

		/* Has an error been found in any task? */
		if( xAreGenericQueueTasksStillRunning() != pdTRUE )
		{
			xMessage.pcMessage = "ERROR: GEN Q";
		}
		else if( xAreQueuePeekTasksStillRunning() != pdTRUE )
		{
			xMessage.pcMessage = "ERROR: PEEK Q";
		}
		else if( xAreBlockingQueuesStillRunning() != pdTRUE )
		{
			xMessage.pcMessage = "ERROR: BLOCK Q";
		}
		else if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
		{
			xMessage.pcMessage = "ERROR: BLOCK TIME";
		}
	    else if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	    {
	        xMessage.pcMessage = "ERROR: SEMAPHR";
	    }
	    else if( xArePollingQueuesStillRunning() != pdTRUE )
	    {
	        xMessage.pcMessage = "ERROR: POLL Q";
	    }
	    else if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
	    {
	        xMessage.pcMessage = "ERROR: INT MATH";
	    }
	    else if( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
	    {
	    	xMessage.pcMessage = "ERROR: REC MUTEX";
	    }

		/* Send the message to the OLED gatekeeper for display.  The
		xHigherPriorityTaskWoken parameter is not actually used here
		as this function is running in the tick interrupt anyway - but
		it must still be supplied. */
		xHigherPriorityTaskWoken = pdFALSE;
		xQueueSendFromISR( xLCDQueue, &xMessage, &xHigherPriorityTaskWoken );

		/* Also toggle and LED.  This can be done from here because in this port
		the LED toggling functions don't use critical sections. */
        vParTestToggleLED( mainCHECK_TASK_LED );
	}
}
/*-----------------------------------------------------------*/

void prvSetupHardware( void )
{
	/* Disable peripherals power. */
	PCONP = 0;

	/* Enable GPIO power. */
	PCONP = PCONP_PCGPIO;

	/* Disable TPIU. */
	PINSEL10 = 0;

	/* Disconnect the main PLL. */
	PLL0CON &= ~PLLCON_PLLC;
	PLL0FEED = PLLFEED_FEED1;
	PLL0FEED = PLLFEED_FEED2;
	while ((PLL0STAT & PLLSTAT_PLLC) != 0);

	/* Turn off the main PLL. */
	PLL0CON &= ~PLLCON_PLLE;
	PLL0FEED = PLLFEED_FEED1;
	PLL0FEED = PLLFEED_FEED2;
	while ((PLL0STAT & PLLSTAT_PLLE) != 0);

	/* No CPU clock divider. */
	CCLKCFG = 0;

	/* OSCEN. */
	SCS = 0x20;
	while ((SCS & 0x40) == 0);

	/* Use main oscillator. */
	CLKSRCSEL = 1;
	PLL0CFG = (PLLCFG_MUL16 | PLLCFG_DIV1);

	PLL0FEED = PLLFEED_FEED1;
	PLL0FEED = PLLFEED_FEED2;

	/*  Activate the PLL by turning it on then feeding the correct
	sequence of bytes. */
	PLL0CON  = PLLCON_PLLE;
	PLL0FEED = PLLFEED_FEED1;
	PLL0FEED = PLLFEED_FEED2;

	/* 6x CPU clock divider (64 MHz) */
	CCLKCFG = 5;

	/*  Wait for the PLL to lock. */
	while ((PLL0STAT & PLLSTAT_PLOCK) == 0);

	/*  Connect the PLL. */
	PLL0CON  = PLLCON_PLLC | PLLCON_PLLE;
	PLL0FEED = PLLFEED_FEED1;
	PLL0FEED = PLLFEED_FEED2;

	/*  Setup the peripheral bus to be the same as the PLL output (64 MHz). */
	PCLKSEL0 = 0x05555555;

	/* Configure the LEDs. */
	vParTestInitialise();
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( xTaskHandle *pxTask, signed portCHAR *pcTaskName )
{
	/* This function will get called if a task overflows its stack. */

	( void ) pxTask;
	( void ) pcTaskName;

	for( ;; );
}
/*-----------------------------------------------------------*/

void vConfigureTimerForRunTimeStats( void )
{
const unsigned long TCR_COUNT_RESET = 2, CTCR_CTM_TIMER = 0x00, TCR_COUNT_ENABLE = 0x01;

	/* This function configures a timer that is used as the time base when
	collecting run time statistical information - basically the percentage
	of CPU time that each task is utilising.  It is called automatically when
	the scheduler is started (assuming configGENERATE_RUN_TIME_STATS is set
	to 1. */

	/* Power up and feed the timer. */
	PCONP |= 0x02UL;
	PCLKSEL0 = (PCLKSEL0 & (~(0x3<<2))) | (0x01 << 2);

	/* Reset Timer 0 */
	T0TCR = TCR_COUNT_RESET;

	/* Just count up. */
	T0CTCR = CTCR_CTM_TIMER;

	/* Prescale to a frequency that is good enough to get a decent resolution,
	but not too fast so as to overflow all the time. */
	T0PR =  ( configCPU_CLOCK_HZ / 10000UL ) - 1UL;

	/* Start the counter. */
	T0TCR = TCR_COUNT_ENABLE;
}
/*-----------------------------------------------------------*/

#else





/*----------------------------------------------------------------------*/
/* FAT file system sample project for FatFs R0.06  (C)ChaN, 2008        */
/*----------------------------------------------------------------------*/


#include <string.h>
#include "LPC17xx.h"
#include "integer.h"
//#include "interrupt.h"
#include "comm.h"
#include "monitor.h"
#include "rtc.h"
#include "diskio.h"
#include "ff.h"

#include "ctl_api.h"

#include "usbhost_lpc1768.h"

DWORD acc_size;				/* Work register for fs command */
WORD acc_files, acc_dirs;
FILINFO finfo;

char linebuf[120];			/* Console input buffer */

FATFS fatfs[_DRIVES];		/* File system object for each logical drive */
FIL file1, file2;			/* File objects */
DIR dir;					/* Directory object */
BYTE Buff[16384] __attribute__ ((aligned (4))) ;		/* Working buffer */

volatile UINT Timer;		/* Performance timer (1kHz increment) */



/*---------------------------------------------------------*/
/* 1000Hz timer interrupt generated by TIMER0              */
/*---------------------------------------------------------*/

void Isr_TIMER0 (void)
{
	T0IR = 1;			/* Clear irq flag */

	Timer++;
   MMC_TimerProc();
}



/*---------------------------------------------------------*/
/* User Provided Timer Function for FatFs module           */
/*---------------------------------------------------------*/
/* This is a real time clock service to be called from     */
/* FatFs module. Any valid time must be returned even if   */
/* the system does not support a real time clock.          */
/* This is not required in read-only configuration.        */


DWORD get_fattime ()
{
	RTC rtc;

	rtc_gettime(&rtc);

	return	        ((DWORD)(rtc.year) << 25)
			| ((DWORD)rtc.month << 21)
			| ((DWORD)rtc.mday << 16)
			| ((DWORD)rtc.hour << 11)
			| ((DWORD)rtc.min << 5)
			| ((DWORD)rtc.sec >> 1);
}


/*--------------------------------------------------------------------------*/
/* Monitor                                                                  */
/*--------------------------------------------------------------------------*/

static
FRESULT scan_files (char* path)
{
	DIR dirs;
	FRESULT res;
	BYTE i;


	if ((res = f_opendir(&dirs, path)) == FR_OK) {
		i = strlen(path);
		while (((res = f_readdir(&dirs, &finfo)) == FR_OK) && finfo.fname[0]) {
			if (finfo.fattrib & AM_DIR) {
				acc_dirs++;
				*(path+i) = '/'; strcpy(path+i+1, &finfo.fname[0]);
				res = scan_files(path);
				*(path+i) = '\0';
				if (res != FR_OK) break;
			} else {
				acc_files++;
				acc_size += finfo.fsize;
			}
		}
	}

	return res;
}



static
void put_rc (FRESULT rc)
{
	const char *p;
	static const char str[] =
		"OK\0" "NOT_READY\0" "NO_FILE\0" "FR_NO_PATH\0" "INVALID_NAME\0" "INVALID_DRIVE\0"
		"DENIED\0" "EXIST\0" "RW_ERROR\0" "WRITE_PROTECTED\0" "NOT_ENABLED\0"
		"NO_FILESYSTEM\0" "INVALID_OBJECT\0" "MKFS_ABORTED\0";
	FRESULT i;

	for (p = str, i = 0; i != rc && *p; i++) {
		while(*p++);
	}
	xprintf("rc=%u FR_%s\n", (UINT)rc, p);
}



static
void IoInit (void)
{
#define PLL_N		1UL
#define PLL_M		12UL
#define CCLK_DIV	4   // 288MHz / 4 = 72MHz
#define USBCLK_DIV      6   // 288MHz / 6 = 48MHz

//_RB_	if ( PLLSTAT & (1 << 25) ) {
//_RB_		PLLCON = 1;				/* Disconnect PLL output if PLL is in use */
//_RB_		PLLFEED = 0xAA; PLLFEED = 0x55;
//_RB_	}
//_RB_	PLLCON = 0;				/* Disable PLL */
//_RB_	PLLFEED = 0xAA; PLLFEED = 0x55;
	CLKSRCSEL = 0;			/* Select IRC (4MHz) as the PLL clock source */

   SCS |= 0x20;			/* Enable main OSC */
   while( !(SCS & 0x40) );	/* Wait until main OSC is usable */
   CLKSRCSEL = 0x1;		/* select main OSC, 12MHz, as the PLL clock source */

//_RB_	PLLCFG = ((PLL_N - 1) << 16) | (PLL_M - 1);	/* Re-configure PLL */
//_RB_	PLLFEED = 0xAA; PLLFEED = 0x55;
//_RB_	PLLCON = 1;				/* Enable PLL */
//_RB_	PLLFEED = 0xAA; PLLFEED = 0x55;

//_RB_	while ((PLLSTAT & (1 << 26)) == 0);	/* Wait for PLL locked */

	CCLKCFG = CCLK_DIV-1;	/* Select CCLK frequency (divide ratio of hclk) */
   USBCLKCFG = USBCLK_DIV-1;		/* usbclk = 288 MHz/6 = 48 MHz */
//_RB_   PLLCON = 3;				/* Connect PLL output to the sysclk */
//_RB_	PLLFEED = 0xAA; PLLFEED = 0x55;

//_RB_	MAMCR = 0;				/* Configure MAM for 72MHz operation */
//_RB_	MAMTIM = 3;
//_RB_	MAMCR = 2;

	PCLKSEL0 = 0x00000000;	/* Initialize peripheral clock to default */
	PCLKSEL1 = 0x00000000;

//	ClearVector();			/* Initialie VIC */

	SCS |= 1;				/* Enable FIO0 and FIO1 */

   FIO1DIR = (1<<26);                      /* Disable Piezo */
	FIO2CLR = (1<<26);

	FIO2DIR = (1<<30);                      /* Heartbeat LED output */
	FIO2CLR = (1<<30);

	/* Initialize Timer0 as 1kHz interval timer */
//	RegisterVector(TIMER0_INT, Isr_TIMER0, PRI_LOWEST, CLASS_IRQ);
//_RB_   ctl_set_isr(TIMER0_INT, PRI_LOWEST, CTL_ISR_TRIGGER_FIXED, Isr_TIMER0, 0);
//_RB_   ctl_unmask_isr(TIMER0_INT);

   T0CTCR = 0;
	T0MR0 = 18000 - 1;		/* 18M / 1k = 18000 */
	T0MCR = 0x3;			/* Clear TC and Interrupt on MR0 match */
	T0TCR = 1;

	uart0_init();			/* Initialize UART0 */

//	IrqEnable();			/* Enable Irq */
   ctl_global_interrupts_enable();
}



int main (void)
{
	char *ptr, *ptr2;
	long p1, p2, p3;
	BYTE res, b1;
	WORD w1;
	UINT s1, s2, cnt, blen = sizeof(Buff);
	DWORD ofs = 0, sect = 0;
	FATFS *fs;				/* Pointer to file system object */
	RTC rtc;

   BYTE ActiveDisk = 0;

   USB_INT32S  rc;

	IoInit();
   Host_Init();

	xputs("\nFatFs module test monitor for LPC2468\n");
   xputc('>');
   ptr = linebuf;

	for (;;) {
      if (ConnectedDeviceState == DEVICE_CONNECTED) {
         ConnectedDeviceState = DEVICE_CLEAR;
         xprintf("USB Mass Storage device detected\n");
         rc = Host_EnumDev();       // Enumerate the device connected

         if (rc == OK) {
            xprintf("USB device enumerated\n");
         }
         xputc('>');
      }
      else if (ConnectedDeviceState == DEVICE_DISCONNECTED) {
         ConnectedDeviceState = DEVICE_CLEAR;
         Host_Init();         // FreeDevice();
         xprintf("Device Disconnected\n");
         xputc('>');
      }

		if (get_line(ptr, sizeof(linebuf)) == '\r') {
         switch (*ptr++) {

         case 'm' :
            switch (*ptr++) {
            case 'd' :	/* md <address> [<count>] - Dump memory */
               if (!xatoi(&ptr, &p1)) break;
               if (!xatoi(&ptr, &p2)) p2 = 128;
               for (ptr=(char*)p1; p2 >= 16; ptr += 16, p2 -= 16) {
                  put_dump((BYTE*)ptr, (UINT)ptr, 16);
               }
               if (p2) put_dump((BYTE*)ptr, (UINT)ptr, p2);
               break;
            }
            break;

         case 'd' :
            switch (*ptr++) {
            case 'a' :  /* da [#] - select active disk */
               if (xatoi(&ptr, &p1)) {
                  ActiveDisk = (BYTE)p1;
               }
               ActiveDisk = VerifyActiveDisk(ActiveDisk);
               break;

            case 'd' :	/* dd [<lba>] - Dump secrtor */
               if (!xatoi(&ptr, &p2)) p2 = sect;
               res = disk_read(ActiveDisk, Buff, p2, 1);
//               res = disk_read(ActiveDisk, gUsbXferBuffer, p2, 1);
               if (res) { xprintf("rc=%d\n", (WORD)res); break; }
               sect = p2 + 1;
               xprintf("Sector:%lu\n", p2);
               for (ptr=(char*)Buff, ofs = 0; ofs < 0x200; ptr+=16, ofs+=16) {
//               for (ptr=(char*)gUsbXferBuffer, ofs = 0; ofs < 0x200; ptr+=16, ofs+=16) {
                  put_dump((BYTE*)ptr, ofs, 16);
               }
               break;

            case 'i' :	/* di - Initialize disk */
               xprintf("rc=%d\n", (WORD)disk_initialize(ActiveDisk));
               break;

            case 's' :	/* ds <phy_drv#> - Show disk status */
//            	if (!xatoi(&ptr, &p1)) break;
               if (disk_ioctl(ActiveDisk, GET_SECTOR_COUNT, &p2) == RES_OK)
                  { xprintf("Drive size: %lu sectors\n", p2); }
               if (disk_ioctl(ActiveDisk, GET_SECTOR_SIZE, &w1) == RES_OK)
                  { xprintf("Sector size: %u\n", w1); }
               if (disk_ioctl(ActiveDisk, GET_BLOCK_SIZE, &p2) == RES_OK)
                  { xprintf("Erase block size: %lu sectors\n", p2); }
               if (disk_ioctl(ActiveDisk, MMC_GET_TYPE, &b1) == RES_OK)
                  { xprintf("MMC/SDC type: %u\n", b1); }
               if (disk_ioctl(ActiveDisk, MMC_GET_CSD, Buff) == RES_OK)
                  { xputs("CSD:\n"); put_dump(Buff, 0, 16); }
               if (disk_ioctl(ActiveDisk, MMC_GET_CID, Buff) == RES_OK)
                  { xputs("CID:\n"); put_dump(Buff, 0, 16); }
               if (disk_ioctl(ActiveDisk, MMC_GET_OCR, Buff) == RES_OK)
                  { xputs("OCR:\n"); put_dump(Buff, 0, 4); }
               if (disk_ioctl(ActiveDisk, MMC_GET_SDSTAT, Buff) == RES_OK) {
                  xputs("SD Status:\n");
                  for (s1 = 0; s1 < 64; s1 += 16) put_dump(Buff+s1, s1, 16);
               }
               break;
            }
            break;

         case 'b' :
            switch (*ptr++) {
            case 'd' :	/* bd <addr> - Dump R/W buffer */
               if (!xatoi(&ptr, &p1)) break;
               for (ptr=(char*)&Buff[p1], ofs = p1, cnt = 32; cnt; cnt--, ptr+=16, ofs+=16) {
                  put_dump((BYTE*)ptr, ofs, 16);
               }
               break;

            case 'e' :	/* be <addr> [<data>] ... - Edit R/W buffer */
               if (!xatoi(&ptr, &p1)) break;
               if (xatoi(&ptr, &p2)) {
                  do {
                     Buff[p1++] = (BYTE)p2;
                  } while (xatoi(&ptr, &p2));
                  break;
               }
               for (;;) {
                  xprintf("%04X %02X-", (WORD)(p1), (WORD)Buff[p1]);
                  get_line(linebuf, sizeof(linebuf));
                  ptr = linebuf;
                  if (*ptr == '.') break;
                  if (*ptr < ' ') { p1++; continue; }
                  if (xatoi(&ptr, &p2))
                     Buff[p1++] = (BYTE)p2;
                  else
                     xputs("???\n");
               }
               break;

            case 'r' :	/* br <lba> [<num>] - Read disk into R/W buffer */
               if (!xatoi(&ptr, &p2)) break;
               if (!xatoi(&ptr, &p3)) p3 = 1;
               xprintf("rc=%u\n", (WORD)disk_read(ActiveDisk, Buff, p2, p3));
               break;

            case 'w' :	/* bw <lba> [<num>] - Write R/W buffer into disk */
               if (!xatoi(&ptr, &p2)) break;
               if (!xatoi(&ptr, &p3)) p3 = 1;
               xprintf("rc=%u\n", (WORD)disk_write(ActiveDisk, Buff, p2, p3));
               break;

            case 'f' :	/* bf <val> - Fill working buffer */
               if (!xatoi(&ptr, &p1)) break;
               memset(Buff, (BYTE)p1, sizeof(Buff));
               break;
            }
            break;

         case 'f' :
            switch (*ptr++) {

            case 'i' :	/* fi <log drv#> - Initialize logical drive */
               if (!xatoi(&ptr, &p1)) break;
               put_rc(f_mount((BYTE)p1, &fatfs[p1]));
//               put_rc(f_mount(ActiveDisk, &fatfs[ActiveDisk]));
               break;

            case 's' :	/* fs [<path>] - Show logical drive status */
               res = f_getfree(ptr, (DWORD*)&p2, &fs);
               if (res) { put_rc(res); break; }
               xprintf("FAT type = %u\nBytes/Cluster = %lu\nNumber of FATs = %u\n"
                  "Root DIR entries = %u\nSectors/FAT = %lu\nNumber of clusters = %lu\n"
                  "FAT start (lba) = %lu\nDIR start (lba,cluster) = %lu\nData start (lba) = %lu\n\n",
						(WORD)fs->fs_type, (DWORD)fs->csize * 512, (WORD)fs->n_fats,
						fs->n_rootdir, fs->sects_fat, (DWORD)fs->max_clust - 2,
						fs->fatbase, fs->dirbase, fs->database
               );
               acc_size = acc_files = acc_dirs = 0;
               res = scan_files(ptr);
               if (res) { put_rc(res); break; }
               xprintf("%u files, %lu bytes.\n%u folders.\n"
						"%lu KB total disk space.\n%lu KB available.\n",
						acc_files, acc_size, acc_dirs,
						(fs->max_clust - 2) * (fs->csize / 2), p2 * (fs->csize / 2)
               );
               break;

            case 'l' :	/* fl [<path>] - Directory listing */
               res = f_opendir(&dir, ptr);
               if (res) { put_rc(res); break; }
               p1 = s1 = s2 = 0;
               for(;;) {
                  res = f_readdir(&dir, &finfo);
                  if ((res != FR_OK) || !finfo.fname[0]) break;
                  if (finfo.fattrib & AM_DIR) {
                     s2++;
                  } else {
                     s1++; p1 += finfo.fsize;
                  }
                  xprintf("%c%c%c%c%c %u/%02u/%02u %02u:%02u %9lu  %s\n",
							(finfo.fattrib & AM_DIR) ? 'D' : '-',
							(finfo.fattrib & AM_RDO) ? 'R' : '-',
							(finfo.fattrib & AM_HID) ? 'H' : '-',
							(finfo.fattrib & AM_SYS) ? 'S' : '-',
							(finfo.fattrib & AM_ARC) ? 'A' : '-',
                     (finfo.fdate >> 9) + 1980, (finfo.fdate >> 5) & 15, finfo.fdate & 31,
							(finfo.ftime >> 11), (finfo.ftime >> 5) & 63,
							finfo.fsize, &(finfo.fname[0]));
               }
               xprintf("%4u File(s),%10lu bytes total\n%4u Dir(s)", s1, p1, s2);
               if (f_getfree(ptr, (DWORD*)&p1, &fs) == FR_OK)
                  xprintf(", %10lu bytes free\n", p1 * fs->csize * 512);
               break;

            case 'o' :	/* fo <mode> <file> - Open a file */
               if (!xatoi(&ptr, &p1)) break;
               put_rc(f_open(&file1, ptr, (BYTE)p1));
               break;

            case 'c' :	/* fc - Close a file */
               put_rc(f_close(&file1));
               break;

            case 'e' :	/* fe - Seek file pointer */
               if (!xatoi(&ptr, &p1)) break;
               res = f_lseek(&file1, p1);
               put_rc(res);
               if (res == FR_OK)
                  xprintf("fptr=%lu(0x%lX)\n", file1.fptr, file1.fptr);
               break;

            case 'd' :	/* fd <len> - read and dump file from current fp */
               if (!xatoi(&ptr, &p1)) break;
               ofs = file1.fptr;
               while (p1) {
                  if ((UINT)p1 >= 16) { cnt = 16; p1 -= 16; }
                  else 				{ cnt = p1; p1 = 0; }
                  res = f_read(&file1, Buff, cnt, &cnt);
                  if (res != FR_OK) { put_rc(res); break; }
                  if (!cnt) break;
                  put_dump(Buff, ofs, cnt);
                  ofs += 16;
               }
               break;

            case 'r' :	/* fr <len> - read file */
               if (!xatoi(&ptr, &p1)) break;
               p2 = 0;
               Timer = 0;
               while (p1) {
                  if ((UINT)p1 >= blen) {
                     cnt = blen; p1 -= blen;
                  } else {
                     cnt = p1; p1 = 0;
                  }
                  res = f_read(&file1, Buff, cnt, &s2);
                  if (res != FR_OK) { put_rc(res); break; }
                  p2 += s2;
                  if (cnt != s2) break;
               }
               xprintf("%lu bytes read with %lu kB/sec.\n", p2, p2 / Timer);
               break;

            case 'w' :	/* fw <len> <val> - write file */
               if (!xatoi(&ptr, &p1) || !xatoi(&ptr, &p2)) break;
               memset(Buff, (BYTE)p2, blen);
               p2 = 0;
               Timer = 0;
               while (p1) {
                  if ((UINT)p1 >= blen) {
                     cnt = blen; p1 -= blen;
                  } else {
                     cnt = p1; p1 = 0;
                  }
                  res = f_write(&file1, Buff, cnt, &s2);
                  if (res != FR_OK) { put_rc(res); break; }
                  p2 += s2;
                  if (cnt != s2) break;
               }
               xprintf("%lu bytes written with %lu kB/sec.\n", p2, p2 / Timer);
               break;

            case 'n' :	/* fn <old_name> <new_name> - Change file/dir name */
               while (*ptr == ' ') ptr++;
               ptr2 = strchr(ptr, ' ');
               if (!ptr2) break;
               *ptr2++ = 0;
               while (*ptr2 == ' ') ptr2++;
               put_rc(f_rename(ptr, ptr2));
               break;

            case 'u' :	/* fu <name> - Unlink a file or dir */
               put_rc(f_unlink(ptr));
               break;

            case 'v' :	/* fv - Truncate file */
               put_rc(f_truncate(&file1));
               break;

            case 'k' :	/* fk <name> - Create a directory */
               put_rc(f_mkdir(ptr));
               break;

            case 'a' :	/* fa <atrr> <mask> <name> - Change file/dir attribute */
               if (!xatoi(&ptr, &p1) || !xatoi(&ptr, &p2)) break;
               put_rc(f_chmod(ptr, p1, p2));
               break;

            case 't' :	/* ft <year> <month> <day> <hour> <min> <sec> <name> - Change timestamp */
               if (!xatoi(&ptr, &p1) || !xatoi(&ptr, &p2) || !xatoi(&ptr, &p3)) break;
               finfo.fdate = ((p1 - 1980) << 9) | ((p2 & 15) << 5) | (p3 & 31);
               if (!xatoi(&ptr, &p1) || !xatoi(&ptr, &p2) || !xatoi(&ptr, &p3)) break;
               finfo.ftime = ((p1 & 31) << 11) | ((p1 & 63) << 5) | ((p1 >> 1) & 31);
               put_rc(f_utime(ptr, &finfo));
               break;

            case 'x' : /* fx <src_name> <dst_name> - Copy file */
               while (*ptr == ' ') ptr++;
               ptr2 = strchr(ptr, ' ');
               if (!ptr2) break;
               *ptr2++ = 0;
               while (*ptr2 == ' ') ptr2++;
               xprintf("Opening \"%s\"", ptr);
               res = f_open(&file1, ptr, FA_OPEN_EXISTING | FA_READ);
               xputc('\n');
               if (res) {
                  put_rc(res);
                  break;
               }
               xprintf("Creating \"%s\"", ptr2);
               res = f_open(&file2, ptr2, FA_CREATE_ALWAYS | FA_WRITE);
               xputc('\n');
               if (res) {
                  put_rc(res);
                  f_close(&file1);
                  break;
               }
               xprintf("Copying file...");
               Timer = 0;
               p1 = 0;
               for (;;) {
                  res = f_read(&file1, Buff, blen, &s1);
                  if (res || s1 == 0) break;   /* error or eof */
                  res = f_write(&file2, Buff, s1, &s2);
                  p1 += s2;
                  if (res || s2 < s1) break;   /* error or disk full */
               }
               xprintf("%lu bytes copied with %lu kB/sec.\n", p1, p1 / Timer);
               f_close(&file1);
               f_close(&file2);
               break;
#if _USE_MKFS
            case 'm' :	/* fm <partition rule> <cluster size> - Create file system */
               if (!xatoi(&ptr, &p2) || !xatoi(&ptr, &p3)) break;
               xprintf("The drive %u will be formatted. Are you sure? (Y/n)=", ActiveDisk);
               get_line(ptr, sizeof(linebuf));
               if (*ptr == 'Y')
                  put_rc(f_mkfs(ActiveDisk, (BYTE)p2, (WORD)p3));
               break;
#endif
            case 'z' :	/* fz [<rw size>] - Change R/W length for fr/fw/fx command */
               if (xatoi(&ptr, &p1) && p1 >= 1 && p1 <= sizeof(Buff))
                  blen = p1;
               xprintf("blen=%u\n", blen);
               break;
            }
            break;

         case 't' :	/* t [<year> <mon> <mday> <hour> <min> <sec>] */
            if (xatoi(&ptr, &p1)) {
               rtc.year = (WORD)p1;
               xatoi(&ptr, &p1); rtc.month = (BYTE)p1;
               xatoi(&ptr, &p1); rtc.mday = (BYTE)p1;
               xatoi(&ptr, &p1); rtc.hour = (BYTE)p1;
               xatoi(&ptr, &p1); rtc.min = (BYTE)p1;
               if (!xatoi(&ptr, &p1)) break;
               rtc.sec = (BYTE)p1;
               rtc_settime(&rtc);
            }
            rtc_gettime(&rtc);
            xprintf("%u/%u/%u %02u:%02u:%02u\n", rtc.year, rtc.month, rtc.mday, rtc.hour, rtc.min, rtc.sec);
            break;

         case 'u' : /* usb test commands */
            switch (*ptr++) {

            case 's' :	/* print bulk size */
            xprintf("MS Bulk size %lu\n", MS_BlkSize);
            break;
            }
         break;
         }
         xputc('>');
         ptr = linebuf;
      }
   }
}

void vApplicationTickHook( void )
{
}
/*-----------------------------------------------------------*/


void vConfigureTimerForRunTimeStats( void )
{
}

void vApplicationStackOverflowHook( xTaskHandle *pxTask, signed portCHAR *pcTaskName )
{
}
xQueueHandle xLCDQueue;
#endif
