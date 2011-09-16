/***********************************************************************************
Filename: lcd.c
DESCRIPTION   LCD Module utility functions.
		Written for KS0066u compatible LCD Module.
		(8 characters by 2 lines)

Copyright   : 2006 Renesas Technology Europe Ltd.
Copyright   : 2006 Renesas Technology Corporation.
All Rights Reserved

***********************************************************************************/

/***********************************************************************************
Revision History
DD.MM.YYYY OSO-UID Description
26.07.2006 RTE-MBA First Release
***********************************************************************************/

/**********************************************************************************
System Includes
***********************************************************************************/
#include <machine.h>

/**********************************************************************************
User Includes
***********************************************************************************/
/* iodefine.h provides a structure to access all of the device registers. */
#include "iodefine.h"
/* rsk1664def.h provides common defines for widely used items. */
#include "rskrx210def.h"
#include "lcd.h"

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"


/**********************************************************************************
Global variables
***********************************************************************************/
xQueueHandle SwitchQueue;
xSemaphoreHandle LCD_Mutex;

char datastring[]=
"........Rx210 Highlights....1.56 DMips/MHz....DSP functions....1.62V-5.5V operation....200 uA/MHz....Up to 512 kBytes Flash....up to 64 kbytes SRAM....EE Dataflash with 100k w/e....1.3 uA in Real Time Clock Mode....Powerful Motor control timer....4 x 16-bit timers....4 x 8-bit timers....Full Real Time Clock calendar with calibration and alarm functions....Up to 16 channels 1 uS 12-bit ADC, with Dual group programmable SCAN, 3 sample and holds, sample accumulate function....DMA controller....Data Transfer Controller....Up to 9 serial Channels....Up to 6 USARTs ( with Simple I2C / SPI )....USART ( with unique Frame based protocol support )....Multimaster IIC....RSPI....Temperature Sensor....Event Link Controller....Comparators....Safety features include CRC....March X....Dual watchdog Timers with window and independent oscillator....ADC self test....I/O Pin Test....Supported with E1 on chip debugger and RSK210 evaluation system....Rx210 Highlights........";



struct _LCD_Params Line1 = 
{
	LCD_LINE1, 215, datastring	
};

struct _LCD_Params Line2 = 
{
	LCD_LINE2, 350, datastring	
};



/**********************************************************************************
User Program Code
***********************************************************************************/

/*****************************************************************************
Name:			InitDisplay 
Parameters:		none				
Returns:		none
Description:	Intializes the LCD display. 
*****************************************************************************/
void InitialiseDisplay( void )
{
	/* Power Up Delay for LCD Module */
	EN_PIN = SET_BIT_HIGH;
	DisplayDelay(7000);
	EN_PIN = SET_BIT_LOW;
  
	/* Display initialises in 8 bit mode - so send one write (seen as 8 bit)
		to set to 4 bit mode. */

	/* Function Set */
	LCD_nibble_write(CTRL_WR,0x03);
	LCD_nibble_write(CTRL_WR,0x03);
	DisplayDelay(39);
 
	/* Configure display */
	LCD_nibble_write(CTRL_WR,0x03);
	LCD_nibble_write(CTRL_WR,0x02);
	LCD_nibble_write(CTRL_WR,(LCD_DISPLAY_ON | LCD_TWO_LINE ));
	LCD_nibble_write(CTRL_WR,(LCD_DISPLAY_ON | LCD_TWO_LINE ));
	DisplayDelay(39);

	/* Display ON/OFF control */
	LCD_write(CTRL_WR,LCD_CURSOR_OFF);
	DisplayDelay(39);

	/* Display Clear */
	LCD_write(CTRL_WR,LCD_CLEAR);
	DisplayDelay(1530);

	/* Entry Mode Set */
	LCD_write(CTRL_WR,0x06);
	LCD_write(CTRL_WR,LCD_HOME_L1);
}
/**********************************************************************************
End of function InitialiseDisplay
***********************************************************************************/   

/*****************************************************************************
Name:		DisplayString   
Parameters:	position  Line number of display
			string	Pointer to data to be written to display.
					Last character should be null.
Returns:	none

Description:	This function controls LCD writes to line 1 or 2 of the LCD.
				You need to use the defines LCD_LINE1 and LCD_LINE2 in order
				to specify the starting position.
				For example, to start at the 2nd position on line 1...
				DisplayString(LCD_LINE1 + 1, "Hello")
*****************************************************************************/
void DisplayString(unsigned char position, char * string)
{
	static unsigned char next_pos = 0xFF;

	/* Set line position if needed. We don't want to if we don't need 
		to because LCD control operations take longer than LCD data
		operations. */
	if( next_pos != position)
	{
		if(position < LCD_LINE2)
		{
			/* Display on Line 1 */
			LCD_write(CTRL_WR, (unsigned char)(LCD_HOME_L1 + position) );
		}
		else
		{
			/* Display on Line 2 */
			LCD_write(CTRL_WR, (unsigned char)(LCD_HOME_L2 + position - LCD_LINE2) );
		}
		/* set position index to known value */
		next_pos = position;	
	}

	do
	{
		LCD_write(DATA_WR,*string++);
		/* increment position index */
		next_pos++;	   
	}
	while(*string);
}
/**********************************************************************************
End of function DisplayString
***********************************************************************************/   

/*****************************************************************************
Name:		LCD_write
Parameters:	value - the value to write
			data_or_ctrl - To write value as DATA or CONTROL
							1 = DATA
							0 = CONTROL
Returns:	none

Description:	Writes data to display. Sends command to display.  
*****************************************************************************/
void LCD_write(unsigned char data_or_ctrl, unsigned char value)
{
	/* Write upper nibble first */
	LCD_nibble_write(data_or_ctrl, (value & 0xF0) >> 4);

	/* Write lower nibble second */
	LCD_nibble_write(data_or_ctrl, (value & 0x0F));
}
/**********************************************************************************
End of function LCD_write
***********************************************************************************/   

/*****************************************************************************
Name:		LCD_nibble_write
Parameters:	value - the value to write
			data_or_ctrl - To write value as DATA or CONTROL
							1 = DATA
							0 = CONTROL
Returns:	none

Description:	Writes data to display. Sends command to display.  
*****************************************************************************/
void LCD_nibble_write(unsigned char data_or_ctrl, unsigned char value)
{
	unsigned char ucStore;
	if (data_or_ctrl == DATA_WR)
	{
		RS_PIN = SET_BIT_HIGH;
	}
	else
	{
		RS_PIN = SET_BIT_LOW;
	}
	/* There must be 40ns between RS write and EN write */
	DisplayDelay(1);
	/* EN enable chip (HIGH) */
	EN_PIN = SET_BIT_HIGH;
	/* Tiny delay */		
	DisplayDelay(1);
	/* Clear port bits used */  
	/* Set upper lower 4 bits of nibble on port pins. */
	ucStore = DATA_PORT;
	ucStore &= ~DATA_PORT_MASK;
	/* OR in data */  
	ucStore |= ((value << DATA_PORT_SHIFT) & DATA_PORT_MASK );
	/* Write lower 4 bits of nibble */
	DATA_PORT = ucStore;

	/* write delay while En High */
	DisplayDelay(20);
	/* Latch data by dropping EN */		 
	EN_PIN = SET_BIT_LOW;
	/* Data hold delay */	   
	DisplayDelay(20);		 

	if(data_or_ctrl == CTRL_WR)
	{
		/* Extra delay needed for control writes */
		DisplayDelay(40);	   
	}	   
}
/**********************************************************************************
End of function LCD_nibble_write
***********************************************************************************/   

/*****************************************************************************
Name:		DisplayDelay 
Parameters:	units - Approximately in microseconds				   
Returns:	none 

Description:   Delay routine for LCD display.
*****************************************************************************/
void DisplayDelay(unsigned long int units)
{
	unsigned long counter = units * DELAY_TIMING;
	while(counter--)
	{
		nop();		// ~ 10ns
	}
}
/**********************************************************************************
End of function DisplayDelay
***********************************************************************************/   


void prvLCDTaskLine1( void *pvParameters )
{
	#define		RIGHT_TO_LEFT	0
	#define		LEFT_TO_RIGHT	1
	
	struct _LCD_Params *Local_Params = (struct _LCD_Params*)pvParameters;
	
	char str_lcd[9];
	unsigned short pos = 0;
	unsigned char Direction = RIGHT_TO_LEFT;
	
	for(;;)
	{
		vTaskDelay( Local_Params->Speed / portTICK_RATE_MS );		

		strncpy(str_lcd, &Local_Params->ptr_str[pos], 8);
	
		xSemaphoreTake( LCD_Mutex, portMAX_DELAY );
		DisplayString(Local_Params->Line, str_lcd);
		xSemaphoreGive( LCD_Mutex );
		
		if(Direction == RIGHT_TO_LEFT)
		{
			pos++;
			if( pos == strlen(datastring) - 7)
			{
				Direction = LEFT_TO_RIGHT;
				pos--;				
			}
		}
		else
		{
			pos--;
			if( pos == 0 )
			{
				Direction = RIGHT_TO_LEFT;				
			}
		}			
	}
}

void prvLCDTaskLine2( void *pvParameters )
{
	#define		RIGHT_TO_LEFT	0
	#define		LEFT_TO_RIGHT	1
	#define		RUNNING			0
	#define		STOPPED			1

	
	struct _LCD_Params *Local_Params = (struct _LCD_Params*)pvParameters;
	
	char str_lcd[9];
	unsigned short pos = 0;
	unsigned char Direction = RIGHT_TO_LEFT;
	unsigned char Status = RUNNING;
	
	unsigned char QueueData;
	portTickType Delay = ( Local_Params->Speed / portTICK_RATE_MS );
	
	for(;;)
	{
//		vTaskDelay( Local_Params->Speed / portTICK_RATE_MS );		

		if( xQueueReceive (SwitchQueue, &QueueData, Delay) != pdPASS )
		{
			strncpy(str_lcd, &Local_Params->ptr_str[pos], 8);
		
			xSemaphoreTake( LCD_Mutex, portMAX_DELAY );
			DisplayString(Local_Params->Line, str_lcd);
			xSemaphoreGive( LCD_Mutex );
			
			if(Direction == RIGHT_TO_LEFT)
			{
				pos++;
				if( pos == strlen(datastring) - 7)
				{
					Direction = LEFT_TO_RIGHT;
					pos--;				
				}
			}
			else
			{
				pos--;
				if( pos == 0 )
				{
					Direction = RIGHT_TO_LEFT;				
				}
			}			
		}
		else
		{
			if(QueueData == 0x02)	// stop/start
			{
				if(Delay != portMAX_DELAY)
				{
					Delay = portMAX_DELAY;
					Status = STOPPED;
				}
				else
				{
					Delay = ( Local_Params->Speed / portTICK_RATE_MS );
					Status = RUNNING;
				}				
			}
			
			if(QueueData == 0x01)	// RIGHT or shift back
			{
				if(Status == STOPPED)
				{
					if(pos != 0)
					{
						pos--;
											
						strncpy(str_lcd, &Local_Params->ptr_str[pos], 8);
		
						xSemaphoreTake( LCD_Mutex, portMAX_DELAY );
						DisplayString(Local_Params->Line, str_lcd);
						xSemaphoreGive( LCD_Mutex );
					}
				}
			}
			
			if(QueueData == 0x03)	// LEFT or shift forward
			{
				if(Status == STOPPED)
				{
					if(pos != strlen(datastring) - 7)
					{
						pos++;
						strncpy(str_lcd, &Local_Params->ptr_str[pos], 8);
		
						xSemaphoreTake( LCD_Mutex, portMAX_DELAY );
						DisplayString(Local_Params->Line, str_lcd);
						xSemaphoreGive( LCD_Mutex );
					}
				}
			}
		}
	}
}