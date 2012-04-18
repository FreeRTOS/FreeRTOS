/***********************************************************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only intended for use with Renesas products. No 
* other uses are authorized. This software is owned by Renesas Electronics Corporation and is protected under all 
* applicable laws, including copyright laws. 
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING
* THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, 
* FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED. TO THE MAXIMUM 
* EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES 
* SHALL BE LIABLE FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR ANY REASON RELATED TO THIS 
* SOFTWARE, EVEN IF RENESAS OR ITS AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software and to discontinue the availability of 
* this software. By using this software, you agree to the additional terms and conditions found by accessing the 
* following link:
* http://www.renesas.com/disclaimer 
*
* Copyright (C) 2012 Renesas Electronics Corporation. All rights reserved.    
***********************************************************************************************************************/
/***********************************************************************************************************************
* File Name	   : lcd.c
* Device(s)    : RX
* H/W Platform : RSK+RX63N
* Description  : Provides variable and function declarations for lcd.c file
***********************************************************************************************************************/
/***********************************************************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 22.11.2011 1.00     First Release
***********************************************************************************************************************/

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
/* Processor-specific details */
#include <machine.h>
/* Standard string manipulation & formatting functions */
#include <stdio.h>
#include <string.h>
/* Defines standard variable types used in this function */
#include <stdint.h>
/* Bring in board includes. */
#include "platform.h"
/* Following header file provides function prototypes for LCD controlling functions & macro defines */
#include "lcd.h"

/***********************************************************************************************************************
Private global variables and functions
***********************************************************************************************************************/
static void lcd_delay(volatile int32_t nsecs);
static void lcd_nibble_write(uint8_t data_or_ctrl, uint8_t value);
static void lcd_write(uint8_t data_or_ctrl, uint8_t value);

/***********************************************************************************************************************
* Function name : lcd_initialize
* Description   : Initializes the LCD display. 
* Arguments     : none
* Return Value  : none
***********************************************************************************************************************/
void lcd_initialize(void)
{
    /* Set LCD data pins as outputs. */
    PORT8.PDR.BYTE |= 0xF0;
    
    /* Set LCD control pins as outputs. */
    RS_PIN_DDR = 1;
    E_PIN_DDR = 1;
	
	/* Power Up Delay for the LCD Module */   	
    lcd_delay(50000000);

	/* Display initialises in 8 bit mode - so send one write (seen as 8 bit) to set to 4 bit mode. */
	lcd_nibble_write(CTRL_WR, 0x03);
    lcd_delay(5000000);
	lcd_nibble_write(CTRL_WR, 0x03);
    lcd_delay(5000000);
	lcd_nibble_write(CTRL_WR, 0x03);
	lcd_delay(5000000);
    
	/* Function Set */
	lcd_nibble_write(CTRL_WR, 0x02);
    lcd_delay(39000);    
	lcd_nibble_write(CTRL_WR, 0x02);
	lcd_nibble_write(CTRL_WR, (LCD_DISPLAY_ON | LCD_TWO_LINE ));
    lcd_delay(39000);    
 
	/* Display ON/OFF control */
	lcd_write(CTRL_WR, LCD_CURSOR_OFF);
    lcd_delay(39000);

	/* Display Clear */
	lcd_write(CTRL_WR, LCD_CLEAR);
    lcd_delay(2000000);

	/* Entry Mode Set */
	lcd_write(CTRL_WR, 0x06);
    lcd_delay(39000);

    /* Home the cursor */
	lcd_write(CTRL_WR, LCD_HOME_L1);
    lcd_delay(5000000);    
}

/***********************************************************************************************************************
* Function name : lcd_clear
* Description   : Clears the LCD
* Arguments     : none
* Return Value  : none
***********************************************************************************************************************/
void lcd_clear(void)
{
	/* Display Clear */
	lcd_write(CTRL_WR, LCD_CLEAR);
    lcd_delay(2000000);    
}

/***********************************************************************************************************************
* Function name : lcd_display
* Description   : This function controls LCD writes to line 1 or 2 of the LCD.
*                 You need to use the defines LCD_LINE1 and LCD_LINE2 in order to specify the starting position.
*				  For example, to start at the 2nd position on line 1...
*				   		lcd_display(LCD_LINE1 + 1, "Hello")
* Arguments     : position - 
*                     Line number of display
*                 string - 
*                     Pointer to null terminated string
* Return Value  : none
***********************************************************************************************************************/
void lcd_display(uint8_t position, uint8_t const * string)
{
	/* Declare next position variable */
	static uint8_t next_pos = 0xFF;
	
	/* Set line position if needed. We don't want to if we don't need to because LCD control operations take longer 
       than LCD data operations. */
	if (next_pos != position)
	{
		if(position < LCD_LINE2)
		{
			/* Display on Line 1 */
		  	lcd_write(CTRL_WR, ((uint8_t)(LCD_HOME_L1 + position)));
		}
		else
		{
			/* Display on Line 2 */
		  	lcd_write(CTRL_WR, ((uint8_t)((LCD_HOME_L2 + position) - LCD_LINE2)));
		}

        lcd_delay(39000);

		/* set position index to known value */
		next_pos = position;		
	}

	do
	{
        /* Write character to LCD. */
		lcd_write(DATA_WR,*string++);

        lcd_delay(43000);
		
		/* Increment position index */
		next_pos++;				
	} 
	while(*string);	
}

/***********************************************************************************************************************
* Function name : lcd_delay
* Description   : Implements LCD required delays.
* Arguments     : nsecs - 
*                     Number of nanoseconds to delay. RX600 has max clock of 100MHz which gives a cycle time of 10ns.
*                     This means that nothing under 100ns should be input. 100ns would be 10 cycles which is still 
*                     being optimistic for getting in and out of this function.
* Return Value  : none
***********************************************************************************************************************/
static void lcd_delay(volatile int32_t nsecs)
{
    while (0 < nsecs)
    {
        /* Subtract off 10 cycles per iteration. This number was obtained when using the Renesas toolchain at 
           optimization level 2. The number to nanoseconds to subtract off below is calculated off of the ICLK speed. */
        nsecs -= (int32_t)((100.0)*(100000000.0/(float)ICLK_HZ));
    }
}

/***********************************************************************************************************************
* Function name : lcd_nibble_write
* Description   : Writes data to display. Sends command to display. 
* Arguments     : value - 
*                     The value to write
*                 data_or_ctrl -
*                     Whether to write data or control.
*                     1 = DATA
*                     0 = CONTROL
* Return Value  : none
***********************************************************************************************************************/
static void lcd_nibble_write(uint8_t data_or_ctrl, uint8_t value)
{
	/* Set Register Select pin high for Data */
	if (data_or_ctrl == DATA_WR)
	{
        /* Data write. */
        RS_PIN = 1;
	}
	else
	{
        /* Control write. */
        RS_PIN = 0;
	}
	
	/* tsu1 delay */
    lcd_delay(60);    
	
  	/* EN enable chip (HIGH) */
    E_PIN = 1;    
	
	/* Output the data */
    PORT8.PODR.BYTE = (value << 4u);
	
	/* tw delay */	            
    lcd_delay(450);    
	
	/* Latch data by dropping E */		
    E_PIN = 0;
	
	/* th2 delay */				
    lcd_delay(10);
	
	/* tc delay */
    lcd_delay(480);
}

/***********************************************************************************************************************
* Function name : lcd_write
* Description   : This function controls LCD writes to line 1 or 2 of the LCD. You need to use the defines LCD_LINE1 and 
*                 LCD_LINE2 in order to specify the starting position.
*				  For example, to start at the 2nd position on line 1...
*				   		lcd_display(LCD_LINE1 + 1, "Hello") 
* Arguments     : value - 
*                     The value to write
*                 data_or_ctrl -
*                     Whether to write data or control.
*                     1 = DATA
*                     0 = CONTROL
* Return Value  : none
***********************************************************************************************************************/
static void lcd_write(uint8_t data_or_ctrl, uint8_t value)
{
	/* Write upper nibble first */
	lcd_nibble_write(data_or_ctrl, (uint8_t)((value & 0xF0) >> 4));
	
	/* Write lower nibble second */
	lcd_nibble_write(data_or_ctrl, (uint8_t)(value & 0x0F));
}

