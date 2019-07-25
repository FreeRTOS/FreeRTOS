/*****************************************************************************
 *
 * Project          : lwIP Web
 * Subproject       : 
 * Name             : portlcd.c
 * Function         : Routines for LCD
 * Designer         : K. Sterckx
 * Creation date    : 22/01/2007
 * Compiler         : GNU ARM
 * Processor        : LPC2368
 * Last update      :
 * Last updated by  :
 * History          : 
 *  based on example code from NXP
 *
 ************************************************************************
 *
 *  This code is used to place text on the LCD.
 *
 ************************************************************************/

#include "portlcd.h"
#include "FreeRTOS.h"
#include "task.h"

/* Please note, on old MCB2300 board, the LCD_E bit is p1.30, on the new board
it's p1.31, please check the schematic carefully, and change LCD_CTRL and LCD_E 
accordingly if you have a different board. */

/* LCD IO definitions */
#define LCD_E     0x80000000            /* Enable control pin                */
#define LCD_RW    0x20000000            /* Read/Write control pin            */
#define LCD_RS    0x10000000            /* Data/Instruction control          */
#define LCD_CTRL  0xB0000000            /* Control lines mask                */
#define LCD_DATA  0x0F000000            /* Data lines mask                   */

/* Local variables */
static unsigned int lcd_ptr;

/* 8 user defined characters to be loaded into CGRAM (used for bargraph) */
static const unsigned char UserFont[8][8] = {
	{ 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00 },
	{ 0x10,0x10,0x10,0x10,0x10,0x10,0x10,0x10 },
	{ 0x18,0x18,0x18,0x18,0x18,0x18,0x18,0x18 },
	{ 0x1C,0x1C,0x1C,0x1C,0x1C,0x1C,0x1C,0x1C },
	{ 0x1E,0x1E,0x1E,0x1E,0x1E,0x1E,0x1E,0x1E },
	{ 0x1F,0x1F,0x1F,0x1F,0x1F,0x1F,0x1F,0x1F },
	{ 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00 },
	{ 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00 }
};

/* Local Function Prototypes */
static void     lcd_write( unsigned int c );
static void     lcd_write_4bit( unsigned int c );
static unsigned int lcd_read_stat( void );
static void     lcd_write_cmd( unsigned int c );
static void     lcd_write_data( unsigned int d );
static void     lcd_wait_busy( void );


/******************************************************************************
** Function name:  lcd_write_4bit
**
** Descriptions:
**
** parameters:     four bits to write
** Returned value: None
** 
******************************************************************************/
static void lcd_write_4bit(unsigned int c)
{
	/* Write a 4-bit command to LCD controller. */
	FIO1DIR |= LCD_DATA | LCD_CTRL;
	FIO1CLR  = LCD_RW   | LCD_DATA;
	FIO1SET  = (c & 0xF) << 24;
	FIO1SET  = LCD_E;
	vTaskDelay(0);
	FIO1CLR  = LCD_E;
	vTaskDelay(0);
	return;
}

/******************************************************************************
** Function name: lcd_write
**
** Descriptions:
**
** parameters:     word to write
** Returned value: None
** 
******************************************************************************/
static void lcd_write(unsigned int c)
{
	/* Write data/command to LCD controller. */
	lcd_write_4bit (c >> 4);
	lcd_write_4bit (c);
	return;
}

/******************************************************************************
** Function name: lcd_read_stat
**
** Descriptions:
**
** parameters:     None
** Returned value: status
** 
******************************************************************************/
static unsigned int lcd_read_stat(void)
{
	/* Read status of LCD controller (ST7066) */
	unsigned int stat;

	FIO1DIR &= ~LCD_DATA;
	FIO1CLR  = LCD_RS;
	FIO1SET  = LCD_RW;
	vTaskDelay( 0 );
	FIO1SET  = LCD_E;
	vTaskDelay( 0 );
	stat    = (FIO1PIN >> 20) & 0xF0;
	FIO1CLR  = LCD_E;
	vTaskDelay( 0 );
	FIO1SET  = LCD_E;
	vTaskDelay( 0 );
	stat   |= (FIO1PIN >> 24) & 0xF;
	FIO1CLR  = LCD_E;
	return (stat);
}

/******************************************************************************
** Function name: lcd_wait_busy
**
** Descriptions:
**
** parameters:     None
** Returned value: None
** 
******************************************************************************/
static void lcd_wait_busy(void)
{
	/* Wait until LCD controller (ST7066) is busy. */
	unsigned int stat;

	do
	{
		stat = lcd_read_stat();
	}
	while (stat & 0x80); /* Wait for busy flag */

	return;
}

/******************************************************************************
** Function name: lcd_write_cmd
**
** Descriptions:
**
** parameters:     command word
** Returned value: None
** 
******************************************************************************/
static void lcd_write_cmd(unsigned int c)
{
	/* Write command to LCD controller. */
	lcd_wait_busy();
	FIO1CLR = LCD_RS;
	lcd_write(c);
	return;
}

/******************************************************************************
** Function name: lcd_write_data
**
** Descriptions:
**
** parameters:     data word
** Returned value: None
** 
******************************************************************************/
static void lcd_write_data(unsigned int d)
{
	/* Write data to LCD controller. */
	lcd_wait_busy();
	FIO1SET = LCD_RS;
	lcd_write(d);
	return;
}

/******************************************************************************
** Function name: LCD_init
**
** Descriptions:
**
** parameters:     None
** Returned value: None
** 
******************************************************************************/
void LCD_init(void)
{
	/* Initialize the ST7066 LCD controller to 4-bit mode. */
	PINSEL3 = 0x00000000;
#if USE_FIO
	SCS |= 0x00000001;/* set GPIOx to use Fast I/O */
#endif
	FIO1DIR |= LCD_CTRL | LCD_DATA;
	FIO1CLR  = LCD_RW   | LCD_RS   | LCD_DATA;

	lcd_write_4bit(0x3);                /* Select 4-bit interface            */
	vTaskDelay(100);
	lcd_write_4bit(0x3);
	vTaskDelay(100);
	lcd_write_4bit(0x3);
	lcd_write_4bit(0x2);

	lcd_write_cmd(0x28);                /* 2 lines, 5x8 character matrix     */
	lcd_write_cmd(0x0e);                /* Display ctrl:Disp/Curs/Blnk=ON    */
	lcd_write_cmd(0x06);                /* Entry mode: Move right, no shift  */

	LCD_load( (unsigned char *)&UserFont, sizeof (UserFont) );
	LCD_cls();
	return;
}

/******************************************************************************
** Function name: LCD_load
**
** Descriptions:
**
** parameters:     pointer to the buffer and counter
** Returned value: None
** 
******************************************************************************/
void LCD_load(unsigned char *fp, unsigned int cnt)
{
	/* Load user-specific characters into CGRAM */
	unsigned int i;

	lcd_write_cmd( 0x40 );                /* Set CGRAM address counter to 0    */
	for (i = 0; i < cnt; i++, fp++)  
	{
		lcd_write_data( *fp );
	}
	return;
}

/******************************************************************************
** Function name: LCD_gotoxy
**
** Descriptions:
**
** parameters:     pixel X and Y
** Returned value: None
** 
******************************************************************************/
void LCD_gotoxy(unsigned int x, unsigned int y)
{
	/* Set cursor position on LCD display. Left corner: 1,1, right: 16,2 */
	unsigned int c;

	c = --x;
	if (--y) 
	{
		c |= 0x40;
	}
	lcd_write_cmd (c | 0x80);
	lcd_ptr = y*16 + x;
	return;
}

/******************************************************************************
** Function name: LCD_cls
**
** Descriptions:
**
** parameters:     None
** Returned value: None
** 
******************************************************************************/
void LCD_cls(void)
{
	/* Clear LCD display, move cursor to home position. */
	lcd_write_cmd (0x01);
	LCD_gotoxy (1,1);
	return;
}

/******************************************************************************
** Function name: LCD_cur_off
**
** Descriptions:
**
** parameters:     None
** Returned value: None
** 
******************************************************************************/
void LCD_cur_off(void)
{
	/* Switch off LCD cursor. */
	lcd_write_cmd(0x0c);
	return;
}


/******************************************************************************
** Function name: LCD_on
**
** Descriptions:
**
** parameters:     None
** Returned value: None
** 
******************************************************************************/
void LCD_on(void)
{
	/* Switch on LCD and enable cursor. */
	lcd_write_cmd (0x0e);
	return;
}

/******************************************************************************
** Function name: LCD_putc
**
** Descriptions:
**
** parameters:     unsigned char character
** Returned value: None
** 
******************************************************************************/
void LCD_putc(unsigned char c)
{ 
	/* Print a character to LCD at current cursor position. */
	if (lcd_ptr == 16) 
	{
		lcd_write_cmd (0xc0);
	}
	lcd_write_data(c);
	lcd_ptr++;
	return;
}

/******************************************************************************
** Function name: LCD_puts
**
** Descriptions:
**
** parameters:     pointer to the buffer
** Returned value: None
** 
******************************************************************************/
void LCD_puts(char *sp)
{
	/* Print a string to LCD display. */
	while (*sp) 
	{
		LCD_putc (*sp++);
	}
	return;
}

/******************************************************************************
** Function name: LCD_bargraph
**
** Descriptions:
**
** parameters:     value and size
** Returned value: None
** 
******************************************************************************/
void LCD_bargraph(unsigned int val, unsigned int size)
{
	/* Print a bargraph to LCD display.  */
	/* - val:  value 0..100 %            */
	/* - size: size of bargraph 1..16    */
	unsigned int i;

	val = val * size / 20;               /* Display matrix 5 x 8 pixels       */
	for (i = 0; i < size; i++) 
	{
		if (val > 5) 
		{
			LCD_putc(5);
			val -= 5;
		}
		else
		{
			LCD_putc(val);
			break;
		}
	}
	return;
}
