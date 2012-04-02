/*------------------------------------------------------------------------/
/  EZ-LCD - Generic control module for HD44780 LCDC - R0.01c
/-------------------------------------------------------------------------/
/
/  Copyright (C) 2010, ChaN, all right reserved.
/
/ * This software is a free software and there is NO WARRANTY.
/ * No restriction on use. You can use, modify and redistribute it for
/   personal, non-profit or commercial products UNDER YOUR RESPONSIBILITY.
/ * Redistributions of source code must retain the above copyright notice.
/
/-------------------------------------------------------------------------/
/ Nov 12,'10 R0.01c  First release.
/------------------------------------------------------------------------*/
#include <machine.h>
#include "hd44780.h"

/*-------------------------------------------------------------------------*/
/* Platform dependent macros and functions needed to be modified           */
/*-------------------------------------------------------------------------*/

/* Bus controls */
#include "iodefine.h"			/* Device specific include file */
#include "rskrx210def.h"

#define	IF_BUS		4			/* Data bus width (4 or 8) */
#define	IF_INIT()	{}			/* Initialize control port */
#define E1_HIGH()	LCD_EN = 1	/* Set E(E1) high */
#define E1_LOW()	LCD_EN = 0  /* Set E(E1) low */
#define E2_HIGH()				/* Set E2 high (dual controller only) */
#define E2_LOW()				/* Set E2 low (dual controller only) */
#define	RS_HIGH()	LCD_RS = 1	/* Set RS high */
#define	RS_LOW()	LCD_RS = 0	/* Set RS low */
#define	OUT_DATA(d)	LCD_DATA = (d & 0x0F)//LCD_DATA = ((LCD_DATA & 0xF0) | (d & 0x0F))	/* Output a byte d on the data bus (higher 4 bits of d in 4-bit mode) */
#define	IF_DLY60()	{nop();nop();nop(); }			/* Delay >=60ns (can be blanked for most uC) */
#define	IF_DLY450()	{unsigned long x; for(x=0; x<22; x++){nop();}}			/* Delay >=450ns@3V, >=250ns@5V */
#define DELAY_US(n)	{unsigned long x; for(x=0; x<(n*50); x++){nop();}}			/* Delay n microseconds */

/* Characteristics of LCD module  */
#define	LCD_ETIME_1	1530		/* Execution time of Clear Display command [us] */
#define	LCD_ETIME_2	43			/* Execution time of other command and data write [us] */
#define	LCD_DLF		2.0			/* Delay factor (>=2.0) */



/*-------------------------------------------------------------------------*/


#if _LCD_ROWS >= 2 || _LCD_COLS > 8
 #define LCD_IF_2ROW 8		/* 2-row cfg. */
 #if _LCD_ROWS == 1
  #define LCD_IF_SPLIT 1	/* Half split row */
 #else
  #define LCD_IF_SPLIT 0	/* Direct row */
 #endif
#else
 #define LCD_IF_2ROW 0		/* 1-row cfg. */
#endif

#if _LCD_ROWS == 4 && _LCD_COLS <= 20
 #define LCD_IF_ALTROW	1	/* Alternate row layout */
#else
 #define LCD_IF_ALTROW	0	/* Incremental row layout */
#endif

#if _LCD_ROWS == 4 && _LCD_COLS > 20
 #define LCD_IF_DUAL 	1	/* Dual controller */
#else
 #define LCD_IF_DUAL 	0	/* Single controller */
#endif

#define	LCD_DT1		((uint16_t)(LCD_ETIME_1 * LCD_DLF))
#define	LCD_DT2		((uint16_t)(LCD_ETIME_2 * LCD_DLF))



static
uint8_t Row, Column;	/* Current cursor position */
#if _USE_CURSOR
static
uint8_t Csr;	/* Current cursor state */
#endif




/*----------------------------------------------*/
/* Write a byte to the LCD controller           */
/*----------------------------------------------*/

static
void lcd_write (
	uint8_t reg,	/* b0:command(0)/data(1), b2..1:E1(2)/E2(1)/both(0)(don't care on single controller), b3:write high nibble only(don't care on 8-bit bus) */
	uint8_t dat		/* Byte to be written */
)
{
	if (reg & 1)	/* Select register */
		RS_HIGH();
	else
		RS_LOW();
	IF_DLY60();

#if IF_BUS == 4
	if (!(reg & 8)) {
		OUT_DATA(dat);
#if LCD_IF_DUAL
		if (!(reg & 2)) E1_HIGH();
		if (!(reg & 4)) E2_HIGH();
		IF_DLY450();
		E1_LOW();
		E2_LOW();
#else
		E1_HIGH();
		IF_DLY450();
		E1_LOW();
#endif
		IF_DLY450();
		dat <<= 4;
	}
#endif

	OUT_DATA(dat);
#if LCD_IF_DUAL
	if (!(reg & 2)) E1_HIGH();
	if (!(reg & 4)) E2_HIGH();
	IF_DLY450();
	E1_LOW();
	E2_LOW();
#else
	E1_HIGH();
	IF_DLY450();
	E1_LOW();
#endif

	DELAY_US(LCD_DT2);	/* Always use timer */
}



/*-----------------------------------------------------------------------*/
/* Initialize LCD module                                                 */
/*-----------------------------------------------------------------------*/

void lcd_init (void)
{
	uint8_t d;
	
	E1_HIGH();
	DELAY_US(40000);
	E1_LOW();

//	IF_INIT();

//	DELAY_US(40000);
	lcd_write(8, 0x30);
	DELAY_US(4100);
	lcd_write(8, 0x30);
	DELAY_US(100);
	lcd_write(8, 0x30);

	d = (IF_BUS == 4 ? 0x20 : 0x30) | LCD_IF_2ROW;
	lcd_write(8, d);
#if IF_BUS == 4
	lcd_write(0, d);
#endif
	lcd_write(0, 0x08);
	lcd_write(0, 0x01);
	DELAY_US(LCD_DT1);
	lcd_write(0, 0x06);
	lcd_write(0, 0x0C);

	Row = Column = 0;
#if _USE_CURSOR
	Csr = 0;
#endif
}



/*-----------------------------------------------------------------------*/
/* Set cursor position                                                   */
/*-----------------------------------------------------------------------*/

void lcd_locate (
	uint8_t row,	/* Cursor row position (0.._LCD_ROWS-1) */
	uint8_t col		/* Cursor column position (0.._LCD_COLS-1) */
)
{
	Row = row; Column = col;

	if (row < _LCD_ROWS && col < _LCD_COLS) {
		if (_LCD_COLS >= 2 && (row & 1)) col += 0x40;
		if (LCD_IF_SPLIT && col >= _LCD_COLS / 2) col += 0x40 - _LCD_COLS / 2;
		if (LCD_IF_ALTROW && (row & 2)) col += _LCD_COLS;
		col |= 0x80;
	} else {
		col = 0x0C;
	}

#if LCD_IF_DUAL
	if (_USE_CURSOR && !(row &= 2)) row |= 4;
	lcd_write(row, col);
#if _USE_CURSOR
	if (col != 0x0C) lcd_write(row, Csr | 0x0C);
	row ^= 6;
	lcd_write(row, 0x0C);
#endif
#else
	lcd_write(0, col);
#if _USE_CURSOR
	if (col != 0x0C) lcd_write(0, Csr | 0x0C);
#endif
#endif
}



/*-----------------------------------------------------------------------*/
/* Put a character                                                       */
/*-----------------------------------------------------------------------*/

void lcd_putc (
	uint8_t chr
)
{
	if (chr == '\f') {		/* Clear Screen and Return Home */
		lcd_write(0, 0x01);
		DELAY_US(LCD_DT1);
		lcd_locate(0, 0);
		return;
	}

	if (Row >= _LCD_ROWS) return;

	if (chr == '\r') {	/* Cursor return */
		lcd_locate(Row, 0);
		return;
	}
	if (chr == '\n') {	/* Next row */
		lcd_locate(Row + 1, 0);
		return;
	}
	if (chr == '\b') {	/* Cursor back */
		if (Column)
			lcd_locate(Row, Column - 1);
		return;
	}

	if (Column >= _LCD_COLS) return;

	lcd_write((LCD_IF_DUAL && Row >= 2) ? 3 : 5, chr);
	Column++;

	if (LCD_IF_SPLIT && Column == _LCD_COLS / 2)
		lcd_write(0, 0x40);

	if (Column >= _LCD_COLS)
		lcd_locate(Row + 1, 0);
}



/*-----------------------------------------------------------------------*/
/* Set cursor form                                                       */
/*-----------------------------------------------------------------------*/

#if _USE_CURSOR
void lcd_cursor (
	uint8_t stat	/* 0:off, 1:blinking block, 2:under-line */
)
{
	Csr = stat & 3;
	lcd_locate(Row, Column);
}
#endif



/*-----------------------------------------------------------------------*/
/* Register user character pattern                                       */
/*-----------------------------------------------------------------------*/

#if _USE_CGRAM
void lcd_setcg (
	uint8_t chr,		/* Character code to be registered (0..7) */
	uint8_t n,			/* Number of characters to register */
	const uint8_t* p	/* Pointer to the character pattern (8 * n bytes) */
)
{
	lcd_write(0, 0x40 | chr * 8);
	n *= 8;
	do
		lcd_write(1, *p++);
	while (--n);

	lcd_locate(Row, Column);
}
#endif



/*-----------------------------------------------------------------------*/
/* Put a fuel indicator                                                  */
/*-----------------------------------------------------------------------*/

#if _USE_FUEL && _USE_CGRAM
void lcd_put_fuel (
	int8_t val,		/* Fuel level (-1:plugged, 0:empty cell, ..., 5:full cell) */
	uint8_t chr		/* User character to use */
)
{
	static const uint8_t plg[8] = {10,10,31,31,14,4,7,0};
	uint8_t gfx[8], d, *p;
	int8_t i;


	if (val >= 0) {		/* Cell (0..5) */
		p = &gfx[8];
		*(--p) = 0; *(--p) = 0x1F;
		for (i = 1; i <= 5; i++) {
			d = 0x1F;
			if (val < i) d = (i == 5) ? 0x1B : 0x11;
			*(--p) = d;
		}
		*(--p) = 0x0E;
	} else {			/* Plug (-1) */
		p = (uint8_t*)plg;
	}
	lcd_setcg(chr, 1, p);
	lcd_putc(chr);
}


#endif



/*-----------------------------------------------------------------------*/
/* Draw bargraph                                                         */
/*-----------------------------------------------------------------------*/

#if _USE_BAR && _USE_CGRAM
void lcd_put_bar (
	uint16_t val,	/* Bar length (0 to _MAX_BAR represents bar length from left end) */
	uint8_t width,	/* Display area (number of chars from cursor position) */
	uint8_t chr		/* User character code (2 chars used from this) */
)
{
	static const uint8_t ptn[] = {
		0xE0, 0xE0, 0xE0, 0xC0, 0xC0, 0xC0, 0x80, 0,
		0xF0, 0xE0, 0xE0, 0xE0, 0xC0, 0xC0, 0xC0, 0,
		0xF0, 0xF0, 0xE0, 0xE0, 0xE0, 0xC0, 0xC0, 0
	};
	const uint8_t *pp;
	uint16_t n, m, s, gi;
	uint8_t gfx[16];


	for (n = 0; n < 16; n++)		/* Register common pattern (space/fill) */
		gfx[n] = n < 7 ? 0 : 0xFF;
	lcd_setcg(_BASE_GRAPH, 2, gfx);

	/* Draw edge pattern into gfx[] */
	val = (unsigned long)val * (width * 18) / (_MAX_BAR + 1);
	pp = &ptn[(val % 3) * 8];		/* Get edge pattern */
	s = val / 3 % 6;				/* Bit shift */
	for (n = 0; n < 7; n++) {		/* Draw edge pattern into the pattern buffer */
		m = (*pp++ | 0xFF00) >> s;
		gfx[n] = m;
		gfx[n + 8] = m >> 6;
	}

	/* Put graphic pattern into the LCD module */
	gi = val / 18;						/* Indicator start position */
	for (n = 1; n <= width; n++) {		/* Draw each location in the bargraph */
		if (n == gi) {					/* When edge pattern is exist at the location */
			m = chr + 1;				/* A edge pattern */
		} else {
			if (n == gi + 1) {
				lcd_setcg(chr, 2, gfx);	/* Register edge pattern */
				m = chr;
			} else {
				m = (n >= gi) ? _BASE_GRAPH : _BASE_GRAPH + 1;	/* A space or fill */
			}
		}
		lcd_putc(m);					/* Put the character into the LCD */
	}
}
#endif



/*-----------------------------------------------------------------------*/
/* Draw point indicator                                                  */
/*-----------------------------------------------------------------------*/

#if _USE_POINT && _USE_CGRAM
void lcd_put_point (
	uint16_t val,	/* Dot position (0 to _MAX_POINT represents left end to write end) */
	uint8_t width,	/* Display area (number of chars from cursor position) */
	uint8_t chr		/* User character code (2 chars used from this) */
)
{
	static const uint8_t ptn[] = {
		0x06, 0x0C, 0x0C, 0x0C, 0x18, 0x18, 0x18, 0,
		0x06, 0x06, 0x0C, 0x0C, 0x0C, 0x18, 0x18, 0,
		0x06, 0x06, 0x06, 0x0C, 0x0C, 0x0C, 0x18, 0
	};
	const uint8_t *pp;
	uint16_t n, m, s, gi;
	uint8_t gfx[16];


	for (n = 0; n < 16; n++)		/* Register common pattern (space) */
		gfx[n] = n < 7 ? 0 : 0xFF;
	lcd_setcg(_BASE_GRAPH, 1, gfx);

	/* Draw edge pattern into gfx[] */
	val = (uint32_t)val * (width * 18 - 12) / (_MAX_BAR + 1);
	pp = &ptn[(val % 3) * 8];		/* Get edge pattern */
	s = val / 3 % 6;				/* Bit shift */
	for (n = 0; n < 7; n++) {		/* Draw edge pattern into the pattern buffer */
		m = *pp++; m <<= 6; m >>= s;
		gfx[n] = m;
		gfx[n + 8] = m >> 6;
	}
	lcd_setcg(chr, 2, gfx);				/* Register dot pattern */

	/* Put graphic pattern into the LCD module */
	gi = val / 18;						/* Indicator start position */
	for (n = 0; n < width; n++) {		/* Draw each location in the bargraph */
		if (n == gi) {					/* When edge pattern is exist at the location */
			m = chr + 1;				/* A edge pattern */
		} else {
			if (n == gi + 1)
				m = chr;
			else
				m = _BASE_GRAPH;		/* A space */
		}
		lcd_putc(m);					/* Put the character into the LCD */
	}
}
#endif


