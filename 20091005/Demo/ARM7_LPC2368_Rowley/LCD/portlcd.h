/*****************************************************************************
 *   rtc.h:  Header file for NXP LPC23xx/24xx Family Microprocessors
 *
 *   Copyright(C) 2006, NXP Semiconductor
 *   All rights reserved.
 *
 *   History
 *   2006.07.13  ver 1.00    Prelimnary version, first Release
 *
******************************************************************************/
#ifndef __PORTLCD_H 
#define __PORTLCD_H

extern void LCD_init(void);
extern void LCD_load(unsigned char *fp, unsigned int cnt);
extern void LCD_gotoxy(unsigned int x, unsigned int y);
extern void LCD_cls(void);
extern void LCD_cur_off(void);
extern void LCD_on(void);
extern void LCD_putc(unsigned char c);
extern void LCD_puts(unsigned char *sp);
extern void LCD_bargraph(unsigned int val, unsigned int size);

extern void LCD_putnibble(unsigned char nibble);
extern void LCD_puthexbyte(unsigned char abyte);


#endif /* end __PORTLCD_H */
/*****************************************************************************
**                            End Of File
******************************************************************************/
