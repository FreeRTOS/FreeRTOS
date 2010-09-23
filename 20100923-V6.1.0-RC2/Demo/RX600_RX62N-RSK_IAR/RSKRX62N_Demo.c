/*
 * Copyright (c) 20010 IAR Systems AB.
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */

/*
 * IAR Embedded Workbench tutorial
 *
 * Test Program for the RSKRX62N Board.
 * LED's perform different display according to
 * which switch is pressed.
 * Used to check that all the LED's, switches,
 * clock function and AD trigger are working fine.
 *
 * $Revision: 1556 $
 */

#include "iorx62n.h"
#include "intrinsics.h"

void ScrollLedsLowHigh(void);
void ScrollLedsHighLow(void);

unsigned long pause;
unsigned long off_set;

#define ON  0
#define OFF 1
#define LED0 PORT0.DR.BIT.B2  // P02 LED0
#define LED1 PORT0.DR.BIT.B3  // P03 LED1
#define LED2 PORT0.DR.BIT.B5  // P05 LED2
#define LED3 PORT3.DR.BIT.B4  // P34 LED3
#define LED4 PORT6.DR.BIT.B0  // P50 LED4
#define LED5 PORT7.DR.BIT.B3  // P73 LED5

/* defined words used in this program */
enum {
  SW1,
  SW2,
  SW3,
  NONE
}GetKey;

/* SW1 ISR */
#pragma vector = 72
__interrupt void isr_sw1(void)
{
  GetKey=SW1;   
   
  CMT.CMSTR0.BIT.STR0 = 0; // stop timer
  ICU.IR[72].BIT.IR = 0;   // clear interrupt request flag 
}

/* SW2 ISR */
#pragma vector = 73
__interrupt void isr_sw2(void)
{
  GetKey=SW2;   
    
  CMT.CMSTR0.BIT.STR0 = 0; // stop timer
  ICU.IR[73].BIT.IR = 0;   // clear interrupt request flag  
}

/* SW3 ISR */
#pragma vector = 79
__interrupt void isr_sw3(void)
{
  GetKey=SW3;   
  
  CMT.CMSTR0.BIT.STR0 = 1; // start timer
  ICU.IR[79].BIT.IR = 0;   // clear interrupt request flag    
}

/* Timer ISR */
#pragma vector = 0x1c
__interrupt void isr_cmt0(void)
{
  // Toggle LED's
  LED0 = ~LED0;
  LED1 = ~LED1;
  LED2 = ~LED2;
  LED3 = ~LED3;
  LED4 = ~LED4;
  LED5 = ~LED5;  
  ICU.IR[70].BIT.IR = 0;         // clear interrupt request flag
}

/* Main program. */
void main (void)
{
  // enable modules
  SYSTEM.MSTPCRA.BIT.MSTPA23 = 0; // A/D Converter (Unit 0) Module
  
  // Set up RV1 (potentiometer)
  AD0.ADCR.BIT.MODE = 2;  // Continuous scan mode
  AD0.ADCSR.BIT.CH = 0;   // only AD0
  AD0.ADCSR.BIT.ADST = 1; // Start A/D
  
  // Set up SW1, SW2, SW3
  PORT0.DDR.BIT.B0 = 0; // SW1 input on P00
  PORT0.DDR.BIT.B1 = 0; // SW2 input on P01
  PORT0.DDR.BIT.B7 = 0; // SW3 input on P07  

  PORT0.ICR.BIT.B0 = 1; // Enable input buffer
  PORT0.ICR.BIT.B1 = 1; // Enable input buffer
  PORT0.ICR.BIT.B7 = 1; // Enable input buffer
  
  // IRQ8-A used for SW1
  IOPORT.PF8IRQ.BIT.ITS8 = 0; // P00 is designated as the IRQ8-A input pin.
  IEN(ICU,IRQ8) = 1;
  IPR(ICU,IRQ8) = 3;         
  
  // IRQ9-A used for SW2
  IOPORT.PF8IRQ.BIT.ITS9 = 0; // P01 is designated as IRQ9-A input pin.
  IEN(ICU,IRQ9) = 1;
  IPR(ICU,IRQ9) = 3;    

  // IRQ15-A used for SW3
  IOPORT.PF8IRQ.BIT.ITS15 = 0; // P07 is designated as the IRQ15-A input pin.
  IEN(ICU,IRQ15) = 1;
  IPR(ICU,IRQ15) = 3; 
  
  // Set up LED's
  PORT0.DDR.BIT.B2 = 1;   // P02 LED0 
  PORT0.DDR.BIT.B3 = 1;   // P03 LED1
  PORT0.DDR.BIT.B5 = 1;   // P05 LED2
  PORT3.DDR.BIT.B4 = 1;   // P34 LED3
  PORT6.DDR.BIT.B0 = 1;   // P50 LED4
  PORT7.DDR.BIT.B3 = 1;   // P73 LED5

  // Turn al LED's off
  LED0 = LED1 = LED2 = LED3 = LED4 = LED5 = OFF;
  
  // Set up Timer
  SYSTEM.MSTPCRA.BIT.MSTPA15 = 0; // CMT timers 0, 
  CMT0.CMCR.BIT.CKS = 3;          // 25MHz/512 = 48.8kHz
  CMT0.CMCR.BIT.CMIE = 1;         // enable peripheral interrupt source
  CMT0.CMCOR = 12212;             // 4 Hz operation
  ICU.IER[3].BIT.IEN4 = 1;        // enable timer 0 interrupt  
  IPR(CMT0,CMI0) = 1;             // LED level 1
  
  __enable_interrupt();  
  
  GetKey=SW1;
  
  for (;;)
  {
    switch (GetKey) 
    {
      case SW1:
        ScrollLedsLowHigh();
        break;
      case SW2:
        ScrollLedsHighLow();
        break;
      case SW3:
        GetKey=NONE;
        break;
    }
  }
}

/* scrolls the LED's from low to high */
void ScrollLedsLowHigh()
{
  char led_number = 0;
  
  while (GetKey == SW1)
  {
    if (led_number > 5)
      led_number = 0;
    
    switch(led_number)
    {
    case 0:
      LED0=ON;
      LED1=LED2=LED3=LED4=LED5=OFF;
      break;      
    case 1:
      LED1=ON;
      LED0=LED2=LED3=LED4=LED5=OFF;
      break;      
    case 2:
      LED2=ON;
      LED0=LED1=LED3=LED4=LED5=OFF;
      break;      
    case 3:
      LED3=ON;
      LED0=LED1=LED2=LED4=LED5=OFF;
      break;      
    case 4:
      LED4=ON;
      LED0=LED1=LED2=LED3=LED5=OFF;
      break;      
    case 5:
      LED5=ON;
      LED0=LED1=LED2=LED3=LED4=OFF;
      break;      
    }
    led_number++;

    off_set = AD0.ADDRA*1000;
    for (pause = off_set; pause != 0; pause --);
  }
}

/* scrolls the LED's from high to low */
void ScrollLedsHighLow()
{
  signed char led_number = 3;

  while (GetKey == SW2)
  {
    if (led_number < 0)
      led_number = 5;
    
    switch(led_number)
    {
    case 0:
      LED0=ON;
      LED1=LED2=LED3=LED4=LED5=OFF;
      break;      
    case 1:
      LED1=ON;
      LED0=LED2=LED3=LED4=LED5=OFF;
      break;      
    case 2:
      LED2=ON;
      LED0=LED1=LED3=LED4=LED5=OFF;
      break;      
    case 3:
      LED3=ON;
      LED0=LED1=LED2=LED4=LED5=OFF;
      break;      
    case 4:
      LED4=ON;
      LED0=LED1=LED2=LED3=LED5=OFF;
      break;      
    case 5:
      LED5=ON;
      LED0=LED1=LED2=LED3=LED4=OFF;
      break;      
    }
    led_number--;

    off_set = AD0.ADDRA*1000;
    for (pause = off_set; pause != 0; pause --);
  }
}
