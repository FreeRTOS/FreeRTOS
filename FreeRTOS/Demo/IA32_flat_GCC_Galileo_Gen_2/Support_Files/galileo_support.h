/*--------------------------------------------------------------------
 Copyright(c) 2015 Intel Corporation. All rights reserved.

 Redistribution and use in source and binary forms, with or without
 modification, are permitted provided that the following conditions
 are met:

 * Redistributions of source code must retain the above copyright
 notice, this list of conditions and the following disclaimer.
 * Redistributions in binary form must reproduce the above copyright
 notice, this list of conditions and the following disclaimer in
 the documentation and/or other materials provided with the
 distribution.
 * Neither the name of Intel Corporation nor the names of its
 contributors may be used to endorse or promote products derived
 from this software without specific prior written permission.

 THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 --------------------------------------------------------------------*/

#ifndef __GALILEO_SUPPORT_H__
#define __GALILEO_SUPPORT_H__

#ifdef __cplusplus
	extern "C" {
#endif

//---------------------------------------------------------------------
// Any required includes
//---------------------------------------------------------------------
#include "FreeRTOS.h"
#include "semphr.h"
#include "galileo_gen_defs.h"
#include "GPIO_I2C.h"
#include "HPET.h"

//---------------------------------------------------------------------
// Application main entry point
//---------------------------------------------------------------------
extern int main( void );

//---------------------------------------------------------------------
// Defines for GDT
//---------------------------------------------------------------------
#define	NGDE				8		/* Number of global descriptor entries	*/
#define FLAGS_GRANULARITY	0x80
#define FLAGS_SIZE			0x40
#define	FLAGS_SETTINGS		( FLAGS_GRANULARITY | FLAGS_SIZE )
#define	PAGE_SIZE			4096

struct __attribute__ ((__packed__)) sd
{
	unsigned short	sd_lolimit;
	unsigned short	sd_lobase;
	unsigned char	sd_midbase;
	unsigned char   sd_access;
	unsigned char	sd_hilim_fl;
	unsigned char	sd_hibase;
};

void setsegs();

//---------------------------------------------------------------------
// Debug serial port display update definitions
//---------------------------------------------------------------------
#define ANSI_CLEAR_SB			"\e[3J"
#define ANSI_CLEAR_LINE			"\x1b[2K"
#define ANSI_CLEAR_SCREEN		"\x1b[2J"
#define ANSI_COLOR_RED     		"\x1b[31m"
#define ANSI_COLOR_GREEN   		"\x1b[32m"
#define ANSI_COLOR_YELLOW  		"\x1b[33m"
#define ANSI_COLOR_BLUE    		"\x1b[34m"
#define ANSI_COLOR_MAGENTA 		"\x1b[35m"
#define ANSI_COLOR_CYAN    		"\x1b[36m"
#define ANSI_COLOR_RESET   		"\x1b[0m"
#define ANSI_COLOR_WHITE   		ANSI_COLOR_RESET

#define DEFAULT_SCREEN_COLOR	ANSI_COLOR_YELLOW
#define DEFAULT_BANNER_COLOR	ANSI_COLOR_CYAN

#define ANSI_HIDE_CURSOR		"\x1b[?25l"
#define ANSI_SHOW_CURSOR		"\x1b[?25h"

void ClearScreen(void);
void MoveToScreenPosition(uint8_t row, uint8_t col);
void UngatedMoveToScreenPosition(uint8_t row, uint8_t col);
void SetScreenColor(const char *);
void g_printf(const char *format, ...);
void g_printf_rcc(uint8_t row, uint8_t col, const char *color, const char *format, ...);
void vPrintBanner( void );

//---------------------------------------------------------------------
// 8259 PIC (programmable interrupt controller) definitions
//---------------------------------------------------------------------
#define IMR1 (0x21)       /* Interrupt Mask Register #1           */
#define IMR2 (0xA1)       /* Interrupt Mask Register #2           */
#define ICU1 (0x20)
#define ICU2 (0xA0)
#define EOI  (0x20)

void vInitialize8259Chips(void);
void vClearIRQMask(uint8_t IRQNumber);
void vSetIRQMask(uint8_t IRQNumber);

//---------------------------------------------------------------------
// 82C54 PIT (programmable interval timer) definitions
//---------------------------------------------------------------------
#define GATE_CONTROL	0x61
#define CHANNEL2_DATA	0x42
#define	MODE_REGISTER	0x43
#define ONESHOT_MODE	0xB2
#define	CLKBASE			0x40
#define	CLKCNTL			MODE_REGISTER

void vInitializePIT(void);

//---------------------------------------------------------------------
// LED support for main_blinky()
//---------------------------------------------------------------------
#define LED_ON			( 1 )
#define LED_OFF	  		( 0 )

uint32_t ulBlinkLED(void); /* Blink the LED and return the LED status. */

//---------------------------------------------------------------------
// Serial port support definitions
//---------------------------------------------------------------------
#define CLIENT_SERIAL_PORT 				0
#define DEBUG_SERIAL_PORT 				1

#define R_UART_THR                      0
#define R_UART_IER                      0x04
#define R_UART_BAUD_THR                 R_UART_THR
#define R_UART_BAUD_LOW                 R_UART_BAUD_THR
#define R_UART_BAUD_HIGH                R_UART_IER
#define R_UART_FCR                      0x08
#define B_UARY_FCR_TRFIFIE              BIT0
#define B_UARY_FCR_RESETRF              BIT1
#define B_UARY_FCR_RESETTF              BIT2
#define R_UART_LCR                      0x0C
#define B_UARY_LCR_DLAB                 BIT7
#define R_UART_MCR                      0x10
#define R_UART_LSR                      0x14
#define B_UART_LSR_RXRDY                BIT0
#define B_UART_LSR_OE                   BIT1
#define B_UART_LSR_PE                   BIT2
#define B_UART_LSR_FE                   BIT3
#define B_UART_LSR_BI                   BIT4
#define B_UART_LSR_TXRDY                BIT5
#define B_UART_LSR_TEMT                 BIT6
#define R_UART_MSR                      0x18
#define R_UART_SCR                      0x1C

void vInitializeGalileoSerialPort(uint32_t portnumber);
void vGalileoPrintc(char c);
uint8_t ucGalileoGetchar();
void vGalileoPuts(const char *string);

#ifdef __cplusplus
	} /* extern C */
#endif

#endif /* __GALILEO_SUPPORT_H__ */

