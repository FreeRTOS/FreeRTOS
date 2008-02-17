/*-------------------------------------------------------------------------
   Register Declarations for the Cygnal C8051F12x Processor Range

   Copyright (C) 2003 - Maarten Brock, sourceforge.brock@dse.nl

   This library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   This library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with this library; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA
-------------------------------------------------------------------------*/

#ifndef C8051F120_H
#define C8051F120_H


/*  BYTE Registers  */

/*  All Pages */
sfr at 0x80 P0       ;  /* PORT 0                                        */
sfr at 0x81 SP       ;  /* STACK POINTER                                 */
sfr at 0x82 DPL      ;  /* DATA POINTER - LOW BYTE                       */
sfr at 0x83 DPH      ;  /* DATA POINTER - HIGH BYTE                      */
sfr at 0x84 SFRPAGE  ;  /* SFR PAGE SELECT                               */
sfr at 0x85 SFRNEXT  ;  /* SFR STACK NEXT PAGE                           */
sfr at 0x86 SFRLAST  ;  /* SFR STACK LAST PAGE                           */
sfr at 0x87 PCON     ;  /* POWER CONTROL                                 */
sfr at 0x90 P1       ;  /* PORT 1                                        */
sfr at 0xA0 P2       ;  /* PORT 2                                        */
sfr at 0xA8 IE       ;  /* INTERRUPT ENABLE                              */
sfr at 0xB0 P3       ;  /* PORT 3                                        */
sfr at 0xB1 PSBANK   ;  /* FLASH BANK SELECT                             */
sfr at 0xB8 IP       ;  /* INTERRUPT PRIORITY                            */
sfr at 0xD0 PSW      ;  /* PROGRAM STATUS WORD                           */
sfr at 0xE0 ACC      ;  /* ACCUMULATOR                                   */
sfr at 0xE6 EIE1     ;  /* EXTERNAL INTERRUPT ENABLE 1                   */
sfr at 0xE7 EIE2     ;  /* EXTERNAL INTERRUPT ENABLE 2                   */
sfr at 0xF0 B        ;  /* B REGISTER                                    */
sfr at 0xF6 EIP1     ;  /* EXTERNAL INTERRUPT PRIORITY REGISTER 1        */
sfr at 0xF7 EIP2     ;  /* EXTERNAL INTERRUPT PRIORITY REGISTER 2        */
sfr at 0xFF WDTCN    ;  /* WATCHDOG TIMER CONTROL                        */

/*  Page 0x00 */
sfr at 0x88 TCON     ;  /* TIMER CONTROL                                 */
sfr at 0x89 TMOD     ;  /* TIMER MODE                                    */
sfr at 0x8A TL0      ;  /* TIMER 0 - LOW BYTE                            */
sfr at 0x8B TL1      ;  /* TIMER 1 - LOW BYTE                            */
sfr at 0x8C TH0      ;  /* TIMER 0 - HIGH BYTE                           */
sfr at 0x8D TH1      ;  /* TIMER 1 - HIGH BYTE                           */
sfr at 0x8E CKCON    ;  /* TIMER 0/1 CLOCK CONTROL                       */
sfr at 0x8F PSCTL    ;  /* FLASH WRITE/ERASE CONTROL                     */
sfr at 0x91 SSTA0    ;  /* UART 0 STATUS                                 */
sfr at 0x98 SCON0    ;  /* UART 0 CONTROL                                */
sfr at 0x98 SCON     ;  /* UART 0 CONTROL                                */
sfr at 0x99 SBUF0    ;  /* UART 0 BUFFER                                 */
sfr at 0x99 SBUF     ;  /* UART 0 BUFFER                                 */
sfr at 0x9A SPI0CFG  ;  /* SPI 0 CONFIGURATION                           */
sfr at 0x9B SPI0DAT  ;  /* SPI 0 DATA                                    */
sfr at 0x9D SPI0CKR  ;  /* SPI 0 CLOCK RATE CONTROL                      */
sfr at 0xA1 EMI0TC   ;  /* EMIF TIMING CONTROL                           */
sfr at 0xA2 EMI0CN   ;  /* EMIF CONTROL                                  */
sfr at 0xA2 _XPAGE   ;  /* XDATA/PDATA PAGE                              */
sfr at 0xA3 EMI0CF   ;  /* EMIF CONFIGURATION                            */
sfr at 0xA9 SADDR0   ;  /* UART 0 SLAVE ADDRESS                          */
sfr at 0xB7 FLSCL    ;  /* FLASH SCALE                                   */
sfr at 0xB9 SADEN0   ;  /* UART 0 SLAVE ADDRESS MASK                     */
sfr at 0xBA AMX0CF   ;  /* ADC 0 MUX CONFIGURATION                       */
sfr at 0xBB AMX0SL   ;  /* ADC 0 MUX CHANNEL SELECTION                   */
sfr at 0xBC ADC0CF   ;  /* ADC 0 CONFIGURATION                           */
sfr at 0xBE ADC0L    ;  /* ADC 0 DATA - LOW BYTE                         */
sfr at 0xBF ADC0H    ;  /* ADC 0 DATA - HIGH BYTE                        */
sfr at 0xC0 SMB0CN   ;  /* SMBUS 0 CONTROL                               */
sfr at 0xC1 SMB0STA  ;  /* SMBUS 0 STATUS                                */
sfr at 0xC2 SMB0DAT  ;  /* SMBUS 0 DATA                                  */
sfr at 0xC3 SMB0ADR  ;  /* SMBUS 0 SLAVE ADDRESS                         */
sfr at 0xC4 ADC0GTL  ;  /* ADC 0 GREATER-THAN REGISTER - LOW BYTE        */
sfr at 0xC5 ADC0GTH  ;  /* ADC 0 GREATER-THAN REGISTER - HIGH BYTE       */
sfr at 0xC6 ADC0LTL  ;  /* ADC 0 LESS-THAN REGISTER - LOW BYTE           */
sfr at 0xC7 ADC0LTH  ;  /* ADC 0 LESS-THAN REGISTER - HIGH BYTE          */
sfr at 0xC8 TMR2CN   ;  /* TIMER 2 CONTROL                               */
sfr at 0xC9 TMR2CF   ;  /* TIMER 2 CONFIGURATION                         */
sfr at 0xCA RCAP2L   ;  /* TIMER 2 CAPTURE REGISTER - LOW BYTE           */
sfr at 0xCB RCAP2H   ;  /* TIMER 2 CAPTURE REGISTER - HIGH BYTE          */
sfr at 0xCC TMR2L    ;  /* TIMER 2 - LOW BYTE                            */
sfr at 0xCC TL2      ;  /* TIMER 2 - LOW BYTE                            */
sfr at 0xCD TMR2H    ;  /* TIMER 2 - HIGH BYTE                           */
sfr at 0xCD TH2      ;  /* TIMER 2 - HIGH BYTE                           */
sfr at 0xCF SMB0CR   ;  /* SMBUS 0 CLOCK RATE                            */
sfr at 0xD1 REF0CN   ;  /* VOLTAGE REFERENCE 0 CONTROL                   */
sfr at 0xD2 DAC0L    ;  /* DAC 0 REGISTER - LOW BYTE                     */
sfr at 0xD3 DAC0H    ;  /* DAC 0 REGISTER - HIGH BYTE                    */
sfr at 0xD4 DAC0CN   ;  /* DAC 0 CONTROL                                 */
sfr at 0xD8 PCA0CN   ;  /* PCA 0 COUNTER CONTROL                         */
sfr at 0xD9 PCA0MD   ;  /* PCA 0 COUNTER MODE                            */
sfr at 0xDA PCA0CPM0 ;  /* PCA 0 MODULE 0 CONTROL                        */
sfr at 0xDB PCA0CPM1 ;  /* PCA 0 MODULE 1 CONTROL                        */
sfr at 0xDC PCA0CPM2 ;  /* PCA 0 MODULE 2 CONTROL                        */
sfr at 0xDD PCA0CPM3 ;  /* PCA 0 MODULE 3 CONTROL                        */
sfr at 0xDE PCA0CPM4 ;  /* PCA 0 MODULE 4 CONTROL                        */
sfr at 0xDF PCA0CPM5 ;  /* PCA 0 MODULE 5 CONTROL                        */
sfr at 0xE1 PCA0CPL5 ;  /* PCA 0 MODULE 5 CAPTURE/COMPARE - LOW BYTE     */
sfr at 0xE2 PCA0CPH5 ;  /* PCA 0 MODULE 5 CAPTURE/COMPARE - HIGH BYTE    */
sfr at 0xE8 ADC0CN   ;  /* ADC 0 CONTROL                                 */
sfr at 0xE9 PCA0CPL2 ;  /* PCA 0 MODULE 2 CAPTURE/COMPARE - LOW BYTE     */
sfr at 0xEA PCA0CPH2 ;  /* PCA 0 MODULE 2 CAPTURE/COMPARE - HIGH BYTE    */
sfr at 0xEB PCA0CPL3 ;  /* PCA 0 MODULE 3 CAPTURE/COMPARE - LOW BYTE     */
sfr at 0xEC PCA0CPH3 ;  /* PCA 0 MODULE 3 CAPTURE/COMPARE - HIGH BYTE    */
sfr at 0xED PCA0CPL4 ;  /* PCA 0 MODULE 4 CAPTURE/COMPARE - LOW BYTE     */
sfr at 0xEE PCA0CPH4 ;  /* PCA 0 MODULE 4 CAPTURE/COMPARE - HIGH BYTE    */
sfr at 0xEF RSTSRC   ;  /* RESET SOURCE                                  */
sfr at 0xF8 SPI0CN   ;  /* SPI 0 CONTROL                                 */
sfr at 0xF9 PCA0L    ;  /* PCA 0 TIMER - LOW BYTE                        */
sfr at 0xFA PCA0H    ;  /* PCA 0 TIMER - HIGH BYTE                       */
sfr at 0xFB PCA0CPL0 ;  /* PCA 0 MODULE 0 CAPTURE/COMPARE - LOW BYTE     */
sfr at 0xFC PCA0CPH0 ;  /* PCA 0 MODULE 0 CAPTURE/COMPARE - HIGH BYTE    */
sfr at 0xFD PCA0CPL1 ;  /* PCA 0 MODULE 1 CAPTURE/COMPARE - LOW BYTE     */
sfr at 0xFE PCA0CPH1 ;  /* PCA 0 MODULE 1 CAPTURE/COMPARE - HIGH BYTE    */

/*  Page 0x01 */
sfr at 0x88 CPT0CN   ;  /* COMPARATOR 0 CONTROL                          */
sfr at 0x89 CPT0MD   ;  /* COMPARATOR 0 CONFIGURATION                    */
sfr at 0x98 SCON1    ;  /* UART 1 CONTROL                                */
sfr at 0x99 SBUF1    ;  /* UART 1 BUFFER                                 */
sfr at 0xC8 TMR3CN   ;  /* TIMER 3 CONTROL                               */
sfr at 0xC9 TMR3CF   ;  /* TIMER 3 CONFIGURATION                         */
sfr at 0xCA RCAP3L   ;  /* TIMER 3 CAPTURE REGISTER - LOW BYTE           */
sfr at 0xCB RCAP3H   ;  /* TIMER 3 CAPTURE REGISTER - HIGH BYTE          */
sfr at 0xCC TMR3L    ;  /* TIMER 3 - LOW BYTE                            */
sfr at 0xCD TMR3H    ;  /* TIMER 3 - HIGH BYTE                           */
sfr at 0xD2 DAC1L    ;  /* DAC 1 REGISTER - LOW BYTE                     */
sfr at 0xD3 DAC1H    ;  /* DAC 1 REGISTER - HIGH BYTE                    */
sfr at 0xD4 DAC1CN   ;  /* DAC 1 CONTROL                                 */

/*  Page 0x02 */
sfr at 0x88 CPT1CN   ;  /* COMPARATOR 1 CONTROL                          */
sfr at 0x89 CPT1MD   ;  /* COMPARATOR 1 CONFIGURATION                    */
sfr at 0xBA AMX2CF   ;  /* ADC 2 MUX CONFIGURATION                       */
sfr at 0xBB AMX2SL   ;  /* ADC 2 MUX CHANNEL SELECTION                   */
sfr at 0xBC ADC2CF   ;  /* ADC 2 CONFIGURATION                           */
sfr at 0xBE ADC2     ;  /* ADC 2 DATA                                    */
sfr at 0xC4 ADC2GT   ;  /* ADC 2 GREATER-THAN REGISTER                   */
sfr at 0xC6 ADC2LT   ;  /* ADC 2 LESS-THAN REGISTER                      */
sfr at 0xC8 TMR4CN   ;  /* TIMER 4 CONTROL                               */
sfr at 0xC9 TMR4CF   ;  /* TIMER 4 CONFIGURATION                         */
sfr at 0xCA RCAP4L   ;  /* TIMER 4 CAPTURE REGISTER - LOW BYTE           */
sfr at 0xCB RCAP4H   ;  /* TIMER 4 CAPTURE REGISTER - HIGH BYTE          */
sfr at 0xCC TMR4L    ;  /* TIMER 4 - LOW BYTE                            */
sfr at 0xCD TMR4H    ;  /* TIMER 4 - HIGH BYTE                           */

/*  Page 0x02 */
sfr at 0x91 MAC0BL   ;  /* MAC0 B Register Low Byte                      */
sfr at 0x92 MAC0BH   ;  /* MAC0 B Register High Byte                     */
sfr at 0x93 MAC0ACC0 ;  /* MAC0 Accumulator Byte 0 (LSB)                 */
sfr at 0x94 MAC0ACC1 ;  /* MAC0 Accumulator Byte 1                       */
sfr at 0x95 MAC0ACC2 ;  /* MAC0 Accumulator Byte 2                       */
sfr at 0x96 MAC0ACC3 ;  /* MAC0 Accumulator Byte 3 (MSB)                 */
sfr at 0x97 MAC0OVR  ;  /* MAC0 Accumulator Overflow                     */
sfr at 0xC0 MAC0STA  ;  /* MAC0 Status Register                          */
sfr at 0xC1 MAC0AL   ;  /* MAC0 A Register Low Byte                      */
sfr at 0xC2 MAC0AH   ;  /* MAC0 A Register High Byte                     */
sfr at 0xC3 MAC0CF   ;  /* MAC0 Configuration                            */
sfr at 0xCE MAC0RNDL ;  /* MAC0 Rounding Register Low Byte               */
sfr at 0xCF MAC0RNDH ;  /* MAC0 Rounding Register High Byte              */

/*  Page 0x0F */
sfr at 0x88 FLSTAT   ;  /* FLASH STATUS                                  */
sfr at 0x89 PLL0CN   ;  /* PLL 0 CONTROL                                 */
sfr at 0x8A OSCICN   ;  /* INTERNAL OSCILLATOR CONTROL                   */
sfr at 0x8B OSCICL   ;  /* INTERNAL OSCILLATOR CALIBRATION               */
sfr at 0x8C OSCXCN   ;  /* EXTERNAL OSCILLATOR CONTROL                   */
sfr at 0x8D PLL0DIV  ;  /* PLL 0 DIVIDER                                 */
sfr at 0x8E PLL0MUL  ;  /* PLL 0 MULTIPLIER                              */
sfr at 0x8F PLL0FLT  ;  /* PLL 0 FILTER                                  */
sfr at 0x96 SFRPGCN  ;  /* SFR PAGE CONTROL                              */
sfr at 0x97 CLKSEL   ;  /* SYSTEM CLOCK SELECT                           */
sfr at 0x9A CCH0MA   ;  /* CACHE MISS ACCUMULATOR                        */
sfr at 0x9C P4MDOUT  ;  /* PORT 4 OUTPUT MODE                            */
sfr at 0x9D P5MDOUT  ;  /* PORT 5 OUTPUT MODE                            */
sfr at 0x9E P6MDOUT  ;  /* PORT 6 OUTPUT MODE                            */
sfr at 0x9F P7MDOUT  ;  /* PORT 7 OUTPUT MODE                            */
sfr at 0xA1 CCH0CN   ;  /* CACHE CONTROL                                 */
sfr at 0xA2 CCH0TN   ;  /* CACHE TUNING REGISTER                         */
sfr at 0xA3 CCH0LC   ;  /* CACHE LOCK                                    */
sfr at 0xA4 P0MDOUT  ;  /* PORT 0 OUTPUT MODE                            */
sfr at 0xA5 P1MDOUT  ;  /* PORT 1 OUTPUT MODE                            */
sfr at 0xA6 P2MDOUT  ;  /* PORT 2 OUTPUT MODE CONFIGURATION              */
sfr at 0xA7 P3MDOUT  ;  /* PORT 3 OUTPUT MODE CONFIGURATION              */
sfr at 0xAD P1MDIN   ;  /* PORT 1 INPUT MODE                             */
sfr at 0xB7 FLACL    ;  /* FLASH ACCESS LIMIT                            */
sfr at 0xC8 P4       ;  /* PORT 4                                        */
sfr at 0xD8 P5       ;  /* PORT 5                                        */
sfr at 0xE1 XBR0     ;  /* CROSSBAR CONFIGURATION REGISTER 0             */
sfr at 0xE2 XBR1     ;  /* CROSSBAR CONFIGURATION REGISTER 1             */
sfr at 0xE3 XBR2     ;  /* CROSSBAR CONFIGURATION REGISTER 2             */
sfr at 0xE8 ADC2CN   ;  /* ADC 2 CONTROL                                 */
sfr at 0xE8 P6       ;  /* PORT 6                                        */
sfr at 0xF8 P7       ;  /* PORT 7                                        */


/*  BIT Registers  */

/*  P0  0x80 */
sbit at 0x80 P0_0    ;
sbit at 0x81 P0_1    ;
sbit at 0x82 P0_2    ;
sbit at 0x83 P0_3    ;
sbit at 0x84 P0_4    ;
sbit at 0x85 P0_5    ;
sbit at 0x86 P0_6    ;
sbit at 0x87 P0_7    ;

/*  TCON  0x88 */
sbit at 0x88 IT0     ;  /* EXT. INTERRUPT 0 TYPE                         */
sbit at 0x89 IE0     ;  /* EXT. INTERRUPT 0 EDGE FLAG                    */
sbit at 0x8A IT1     ;  /* EXT. INTERRUPT 1 TYPE                         */
sbit at 0x8B IE1     ;  /* EXT. INTERRUPT 1 EDGE FLAG                    */
sbit at 0x8C TR0     ;  /* TIMER 0 ON/OFF CONTROL                        */
sbit at 0x8D TF0     ;  /* TIMER 0 OVERFLOW FLAG                         */
sbit at 0x8E TR1     ;  /* TIMER 1 ON/OFF CONTROL                        */
sbit at 0x8F TF1     ;  /* TIMER 1 OVERFLOW FLAG                         */

/*  CPT0CN  0x88 */
sbit at 0x88 CP0HYN0 ;  /* COMPARATOR 0 NEGATIVE HYSTERESIS 0            */
sbit at 0x89 CP0HYN1 ;  /* COMPARATOR 0 NEGATIVE HYSTERESIS 1            */
sbit at 0x8A CP0HYP0 ;  /* COMPARATOR 0 POSITIVE HYSTERESIS 0            */
sbit at 0x8B CP0HYP1 ;  /* COMPARATOR 0 POSITIVE HYSTERESIS 1            */
sbit at 0x8C CP0FIF  ;  /* COMPARATOR 0 FALLING EDGE INTERRUPT           */
sbit at 0x8D CP0RIF  ;  /* COMPARATOR 0 RISING EDGE INTERRUPT            */
sbit at 0x8E CP0OUT  ;  /* COMPARATOR 0 OUTPUT                           */
sbit at 0x8F CP0EN   ;  /* COMPARATOR 0 ENABLE                           */

/*  CPT1CN  0x88 */
sbit at 0x88 CP1HYN0 ;  /* COMPARATOR 1 NEGATIVE HYSTERESIS 0            */
sbit at 0x89 CP1HYN1 ;  /* COMPARATOR 1 NEGATIVE HYSTERESIS 1            */
sbit at 0x8A CP1HYP0 ;  /* COMPARATOR 1 POSITIVE HYSTERESIS 0            */
sbit at 0x8B CP1HYP1 ;  /* COMPARATOR 1 POSITIVE HYSTERESIS 1            */
sbit at 0x8C CP1FIF  ;  /* COMPARATOR 1 FALLING EDGE INTERRUPT           */
sbit at 0x8D CP1RIF  ;  /* COMPARATOR 1 RISING EDGE INTERRUPT            */
sbit at 0x8E CP1OUT  ;  /* COMPARATOR 1 OUTPUT                           */
sbit at 0x8F CP1EN   ;  /* COMPARATOR 1 ENABLE                           */

/*  FLSTAT  0x88 */
sbit at 0x88 FLHBUSY ;  /* FLASH BUSY                                    */

/*  SCON0  0x98 */
sbit at 0x98 RI0     ;  /* UART 0 RX INTERRUPT FLAG                      */
sbit at 0x98 RI      ;  /* UART 0 RX INTERRUPT FLAG                      */
sbit at 0x99 TI0     ;  /* UART 0 TX INTERRUPT FLAG                      */
sbit at 0x99 TI      ;  /* UART 0 TX INTERRUPT FLAG                      */
sbit at 0x9A RB80    ;  /* UART 0 RX BIT 8                               */
sbit at 0x9B TB80    ;  /* UART 0 TX BIT 8                               */
sbit at 0x9C REN0    ;  /* UART 0 RX ENABLE                              */
sbit at 0x9C REN     ;  /* UART 0 RX ENABLE                              */
sbit at 0x9D SM20    ;  /* UART 0 MULTIPROCESSOR EN                      */
sbit at 0x9E SM10    ;  /* UART 0 MODE 1                                 */
sbit at 0x9F SM00    ;  /* UART 0 MODE 0                                 */

/*  SCON1  0x98 */
sbit at 0x98 RI1     ;  /* UART 1 RX INTERRUPT FLAG                      */
sbit at 0x99 TI1     ;  /* UART 1 TX INTERRUPT FLAG                      */
sbit at 0x9A RB81    ;  /* UART 1 RX BIT 8                               */
sbit at 0x9B TB81    ;  /* UART 1 TX BIT 8                               */
sbit at 0x9C REN1    ;  /* UART 1 RX ENABLE                              */
sbit at 0x9D MCE1    ;  /* UART 1 MCE                                    */
sbit at 0x9F S1MODE  ;  /* UART 1 MODE                                   */

/*  IE  0xA8 */
sbit at 0xA8 EX0     ;  /* EXTERNAL INTERRUPT 0 ENABLE                   */
sbit at 0xA9 ET0     ;  /* TIMER 0 INTERRUPT ENABLE                      */
sbit at 0xAA EX1     ;  /* EXTERNAL INTERRUPT 1 ENABLE                   */
sbit at 0xAB ET1     ;  /* TIMER 1 INTERRUPT ENABLE                      */
sbit at 0xAC ES0     ;  /* UART0 INTERRUPT ENABLE                        */
sbit at 0xAC ES      ;  /* UART0 INTERRUPT ENABLE                        */
sbit at 0xAD ET2     ;  /* TIMER 2 INTERRUPT ENABLE                      */
sbit at 0xAF EA      ;  /* GLOBAL INTERRUPT ENABLE                       */

/*  IP  0xB8 */
sbit at 0xB8 PX0     ;  /* EXTERNAL INTERRUPT 0 PRIORITY                 */
sbit at 0xB9 PT0     ;  /* TIMER 0 PRIORITY                              */
sbit at 0xBA PX1     ;  /* EXTERNAL INTERRUPT 1 PRIORITY                 */
sbit at 0xBB PT1     ;  /* TIMER 1 PRIORITY                              */
sbit at 0xBC PS      ;  /* SERIAL PORT PRIORITY                          */
sbit at 0xBD PT2     ;  /* TIMER 2 PRIORITY                              */

/* SMB0CN 0xC0 */
sbit at 0xC0 SMBTOE  ;  /* SMBUS 0 TIMEOUT ENABLE                        */
sbit at 0xC1 SMBFTE  ;  /* SMBUS 0 FREE TIMER ENABLE                     */
sbit at 0xC2 AA      ;  /* SMBUS 0 ASSERT/ACKNOWLEDGE FLAG               */
sbit at 0xC3 SI      ;  /* SMBUS 0 INTERRUPT PENDING FLAG                */
sbit at 0xC4 STO     ;  /* SMBUS 0 STOP FLAG                             */
sbit at 0xC5 STA     ;  /* SMBUS 0 START FLAG                            */
sbit at 0xC6 ENSMB   ;  /* SMBUS 0 ENABLE                                */
sbit at 0xC7 BUSY    ;  /* SMBUS 0 BUSY                                  */

/*  TMR2CN  0xC8 */
sbit at 0xC8 CPRL2   ;  /* TIMER 2 CAPTURE SELECT                        */
sbit at 0xC9 CT2     ;  /* TIMER 2 COUNTER SELECT                        */
sbit at 0xCA TR2     ;  /* TIMER 2 ON/OFF CONTROL                        */
sbit at 0xCB EXEN2   ;  /* TIMER 2 EXTERNAL ENABLE FLAG                  */
sbit at 0xCE EXF2    ;  /* TIMER 2 EXTERNAL FLAG                         */
sbit at 0xCF TF2     ;  /* TIMER 2 OVERFLOW FLAG                         */

/*  TMR3CN  0xC8 */
sbit at 0xC8 CPRL3   ;  /* TIMER 3 CAPTURE SELECT                        */
sbit at 0xC9 CT3     ;  /* TIMER 3 COUNTER SELECT                        */
sbit at 0xCA TR3     ;  /* TIMER 3 ON/OFF CONTROL                        */
sbit at 0xCB EXEN3   ;  /* TIMER 3 EXTERNAL ENABLE FLAG                  */
sbit at 0xCE EXF3    ;  /* TIMER 3 EXTERNAL FLAG                         */
sbit at 0xCF TF3     ;  /* TIMER 3 OVERFLOW FLAG                         */

/*  TMR4CN  0xC8 */
sbit at 0xC8 CPRL4   ;  /* TIMER 4 CAPTURE SELECT                        */
sbit at 0xC9 CT4     ;  /* TIMER 4 COUNTER SELECT                        */
sbit at 0xCA TR4     ;  /* TIMER 4 ON/OFF CONTROL                        */
sbit at 0xCB EXEN4   ;  /* TIMER 4 EXTERNAL ENABLE FLAG                  */
sbit at 0xCE EXF4    ;  /* TIMER 4 EXTERNAL FLAG                         */
sbit at 0xCF TF4     ;  /* TIMER 4 OVERFLOW FLAG                         */

/*  P4  0xC8 */
sbit at 0xC8 P4_0    ;
sbit at 0xC9 P4_1    ;
sbit at 0xCA P4_2    ;
sbit at 0xCB P4_3    ;
sbit at 0xCC P4_4    ;
sbit at 0xCD P4_5    ;
sbit at 0xCE P4_6    ;
sbit at 0xCF P4_7    ;

/*  PSW  0xD0 */
sbit at 0xD0 P       ;  /* ACCUMULATOR PARITY FLAG                       */
sbit at 0xD1 F1      ;  /* USER FLAG 1                                   */
sbit at 0xD2 OV      ;  /* OVERFLOW FLAG                                 */
sbit at 0xD3 RS0     ;  /* REGISTER BANK SELECT 0                        */
sbit at 0xD4 RS1     ;  /* REGISTER BANK SELECT 1                        */
sbit at 0xD5 F0      ;  /* USER FLAG 0                                   */
sbit at 0xD6 AC      ;  /* AUXILIARY CARRY FLAG                          */
sbit at 0xD7 CY      ;  /* CARRY FLAG                                    */

/* PCA0CN D8H */
sbit at 0xD8 CCF0    ;  /* PCA 0 MODULE 0 INTERRUPT FLAG                 */
sbit at 0xD9 CCF1    ;  /* PCA 0 MODULE 1 INTERRUPT FLAG                 */
sbit at 0xDA CCF2    ;  /* PCA 0 MODULE 2 INTERRUPT FLAG                 */
sbit at 0xDB CCF3    ;  /* PCA 0 MODULE 3 INTERRUPT FLAG                 */
sbit at 0xDC CCF4    ;  /* PCA 0 MODULE 4 INTERRUPT FLAG                 */
sbit at 0xDD CCF5    ;  /* PCA 0 MODULE 5 INTERRUPT FLAG                 */
sbit at 0xDE CR      ;  /* PCA 0 COUNTER RUN CONTROL BIT                 */
sbit at 0xDF CF      ;  /* PCA 0 COUNTER OVERFLOW FLAG                   */

/*  P5  0xD8 */
sbit at 0xD8 P5_0    ;
sbit at 0xD9 P5_1    ;
sbit at 0xDA P5_2    ;
sbit at 0xDB P5_3    ;
sbit at 0xDC P5_4    ;
sbit at 0xDD P5_5    ;
sbit at 0xDE P5_6    ;
sbit at 0xDF P5_7    ;

/* ADC0CN E8H */
sbit at 0xE8 AD0LJST ;  /* ADC 0 RIGHT JUSTIFY DATA BIT                  */
sbit at 0xE9 AD0WINT ;  /* ADC 0 WINDOW INTERRUPT FLAG                   */
sbit at 0xEA AD0CM0  ;  /* ADC 0 CONVERT START MODE BIT 0                */
sbit at 0xEB AD0CM1  ;  /* ADC 0 CONVERT START MODE BIT 1                */
sbit at 0xEC AD0BUSY ;  /* ADC 0 BUSY FLAG                               */
sbit at 0xED AD0INT  ;  /* ADC 0 EOC INTERRUPT FLAG                      */
sbit at 0xEE AD0TM   ;  /* ADC 0 TRACK MODE                              */
sbit at 0xEF AD0EN   ;  /* ADC 0 ENABLE                                  */

/* ADC2CN E8H */
sbit at 0xE8 AD2WINT ;  /* ADC 2 WINDOW INTERRUPT FLAG                   */
sbit at 0xE9 AD2CM0  ;  /* ADC 2 CONVERT START MODE BIT 0                */
sbit at 0xEA AD2CM1  ;  /* ADC 2 CONVERT START MODE BIT 1                */
sbit at 0xEB AD2CM2  ;  /* ADC 2 CONVERT START MODE BIT 2                */
sbit at 0xEC AD2BUSY ;  /* ADC 2 BUSY FLAG                               */
sbit at 0xED AD2INT  ;  /* ADC 2 EOC INTERRUPT FLAG                      */
sbit at 0xEE AD2TM   ;  /* ADC 2 TRACK MODE                              */
sbit at 0xEF AD2EN   ;  /* ADC 2 ENABLE                                  */

/*  P6  0xE8 */
sbit at 0xE8 P6_0    ;
sbit at 0xE9 P6_1    ;
sbit at 0xEA P6_2    ;
sbit at 0xEB P6_3    ;
sbit at 0xEC P6_4    ;
sbit at 0xED P6_5    ;
sbit at 0xEE P6_6    ;
sbit at 0xEF P6_7    ;

/* SPI0CN F8H */
sbit at 0xF8 SPIEN   ;  /* SPI 0 SPI ENABLE                              */
sbit at 0xF9 TXBMT   ;  /* SPI 0 TX BUFFER EMPTY FLAG                    */
sbit at 0xFA NSSMD0  ;  /* SPI 0 SLAVE SELECT MODE 0                     */
sbit at 0xFB NSSMD1  ;  /* SPI 0 SLAVE SELECT MODE 1                     */
sbit at 0xFC RXOVRN  ;  /* SPI 0 RX OVERRUN FLAG                         */
sbit at 0xFD MODF    ;  /* SPI 0 MODE FAULT FLAG                         */
sbit at 0xFE WCOL    ;  /* SPI 0 WRITE COLLISION FLAG                    */
sbit at 0xFF SPIF    ;  /* SPI 0 INTERRUPT FLAG                          */

/*  P7  0xF8 */
sbit at 0xF8 P7_0    ;
sbit at 0xF9 P7_1    ;
sbit at 0xFA P7_2    ;
sbit at 0xFB P7_3    ;
sbit at 0xFC P7_4    ;
sbit at 0xFD P7_5    ;
sbit at 0xFE P7_6    ;
sbit at 0xFF P7_7    ;


/* Predefined SFR Bit Masks */

#define IDLE              0x01    /* PCON                                */
#define STOP              0x02    /* PCON                                */
#define ECCF              0x01    /* PCA0CPMn                            */
#define PWM               0x02    /* PCA0CPMn                            */
#define TOG               0x04    /* PCA0CPMn                            */
#define MAT               0x08    /* PCA0CPMn                            */
#define CAPN              0x10    /* PCA0CPMn                            */
#define CAPP              0x20    /* PCA0CPMn                            */
#define ECOM              0x40    /* PCA0CPMn                            */
#define PWM16             0x80    /* PCA0CPMn                            */
#define PORSF             0x02    /* RSTSRC                              */
#define SWRSF             0x10    /* RSTSRC                              */


/* SFR PAGE DEFINITIONS */

#define CONFIG_PAGE       0x0F     /* SYSTEM AND PORT CONFIGURATION PAGE */
#define LEGACY_PAGE       0x00     /* LEGACY SFR PAGE                    */
#define TIMER01_PAGE      0x00     /* TIMER 0 AND TIMER 1                */
#define CPT0_PAGE         0x01     /* COMPARATOR 0                       */
#define CPT1_PAGE         0x02     /* COMPARATOR 1                       */
#define UART0_PAGE        0x00     /* UART 0                             */
#define UART1_PAGE        0x01     /* UART 1                             */
#define SPI0_PAGE         0x00     /* SPI 0                              */
#define EMI0_PAGE         0x00     /* EXTERNAL MEMORY INTERFACE          */
#define ADC0_PAGE         0x00     /* ADC 0                              */
#define ADC2_PAGE         0x02     /* ADC 2                              */
#define SMB0_PAGE         0x00     /* SMBUS 0                            */
#define TMR2_PAGE         0x00     /* TIMER 2                            */
#define TMR3_PAGE         0x01     /* TIMER 3                            */
#define TMR4_PAGE         0x02     /* TIMER 4                            */
#define DAC0_PAGE         0x00     /* DAC 0                              */
#define DAC1_PAGE         0x01     /* DAC 1                              */
#define PCA0_PAGE         0x00     /* PCA 0                              */
#define PLL0_PAGE         0x0F     /* PLL 0                              */

#endif
