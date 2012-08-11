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
* http:/*www.renesas.com/disclaimer 
*
* Copyright (C) 2012 Renesas Electronics Corporation. All rights reserved.    
***********************************************************************************************************************/
/***********************************************************************************************************************
* File Name	   : yrdkrx63n.h
* H/W Platform : YRDKRX63N
* Description  : Board specific definitions for the RDKRX63N.
***********************************************************************************************************************/
/***********************************************************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 30.11.2011 1.00     First Release
***********************************************************************************************************************/

#ifndef RDK_RX63N_H
#define RDK_RX63N_H


/* Local defines */
#define LED_ON              (0)
#define LED_OFF             (1)

/* I/0 port 1 */
#define USB_VBUSEN          PORT1.PODR.BIT.B6 
#define AUDIO_OUT_R         PORT1.PODR.BIT.B7

/* I/0 port 2 */
#define BL_ENA              PORT2.PODR.BIT.B1 
#define USB_DPUPEA          PORT2.PODR.BIT.B3 

/* I/O port 3 */
#define CAN_WIFI_TX         PORT3.PODR.BIT.B2    

/* I/O port 4: switches and various peripherals  */
#define SW_ACTIVE           (0)
#define SW1                 PORT4.PIDR.BIT.B0   
#define SW1_PMR             PORT4.PMR.BIT.B0
#define SW1_PDR             PORT4.PDR.BIT.B0
#define SW2                 PORT4.PIDR.BIT.B1    
#define SW2_PMR             PORT4.PMR.BIT.B1
#define SW2_PDR             PORT4.PDR.BIT.B1
#define POTENTIOMETER       PORT4.PODR.BIT.B2
#define JN1_AN3             PORT4.PODR.BIT.B3
#define SW3                 PORT4.PIDR.BIT.B4 
#define SW3_PMR             PORT4.PMR.BIT.B4
#define SW3_PDR             PORT4.PDR.BIT.B4
#define MICROPHONE          PORT4.PODR.BIT.B5
#define AUDIO_IN_R          PORT4.PODR.BIT.B6
#define PWMLP_IN            PORT4.PODR.BIT.B7

/* I/O port 5  */
#define LCD_RS              PORT5.PODR.BIT.B1
#define BCLK                PORT5.PODR.BIT.B3
#define PWMLP_OUT           PORT5.PODR.BIT.B4

/* I/O port A:  Extension slot (JN2) and E/N pins */
#define JN2_SSLA1_B         PORTA.PODR.BIT.B0
#define PMOD1_PIN8          PORTA.PODR.BIT.B1
#define AMP_SHDN            PORTA.PODR.BIT.B2
#define ETH_MDIO            PORTA.PODR.BIT.B3
#define ETH_MDC             PORTA.PODR.BIT.B4
#define ETH_LINK            PORTA.PODR.BIT.B5

/* I/O port B:  Ethernet I/O pins definitions */
#define RMII_RXD1           PORTB.PODR.BIT.B0
#define RMII_RXD0           PORTB.PODR.BIT.B1
#define ETH_CLK             PORTB.PODR.BIT.B2
#define RMII_RX_ER          PORTB.PODR.BIT.B3
#define RMII_TX_EN          PORTB.PODR.BIT.B4        
#define RMII_TXD0           PORTB.PODR.BIT.B5        
#define RMII_TXD1           PORTB.PODR.BIT.B6    
#define ETH_CRS             PORTB.PODR.BIT.B7

/* I/O port C:  RSPI and peripheral I/O pins definitions */
#define RSPI_CHANNEL_0      0
#define RSPI_CHANNEL_1      1
#define FLASH_CS            PORTC.PODR.BIT.B0        /* SSL 1 */
#define AUDIO_OUT_L         PORTC.PODR.BIT.B1
#define LCD_CS              PORTC.PODR.BIT.B2        /* SSL 3 */
#define LCD_RESET           PORTC.PODR.BIT.B3         
#define SDMICRO_CS          PORTC.PODR.BIT.B4        /* SSL 0 */
#define RSPI_SCLOCK         PORTC.PODR.BIT.B5        
#define RSPI_MOSI           PORTC.PODR.BIT.B6        
#define RSPI_MISO           PORTC.PODR.BIT.B7

/* I/O ports D & E:  LEDs */
#define LED4                PORTD.PODR.BIT.B5
#define LED5                PORTE.PODR.BIT.B3
#define LED6                PORTD.PODR.BIT.B2     
#define LED7                PORTE.PODR.BIT.B0
#define LED8                PORTD.PODR.BIT.B4
#define LED9                PORTE.PODR.BIT.B2
#define LED10               PORTD.PODR.BIT.B1
#define LED11               PORTD.PODR.BIT.B7
#define LED12               PORTD.PODR.BIT.B3
#define LED13               PORTE.PODR.BIT.B1
#define LED14               PORTD.PODR.BIT.B0
#define LED15               PORTD.PODR.BIT.B6

/* WiFi chip select */
#define WIFI_CS             PORTJ.PODR.BIT.B3        

#endif /* RDK_RX63N_H */

