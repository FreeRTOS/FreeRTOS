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
* File Name	   : hwsetup.c
* Device(s)    : RX
* H/W Platform : YRDKRX63N
* Description  : Defines the initialisation routines used each time the MCU is restarted.
***********************************************************************************************************************/
/***********************************************************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 26.10.2011 1.00     First Release
***********************************************************************************************************************/

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
#include <stdint.h>
/* I/O Register and board definitions */
#include "platform.h"

/***********************************************************************************************************************
Private global variables and functions
***********************************************************************************************************************/
/* MCU I/O port configuration function delcaration */
static void output_ports_configure(void);

/* Interrupt configuration function delcaration */
static void interrupts_configure(void);

/* MCU peripheral module configuration function declaration */
static void peripheral_modules_enable(void);


/***********************************************************************************************************************
* Function name: hardware_setup
* Description  : Contains setup functions called at device restart
* Arguments    : none
* Return value : none
***********************************************************************************************************************/
void hardware_setup(void)
{
    output_ports_configure();
    interrupts_configure();
    peripheral_modules_enable();
}

/***********************************************************************************************************************
* Function name: output_ports_configure
* Description  : Configures the port and pin direction settings, and sets the pin outputs to a safe level.
* Arguments    : none
* Return value : none
***********************************************************************************************************************/
void output_ports_configure(void)
{
    SYSTEM.PRCR.WORD = 0xA50B;			/* Protect off */
    MPC.PWPR.BIT.B0WI = 0 ;     		/* Unlock protection register */
    MPC.PWPR.BIT.PFSWE = 1 ;    		/* Unlock MPC registers */
    
    MSTP(EDMAC) = 0 ;                   /* Power up ethernet block */
    
    /* Port 0 - DAC & ethernet IRQ */
    PORT0.PODR.BYTE = 0x00 ;    /* All outputs low to start */
    PORT0.PDR.BYTE  = 0x10 ;    /* DA1 is an ouput, all others are inputs */
    
    /* Port 1 - I2C and USB over-current & pull-up control */
    PORT1.PODR.BYTE = 0x00 ;    /* All outputs low to start */
    PORT1.PDR.BYTE  = 0x80 ;    /* AUD_R (P1.7) is an output, all others are inputs (I2C lines setup by 
    *                              I2C driver later */
    
    /* Port 2 - USB control and some expansion signals */
    PORT2.PODR.BYTE = 0x02 ;    /* All outputs low to start except backlight enable */
    PORT2.PDR.BYTE  = 0x02 ;    /* All inputs except backlight enable - some will be overridden by USB driver later */
    
    /* Port 3 - Serial port & JTAG */
    PORT3.PODR.BYTE = 0x00 ;    /* All outputs low to start */
    PORT3.PDR.BIT.B2  = 0x01 ;  /* Transmit line for SCI6/ CAN 0 TxD is an output */
    
    /* Port 4 -  */
    PORT4.PODR.BYTE = 0x00 ;    /* These are all inputs */
    PORT4.PDR.BYTE  = 0x00 ;    /* Analog inputs and switches, all inputs */
    PORT4.PMR.BYTE  = 0x00 ;

    /* Port 5 -  */
    PORT5.PODR.BYTE = 0x00 ;    /* All outputs low to start */
    PORT5.PDR.BYTE  = 0x13 ;    /* SCI 2 TxD, LCD_RS, PWMLP_OUT are outputs */
    MPC.P50PFS.BYTE = 0x0A ;    /* P50 is TXD2. */
    MPC.P52PFS.BYTE = 0x0A ;    /* P52 is RXD2. */
    PORT5.PMR.BYTE  = 0x05 ;    /* P50 and P52 are used for SCI2. */

    /* Port A - Ethernet MDIO */
    PORTA.PODR.BYTE = 0x00 ;    /* */
    PORTA.PMR.BYTE  = 0x00 ;    /* All GPIO for now */
    MPC.PA3PFS.BYTE = 0x11 ;    /* PA3 is RMII MDIO */
    MPC.PA4PFS.BYTE = 0x11 ;    /* PA4 is RMII MDC */
    MPC.PA5PFS.BYTE = 0x11 ;    /* PA5 is RMII LINK_STA */
    PORTA.PMR.BYTE  = 0x38 ;    /* PA3-5 are used by Ethernet peripheral */
    PORTA.PDR.BYTE  = 0xFF ;    /* */
    
    /* Port B - Ethernet signals */
    PORTB.PODR.BYTE = 0x00 ;    /* */
    PORTB.PMR.BYTE  = 0x00 ;    /* All GPIO for now */
    MPC.PB0PFS.BYTE = 0x12 ;    /* PB0 is RMII_RXD1 */
    MPC.PB1PFS.BYTE = 0x12 ;    /* PB1 is RMII_RXD0 */
    MPC.PB2PFS.BYTE = 0x12 ;    /* PB2 is REF50CK */
    MPC.PB3PFS.BYTE = 0x12 ;    /* PB3 is RMI_RX_ERR */
    MPC.PB4PFS.BYTE = 0x12 ;    /* PB4 is RMII_TXD_EN */
    MPC.PB5PFS.BYTE = 0x12 ;    /* PB5 is RMII_TXD0 */
    MPC.PB6PFS.BYTE = 0x12 ;    /* PB6 is RMII_TXD1 */
    MPC.PB7PFS.BYTE = 0x12 ;    /* PB7 is RMII_CRS_DV */
    PORTB.PMR.BYTE  = 0xFF ;    /* All pins assigned to peripheral */
    PORTB.PDR.BYTE  = 0xF0 ;    /* */
    
    /* Port C -  SPI signals, chip selects, peripheral reset */
    PORTC.PODR.BYTE = 0x00 ;    /* */
    PORTC.PMR.BYTE  = 0x00 ;    /* All GPIO for now */
    MPC.PC5PFS.BYTE = 0x0D ;    /* PC5 is RSPCKA */
    MPC.PC6PFS.BYTE = 0x0D ;    /* PC6 is MOSIA */
    MPC.PC7PFS.BYTE = 0x0D ;    /* PC7 is MISOA */
    PORTC.PMR.BYTE  = 0xE0 ;    /* PC5-7 assigned to SPI peripheral */
    PORTC.PODR.BYTE = 0x17 ;    /* All outputs low to start */
    PORTC.PDR.BYTE  = 0x7F ;    /* All outputs except MISO */


    /* Port D -  LED's */
    PORTD.PODR.BYTE = 0xFF ;    /* All outputs LED's off */
    PORTD.PDR.BYTE  = 0xFF ;    /* All outputs */

    /* Port E -  LED's, WiFi & PMOD control */
    PORTE.PODR.BYTE = 0xFF ;    /* All LED's off, all chip selects inactive */
    PORTE.PDR.BYTE  = 0x7F ;    /* All outputs except PMOD_MISO */

    /* Port J -  WiFi chip select */
    PORTJ.PODR.BYTE = 0x04 ;    /* WiFi CS de-asserted at power up */
    PORTJ.PDR.BYTE  = 0x04 ;    /* WiFi CS is an output */
}

/***********************************************************************************************************************
* Function name: interrupts_configure
* Description  : Configures interrupts used
* Arguments    : none
* Return value : none
***********************************************************************************************************************/
void interrupts_configure(void)
{
    /* Add code here to setup additional interrupts */
}

/***********************************************************************************************************************
* Function name: peripheral_modules_enable
* Description  : Enables and configures peripheral devices on the MCU
* Arguments    : none
* Return value : none
***********************************************************************************************************************/
void peripheral_modules_enable(void)
{
    /* Add code here to enable peripherals used by the application */
}
