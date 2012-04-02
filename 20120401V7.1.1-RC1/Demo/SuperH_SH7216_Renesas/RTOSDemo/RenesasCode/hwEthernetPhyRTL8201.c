/******************************************************************************
* File Name    : hwEthernetPhy.c
* Version      : 1.0
* Device(s)    : Renesas
* Tool-Chain   : Renesas SH2A V9+
* OS           : None
* H/W Platform : SH2A
* Description  : Hardware driver for the LAN8700 PHY
*******************************************************************************
* History      : DD.MM.YYYY Ver. Description
*              : 01.08.2009 1.00 MAB First Release
******************************************************************************/

/******************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Technology Corp. and is only
* intended for use with Renesas products. No other uses are authorized.
* This software is owned by Renesas Technology Corp. and is protected under
* all applicable laws, including copyright laws.
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES
* REGARDING THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY,
* INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A
* PARTICULAR PURPOSE AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY
* DISCLAIMED.
* TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS
* TECHNOLOGY CORP. NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE
* FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES
* FOR ANY REASON RELATED TO THE THIS SOFTWARE, EVEN IF RENESAS OR ITS
* AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this
* software and to discontinue the availability of this software.
* By using this software, you agree to the additional terms and
* conditions found by accessing the following link:
* http://www.renesas.com/disclaimer
******************************************************************************/
/* Copyright (C) 2008. Renesas Technology Corp.,       All Rights Reserved.  */
/* Copyright (C) 2009. Renesas Technology Europe Ltd., All Rights Reserved.  */
/*****************************************************************************/

/*****************************************************************************
System Includes
******************************************************************************/

#include <stdio.h>
/* Header file for sleep() and nop() functions */
#include <machine.h>

/*****************************************************************************
User Includes
******************************************************************************/

/* Defines for I/O registers */
#include "iodefine.h"
/* rsk7216def.h provides common defines for widely used items. */
#include "rsk7216def.h"
/* Physical layer functions */
#include "hwEthernetPhy.h"
#include "Trace.h"

#include "FreeRTOS.h"
#include "task.h"

/*****************************************************************************
Constant Macros
******************************************************************************/

/* Preamble */
#define PHY_ST                              0x0001
/* Operation to be executed on PHY registers */
#define PHY_READ                            0x0002
#define PHY_WRITE                           0x0001
/* Physical address of PHY device */
#define PHY_ADDR                            0x001F

/* Description of PHY data registers */
#define PHY_BASIC_MODE_CONTROL              0x0000
#define PHY_BASIC_MODE_STATUS               0x0001
#define PHY_IDENTIFIER1                     0x0002
#define PHY_IDENTIFIER2                     0x0003
#define PHY_AN_ADVERTISEMENT                0x0004
#define PHY_AN_LINK_PARTNER_ABILITY         0x0005

/* Definitions of some configuration bits */
#define PHY_RESET                           0x8000
#define PHY_AN_ENABLE                       0x1200
/* Bits for auto negotiation for 100, 10 half and full duplex set */
#define PHY_AN_10_100_F_H                   0xDE1
/* Link partner ability register bits for establising the result of the
   auto negotiation */
#define PHY_AN_100F                         BIT_8
#define PHY_AN_100H                         BIT_7
#define PHY_AN_10F                          BIT_6
#define PHY_AN_10H                          BIT_5

/*****************************************************************************
Function Prototypes
******************************************************************************/

static USHORT phyReadReg(USHORT usRegAddr);
static void phyWriteReg(USHORT usRegAddr, USHORT usData);
static void phyPreamble(void);
static void phyMiiWrite1(void);
static void phyMiiWrite0(void);
static void phyRegSet(USHORT usRegAddr, long lOption);
static void phyRegRead(PUSHORT pusData);
static void phyRegWrite(USHORT usData);
static void phyTaZ0(void);
static void phyTa10(void);
static void phyDelay(void);

/*****************************************************************************
Public Functions
******************************************************************************/

/*****************************************************************************
Function Name:  phyReset
Description:    Executes software reset of PHY and sets to auto negotiate link
Parameters:     None
Return value:   0 for success -1 on error
******************************************************************************/
int phyReset(void)
{
	/* One second of attempting to reset the PHY */
    int iCount = 1000; 
    /* Set software reset */
    phyWriteReg(PHY_BASIC_MODE_CONTROL, PHY_RESET);
    while (iCount--)
    {
        USHORT  usData;
		
		vTaskDelay( 2 / portTICK_RATE_MS );
		
		/* Read the status of the PHY */
        usData = phyReadReg(PHY_BASIC_MODE_CONTROL);
        /* Wait for the reset flag to be cleared */
        if ((usData & PHY_RESET) == 0)
        {
            /* Set auto negoatiation for 10,100 full and half duplex */
            phyWriteReg(PHY_AN_ADVERTISEMENT, PHY_AN_10_100_F_H);
            /* Set auto negotiate and restart auto negotiate bits */
            phyWriteReg(PHY_BASIC_MODE_CONTROL, PHY_AN_ENABLE);

            /* Auto negotiation will now take place wait for two seconds */
            vTaskDelay( 2000 / portTICK_RATE_MS );

			/* Success */
            return 0;
        }
    }
    /* Phy did not respond to software reset */
    return -1;
}
/*****************************************************************************
End of function phyReset
 ******************************************************************************/

/*****************************************************************************
Function Name: phyStatus
Description:   Function to reurn the type of physical link
Parameters:    none
Return value:  The link type
*****************************************************************************/
NETLNK phyStatus(void)
{
    /* The state of this flag depens on the hardware connection to the MAC */
    if (!EtherC.PSR.BIT.LMON)
    {
        /* Read the auto negotiation link partner ability register to establish
           the type of link */
        USHORT  usData = phyReadReg(PHY_AN_LINK_PARTNER_ABILITY);
        if (usData & PHY_AN_100F)
        {
            return PHY_LINK_100F;
        }
        if (usData & PHY_AN_100H)
        {
            return PHY_LINK_100H;
        }
        if (usData & PHY_AN_10F)
        {
            return PHY_LINK_10F;
        }
        if (usData & PHY_AN_10H)
        {
            return PHY_LINK_10H;
        }
    }
    return PHY_NO_LINK;
}
/*****************************************************************************
End of function  phyStatus
******************************************************************************/

/*****************************************************************************
Private Functions
******************************************************************************/

/*****************************************************************************
Function Name:  phyReadReg
Description:    Reads data from a register with the address usRegAddr
Parameters:     (USHORT) usRegAddr - address to be read;
Return value:   (USHORT) - value from read register;
******************************************************************************/
static USHORT phyReadReg(USHORT usRegAddr)
{
    USHORT  usData;
    phyPreamble();
    phyRegSet(usRegAddr, PHY_READ);
    phyTaZ0();
    phyRegRead(&usData);
    phyTaZ0();
    return usData;
}
/*****************************************************************************
End of function phyReadReg
******************************************************************************/

/*****************************************************************************
Function Name:  phyWriteReg
Description:    Write data to register with the address usRegAddr
Parameters:     (USHORT) usRegAddr - address of register where to be written;
                (USHORT) usData - value to write;
Return value:   None
******************************************************************************/
static void phyWriteReg(USHORT usRegAddr, USHORT usData)
{
    phyPreamble();
    phyRegSet(usRegAddr, PHY_WRITE);
    phyTa10();
    phyRegWrite(usData);
    phyTaZ0();
}
/*****************************************************************************
End of function phyWriteReg
******************************************************************************/

/*****************************************************************************
Function Name:  phyPreamble
Description:    Writing 32 bits of '1'
Parameters:     None
Return value:   None
******************************************************************************/
static void phyPreamble(void)
{
    int iCount = 32;
    while (iCount--)
    {
        phyMiiWrite1();
    }
}
/*****************************************************************************
End of function phyPreamble
******************************************************************************/

/*****************************************************************************
Function Name:  phyRegSet
Description:    Sets the address of register
Parameters:     (USHORT) usRegAddr - address to be set;
                (long) lOption - PHY_READ or PHY_WRITE;
Return value:   None
******************************************************************************/
static void phyRegSet(USHORT usRegAddr, long lOption)
{
    int iBit = 14;
    USHORT usData;

	/* Format of PHY Address Set Transmission */
	/* ST R/W PAddress Address    */
	/* 1  10  11111    xxxx    00 */ //Read
	/* 1  01  11111    xxxx    00 */ //Write

    usData = 0;
    /* ST code */
    usData = (PHY_ST << 14);
    if (lOption == PHY_READ)
    {
        /* Option code (RD) */
        usData |= (PHY_READ << 12);
    }
    else
    {
        /* Option code (WT) */
        usData |= (PHY_WRITE << 12);
    }
    /* PHY Address  */
    usData |= ((BYTE)PHY_ADDR << 7);
    /* Reg Address  */
    usData |= (USHORT)(usRegAddr << 2);

    while (iBit--)
    {
        if ((usData & 0x8000) == 0)
        {
            phyMiiWrite0();
        }
        else
        {
            phyMiiWrite1();
        }
        usData <<= 1;
    }
}
/*****************************************************************************
End of function phyRegSet
******************************************************************************/

/*****************************************************************************
Function Name:  phyRegRead
Description:    Read data from register
Parameters:     IN  pusDest - value to be read;
Return value:   None
******************************************************************************/
static void phyRegRead(PUSHORT pusDest)
{
    USHORT usData = 0;
    int    iBit = 16;
    while (iBit--)
    {
        EtherC.PIR.LONG = 0x00UL;
        EtherC.PIR.LONG = 0x01UL;
        usData <<= 1;

        /* MDI read */
        usData |= (USHORT)((EtherC.PIR.LONG & 0x08UL) >> 3);

        EtherC.PIR.LONG = 0x01UL;
        EtherC.PIR.LONG = 0x00UL;
    }
    *pusDest = usData;
}
/*****************************************************************************
End of function phyRegRead
******************************************************************************/

/*****************************************************************************
Function Name:  phyRegWrite
Description:    Write 2 bytes (16 bit) to MII
Parameters:     IN usData - value to be written;
Return value:   None
******************************************************************************/
static void phyRegWrite(USHORT usData)
{
    int iBit = 16;
    while (iBit--)
    {
        if ((usData & 0x8000) == 0)
        {
            phyMiiWrite0();
        }
        else
        {
            phyMiiWrite1();
        }
        usData <<= 1;
    }
}
/*****************************************************************************
End of function phyRegWrite
******************************************************************************/

/*****************************************************************************
Function Name:  phyTaZ0
Description:    Set bus to high Z
Parameters:     None
Return value:   None
******************************************************************************/
static void phyTaZ0(void)
{
    EtherC.PIR.LONG = 0x00UL;
    EtherC.PIR.LONG = 0x01UL;
    EtherC.PIR.LONG = 0x01UL;
    EtherC.PIR.LONG = 0x00UL;
}
/*****************************************************************************
End of function phyTaZ0
******************************************************************************/

/*****************************************************************************
Function Name:  phyTa10
Description:    Set bus to output
Parameters:     None
Return value:   None
******************************************************************************/
static void phyTa10(void)
{
    EtherC.PIR.LONG = 0x06UL;
    EtherC.PIR.LONG = 0x07UL;
    EtherC.PIR.LONG = 0x07UL;
    EtherC.PIR.LONG = 0x06UL;
    EtherC.PIR.LONG = 0x02UL;
    EtherC.PIR.LONG = 0x03UL;
    EtherC.PIR.LONG = 0x03UL;
    EtherC.PIR.LONG = 0x02UL;
}
/*****************************************************************************
End of function phyTa10
******************************************************************************/

/*****************************************************************************
Function Name:  phyMiiWrite1
Description:    Write 1 to MII
Parameters:     None
Return value:   None
******************************************************************************/
static void phyMiiWrite1(void)
{
    EtherC.PIR.LONG = 0x06UL;
    EtherC.PIR.LONG = 0x07UL;
    EtherC.PIR.LONG = 0x07UL;
    EtherC.PIR.LONG = 0x06UL;
}
/*****************************************************************************
End of function phyMiiWrite1
******************************************************************************/

/*****************************************************************************
Function Name:  phyMiiWrite0
Description:    Write 0 to MII
Parameters:     None
Return value:   None
******************************************************************************/
static void phyMiiWrite0(void)
{
    EtherC.PIR.LONG = 0x02UL;
    EtherC.PIR.LONG = 0x03UL;
    EtherC.PIR.LONG = 0x03UL;
    EtherC.PIR.LONG = 0x02UL;
}
/*****************************************************************************
End of function phyMiiWrite0
******************************************************************************/

/*****************************************************************************
End  Of File
******************************************************************************/
