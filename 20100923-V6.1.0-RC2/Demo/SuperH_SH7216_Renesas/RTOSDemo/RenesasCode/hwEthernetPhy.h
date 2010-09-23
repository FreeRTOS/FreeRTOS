/******************************************************************************
* File Name    : hwEthernetPhy.h
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

#ifndef HWETHERNETPHY_H_INCLUDED
#define HWETHERNETPHY_H_INCLUDED

/*****************************************************************************
Enumerated Types
******************************************************************************/

typedef enum _NETLNK
{
    PHY_NO_LINK = 0,
    PHY_LINK_10H,
    PHY_LINK_10F,
    PHY_LINK_100H,
    PHY_LINK_100F
    
} NETLNK;

/*****************************************************************************
Public Functions
******************************************************************************/

#ifdef __cplusplus
extern "C" {
#endif

/*****************************************************************************
Function Name:  phyReset
Description:    Executes software reset of PHY and sets to auto negotiate link
Parameters:     None
Return value:   0 for success -1 on error
******************************************************************************/

extern  int phyReset(void);

/*****************************************************************************
Function Name: phyStatus
Description:   Function to reurn the type of physical link
Parameters:    none
Return value:  The link type
*****************************************************************************/

extern  NETLNK phyStatus(void);

#ifdef __cplusplus
}
#endif

#endif                              /* HWETHERNETPHY_H_INCLUDED */

/*****************************************************************************
End  Of File
******************************************************************************/