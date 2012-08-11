/******************************************************************************
* DISCLAIMER
* Please refer to http://www.renesas.com/disclaimer
******************************************************************************
  Copyright (C) 2008. Renesas Technology Corp., All Rights Reserved.
*******************************************************************************
* File Name    : phy.h
* Version      : 1.02
* Description  : Ethernet PHY device driver
******************************************************************************
* History : DD.MM.YYYY Version Description
*         : 15.02.2010 1.00    First Release
*         : 17.03.2010 1.01    Modification of macro definitions for access timing
*         : 06.04.2010 1.02    RX62N changes
******************************************************************************/

#ifndef	PHY_H
#define	PHY_H

/******************************************************************************
Includes   <System Includes> , "Project Includes"
******************************************************************************/
#include <stdint.h>

/******************************************************************************
Typedef definitions
******************************************************************************/

/******************************************************************************
Macro definitions
******************************************************************************/
/* Standard PHY Registers */
#define	BASIC_MODE_CONTROL_REG		0       
#define	BASIC_MODE_STATUS_REG		1       
#define	PHY_IDENTIFIER1_REG		    2       
#define	PHY_IDENTIFIER2_REG		    3       
#define	AN_ADVERTISEMENT_REG		4       
#define	AN_LINK_PARTNER_ABILITY_REG	5       
#define	AN_EXPANSION_REG		    6

/* Media Independent Interface */
#define  PHY_ST    1
#define  PHY_READ  2
#define  PHY_WRITE 1
#define  PHY_ADDR  0x01

#define  MDC_WAIT  2

/* PHY return definitions */
#define R_PHY_OK     0
#define R_PHY_ERROR -1

/* Auto-Negotiation Link Partner Status */
#define PHY_AN_LINK_PARTNER_100BASE	0x0180
#define PHY_AN_LINK_PARTNER_FULL	0x0140
#define PHY_AN_COMPLETE				( 1 << 5 )

/*
 *	Wait counter definitions of PHY-LSI initialization
 *	ICLK = 96MHz
*/
#define PHY_RESET_WAIT				0x00000020L
#define PHY_AUTO_NEGOTIATON_WAIT	75

#define PHY_AN_ENABLE				0x1200
#define PHY_AN_10_100_F_H			0xde1

/******************************************************************************
Variable Externs
******************************************************************************/

/******************************************************************************
Functions Prototypes
******************************************************************************/
/**
 * External prototypes
 **/
int16_t	phy_init( void );
void	phy_set_100full( void );
void	phy_set_10half( void );
int16_t	phy_set_autonegotiate( void );

#endif /* PHY_H */

