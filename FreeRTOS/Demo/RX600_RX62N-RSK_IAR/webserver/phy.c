/******************************************************************************
* DISCLAIMER

* This software is supplied by Renesas Technology Corp. and is only
* intended for use with Renesas products. No other uses are authorized.

* This software is owned by Renesas Technology Corp. and is protected under
* all applicable laws, including copyright laws.

* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES
* REGARDING THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY,
* INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A
* PARTICULAR PURPOSE AND NON-INFRINGEMENT.  ALL SUCH WARRANTIES ARE EXPRESSLY
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
******************************************************************************
* Copyright (C) 2008. Renesas Technology Corp., All Rights Reserved.
*******************************************************************************	
* File Name    : phy.c
* Version      : 1.01
* Description  : Ethernet PHY device driver
******************************************************************************
* History : DD.MM.YYYY Version Description
*         : 15.02.2010 1.00    First Release
*         : 06.04.2010 1.01    RX62N changes
******************************************************************************/


/******************************************************************************
Includes   <System Includes> , "Project Includes"
******************************************************************************/
#include <iorx62n.h>
#include "r_ether.h"
#include "phy.h"

#include "FreeRTOS.h"
#include "task.h"
/******************************************************************************
Typedef definitions
******************************************************************************/

/******************************************************************************
Macro definitions
******************************************************************************/

/******************************************************************************
Imported global variables and functions (from other files)
******************************************************************************/

/******************************************************************************
Exported global variables and functions (to be accessed by other files)
******************************************************************************/

/******************************************************************************
Private global variables and functions
******************************************************************************/
uint16_t  _phy_read( uint16_t reg_addr );
void  _phy_write( uint16_t reg_addr, uint16_t data );
void  _phy_preamble( void );
void  _phy_reg_set( uint16_t reg_addr, int32_t option );
void  _phy_reg_read( uint16_t *data );
void  _phy_reg_write( uint16_t data );
void  _phy_ta_z0( void );
void  _phy_ta_10( void );
void  _phy_mii_write_1( void );
void  _phy_mii_write_0( void );

/**
 * External functions
 */

/******************************************************************************
* Function Name: phy_init
* Description  : Resets Ethernet PHY device
* Arguments    : none
* Return Value : none
******************************************************************************/
int16_t  phy_init( void )
{
  uint16_t reg;
  uint32_t count;

  /* Reset PHY */
  _phy_write(BASIC_MODE_CONTROL_REG, 0x8000);

  count = 0;

  do
  {
	  vTaskDelay( 2 / portTICK_PERIOD_MS );
      reg = _phy_read(BASIC_MODE_CONTROL_REG);
	  count++;
  } while (reg & 0x8000 && count < PHY_RESET_WAIT);

  if( count < PHY_RESET_WAIT )
  {	
   	return R_PHY_OK;
  }

  return R_PHY_ERROR;
}

/******************************************************************************
* Function Name: phy_set_100full
* Description  : Set Ethernet PHY device to 100 Mbps full duplex
* Arguments    : none
* Return Value : none
******************************************************************************/
void phy_set_100full( void )
{
	_phy_write(BASIC_MODE_CONTROL_REG, 0x2100);
}

/******************************************************************************
* Function Name: phy_set_10half
* Description  : Sets Ethernet PHY device to 10 Mbps half duplexR
* Arguments    : none
* Return Value : none
******************************************************************************/
void phy_set_10half( void )
{
	_phy_write(BASIC_MODE_CONTROL_REG, 0x0000);
}

/******************************************************************************
* Function Name: phy_set_autonegotiate
* Description  : Starts autonegotiate and reports the other side's
*              : physical capability
* Arguments    : none
* Return Value : bit 8 - Full duplex 100 mbps
*              : bit 7 - Half duplex 100 mbps
*              : bit 6 - Full duplex 10 mbps
*              : bit 5 - Half duplex 10 mbps
*              : bit 4:0 - Always set to 00001 (IEEE 802.3)
*              : -1 if error
******************************************************************************/
int16_t phy_set_autonegotiate( void )
{
  uint16_t reg;
  uint32_t count;

  _phy_write(AN_ADVERTISEMENT_REG, 0x01E1);
  _phy_write(BASIC_MODE_CONTROL_REG, 0x1200);

  count = 0;

  do
  {
      reg = _phy_read(BASIC_MODE_STATUS_REG);
      count++;
	  vTaskDelay( 100 / portTICK_PERIOD_MS );
	
	  /* Make sure we don't break out if reg just contains 0xffff. */
	  if( reg == 0xffff )
	  {
		reg = 0;
	  }
	
  } while (!(reg & 0x0020) && (count < PHY_AUTO_NEGOTIATON_WAIT));

  if (count >= PHY_AUTO_NEGOTIATON_WAIT)
  {
      return R_PHY_ERROR;
  }
  else
  {
      /* Get the link partner response */
	  reg = (int16_t)_phy_read(AN_LINK_PARTNER_ABILITY_REG);
	
	  if (reg & ( 1 << 8 ) )
	  {
		  return PHY_LINK_100F;
	  }
	  if (reg & ( 1 << 7 ) )
	  {
	  	  return PHY_LINK_100H;
	  }
	  if (reg & ( 1 << 6 ) )
	  {
		  return PHY_LINK_10F;
	  }
	  if (reg & 1 << 5 )
	  {
		  return PHY_LINK_10H;
	  }	

	  return (-1);
  }
}


/**
 * Internal functions
 */

/******************************************************************************
* Function Name: _phy_read
* Description  : Reads a PHY register
* Arguments    : reg_addr - address of the PHY register
* Return Value : read value
******************************************************************************/
uint16_t _phy_read( uint16_t reg_addr )
{
  uint16_t data;

  _phy_preamble();
  _phy_reg_set( reg_addr, PHY_READ );
  _phy_ta_z0();
  _phy_reg_read( &data );
  _phy_ta_z0();

  return( data );
}

/******************************************************************************
* Function Name: _phy_write
* Description  : Writes to a PHY register
* Arguments    : reg_addr - address of the PHY register
*              : data - value
* Return Value : none
******************************************************************************/
void  _phy_write( uint16_t reg_addr, uint16_t data )
{
  _phy_preamble();
  _phy_reg_set( reg_addr, PHY_WRITE );
  _phy_ta_10();
  _phy_reg_write( data );
  _phy_ta_z0();
}

/******************************************************************************
* Function Name: _phy_preamble
* Description  : As preliminary preparation for access to the PHY module register,
*                "1" is output via the MII management interface.
* Arguments    : none
* Return Value : none
******************************************************************************/
void  _phy_preamble( void )
{
  int16_t i;

  i = 32;
  while( i > 0 )
  {
    _phy_mii_write_1();
    i--;
  }
}

/******************************************************************************
* Function Name: _phy_reg_set
* Description  : Sets a PHY device to read or write mode
* Arguments    : reg_addr - address of the PHY register
*              : option - mode
* Return Value : none
******************************************************************************/
void  _phy_reg_set( uint16_t reg_addr, int32_t option )
{
  int32_t    i;
  uint16_t data;

  data = 0;
  data = (PHY_ST << 14);        /* ST code    */

  if( option == PHY_READ )
  {
    data |= (PHY_READ << 12);  /* OP code(RD)  */
  }
  else
  {
    data |= (PHY_WRITE << 12);  /* OP code(WT)  */
  }

  data |= (PHY_ADDR << 7);    /* PHY Address  */
  data |= (reg_addr << 2);    /* Reg Address  */

  i = 14;
  while( i > 0 )
  {
    if( (data & 0x8000) == 0 )
    {
      _phy_mii_write_0();
    }
    else
    {
      _phy_mii_write_1();
    }
    data <<= 1;
    i--;
  }
}

/******************************************************************************
* Function Name: _phy_reg_read
* Description  : Reads PHY register through MII interface
* Arguments    : data - pointer to store the data read
* Return Value : none
******************************************************************************/
void  _phy_reg_read( uint16_t *data )
{
  int32_t      i, j;
  uint16_t   reg_data;

  reg_data = 0;
  i = 16;
  while( i > 0 )
  {
    for(j = MDC_WAIT; j > 0; j--)
  	{
        ETHERC.PIR.LONG = 0x00000000;
    }
    for(j = MDC_WAIT; j > 0; j--)
  	{
        ETHERC.PIR.LONG = 0x00000001;
    }

	reg_data <<= 1;
    reg_data |= (uint16_t)((ETHERC.PIR.LONG & 0x00000008) >> 3);  /* MDI read  */

    for(j = MDC_WAIT; j > 0; j--)
  	{
        ETHERC.PIR.LONG = 0x00000001;
    }
    for(j = MDC_WAIT; j > 0; j--)
  	{
        ETHERC.PIR.LONG = 0x00000000;
    }
    i--;
  }
  *data = reg_data;
}

/******************************************************************************
* Function Name: _phy_reg_write
* Description  : Writes to PHY register through MII interface
* Arguments    : data - value to write
* Return Value : none
******************************************************************************/
void  _phy_reg_write( uint16_t data )
{
  int32_t  i;

  i = 16;
  while( i > 0 )
  {
    if( (data & 0x8000) == 0 )
    {
      _phy_mii_write_0();
    }
    else
    {
      _phy_mii_write_1();
    }
    i--;
    data <<= 1;
  }
}

/******************************************************************************
* Function Name: _phy_ta_z0
* Description  : Performs bus release so that PHY can drive data
*              : for read operation
* Arguments    : none
* Return Value : none
******************************************************************************/
void  _phy_ta_z0( void )
{
    int32_t j;

    for(j = MDC_WAIT; j > 0; j--)
	{
        ETHERC.PIR.LONG = 0x00000000;
    }
    for(j = MDC_WAIT; j > 0; j--)
	{
        ETHERC.PIR.LONG = 0x00000001;
    }
    for(j = MDC_WAIT; j > 0; j--)
	{
        ETHERC.PIR.LONG = 0x00000001;
    }
    for(j = MDC_WAIT; j > 0; j--)
	{
        ETHERC.PIR.LONG = 0x00000000;
    }
}

/******************************************************************************
* Function Name: _phy_ta_10
* Description  : Switches data bus so MII interface can drive data
*              : for write operation
* Arguments    : none
* Return Value : none
******************************************************************************/
void _phy_ta_10(void)
{
    _phy_mii_write_1();
    _phy_mii_write_0();
}

/******************************************************************************
* Function Name: _phy_mii_write_1
* Description  : Outputs 1 to the MII interface
* Arguments    : none
* Return Value : none
******************************************************************************/
void  _phy_mii_write_1( void )
{
    int32_t j;

    for(j = MDC_WAIT; j > 0; j--)
	{
        ETHERC.PIR.LONG = 0x00000006;
    }
    for(j = MDC_WAIT; j > 0; j--)
	{
        ETHERC.PIR.LONG = 0x00000007;
    }
    for(j = MDC_WAIT; j > 0; j--)
	{
        ETHERC.PIR.LONG = 0x00000007;
    }
    for(j = MDC_WAIT; j > 0; j--)
	{
        ETHERC.PIR.LONG = 0x00000006;
    }
}

/******************************************************************************
* Function Name: _phy_mii_write_0
* Description  : Outputs 0 to the MII interface
* Arguments    : none
* Return Value : none
******************************************************************************/
void  _phy_mii_write_0( void )
{
    int32_t j;

    for(j = MDC_WAIT; j > 0; j--)
	{
        ETHERC.PIR.LONG = 0x00000002;
    }
    for(j = MDC_WAIT; j > 0; j--)
	{
        ETHERC.PIR.LONG = 0x00000003;
    }
    for(j = MDC_WAIT; j > 0; j--)
	{
        ETHERC.PIR.LONG = 0x00000003;
    }
    for(j = MDC_WAIT; j > 0; j--)
	{
        ETHERC.PIR.LONG = 0x00000002;
    }
}


