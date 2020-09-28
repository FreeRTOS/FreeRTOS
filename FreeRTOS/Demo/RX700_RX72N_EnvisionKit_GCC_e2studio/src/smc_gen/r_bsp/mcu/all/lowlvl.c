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
* Copyright (C) 2013 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/
/***********************************************************************************************************************
* File Name    : lowlvl.c
* Description  : Functions to support stream I/O to the E1 virtual Console
***********************************************************************************************************************/
/***********************************************************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 28.02.2019 3.00     Merged processing of all devices.
*                               Fixed coding style.
***********************************************************************************************************************/

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
#include "platform.h"

/* When using the user startup program, disable the following code. */
#if BSP_CFG_STARTUP_DISABLE == 0

/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/
#define BSP_PRV_E1_DBG_PORT (*(volatile st_dbg_t     R_BSP_EVENACCESS_SFR *)0x84080)
#define BSP_PRV_TXFL0EN     (0x00000100)          /* debug tx flow control bit */
#define BSP_PRV_RXFL0EN     (0x00001000)          /* debug RX flow control bit */

/***********************************************************************************************************************
Typedef definitions
***********************************************************************************************************************/
typedef struct
{
    uint32_t   tx_data;     /* Debug Virtual Console TX data */
    char       wk1[12];     /* spacer */
    uint32_t   rx_data;     /* Debug Virtual Console RX data */
    char       wk2[44];     /* spacer */
    uint32_t   dbgstat;     /* Debug Virtual Console Status */
} st_dbg_t;

/***********************************************************************************************************************
Exported global variables (to be accessed by other files)
***********************************************************************************************************************/
#if BSP_CFG_USER_CHARPUT_ENABLED != 0
/* If user has indicated they want to provide their own charput function then this is the prototype. */
void BSP_CFG_USER_CHARPUT_FUNCTION(char output_char);
#endif

#if BSP_CFG_USER_CHARGET_ENABLED != 0
/* If user has indicated they want to provide their own charget function then this is the prototype. */
char BSP_CFG_USER_CHARGET_FUNCTION(void);
#endif

/***********************************************************************************************************************
Private global variables and functions
***********************************************************************************************************************/

/***********************************************************************************************************************
* Function Name: charput
* Description  : Outputs a character on a serial port
* Arguments    : character to output
* Return Value : none
***********************************************************************************************************************/
void charput (char output_char)
{
    /* If user has provided their own charput() function, then call it. */
#if BSP_CFG_USER_CHARPUT_ENABLED == 1
    BSP_CFG_USER_CHARPUT_FUNCTION(output_char);
#else
    /* Wait for transmit buffer to be empty */
    /* WAIT_LOOP */
    while(0 != (BSP_PRV_E1_DBG_PORT.dbgstat & BSP_PRV_TXFL0EN))
    {
        /* do nothing */
        R_BSP_NOP();
    }

    /* Write the character out */
    /* Casting is valid because it matches the type to the right side or argument. */
    BSP_PRV_E1_DBG_PORT.tx_data = (int32_t)output_char;
#endif
} /* End of function charput() */

/***********************************************************************************************************************
* Function Name: charget
* Description  : Gets a character on a serial port
* Arguments    : none
* Return Value : received character
***********************************************************************************************************************/
char charget (void)
{
    /* If user has provided their own charget() function, then call it. */
#if BSP_CFG_USER_CHARGET_ENABLED == 1
    return BSP_CFG_USER_CHARGET_FUNCTION();
#else
    /* Wait for rx buffer buffer to be ready */
    /* WAIT_LOOP */
    while(0 == (BSP_PRV_E1_DBG_PORT.dbgstat & BSP_PRV_RXFL0EN))
    {
        /* do nothing */
        R_BSP_NOP();
    }

    /* Read data, send back up */
    /* Casting is valid because it matches the type to the retern value. */
    return (char)BSP_PRV_E1_DBG_PORT.rx_data;
#endif
} /* End of function charget() */

#endif /* BSP_CFG_STARTUP_DISABLE == 0 */

