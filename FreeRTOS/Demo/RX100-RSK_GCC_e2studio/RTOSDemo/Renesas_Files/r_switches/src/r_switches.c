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
* Copyright (C) 2011 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/
/***********************************************************************************************************************
* File Name    : r_switches.c
* Description  : Functions for using switches with callback functions.
************************************************************************************************************************
* History : DD.MM.YYYY Version Description
*         : 17.01.2012 1.00    First Release
*         : 17.02.2012 1.10    Added RSKRX210 support.
*         : 08.03.2012 1.20    Added GetVersion() function (though it's really a macro).
*         : 04.06.2012 1.30    Code can now be interrupt or poll driven.
*         : 07.11.2012 1.40	   Added support for RSKRX111
***********************************************************************************************************************/

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
/* Board and MCU support. */
#include "platform.h"
/* Switches prototypes. */
#include "r_switches_if.h"
/* Scheduler includes. */
#include "FreeRTOS.h"
typedef int bool;

/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/
/* This helps reduce the amount of unique code for each supported board. */
#define X_IRQ( x )   XX_IRQ( x )
#define XX_IRQ( x )  _ICU_IRQ##x

/* These macros define which IRQ pins are used for the switches. Note that these defintions cannot have parentheses
   around them. */
#if defined(PLATFORM_BOARD_RSKRX111)
    #define SW1_IRQ_NUMBER     0
    #define SW2_IRQ_NUMBER     1
    #define SW3_IRQ_NUMBER     4
#else
	#error This file is only for use on the RX100 RSK
#endif

/* Number of switches on this board. */
#define SWITCHES_NUM            (3)

/* Register definitions not yet correct in iodefine.h. */
#define MPC_P30PFS_REG	( * ( unsigned char * ) 0x0008C158 )
#define MPC_P31PFS_REG ( * ( unsigned char * ) 0x0008C159 )
#define MPC_PE4PFS_REG ( * ( unsigned char * ) 0x0008C1B4 )

/***********************************************************************************************************************
Typedef definitions
***********************************************************************************************************************/
typedef struct
{
    bool    active;
    int32_t debounce_cnt;
} switch_t;

/***********************************************************************************************************************
Private global variables and functions
***********************************************************************************************************************/
#if SWITCHES_DETECTION_MODE == 1
/* Update Hz */
static uint32_t g_sw_debounce_cnts;
/* Used for debounce. */
switch_t g_switches[SWITCHES_NUM];
#endif

/***********************************************************************************************************************
* Function Name: R_SWITCHES_Init
* Description  : Initializes pins to be input and interrupt on switch presses.
* Arguments    :
* Return Value : none
***********************************************************************************************************************/

void R_SWITCHES_Init (void)
{
    /* Unlock protection register */
    MPC.PWPR.BYTE &= 0x7F;
    /* Unlock MPC registers */
    MPC.PWPR.BYTE |= 0x40;

    /* Make switch pins inputs. */
    PORT3.PDR.BYTE &= 0xFC;
    PORTE.PDR.BYTE &= 0xEF;

    /* Set port mode registers for switches. */
    PORT3.PMR.BYTE &= 0xFC;
    PORTE.PMR.BYTE &= 0xEF;

    MPC_P30PFS_REG = 0x40;    /* P30 is used as IRQ pin */
    MPC_P31PFS_REG  = 0x40;    /* P31 is used as IRQ pin */
    MPC_PE4PFS_REG  = 0x40;    /* PE4 is used as IRQ pin */

    /* Set IRQ type (falling edge) */
    ICU.IRQCR[ SW1_IRQ_NUMBER ].BYTE  = 0x04;
    ICU.IRQCR[ SW2_IRQ_NUMBER ].BYTE  = 0x04;
    ICU.IRQCR[ SW3_IRQ_NUMBER ].BYTE  = 0x04;

    /* Set interrupt priorities, which must be below
    configMAX_SYSCALL_INTERRUPT_PRIORITY. */
    _IPR( X_IRQ(SW1_IRQ_NUMBER) ) = configKERNEL_INTERRUPT_PRIORITY;
    _IPR( X_IRQ(SW2_IRQ_NUMBER) ) = configKERNEL_INTERRUPT_PRIORITY;
    _IPR( X_IRQ(SW3_IRQ_NUMBER) ) = configKERNEL_INTERRUPT_PRIORITY;

    /* Clear any pending interrupts */
    _IR( X_IRQ(SW1_IRQ_NUMBER) ) = 0;
    _IR( X_IRQ(SW2_IRQ_NUMBER) ) = 0;
    _IR( X_IRQ(SW3_IRQ_NUMBER) ) = 0;

    /* Enable the interrupts */
    _IEN( X_IRQ(SW1_IRQ_NUMBER) )  = 1;
    _IEN( X_IRQ(SW2_IRQ_NUMBER) )  = 1;
    _IEN( X_IRQ(SW3_IRQ_NUMBER) )  = 1;
}

/* If using polling then the user must call the update function. */

/***********************************************************************************************************************
* Function name: R_SWITCHES_Update
* Description  : Polls switches and calls callback functions as needed. If you are using IRQ mode then this function
*                is not needed and can be removed if desired. It is left in so that code will not fail when switching
*                between polling or IRQ mode.
* Arguments    : none
* Return value : none
***********************************************************************************************************************/
void R_SWITCHES_Update (void)
{
#if SWITCHES_DETECTION_MODE == 1
    /* This code is only needed for polling mode. */
    /* Check switch 1. */
    if (SW1 == SW_ACTIVE)
    {
        if (g_switches[0].active != true)
        {
            if (++g_switches[0].debounce_cnt >= g_sw_debounce_cnts)
            {
                /* Set this to true so we only call the callback function once per press. */
                g_switches[0].active = true;

                /* Call callback function. */
                SW1_CALLBACK_FUNCTION();
            }
        }
    }
    else
    {
        if (0 == g_switches[0].debounce_cnt)
        {
            g_switches[0].active = false;
        }
        else
        {
            g_switches[0].debounce_cnt--;
        }
    }

    /* Check switch 2. */
    if (SW2 == SW_ACTIVE)
    {
        if (g_switches[1].active != true)
        {
            if (++g_switches[1].debounce_cnt >= g_sw_debounce_cnts)
            {
                /* Set this to true so we only call the callback function once per press. */
                g_switches[1].active = true;

                /* Call callback function. */
                SW2_CALLBACK_FUNCTION();
            }
        }
    }
    else
    {
        if (0 == g_switches[1].debounce_cnt)
        {
            g_switches[1].active = false;
        }
        else
        {
            g_switches[1].debounce_cnt--;
        }
    }

    /* Check switch 3. */
    if (SW3 == SW_ACTIVE)
    {
        if (g_switches[2].active != true)
        {
            if (++g_switches[2].debounce_cnt >= g_sw_debounce_cnts)
            {
                /* Set this to true so we only call the callback function once per press. */
                g_switches[2].active = true;

                /* Call callback function. */
                SW3_CALLBACK_FUNCTION();
            }
        }
    }
    else
    {
        if (0 == g_switches[2].debounce_cnt)
        {
            g_switches[2].active = false;
        }
        else
        {
            g_switches[2].debounce_cnt--;
        }
    }
#endif /* SWITCHES_DETECTION_MODE */
}



