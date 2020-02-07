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
* Copyright (C) 2015 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/
/***********************************************************************************************************************
* File Name    : ether_callback.c
* Version      : ----
* Description  : This module solves all the world's problems
***********************************************************************************************************************/
/**********************************************************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 05.01.2015 ----     Clean up source code.
***********************************************************************************************************************/

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
#include "r_ether_rx_if.h"

/***********************************************************************************************************************
Private global variables and functions
***********************************************************************************************************************/
int32_t callback_ether_regist(void);
void callback_ether(void * pparam);
static void callback_wakeon_lan(uint32_t channel);
static void callback_link_on(uint32_t channel);
static void callback_link_off(uint32_t channel);

volatile uint8_t  pause_enable = ETHER_FLAG_OFF;
volatile uint8_t  magic_packet_detect[ETHER_CHANNEL_MAX];
volatile uint8_t  link_detect[ETHER_CHANNEL_MAX];

void EINT_Trig_isr(void *);

/*
 * When that Link Status changes, the following function will be called:
 */
void prvLinkStatusChange( BaseType_t xStatus );

/***********************************************************************************************************************
* Function Name: callback_ether
* Description  : Regist of callback function
* Arguments    : -
* Return Value : 0: success, -1:failed
***********************************************************************************************************************/
int32_t callback_ether_regist(void)
{
    ether_param_t   param;
    ether_cb_t      cb_func;

    int32_t         ret;

    /* Set the callback function (LAN cable connect/disconnect event) */
    cb_func.pcb_func     = &callback_ether;
    param.ether_callback = cb_func;
    ret = R_ETHER_Control(CONTROL_SET_CALLBACK, param);
    if (ETHER_SUCCESS != ret)
    {
        return -1;
    }

    /* Set the callback function (Ether interrupt event) */
    cb_func.pcb_int_hnd     = &EINT_Trig_isr;
    param.ether_callback = cb_func;
    ret = R_ETHER_Control(CONTROL_SET_INT_HANDLER, param);
    if (ETHER_SUCCESS != ret)
    {
        return -1;
    }
    return 0;
} /* End of function callback_ether_regist() */

/***********************************************************************************************************************
* Function Name: callback_ether
* Description  : Sample of the callback function
* Arguments    : pparam -
*
* Return Value : none
***********************************************************************************************************************/
void callback_ether(void * pparam)
{
    ether_cb_arg_t    * pdecode;
    uint32_t            channel;

    pdecode = (ether_cb_arg_t *)pparam;
    channel = pdecode->channel;                             /* Get Ethernet channel number */

    switch (pdecode->event_id)
    {
        /* Callback function that notifies user to have detected magic packet. */
        case ETHER_CB_EVENT_ID_WAKEON_LAN:
            callback_wakeon_lan(channel);
            break;

        /* Callback function that notifies user to have become Link up. */
        case ETHER_CB_EVENT_ID_LINK_ON:
            callback_link_on(channel);
            break;

        /* Callback function that notifies user to have become Link down. */
        case ETHER_CB_EVENT_ID_LINK_OFF:
            callback_link_off(channel);
            break;

        default:
            break;
    }
} /* End of function callback_ether() */

/***********************************************************************************************************************
* Function Name: callback_wakeon_lan
* Description  :
* Arguments    : channel -
*                    Ethernet channel number
* Return Value : none
***********************************************************************************************************************/
static void callback_wakeon_lan(uint32_t channel)
{
    if (ETHER_CHANNEL_MAX > channel)
    {
        magic_packet_detect[channel] = 1;

        /* Please add necessary processing when magic packet is detected.  */
    }
} /* End of function callback_wakeon_lan() */

/***********************************************************************************************************************
* Function Name: callback_link_on
* Description  :
* Arguments    : channel -
*                    Ethernet channel number
* Return Value : none
***********************************************************************************************************************/
static void callback_link_on(uint32_t channel)
{
    if (ETHER_CHANNEL_MAX > channel)
    {
        link_detect[channel] = ETHER_FLAG_ON_LINK_ON;

        /* Please add necessary processing when becoming Link up. */
		prvLinkStatusChange( 1 );
    }
} /* End of function callback_link_on() */

/***********************************************************************************************************************
* Function Name: callback_link_off
* Description  :
* Arguments    : channel -
*                    Ethernet channel number
* Return Value : none
***********************************************************************************************************************/
static void callback_link_off(uint32_t channel)
{
    if (ETHER_CHANNEL_MAX > channel)
    {
        link_detect[channel] = ETHER_FLAG_ON_LINK_OFF;

        /* Please add necessary processing when becoming Link down. */
		prvLinkStatusChange( 0 );
    }
} /* End of function ether_cb_link_off() */

/* End of File */
