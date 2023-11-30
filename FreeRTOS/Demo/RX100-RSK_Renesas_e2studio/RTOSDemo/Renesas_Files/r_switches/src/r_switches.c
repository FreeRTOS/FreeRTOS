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
/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/
/* This helps reduce the amount of unique code for each supported board. */
#define X_IRQ( x )   XX_IRQ( x )
#define XX_IRQ( x )  _ICU_IRQ##x

/* These macros define which IRQ pins are used for the switches. Note that these defintions cannot have parentheses
   around them. */
#if   defined(PLATFORM_BOARD_RDKRX63N)
    #define SW1_IRQ_NUMBER     8
    #define SW2_IRQ_NUMBER     9
    #define SW3_IRQ_NUMBER     12
#elif defined(PLATFORM_BOARD_RSKRX63N)
    #define SW1_IRQ_NUMBER     2
    #define SW2_IRQ_NUMBER     8
    #define SW3_IRQ_NUMBER     15
#elif defined(PLATFORM_BOARD_RSKRX630)
    #define SW1_IRQ_NUMBER     2
    #define SW2_IRQ_NUMBER     12
    #define SW3_IRQ_NUMBER     15
#elif defined(PLATFORM_BOARD_RSKRX62N)
    #define SW1_IRQ_NUMBER     8
    #define SW2_IRQ_NUMBER     9
    #define SW3_IRQ_NUMBER     15
#elif defined(PLATFORM_BOARD_RDKRX62N)
    #define SW1_IRQ_NUMBER     8
    #define SW2_IRQ_NUMBER     9
    #define SW3_IRQ_NUMBER     10
#elif defined(PLATFORM_BOARD_RSKRX62T)
    #define SW1_IRQ_NUMBER     0
    #define SW2_IRQ_NUMBER     1
    #define SW3_IRQ_NUMBER     3
#elif defined(PLATFORM_BOARD_RSKRX610)
    #define SW1_IRQ_NUMBER     8
    #define SW2_IRQ_NUMBER     9
    #define SW3_IRQ_NUMBER     3
#elif defined(PLATFORM_BOARD_RSKRX210)
    #define SW1_IRQ_NUMBER     1
    #define SW2_IRQ_NUMBER     3
    #define SW3_IRQ_NUMBER     4
#elif defined(PLATFORM_BOARD_RSKRX111)
    #define SW1_IRQ_NUMBER     0
    #define SW2_IRQ_NUMBER     1
    #define SW3_IRQ_NUMBER     4
#endif

/* Number of switches on this board. */
#define SWITCHES_NUM            (3)

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
* Arguments    : detection_hz -
*                    The times per second that the user will call R_SWITCHES_Update(). NOTE: this is only when using
*                    polling mode. If you are using interrupt mode, then this argument will be ignored.
*                debouce_counts -
*                    The number of times to check the port value before accepting the change. The slower the rate at
*                    which R_SWITCHES_Update() will likely lower this number.
* Return Value : none
***********************************************************************************************************************/
void R_SWITCHES_Init (uint32_t detection_hz, uint32_t debounce_counts)
{
    uint32_t i;

    /* The SW#_XXX defintions are common macros amongst different boards. To see the definitions for these macros
       see the board defintion file. For example, this file for the RSKRX63N is rskrx63n.h. */

#if defined(MCU_RX62N) || defined(MCU_RX62T) || defined(MCU_RX621) || defined(MCU_RX610)

    /* Make switch pins inputs. */
    SW1_DDR = 0;
    SW2_DDR = 0;
    SW3_DDR = 0;

    /* Enable input buffer control registers. */
    SW1_ICR = 1;
    SW2_ICR = 1;
    SW3_ICR = 1;

#elif defined(MCU_RX63N) || defined(MCU_RX630) || defined(MCU_RX631) || defined(MCU_RX210) || defined(MCU_RX111)

    /* Unlock protection register */
    MPC.PWPR.BIT.B0WI = 0 ;
    /* Unlock MPC registers */
    MPC.PWPR.BIT.PFSWE = 1 ;

    /* Make switch pins inputs. */
    SW1_PDR = 0;
    SW2_PDR = 0;
    SW3_PDR = 0;

    /* Set port mode registers for switches. */
    SW1_PMR = 0;
    SW2_PMR = 0;
    SW3_PMR = 0;

#endif

#if SWITCHES_DETECTION_MODE == 0

    #if defined(PLATFORM_BOARD_RDKRX63N)

    /* The switches on the RDKRX63N are connected to the following pins/IRQ's
    Switch  Port    IRQ
    ------  ----    ----
    SW1     P4.0    IRQ8
    SW2     P4.1    IRQ9
    SW3     P4.4    IRQ12
    */

    MPC.P40PFS.BYTE = 0x40;    /* P40 is used as IRQ pin */
    MPC.P41PFS.BYTE = 0x40;    /* P40 is used as IRQ pin */
    MPC.P44PFS.BYTE = 0x40;    /* P40 is used as IRQ pin */

    #elif defined(PLATFORM_BOARD_RSKRX63N)

    /* The switches on the RSKRX63N are connected to the following pins/IRQ's
    Switch  Port    IRQ
    ------  ----    ----
    SW1     P3.2    IRQ2
    SW2     P0.0    IRQ8
    SW3     P0.7    IRQ15
    */

    MPC.P32PFS.BYTE  = 0x40;    /* P32 is used as IRQ pin */
    MPC.P00PFS.BYTE  = 0x40;    /* P00 is used as IRQ pin */
    MPC.P07PFS.BYTE  = 0x40;    /* P07 is used as IRQ pin */

    #elif defined(PLATFORM_BOARD_RSKRX630)

    /* The switches on the RSKRX630 are connected to the following pins/IRQ's
    Switch  Port    IRQ
    ------  ----    ----
    SW1     P3.2    IRQ2
    SW2     P4.4    IRQ12
    SW3     P0.7    IRQ15
    */

    MPC.P32PFS.BYTE  = 0x40;    /* P32 is used as IRQ pin */
    MPC.P44PFS.BYTE  = 0x40;    /* P44 is used as IRQ pin */
    MPC.P07PFS.BYTE  = 0x40;    /* P07 is used as IRQ pin */

    #elif defined(PLATFORM_BOARD_RSKRX62N)

    /* The switches on the RSKRX62N are connected to the following pins/IRQ's
    Switch  Port    IRQ
    ------  ----    ----
    SW1     P0.0    IRQ8-A
    SW2     P0.1    IRQ9-A
    SW3     P0.7    IRQ15-A
    */

    IOPORT.PF8IRQ.BIT.ITS8  = 0;    /* IRQ8-A pin is used. */
    IOPORT.PF8IRQ.BIT.ITS9  = 0;    /* IRQ9-A pin is used. */
    IOPORT.PF8IRQ.BIT.ITS15 = 0;    /* IRQ15-A pin is used. */

    #elif defined(PLATFORM_BOARD_RDKRX62N)

    /* The switches on the RDKRX62N are connected to the following pins/IRQ's
    Switch  Port    IRQ
    ------  ----    ----
    SW1     P4.0    IRQ8
    SW2     P4.1    IRQ9
    SW3     P4.2    IRQ10
    */

    /* Nothing else needed to do here since RDK has 100-pin package and there are no alternate pins to choose. */

    #elif defined(PLATFORM_BOARD_RSKRX62T)

    /* The switches on the RSKRX62T are connected to the following pins/IRQ's
    Switch  Port    IRQ
    ------  ----    ----
    SW1     PE.5    IRQ0-B
    SW2     PE.4    IRQ1-B
    SW3     PB.4    IRQ3
    */

    IOPORT.PF8IRQ.BIT.ITS0  = 1;    /* IRQ0-B pin is used. */
    IOPORT.PF8IRQ.BIT.ITS1  = 1;    /* IRQ1-B pin is used. */
    /* IRQ3 is only on 1 pin. */

    #elif defined(PLATFORM_BOARD_RSKRX610)

    /* The switches on the RSKRX610 are connected to the following pins/IRQ's
    Switch  Port    IRQ
    ------  ----    ----
    SW1     P0.0    IRQ8-A
    SW2     P0.1    IRQ9-A
    SW3     P1.3    IRQ3-B
    */

    IOPORT.PFCR8.BIT.ITS8  = 0;    /* IRQ8-A pin is used. */
    IOPORT.PFCR8.BIT.ITS9  = 0;    /* IRQ9-A pin is used. */
    IOPORT.PFCR9.BIT.ITS3  = 1;    /* IRQ3-B pin is used. */

    /* Enable IRQ detection. */
    ICU.IRQER[SW1_IRQ_NUMBER].BIT.IRQEN = 1;
    ICU.IRQER[SW2_IRQ_NUMBER].BIT.IRQEN = 1;
    ICU.IRQER[SW3_IRQ_NUMBER].BIT.IRQEN = 1;

    #elif defined(PLATFORM_BOARD_RSKRX210)

    /* The switches on the RSKRX210 are connected to the following pins/IRQ's
    Switch  Port    IRQ
    ------  ----    ----
    SW1     P3.1    IRQ1
    SW2     P3.3    IRQ3
    SW3     P3.4    IRQ4
    */

    MPC.P31PFS.BYTE  = 0x40;    /* P31 is used as IRQ pin */
    MPC.P33PFS.BYTE  = 0x40;    /* P33 is used as IRQ pin */
    MPC.P34PFS.BYTE  = 0x40;    /* P34 is used as IRQ pin */

#elif defined(PLATFORM_BOARD_RSKRX111)

    /* The switches on the RSKRX210 are connected to the following pins/IRQ's
	Switch  Port    IRQ
	------  ----    ----
	SW1     P3.0    IRQ0
	SW2     P3.1    IRQ1
	SW3     PE.4    IRQ4
    */

    MPC.P30PFS.BYTE  = 0x40;    /* P30 is used as IRQ pin */
    MPC.P31PFS.BYTE  = 0x40;    /* P31 is used as IRQ pin */
    MPC.PE4PFS.BYTE  = 0x40;    /* PE4 is used as IRQ pin */

    #endif


    /* Set IRQ type (falling edge) */
    ICU.IRQCR[SW1_IRQ_NUMBER].BIT.IRQMD  = 0x01;
    ICU.IRQCR[SW2_IRQ_NUMBER].BIT.IRQMD  = 0x01;
    ICU.IRQCR[SW3_IRQ_NUMBER].BIT.IRQMD  = 0x01;

    /* Set interrupt priorities which muse be below
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

#else

    /* This is based upon having 3 counts at 10Hz. */
    g_sw_debounce_cnts = debounce_counts;

    /* Init debounce structures. */
    for (i = 0; i < SWITCHES_NUM; i++)
    {
        g_switches[i].active = false;
        g_switches[i].debounce_cnt = 0;
    }

#endif /* SWITCHES_DETECTION_MODE */

}

/* Only define interrupts in interrupt detection mode. */
#if SWITCHES_DETECTION_MODE == 0

    #if defined(SW1_CALLBACK_FUNCTION)
/***********************************************************************************************************************
* Function name: sw1_isr
* Description  : Sample ISR for switch 1 input (must do hardware setup first!)
* Arguments    : none
* Return value : none
***********************************************************************************************************************/
#pragma interrupt (sw1_isr (vect=_VECT(X_IRQ(SW1_IRQ_NUMBER))))
static void sw1_isr (void)
{
    /* TODO: Add some debouncing! */

    /* Call callback function. */
    SW1_CALLBACK_FUNCTION();
}
    #endif /* SW1_CALLBACK_FUNCTION */

    #if defined(SW2_CALLBACK_FUNCTION)
/***********************************************************************************************************************
* Function name: sw2_isr
* Description  : Sample ISR for switch 2 input (must do hardware setup first!)
* Arguments    : none
* Return value : none
***********************************************************************************************************************/
#pragma interrupt (sw2_isr (vect=_VECT(X_IRQ(SW2_IRQ_NUMBER))))
static void sw2_isr (void)
{
    /* TODO: Add some debouncing! */

    /* Call callback function. */
    SW2_CALLBACK_FUNCTION();
}
    #endif /* SW2_CALLBACK_FUNCTION */

    #if defined(SW3_CALLBACK_FUNCTION)
/***********************************************************************************************************************
* Function name: sw3_isr
* Description  : Sample ISR for switch 3 input (must do hardware setup first!)
* Arguments    : none
* Return value : none
***********************************************************************************************************************/
#pragma interrupt (sw3_isr (vect=_VECT(X_IRQ(SW3_IRQ_NUMBER))))
static void sw3_isr (void)
{
    /* TODO: Add some debouncing! */

    /* Call callback function. */
    SW3_CALLBACK_FUNCTION();
}
    #endif /* SW3_CALLBACK_FUNCTION */

#endif

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



