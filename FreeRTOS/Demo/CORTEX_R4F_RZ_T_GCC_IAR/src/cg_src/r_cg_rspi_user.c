/***********************************************************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only intended for use with Renesas products.
* No other uses are authorized. This software is owned by Renesas Electronics Corporation and is protected under all
* applicable laws, including copyright laws.
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIESREGARDING THIS SOFTWARE, WHETHER EXPRESS, IMPLIED
* OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
* NON-INFRINGEMENT.  ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED.TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY
* LAW, NEITHER RENESAS ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE FOR ANY DIRECT,
* INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR ANY REASON RELATED TO THIS SOFTWARE, EVEN IF RENESAS OR
* ITS AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software and to discontinue the availability
* of this software. By using this software, you agree to the additional terms and conditions found by accessing the
* following link:
* http://www.renesas.com/disclaimer
*
* Copyright (C) 2015 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/

/***********************************************************************************************************************
* File Name    : r_cg_rspi_user.c
* Version      : Code Generator for RZ/T1 V1.00.00.09 [02 Mar 2015]
* Device(s)    : R7S910018CBG
* Tool-Chain   : GCCARM
* Description  : This file implements device driver for RSPI module.
* Creation Date: 22/04/2015
***********************************************************************************************************************/

/***********************************************************************************************************************
Pragma directive
***********************************************************************************************************************/
/* Start user code for pragma. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */

/***********************************************************************************************************************
Includes
***********************************************************************************************************************/
#include "r_cg_macrodriver.h"
#include "r_cg_rspi.h"
/* Start user code for include. Do not edit comment generated here */
#include "r_typedefs.h"
/* End user code. Do not edit comment generated here */
#include "r_cg_userdefine.h"

/***********************************************************************************************************************
Global variables and functions
***********************************************************************************************************************/
extern const uint32_t * gp_rspi1_tx_address;         /* RSPI1 transmit buffer address */
extern uint16_t         g_rspi1_tx_count;            /* RSPI1 transmit data number */
/* Start user code for global. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */

/***********************************************************************************************************************
* Function Name: r_rspi1_transmit_interrupt
* Description  : This function is SPTI1 interrupt service routine.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
#ifdef __ICCARM__
	__irq __arm
#endif /* __ICCARM__ */
void r_rspi1_transmit_interrupt(void)
{
    uint16_t frame_cnt;

    /* Clear the interrupt source */
    VIC.PIC2.LONG = 0x00200000UL;

    for (frame_cnt = 0U; frame_cnt < (_RSPI_FRAMES_1 + 1U); frame_cnt++)
    {
        if (g_rspi1_tx_count > 0U)
        {
            /* Write data for transmission */
            RSPI1.SPDR.LONG = (*(uint32_t*)gp_rspi1_tx_address);
            gp_rspi1_tx_address++;
            g_rspi1_tx_count--;
        }
        else
        {
            /* Disable transmit interrupt */
            RSPI1.SPCR.BIT.SPTIE = 0U;

            /* Enable idle interrupt */
            RSPI1.SPCR2.BIT.SPIIE = 1U;
            break;
        }
    }

    /* Dummy write */
    VIC.HVA0.LONG = 0x00000000UL;
}
/***********************************************************************************************************************
* Function Name: r_rspi1_error_interrupt
* Description  : This function is SPEI1 interrupt service routine.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
#ifdef __ICCARM__
	__irq __arm
#endif /* __ICCARM__ */
void r_rspi1_error_interrupt(void)
{
    uint8_t err_type;

    /* Disable RSPI function */
    RSPI1.SPCR.BIT.SPE = 0U;

    /* Disable transmit interrupt */
    RSPI1.SPCR.BIT.SPTIE = 0U;

    /* Disable error interrupt */
    RSPI1.SPCR.BIT.SPEIE = 0U;

    /* Disable idle interrupt */
    RSPI1.SPCR2.BIT.SPIIE = 0U;

    /* Clear error sources */
    err_type = RSPI1.SPSR.BYTE;
    RSPI1.SPSR.BYTE = 0xA0U;

    if (err_type != 0U)
    {
        r_rspi1_callback_error(err_type);
    }
    /* Wait the interrupt signal is disabled */
    while (0U != (VIC.IRQS2.LONG & 0x00400000UL))
    {
        VIC.IEC2.LONG = 0x00400000UL;
    }

    VIC.IEN2.LONG |= 0x00400000UL;

    /* Dummy write */
    VIC.HVA0.LONG = 0x00000000UL;
}
/***********************************************************************************************************************
* Function Name: r_rspi1_idle_interrupt
* Description  : This function is SPII1 interrupt service routine.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
#ifdef __ICCARM__
	__irq __arm
#endif /* __ICCARM__ */
void r_rspi1_idle_interrupt(void)
{
    /* Disable RSPI function */
    RSPI1.SPCR.BIT.SPE = 0U;

    /* Disable idle interrupt */
    RSPI1.SPCR2.BIT.SPIIE = 0U;

    r_rspi1_callback_transmitend();

    /* Wait the interrupt signal is disabled */
    while (0U != (VIC.IRQS2.LONG & 0x00800000UL))
    {
        VIC.IEC2.LONG = 0x00800000UL;
    }

    VIC.IEN2.LONG |= 0x00800000UL;

    /* Dummy write */
    VIC.HVA0.LONG = 0x00000000UL;
}
/***********************************************************************************************************************
* Function Name: r_rspi1_callback_transmitend
* Description  : This function is a callback function when RSPI1 finishes transmission.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void r_rspi1_callback_transmitend(void)
{
    /* Start user code. Do not edit comment generated here */
    /* End user code. Do not edit comment generated here */
}


/***********************************************************************************************************************
* Function Name: r_rspi1_callback_error
* Description  : This function is a callback function when RSPI1 error occurs.
* Arguments    : err_type -
*                    error type value
* Return Value : None
***********************************************************************************************************************/
void r_rspi1_callback_error(uint8_t err_type)
{
    /* Start user code. Do not edit comment generated here */

    /* Used to suppress the warning message generated for unused variables */
    UNUSED_VARIABLE(err_type);

    /* End user code. Do not edit comment generated here */
}

/* Start user code for adding. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */
