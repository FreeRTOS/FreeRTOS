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
* File Name    : r_cg_rspi.c
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
/* End user code. Do not edit comment generated here */
#include "r_cg_userdefine.h"

/***********************************************************************************************************************
Global variables and functions
***********************************************************************************************************************/
const uint32_t * gp_rspi1_tx_address;         /* RSPI1 transmit buffer address */
uint16_t         g_rspi1_tx_count;            /* RSPI1 transmit data number */
/* Start user code for global. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */



/***********************************************************************************************************************
* Function Name: R_RSPI1_Create
* Description  : This function initializes the RSPI1 module.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void R_RSPI1_Create(void)
{
    /* Disable RSPI interrupts */
    VIC.IEC2.LONG = 0x00200000UL; /* Disable SPTI1 interrupt */
    VIC.IEC2.LONG = 0x00400000UL; /* Disable SPEI1 interrupt */
    VIC.IEC2.LONG = 0x00800000UL; /* Disable SPII1 interrupt */

    /* Set interrupt detection type */
    VIC.PLS2.LONG |= 0x00200000UL; /* Set SPTI1 edge detection interrupt */

    /* Cancel RSPI module stop state */
    MSTP(RSPI1) = 0U;

    /* Disable RSPI function */
    RSPI1.SPCR.BIT.SPE = 0U;

    /* Set control registers */
    RSPI1.SPPCR.BYTE = _RSPI_MOSI_LEVEL_HIGH | _RSPI_MOSI_FIXING_MOIFV_BIT | _RSPI_OUTPUT_PIN_CMOS | _RSPI_LOOPBACK_DISABLED | _RSPI_LOOPBACK2_DISABLED;
    RSPI1.SPBR = _RSPI1_DIVISOR;
    RSPI1.SPDCR.BYTE = _RSPI_ACCESS_LONGWORD | _RSPI_FRAMES_1;
    RSPI1.SPSCR.BYTE = _RSPI_SEQUENCE_LENGTH_1;
    RSPI1.SSLP.BYTE = _RSPI_SSL0_POLARITY_LOW | _RSPI_SSL1_POLARITY_LOW;
    RSPI1.SPCKD.BYTE = _RSPI_RSPCK_DELAY_1;
    RSPI1.SSLND.BYTE = _RSPI_SSL_NEGATION_DELAY_1;
    RSPI1.SPND.BYTE = _RSPI_NEXT_ACCESS_DELAY_1;
    RSPI1.SPCR2.BYTE = _RSPI_PARITY_DISABLE;
    RSPI1.SPCMD0.WORD = _RSPI_RSPCK_SAMPLING_EVEN | _RSPI_RSPCK_POLARITY_HIGH | _RSPI_BASE_BITRATE_1 | 
                        _RSPI_SIGNAL_ASSERT_SSL0 | _RSPI_SSL_KEEP_DISABLE | _RSPI_DATA_LENGTH_BITS_8 | 
                        _RSPI_MSB_FIRST | _RSPI_NEXT_ACCESS_DELAY_DISABLE | _RSPI_NEGATION_DELAY_DISABLE | 
                        _RSPI_RSPCK_DELAY_DISABLE;

    /* Set SPTI1 priority level */
    VIC.PRL85.LONG = _RSPI_PRIORITY_LEVEL6;
    
    /* Set SPEI1 priority level */
    VIC.PRL86.LONG = _RSPI_PRIORITY_LEVEL5;
    
    /* Set SPII1 priority level */
    VIC.PRL87.LONG = _RSPI_PRIORITY_LEVEL7;
    
    /* Set SPTI1 interrupt address */
    VIC.VAD85.LONG = (uint32_t)r_rspi1_transmit_interrupt;
    
    /* Set SPEI1 interrupt address */
    VIC.VAD86.LONG = (uint32_t)r_rspi1_error_interrupt;
    
    /* Set SPII1 interrupt address */
    VIC.VAD87.LONG = (uint32_t)r_rspi1_idle_interrupt;
    
    RSPI1.SPCR.BYTE = _RSPI_MODE_SPI | _RSPI_TRANSMIT_ONLY | _RSPI_MASTER_MODE;
}

/***********************************************************************************************************************
* Function Name: R_RSPI1_Start
* Description  : This function starts the RSPI1 module operation.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void R_RSPI1_Start(void)
{
    volatile uint8_t dummy;

    /* Enable RSPI interrupts */
    VIC.IEN2.LONG |= 0x00200000UL; /* Enable SPTI1 interrupt */
    VIC.IEN2.LONG |= 0x00400000UL; /* Enable SPEI1 interrupt */
    VIC.IEN2.LONG |= 0x00800000UL; /* Enable SPII1 interrupt */

    /* Clear error sources */
    dummy = RSPI1.SPSR.BYTE;
    ( void ) dummy;
    RSPI1.SPSR.BYTE = 0x00U;

    /* Disable idle interrupt */
    RSPI1.SPCR2.BIT.SPIIE = 0U;
}

/***********************************************************************************************************************
* Function Name: R_RSPI1_Stop
* Description  : This function stops the RSPI1 module operation.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void R_RSPI1_Stop(void)
{
    /* Disable RSPI interrupts */
    VIC.IEC2.LONG = 0x00200000UL; /* Disable SPTI1 interrupt */
    VIC.IEC2.LONG = 0x00400000UL; /* Disable SPEI1 interrupt */
    VIC.IEC2.LONG = 0x00800000UL; /* Disable SPII1 interrupt */

    /* Disable RSPI function */
    RSPI1.SPCR.BIT.SPE = 0U;
}
/***********************************************************************************************************************
* Function Name: R_RSPI1_Send
* Description  : This function sends RSPI1 data.
* Arguments    : tx_buf -
*                    transfer buffer pointer (not used when data is handled by DMAC)
*                tx_num -
*                    buffer size
* Return Value : status -
*                    MD_OK or MD_ARGERROR
***********************************************************************************************************************/
MD_STATUS R_RSPI1_Send(const uint32_t * tx_buf, uint16_t tx_num)
{
    MD_STATUS status = MD_OK;

    if (tx_num < 1U)
    {
        status = MD_ARGERROR;
    }
    else
    {
        gp_rspi1_tx_address = tx_buf;
        g_rspi1_tx_count = tx_num;

        /* Enable transmit interrupt */
        RSPI1.SPCR.BIT.SPTIE = 1U;

        /* Enable error interrupt */
        RSPI1.SPCR.BIT.SPEIE = 1U;

        /* Enable idle interrupt */
        RSPI1.SPCR2.BIT.SPIIE = 1U;

        /* Enable RSPI function */
        RSPI1.SPCR.BIT.SPE = 1U;
    }

    return (status);
}





/* Start user code for adding. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */
