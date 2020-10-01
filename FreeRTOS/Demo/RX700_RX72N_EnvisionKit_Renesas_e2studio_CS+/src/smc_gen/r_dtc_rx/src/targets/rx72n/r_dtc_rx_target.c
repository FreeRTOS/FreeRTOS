/*******************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only
* intended for use with Renesas products. No other uses are authorized. This
* software is owned by Renesas Electronics Corporation and is protected under
* all applicable laws, including copyright laws.
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING
* THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, INCLUDING BUT NOT
* LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE
* AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED.
* TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS
* ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE
* FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR
* ANY REASON RELATED TO THIS SOFTWARE, EVEN IF RENESAS OR ITS AFFILIATES HAVE
* BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software
* and to discontinue the availability of this software. By using this software,
* you agree to the additional terms and conditions found by accessing the
* following link:
* http://www.renesas.com/disclaimer
*
* Copyright (C) 2019 Renesas Electronics Corporation. All rights reserved.
*******************************************************************************/
/*******************************************************************************
* File Name    : r_dtc_rx_target.c
* Device       : RX72N
* Tool-Chain   : Renesas RXC Toolchain v3.01.00
* OS           : not use
* H/W Platform : not use
* Description  : Functions for using DTC on RX72N.
*******************************************************************************/
/*******************************************************************************
* History : DD.MM.YYYY Version Description
*         : 30.12.2019 1.00    First Release for RX72N.
*******************************************************************************/

/*******************************************************************************
Includes   <System Includes> , "Project Includes"
*******************************************************************************/
/* Defines for DTC support */
#include "r_dtc_rx_if.h"
#include ".\src\r_dtc_rx_private.h"

/* Check MCU Group */
#if defined(BSP_MCU_RX72N)

/*******************************************************************************
Exported global variables (to be accessed by other files)
*******************************************************************************/
/* The array of all interrupt source */
const dtc_activation_source_t g_source_array[DTC_NUM_INTERRUPT_SRC] =
{
DTCE_ICU_SWINT2,DTCE_ICU_SWINT,
DTCE_CMT0_CMI0,
DTCE_CMT1_CMI1,
DTCE_CMTW0_CMWI0,
DTCE_CMTW1_CMWI1,
DTCE_USB0_D0FIFO0,DTCE_USB0_D1FIFO0,
DTCE_RSPI0_SPRI0,DTCE_RSPI0_SPTI0,
DTCE_RSPI1_SPRI1,DTCE_RSPI1_SPTI1,
DTCE_QSPI_SPRI,DTCE_QSPI_SPTI,
DTCE_SDHI_SBFAI,
DTCE_MMCIF_MBFAI,
DTCE_SSIE0_SSITXI0,DTCE_SSIE0_SSIRXI0,
DTCE_SSIE1_SSIRTI1,
DTCE_RIIC1_RXI1,DTCE_RIIC1_TXI1,
DTCE_RIIC0_RXI0,DTCE_RIIC0_TXI0,
DTCE_RIIC2_RXI2,DTCE_RIIC2_TXI2,
DTCE_SCI0_RXI0,DTCE_SCI0_TXI0,
DTCE_SCI1_RXI1,DTCE_SCI1_TXI1,
DTCE_SCI2_RXI2,DTCE_SCI2_TXI2,
DTCE_ICU_IRQ0,DTCE_ICU_IRQ1,DTCE_ICU_IRQ2,DTCE_ICU_IRQ3,DTCE_ICU_IRQ4,DTCE_ICU_IRQ5,DTCE_ICU_IRQ6,DTCE_ICU_IRQ7,
DTCE_ICU_IRQ8,DTCE_ICU_IRQ9,DTCE_ICU_IRQ10,DTCE_ICU_IRQ11,DTCE_ICU_IRQ12,DTCE_ICU_IRQ13,DTCE_ICU_IRQ14,DTCE_ICU_IRQ15,
DTCE_SCI3_RXI3,DTCE_SCI3_TXI3,
DTCE_SCI4_RXI4,DTCE_SCI4_TXI4,
DTCE_SCI5_RXI5,DTCE_SCI5_TXI5,
DTCE_SCI6_RXI6,DTCE_SCI6_TXI6,
DTCE_PDC_PCDFI,
DTCE_SCI7_RXI7,DTCE_SCI7_TXI7,
DTCE_SCI8_RXI8,DTCE_SCI8_TXI8,
DTCE_SCI9_RXI9,DTCE_SCI9_TXI9,
DTCE_SCI10_RXI10,DTCE_SCI10_TXI10,
DTCE_RSPI2_SPRI2,DTCE_RSPI2_SPTI2,
DTCE_SCI11_RXI11,DTCE_SCI11_TXI11,
DTCE_SCI12_RXI12,DTCE_SCI12_TXI12,
DTCE_DMAC_DMAC0I,DTCE_DMAC_DMAC1I,DTCE_DMAC_DMAC2I,DTCE_DMAC_DMAC3I,
DTCE_EXDMAC_EXDMAC0I,DTCE_EXDMAC_EXDMAC1I,
DTCE_PERIB_INTB128,DTCE_PERIB_INTB129,DTCE_PERIB_INTB130,DTCE_PERIB_INTB131,DTCE_PERIB_INTB132,
DTCE_PERIB_INTB133,DTCE_PERIB_INTB134,DTCE_PERIB_INTB135,DTCE_PERIB_INTB136,DTCE_PERIB_INTB137,
DTCE_PERIB_INTB138,DTCE_PERIB_INTB139,DTCE_PERIB_INTB140,DTCE_PERIB_INTB141,DTCE_PERIB_INTB142,
DTCE_PERIB_INTB143,DTCE_PERIB_INTB144,DTCE_PERIB_INTB145,DTCE_PERIB_INTB146,DTCE_PERIB_INTB147,
DTCE_PERIB_INTB148,DTCE_PERIB_INTB149,DTCE_PERIB_INTB150,DTCE_PERIB_INTB151,DTCE_PERIB_INTB152,
DTCE_PERIB_INTB153,DTCE_PERIB_INTB154,DTCE_PERIB_INTB155,DTCE_PERIB_INTB156,DTCE_PERIB_INTB157,
DTCE_PERIB_INTB158,DTCE_PERIB_INTB159,DTCE_PERIB_INTB160,DTCE_PERIB_INTB161,DTCE_PERIB_INTB162,
DTCE_PERIB_INTB163,DTCE_PERIB_INTB164,DTCE_PERIB_INTB165,DTCE_PERIB_INTB166,DTCE_PERIB_INTB167,
DTCE_PERIB_INTB168,DTCE_PERIB_INTB169,DTCE_PERIB_INTB170,DTCE_PERIB_INTB171,DTCE_PERIB_INTB172,
DTCE_PERIB_INTB173,DTCE_PERIB_INTB174,DTCE_PERIB_INTB175,DTCE_PERIB_INTB176,DTCE_PERIB_INTB177,
DTCE_PERIB_INTB178,DTCE_PERIB_INTB179,DTCE_PERIB_INTB180,DTCE_PERIB_INTB181,DTCE_PERIB_INTB182,
DTCE_PERIB_INTB183,DTCE_PERIB_INTB184,DTCE_PERIB_INTB185,DTCE_PERIB_INTB186,DTCE_PERIB_INTB187,
DTCE_PERIB_INTB188,DTCE_PERIB_INTB189,DTCE_PERIB_INTB190,DTCE_PERIB_INTB191,DTCE_PERIB_INTB192,
DTCE_PERIB_INTB193,DTCE_PERIB_INTB194,DTCE_PERIB_INTB195,DTCE_PERIB_INTB196,DTCE_PERIB_INTB197,
DTCE_PERIB_INTB198,DTCE_PERIB_INTB199,DTCE_PERIB_INTB200,DTCE_PERIB_INTB201,DTCE_PERIB_INTB202,
DTCE_PERIB_INTB203,DTCE_PERIB_INTB204,DTCE_PERIB_INTB205,DTCE_PERIB_INTB206,DTCE_PERIB_INTB207,
DTCE_PERIA_INTA208,DTCE_PERIA_INTA209,DTCE_PERIA_INTA210,DTCE_PERIA_INTA211,DTCE_PERIA_INTA212,
DTCE_PERIA_INTA213,DTCE_PERIA_INTA214,DTCE_PERIA_INTA215,DTCE_PERIA_INTA216,DTCE_PERIA_INTA217,
DTCE_PERIA_INTA218,DTCE_PERIA_INTA219,DTCE_PERIA_INTA220,DTCE_PERIA_INTA221,DTCE_PERIA_INTA222,
DTCE_PERIA_INTA223,DTCE_PERIA_INTA224,DTCE_PERIA_INTA225,DTCE_PERIA_INTA226,DTCE_PERIA_INTA227,
DTCE_PERIA_INTA228,DTCE_PERIA_INTA229,DTCE_PERIA_INTA230,DTCE_PERIA_INTA231,DTCE_PERIA_INTA232,
DTCE_PERIA_INTA233,DTCE_PERIA_INTA234,DTCE_PERIA_INTA235,DTCE_PERIA_INTA236,DTCE_PERIA_INTA237,
DTCE_PERIA_INTA238,DTCE_PERIA_INTA239,DTCE_PERIA_INTA240,DTCE_PERIA_INTA241,DTCE_PERIA_INTA242,
DTCE_PERIA_INTA243,DTCE_PERIA_INTA244,DTCE_PERIA_INTA245,DTCE_PERIA_INTA246,DTCE_PERIA_INTA247,
DTCE_PERIA_INTA248,DTCE_PERIA_INTA249,DTCE_PERIA_INTA250,DTCE_PERIA_INTA251,DTCE_PERIA_INTA252,
DTCE_PERIA_INTA253,DTCE_PERIA_INTA254,DTCE_PERIA_INTA255   
};


#if ((0 != BSP_CFG_USER_LOCKING_ENABLED) || (bsp_lock_t != BSP_CFG_USER_LOCKING_TYPE) \
      || (DTC_ENABLE != DTC_CFG_USE_DMAC_FIT_MODULE))
/*******************************************************************************
* Function Name: r_dtc_check_DMAC_locking_byUSER
* Description  : Checks all DMAC channel locking.
* Arguments    : none -
* Return Value : true -
*                    All DMAC channels are unlocked.
*                false -
*                    One or some DMAC channels are locked.
*
*******************************************************************************/
bool r_dtc_check_DMAC_locking_byUSER(void)
{
    bool ret = true;

    /* User has to check the locking of DMAC by themselves. */
    /* do something */

    return ret;
}
#endif


/*******************************************************************************
* Function Name: r_dtc_module_enable
* Description  : Releases module stop state.
* Arguments    : None
* Return Value : None
*******************************************************************************/
void r_dtc_module_enable(void)
{
#if ((R_BSP_VERSION_MAJOR == 5) && (R_BSP_VERSION_MINOR >= 30)) || (R_BSP_VERSION_MAJOR >= 6)
bsp_int_ctrl_t int_ctrl;
#endif
    /* Enable writing to MSTP registers. */
    R_BSP_RegisterProtectDisable(BSP_REG_PROTECT_LPC_CGC_SWR);

#if ((R_BSP_VERSION_MAJOR == 5) && (R_BSP_VERSION_MINOR >= 30)) || (R_BSP_VERSION_MAJOR >= 6)
    R_BSP_InterruptControl(BSP_INT_SRC_EMPTY, BSP_INT_CMD_FIT_INTERRUPT_DISABLE, &int_ctrl);
#endif
    /* Release from module stop state. */
    MSTP(DTC) = 0;

#if ((R_BSP_VERSION_MAJOR == 5) && (R_BSP_VERSION_MINOR >= 30)) || (R_BSP_VERSION_MAJOR >= 6)
    R_BSP_InterruptControl(BSP_INT_SRC_EMPTY, BSP_INT_CMD_FIT_INTERRUPT_ENABLE, &int_ctrl);
#endif
    /* Disable writing to MSTP registers. */
    R_BSP_RegisterProtectEnable(BSP_REG_PROTECT_LPC_CGC_SWR);

    return;
}
/******************************************************************************
 End of function r_dtc_module_enable
 *****************************************************************************/

/*******************************************************************************
* Function Name: r_dtc_module_disable
* Description  : Sets to module stop state.
* Arguments    : None
* Return Value : None
*******************************************************************************/
void r_dtc_module_disable(void)
{
#if ((R_BSP_VERSION_MAJOR == 5) && (R_BSP_VERSION_MINOR >= 30)) || (R_BSP_VERSION_MAJOR >= 6)
bsp_int_ctrl_t int_ctrl;
#endif
    /* Enable writing to MSTP registers. */
    R_BSP_RegisterProtectDisable(BSP_REG_PROTECT_LPC_CGC_SWR);

#if ((R_BSP_VERSION_MAJOR == 5) && (R_BSP_VERSION_MINOR >= 30)) || (R_BSP_VERSION_MAJOR >= 6)
    R_BSP_InterruptControl(BSP_INT_SRC_EMPTY, BSP_INT_CMD_FIT_INTERRUPT_DISABLE, &int_ctrl);
#endif
    /* Set to module stop state. */
    MSTP(DTC) = 1;

#if ((R_BSP_VERSION_MAJOR == 5) && (R_BSP_VERSION_MINOR >= 30)) || (R_BSP_VERSION_MAJOR >= 6)
    R_BSP_InterruptControl(BSP_INT_SRC_EMPTY, BSP_INT_CMD_FIT_INTERRUPT_ENABLE, &int_ctrl);
#endif
    /* Disable writing to MSTP registers. */
    R_BSP_RegisterProtectEnable(BSP_REG_PROTECT_LPC_CGC_SWR);

    return;
}
/******************************************************************************
 End of function r_dtc_module_disable
 *****************************************************************************/

#endif /* defined(BSP_MCU_RX72N) */

/* End of File */
