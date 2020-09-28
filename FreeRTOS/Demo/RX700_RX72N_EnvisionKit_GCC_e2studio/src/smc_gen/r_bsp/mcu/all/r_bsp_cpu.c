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
* File Name    : r_bsp_cpu.c
* Description  : This module implements CPU specific functions. An example is enabling/disabling interrupts.
***********************************************************************************************************************/
/**********************************************************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 28.02.2019 3.00     Merged processing of all devices.
*                               Added support for GNUC and ICCRX.
*                               Fixed coding style.
*         : 26.07.2019 3.10     Added the API function(R_BSP_SoftwareReset).
*                               Modified comment of API function to Doxygen style.
*                               Added the vbatt_voltage_stability_wait function.
*                               Modified the following functions.
*                               - R_BSP_RegisterProtectEnable
*                               - R_BSP_RegisterProtectDisable
*         : 31.07.2019 3.11     Deleted the compile condition for R_BSP_SoftwareReset.
*         : 08.10.2019 3.12     Changed the following functions.
*                               - R_BSP_InterruptsDisable
*                               - R_BSP_InterruptsEnable
*                               - R_BSP_CpuInterruptLevelWrite
*         : 10.12.2019 3.13     Modified the following functions.
*                               - R_BSP_RegisterProtectEnable
*                               - R_BSP_RegisterProtectDisable
***********************************************************************************************************************/

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
/* Platform support. */
#include "platform.h"

/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/
#ifdef BSP_MCU_REGISTER_WRITE_PROTECTION
/* Key code for writing PRCR register. */
#define BSP_PRV_PRCR_KEY        (0xA500)
#endif

#ifdef BSP_MCU_VOLTAGE_LEVEL_SETTING
/* The macro definition for combinations where settings of USBVON bit conflict. */
#define BSP_PRV_USBVON_CONFLICT (BSP_VOL_USB_POWEROFF | BSP_VOL_USB_POWERON)
/* The macro definition for combinations where settings of PGAVLS bit conflict. */
#define BSP_PRV_PGAVLS_CONFLICT (BSP_VOL_AD_NEGATIVE_VOLTAGE_INPUT | BSP_VOL_AD_NEGATIVE_VOLTAGE_NOINPUT)
/* The macro definition for combinations where settings of RICVLS bit conflict. */
#define BSP_PRV_RICVLS_CONFLICT (BSP_VOL_RIIC_4_5V_OROVER | BSP_VOL_RIIC_UNDER_4_5V)
/* Bit number of VOLSR register. */
#define BSP_PRV_VOLSR_RICVLS_BIT_NUM  (7)
#define BSP_PRV_VOLSR_PGAVLS_BIT_NUM  (6)
#define BSP_PRV_VOLSR_USBVON_BIT_NUM  (2)
#endif

/***********************************************************************************************************************
Typedef definitions
***********************************************************************************************************************/

/***********************************************************************************************************************
Exported global variables (to be accessed by other files)
***********************************************************************************************************************/

/***********************************************************************************************************************
Private global variables and functions
***********************************************************************************************************************/
#ifdef BSP_MCU_REGISTER_WRITE_PROTECTION
/* Used for holding reference counters for protection bits. */
static volatile uint16_t s_protect_counters[BSP_REG_PROTECT_TOTAL_ITEMS];

/* Masks for setting or clearing the PRCR register. Use -1 for size because PWPR in MPC is used differently. */
static const    uint16_t s_prcr_masks[BSP_REG_PROTECT_TOTAL_ITEMS-1] = 
{
#ifdef BSP_MCU_RCPC_PRC0
    0x0001,         /* PRC0. */
#endif
#ifdef BSP_MCU_RCPC_PRC1
    0x0002,         /* PRC1. */
#endif
#ifdef BSP_MCU_RCPC_PRC2
    0x0004,         /* PRC2. */
#endif
#ifdef BSP_MCU_RCPC_PRC3
    0x0008,         /* PRC3. */
#endif
};
#endif

/**********************************************************************************************************************
 * Function Name: R_BSP_InterruptsDisable
 ******************************************************************************************************************//**
 * @brief Globally disables interrupts.
 * @details This function globally disables interrupts. This is performed by clearing the 'I' bit in the CPU's 
 * Processor Status Word (PSW) register.
 * @note The 'I' bit of the PSW can only be modified when in Supervisor Mode. If the CPU is in User Mode and this 
 * function is called, this function does nothing.
 */
void R_BSP_InterruptsDisable (void)
{
    uint32_t    pmode;

    /* Read current processor mode. */
    pmode = (R_BSP_GET_PSW() & 0x00100000);

    /* Check current processor mode. */
    if (0 == pmode)
    {
        /* Use the compiler intrinsic function to clear the I flag. */
        R_BSP_CLRPSW_I();
    }

} /* End of function R_BSP_InterruptsDisable() */

/**********************************************************************************************************************
 * Function Name: R_BSP_InterruptsEnable
 ******************************************************************************************************************//**
 * @brief Globally enable interrupts.
 * @details This function globally enables interrupts. This is performed by setting the 'I' bit in the CPU's Processor 
 * Status Word (PSW) register.
 * @note The 'I' bit of the PSW can only be modified when in Supervisor Mode. If the CPU is in User Mode and this 
 * function is called, this function does nothing.
 */
void R_BSP_InterruptsEnable (void)
{
    uint32_t    pmode;

    /* Read current processor mode. */
    pmode = (R_BSP_GET_PSW() & 0x00100000);

    /* Check current processor mode. */
    if (0 == pmode)
    {
        /* Use the compiler intrinsic function to set the I flag. */
        R_BSP_SETPSW_I();
    }

} /* End of function R_BSP_InterruptsEnable() */

/**********************************************************************************************************************
 * Function Name: R_BSP_CpuInterruptLevelRead
 ******************************************************************************************************************//**
 * @brief Reads the CPU's Interrupt Priority Level.
 * @return The CPU's Interrupt Priority Level.
 * @details This function reads the CPU's Interrupt Priority Level. This level is stored in the IPL bits of the 
 * Processor Status Word (PSW) register.
 */
uint32_t R_BSP_CpuInterruptLevelRead (void)
{
    /* Use the compiler intrinsic function to read the CPU IPL. */
    uint32_t psw_value;

    /* Casting is valid because it matches the type to the right side or argument. */
    psw_value = (uint32_t)R_BSP_GET_PSW();
    psw_value = psw_value & 0x0f000000;
    psw_value = psw_value >> 24;

    return psw_value;
} /* End of function R_BSP_CpuInterruptLevelRead() */

/**********************************************************************************************************************
 * Function Name: R_BSP_CpuInterruptLevelWrite
 ******************************************************************************************************************//**
 * @brief Writes the CPU's Interrupt Priority Level.
 * @param[in] level The level to write to the CPU's IPL.
 * @retval true Successful, CPU's IPL has been written.
 * @retval false Failure, provided 'level' has invalid IPL value or called when the CPU is in User Mode.
 * @details This function writes the CPU's Interrupt Priority Level. This level is stored in the IPL bits of the 
 * Processor Status Word (PSW) register. This function does check to make sure that the IPL being written is valid. 
 * The maximum and minimum valid settings for the CPU IPL are defined in mcu_info.h using the BSP_MCU_IPL_MAX and 
 * BSP_MCU_IPL_MIN macros.
 * @note The CPU's IPL can only be modified by the user when in Supervisor Mode. If the CPU is in User Mode and this
 * function is called, this function does not control IPL and return false.
 */
bool R_BSP_CpuInterruptLevelWrite (uint32_t level)
{
    bool ret;
    uint32_t pmode;

    /* The R_BSP_SET_IPL() function use the MVTIPL instruction.
       The MVTIPL instruction needs to set an immediate value to src. */

    ret = false;

    /* Read current processor mode. */
    pmode = (R_BSP_GET_PSW() & 0x00100000);

    /* Check current processor mode. */
    if (0 == pmode)
    {
        ret = true;

        /* Use the compiler intrinsic function to set the CPU IPL. */
        switch (level)
        {
            case (0):

                /* IPL = 0 */
                R_BSP_SET_IPL(0);
                break;

            case (1):

                /* IPL = 1 */
                R_BSP_SET_IPL(1);
                break;

            case (2):

                /* IPL = 2 */
                R_BSP_SET_IPL(2);
                break;

            case (3):

                /* IPL = 3 */
                R_BSP_SET_IPL(3);
                break;

            case (4):

                /* IPL = 4 */
                R_BSP_SET_IPL(4);
                break;

            case (5):

                /* IPL = 5 */
                R_BSP_SET_IPL(5);
                break;

            case (6):

                /* IPL = 6 */
                R_BSP_SET_IPL(6);
                break;

            case (7):

                /* IPL = 7 */
                R_BSP_SET_IPL(7);
                break;

    #if 7 < BSP_MCU_IPL_MAX
            case (8):

                /* IPL = 8 */
                R_BSP_SET_IPL(8);
                break;

            case (9):

                /* IPL = 9 */
                R_BSP_SET_IPL(9);
                break;

            case (10):

                /* IPL = 10 */
                R_BSP_SET_IPL(10);
                break;

            case (11):

                /* IPL = 11 */
                R_BSP_SET_IPL(11);
                break;

            case (12):

                /* IPL = 12 */
                R_BSP_SET_IPL(12);
                break;

            case (13):

                /* IPL = 13 */
                R_BSP_SET_IPL(13);
                break;

            case (14):

                /* IPL = 14 */
                R_BSP_SET_IPL(14);
                break;

            case (15):

                /* IPL = 15 */
                R_BSP_SET_IPL(15);
                break;
    #endif /* BSP_MCU_IPL_MAX */

            default:
                ret = false;
                break;
        }
    }

    return ret;
} /* End of function R_BSP_CpuInterruptLevelWrite() */

/**********************************************************************************************************************
 * Function Name: R_BSP_RegisterProtectEnable
 ******************************************************************************************************************//**
 * @brief Enables write protection for selected registers.
 * @param[in] regs_to_protect Which registers to enable write protection for.
 * @details This function enables write protection for the input registers. Only certain MCU registers have the 
 * ability to be write protected. To see which registers are available to be protected by this function look at the 
 * bsp_reg_protect_t enum in r_bsp_cpu.h for your MCU.
 * This function, and R_BSP_RegisterProtectDisable(), use counters for each entry in the bsp_reg_protect_t enum so 
 * that users can call these functions multiple times without problem. This function uses the interrupt disable / 
 * enable function by controlling the Processor Interrupt Priority Level (IPL) of the R_BSP_InterruptControl function, 
 * because counter control is the critical section. If the function is executed while the processor mode is supervisor 
 * mode, interrupts that are at or below the specified interrupt priority level will be disabled by controlling the 
 * IPL. If the function is executed while the processor mode is user mode, the IPL controlling does not execute. An 
 * example of why this is needed is shown below in the Special Notes section below.
 * @note 
 * (1) About why counters are needed. \n
 * See Section 5.7 in the application note for details.\n
 * (2) Notes on user mode \n
 * The R_BSP_InterruptControl function used to secure atomicity in the critical section of the counter control with 
 * this function is valid only in supervisor mode. When this function is executed in user mode, the 
 * R_BSP_InterruptControl function is executed but atomicity is not to secure.
 */
void R_BSP_RegisterProtectEnable (bsp_reg_protect_t regs_to_protect)
{
#ifdef BSP_MCU_REGISTER_WRITE_PROTECTION
    bsp_int_ctrl_t int_ctrl;

    /* Set IPL to the maximum value to disable all interrupts,
     * so the scheduler can not be scheduled in critical region.
     * Note: Please set this macro more than IPR for other FIT module interrupts. */
    R_BSP_InterruptControl(BSP_INT_SRC_EMPTY, BSP_INT_CMD_FIT_INTERRUPT_DISABLE, &int_ctrl);

    /* Is it safe to disable write access? */
    if (0 != s_protect_counters[regs_to_protect])
    {
        /* Decrement the protect counter */
        s_protect_counters[regs_to_protect]--;
    }

    /* Is it safe to disable write access? */
    if (0 == s_protect_counters[regs_to_protect])
    {
        if (BSP_REG_PROTECT_MPC != regs_to_protect)
        {
            /* Enable protection using PRCR register. */
            /* When writing to the PRCR register the upper 8-bits must be the correct key. Set lower bits to 0 to
               disable writes.
               b15:b8 PRKEY - Write 0xA5 to upper byte to enable writing to lower byte
               b7:b4  Reserved (set to 0)
               b3     PRC3  - Please check the user's manual.
               b2     PRC2  - Please check the user's manual.
               b1     PRC1  - Please check the user's manual.
               b0     PRC0  - Please check the user's manual.
            */
            SYSTEM.PRCR.WORD = (uint16_t)((SYSTEM.PRCR.WORD | BSP_PRV_PRCR_KEY) & (~s_prcr_masks[regs_to_protect]));
        }
        else
        {
            /* Enable protection for MPC using PWPR register. */
            /* Enable writing of PFSWE bit. It could be assumed that the B0WI bit is still cleared from a call to
               protection disable function, but it is written here to make sure that the PFSWE bit always gets
               cleared. */
            MPC.PWPR.BIT.B0WI = 0;

            /* Disable writing to PFS registers. */
            MPC.PWPR.BIT.PFSWE = 0;

            /* Disable writing of PFSWE bit. */
            MPC.PWPR.BIT.B0WI = 1;
        }
    }

    /* Restore the IPL. */
    R_BSP_InterruptControl(BSP_INT_SRC_EMPTY, BSP_INT_CMD_FIT_INTERRUPT_ENABLE, &int_ctrl);

#else /* BSP_MCU_REGISTER_WRITE_PROTECTION */
    /* No registers to protect. */
    /* This code is only used to remove compiler info messages about this parameter not being used. */
    INTERNAL_NOT_USED(regs_to_protect);
#endif /* BSP_MCU_REGISTER_WRITE_PROTECTION */
} /* End of function R_BSP_RegisterProtectEnable() */

/**********************************************************************************************************************
 * Function Name: R_BSP_RegisterProtectDisable
 ******************************************************************************************************************//**
 * @brief Disables write protection for selected registers.
 * @param[in] regs_to_unprotect Which registers to disable write protection for.
 * @details This function disables write protection for the input registers. Only certain MCU registers have the 
 * ability to be write protected. To see which registers are available to be protected by this function look at the 
 * bsp_reg_protect_t enum in r_bsp_cpu.h for your MCU.
 * This function, and R_BSP_RegisterProtectEnable(), use counters for each entry in the bsp_reg_protect_t enum so that 
 * users can call these functions multiple times without problem. This function uses the interrupt disable / 
 * enable function by controlling the Processor Interrupt Priority Level (IPL) of the R_BSP_InterruptControl function, 
 * because counter control is the critical section. If the function is executed while the processor mode is supervisor 
 * mode, interrupts that are at or below the specified interrupt priority level will be disabled by controlling the 
 * IPL. If the function is executed while the processor mode is user mode, the IPL controlling does not execute.
 * @note The R_BSP_InterruptControl function used to secure atomicity in the critical section of the counter control 
 * with this function is valid only in supervisor mode. When this function is executed in user mode, the 
 * R_BSP_InterruptControl function is executed but atomicity is not to secure.
 */
void R_BSP_RegisterProtectDisable (bsp_reg_protect_t regs_to_unprotect)
{
#ifdef BSP_MCU_REGISTER_WRITE_PROTECTION
    bsp_int_ctrl_t int_ctrl;

    /* Set IPL to the maximum value to disable all interrupts,
     * so the scheduler can not be scheduled in critical region.
     * Note: Please set this macro more than IPR for other FIT module interrupts. */
    R_BSP_InterruptControl(BSP_INT_SRC_EMPTY, BSP_INT_CMD_FIT_INTERRUPT_DISABLE, &int_ctrl);

    /* If this is first entry then disable protection. */
    if (0 == s_protect_counters[regs_to_unprotect])
    {
        if (BSP_REG_PROTECT_MPC != regs_to_unprotect)
        {
            /* Enable protection using PRCR register. */
            /* When writing to the PRCR register the upper 8-bits must be the correct key.
               Set lower bits to 1 to enable writes.
               b15:b8 PRKEY - Write 0xA5 to upper byte to enable writing to lower byte
               b7:b4  Reserved (set to 0)
               b3     PRC3  - Please check the user's manual.
               b2     PRC2  - Please check the user's manual.
               b1     PRC1  - Please check the user's manual.
               b0     PRC0  - Please check the user's manual.
            */
            SYSTEM.PRCR.WORD = (uint16_t)((SYSTEM.PRCR.WORD | BSP_PRV_PRCR_KEY) | s_prcr_masks[regs_to_unprotect]);
        }
        else
        {
            /* Disable protection for MPC using PWPR register. */
            /* Enable writing of PFSWE bit. */
            MPC.PWPR.BIT.B0WI = 0;

            /* Enable writing to PFS registers. */
            MPC.PWPR.BIT.PFSWE = 1;
        }
    }

    /* Increment the protect counter */
    s_protect_counters[regs_to_unprotect]++;

    /* Restore the IPL. */
    R_BSP_InterruptControl(BSP_INT_SRC_EMPTY, BSP_INT_CMD_FIT_INTERRUPT_ENABLE, &int_ctrl);

#else /* BSP_MCU_REGISTER_WRITE_PROTECTION */
    /* No registers to protect. */
    /* This code is only used to remove compiler info messages about this parameter not being used. */
    INTERNAL_NOT_USED(regs_to_unprotect);
#endif /* BSP_MCU_REGISTER_WRITE_PROTECTION */
} /* End of function R_BSP_RegisterProtectDisable() */

#ifdef BSP_MCU_VOLTAGE_LEVEL_SETTING
/**********************************************************************************************************************
 * Function Name: R_BSP_VoltageLevelSetting
 ******************************************************************************************************************//**
 * @brief This API function is used excessively with the RX66T and RX72T. It makes settings to the voltage level 
 * setting register (VOLSR) that are necessary in order to use the USB, AD, and RIIC peripheral modules. Call this 
 * function only when it is necessary to change the register settings.
 * @param[in] ctrl_ptn Register Setting Patterns
 * The following setting patterns cannot be selected at the same time.
 * When specifying more than one pattern at the same time, use the "|" (OR) operator.
 * - BSP_VOL_USB_POWEROFF and BSP_VOL_USB_POWERON
 * - BSP_VOL_AD_NEGATIVE_VOLTAGE_INPUT and BSP_VOL_AD_NEGATIVE_VOLTAGE_NOINPUT
 * - BSP_VOL_RIIC_4_5V_OROVER and BSP_VOL_RIIC_UNDER_4_5V
 *
 *   BSP_VOL_USB_POWEROFF: Updates the USBVON bit to 0.
 *
 *   BSP_VOL_USB_POWERON: Updates the USBVON bit to 1.
 *
 *   BSP_VOL_AD_NEGATIVE_VOLTAGE_INPUT: Updates the PGAVLS bit to 0.
 *
 *   BSP_VOL_AD_NEGATIVE_VOLTAGE_NOINPUT: Updates the PGAVLS bit to 1.
 *
 *   BSP_VOL_RIIC_4_5V_OROVER: Updates the RICVLS bit to 0.
 *
 *   BSP_VOL_RIIC_UNDER_4_5V: Updates the RICVLS bit to 1.
 * @retval true Processing completed, register successfully updated.
 * @retval false The function was called under the following conditions, so the register setting was not updated.
 * - Setting patterns that cannot be selected at the same time were selected.
 * - A setting pattern related to the USB was selected when the USB was not in the module stop state.
 * - A setting pattern related to the AD was selected when the AD was not in the module stop state.
 * - A setting pattern related to the RIIC was selected when the RIIC was not in the module stop state.
 * @details This function initializes the voltage level setting register (VOLSR), which is necessary in order to use 
 * the USB, AD and RIIC peripheral modules. When specifying a setting pattern related to the USB, call this function 
 * before the USB is released from the module stop state. When specifying a setting pattern related to the AD, call 
 * this function before the AD (unit 0 and unit 1) is released from the module stop state. When specifying a setting 
 * pattern related to the RIIC, call this function before the RIIC is released from the module stop state. If the 
 * function is called with a setting pattern related to the USB specified after the USB is released from the module 
 * stop state, the function returns "false" as the return value and does not update the register settings. If the 
 * function is called with a setting pattern related to the AD specified after the AD (unit 0 and unit 1) is released 
 * from the module stop state, the function returns "false" as the return value and does not update the register 
 * settings. Finally, if the function is called with a setting pattern related to the RIIC specified after the RIIC is 
 * released from the module stop state, the function returns "false" as the return value and does not update the 
 * register settings.
 */
bool R_BSP_VoltageLevelSetting (uint8_t ctrl_ptn)
{
    uint8_t  *p_volsr_addr;

#if BSP_CFG_PARAM_CHECKING_ENABLE == 1
    /* ---- CHECK ARGUMENTS ---- */
    if (BSP_PRV_USBVON_CONFLICT == (ctrl_ptn & BSP_PRV_USBVON_CONFLICT))
    {
        return false;
    }

    if (BSP_PRV_PGAVLS_CONFLICT == (ctrl_ptn & BSP_PRV_PGAVLS_CONFLICT))
    {
        return false;
    }

    if (BSP_PRV_RICVLS_CONFLICT == (ctrl_ptn & BSP_PRV_RICVLS_CONFLICT))
    {
        return false;
    }
#endif

    /* Check USB module stop state. */
    if(0 != (ctrl_ptn & BSP_PRV_USBVON_CONFLICT))
    {
        /* Casting is valid because it matches the type to the right side or argument. */
        if(0 == MSTP(USB0))
        {
            return false;
        }
    }

    /* Check AD module stop state. */
    if(0 != (ctrl_ptn & BSP_PRV_PGAVLS_CONFLICT))
    {
        /* Casting is valid because it matches the type to the right side or argument. */
        if((0 == MSTP(S12AD)) || (0 == MSTP(S12AD1)))
        {
            return false;
        }
    }

    /* Check RIIC module stop state. */
    if(0 != (ctrl_ptn & BSP_PRV_RICVLS_CONFLICT))
    {
        /* Casting is valid because it matches the type to the right side or argument. */
        if(0 == MSTP(RIIC0))
        {
            return false;
        }
    }

    /* Protect off. */
    SYSTEM.PRCR.WORD = 0xA502;

    /* Casting is valid because it matches the type to the right side or argument. */
    p_volsr_addr = (uint8_t *)&SYSTEM.VOLSR.BYTE;

    /* Updated the RICVLS bit. */
    if(0 != (ctrl_ptn & BSP_VOL_RIIC_UNDER_4_5V))
    {
        R_BSP_BIT_SET(p_volsr_addr, BSP_PRV_VOLSR_RICVLS_BIT_NUM);
    }

    if(0 != (ctrl_ptn & BSP_VOL_RIIC_4_5V_OROVER))
    {
        R_BSP_BIT_CLEAR(p_volsr_addr, BSP_PRV_VOLSR_RICVLS_BIT_NUM);
    }

    /* Updated the PGAVLS bit. */
    if(0 != (ctrl_ptn & BSP_VOL_AD_NEGATIVE_VOLTAGE_NOINPUT))
    {
        R_BSP_BIT_SET(p_volsr_addr, BSP_PRV_VOLSR_PGAVLS_BIT_NUM);
    }

    if(0 != (ctrl_ptn & BSP_VOL_AD_NEGATIVE_VOLTAGE_INPUT))
    {
        R_BSP_BIT_CLEAR(p_volsr_addr, BSP_PRV_VOLSR_PGAVLS_BIT_NUM);
    }

    /* Updated the USBVON bit. */
    if(0 != (ctrl_ptn & BSP_VOL_USB_POWERON))
    {
        R_BSP_BIT_SET(p_volsr_addr, BSP_PRV_VOLSR_USBVON_BIT_NUM);
    }

    if(0 != (ctrl_ptn & BSP_VOL_USB_POWEROFF))
    {
        R_BSP_BIT_CLEAR(p_volsr_addr, BSP_PRV_VOLSR_USBVON_BIT_NUM);
    }

    /* Protect on. */
    SYSTEM.PRCR.WORD = 0xA500;

    return true;
}  /* End of function R_BSP_VoltageLevelSetting() */ 
#endif /* BSP_MCU_VOLTAGE_LEVEL_SETTING */

/**********************************************************************************************************************
 * Function Name: R_BSP_SoftwareReset
 ******************************************************************************************************************//**
 * @details Reset the MCU by Software Reset.
 */
void R_BSP_SoftwareReset(void)
{
#ifdef BSP_MCU_REGISTER_WRITE_PROTECTION
    /* Protect off. */
    R_BSP_RegisterProtectDisable(BSP_REG_PROTECT_LPC_CGC_SWR);
#endif

    /* Resets the MCU. */
    SYSTEM.SWRR = 0xA501;

    /* WAIT_LOOP */
    while(1)
    {
         R_BSP_NOP();
    }
} /* End of function R_BSP_SoftwareReset() */

/***********************************************************************************************************************
* Function Name: bsp_register_protect_open
* Description  : Initializes variables needed for register protection functionality.
* Arguments    : none
* Return Value : none
***********************************************************************************************************************/
void bsp_register_protect_open (void)
{
#ifdef BSP_MCU_REGISTER_WRITE_PROTECTION
    uint32_t i;

    /* Initialize reference counters to 0. */
    /* WAIT_LOOP */
    for (i = 0; i < BSP_REG_PROTECT_TOTAL_ITEMS; i++)
    {
        s_protect_counters[i] = 0;
    }
#else
    /* No registers to protect. */
#endif
} /* End of function bsp_register_protect_open() */

/***********************************************************************************************************************
* Function Name: bsp_ram_initialize
* Description  : Initialize ram variable.
* Arguments    : none
* Return Value : none
***********************************************************************************************************************/
void bsp_ram_initialize (void)
{
    uint32_t i;

    /* Initialize g_bsp_Locks to 0. */
    /* WAIT_LOOP */
    for (i = 0; i < BSP_NUM_LOCKS; i++)
    {
        g_bsp_Locks[i].lock = 0;
    }
} /* End of function bsp_ram_initialize() */

