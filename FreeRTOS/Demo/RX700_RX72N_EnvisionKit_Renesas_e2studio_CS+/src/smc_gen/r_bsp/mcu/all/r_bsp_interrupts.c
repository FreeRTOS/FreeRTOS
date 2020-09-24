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
* File Name    : r_bsp_interrupts.c
* Description  : This module allows for callbacks to be registered for certain interrupts. 
*                And handle exception interrupts.
***********************************************************************************************************************/
/**********************************************************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 28.02.2019 1.00     First Release
*         : 08.04.2019 1.01     Added process for Group IE0 interrupts.
*                               Added process for EXNMI interrupts.
*         : 26.07.2019 1.10     Modified comment of API function to Doxygen style.
*                               Modified the following function for added function.
*                               - R_BSP_InterruptControl
*                               Added the following functions.
*                               - bsp_fit_interrupts_control
*                               - bsp_fit_interrupt_enable
*                               - bsp_fit_interrupt_disable
*                               Fixed coding style.
*         : 08.10.2019 1.11     Added process for software interrupt.
*         : 10.12.2019 1.12     Modified comment.
***********************************************************************************************************************/

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
#include "platform.h"

/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/
#ifdef BSP_MCU_FLOATING_POINT
/* Defines CV, CO, CZ, CU, CX, and CE bits. */
#define BSP_PRV_FPU_CAUSE_FLAGS     (0x000000FC)
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
/* This array holds callback functions. */
static void (* g_bsp_vectors[BSP_INT_SRC_TOTAL_ITEMS])(void * pdata);

static bsp_int_err_t bsp_fit_interrupts_control (bool enable, bsp_int_ctrl_t * pdata);

#ifdef BSP_MCU_GROUP_INTERRUPT
static bsp_int_err_t bsp_gr_int_enable_disable (bsp_int_src_t vector, bool enable, uint32_t ipl);
#endif /* BSP_MCU_GROUP_INTERRUPT */

/**********************************************************************************************************************
 * Function Name: R_BSP_InterruptRequestEnable
 ******************************************************************************************************************//**
 * @brief Enable the specified interrupt request.
 * @param[in] vector Interrupt vector number.
 * @details Enable the specified interrupt request. Calculate the corresponding IER [m].IEN [j] from the vector number 
 * of the argument, and set "1" to that bit. The macro defined in iodefine.h can be used to the setting of the 
 * argument "vector". A description example is shown in Example.
 * @note When setting an immediate value for an argument "vector", the argument must be 0 to 255. Don't set the 
 * vector number of the reserved interrupt source to the argument.
 */
void R_BSP_InterruptRequestEnable (uint32_t vector)
{
    uint32_t ier_reg_num;
    uint32_t ien_bit_num;
    uint8_t  *p_ier_addr;

    /* Calculate the register number. (IER[m].IENj)(m = vector_number / 8) */
    ier_reg_num = vector >> 3;

    /* Calculate the bit number. (IERm.IEN[j])(j = vector_number % 8) */
    ien_bit_num = vector & 0x00000007;

    /* Casting is valid because it matches the type to the right side or argument. */
    p_ier_addr = (uint8_t *)&ICU.IER[ier_reg_num].BYTE;

    /* Casting is valid because it matches the type to the right side or argument. */
    R_BSP_BIT_SET(p_ier_addr, ien_bit_num);
} /* End of function R_BSP_InterruptRequestEnable() */

/**********************************************************************************************************************
 * Function Name: R_BSP_InterruptRequestDisable
 ******************************************************************************************************************//**
 * @brief Disable the specified interrupt request.
 * @param[in] vector Interrupt vector number.
 * @details Disable the specified interrupt request. Calculate the corresponding IER [m].IEN [j] from the vector 
 * number of the argument, and clear "0" to that bit. The macro defined in iodefine.h can be used to the setting of 
 * the argument "vector". A description example is shown in Example.
 * @note When setting an immediate value for an argument "vector", the argument must be 0 to 255. Don't set the 
 * vector number of the reserved interrupt source to the argument.
 */
void R_BSP_InterruptRequestDisable (uint32_t vector)
{
    uint32_t ier_reg_num;
    uint32_t ien_bit_num;
    uint8_t  *p_ier_addr;

    /* Calculate the register number. (IER[m].IENj)(m = vector_number / 8) */
    ier_reg_num = vector >> 3;

    /* Calculate the bit number. (IERm.IEN[j])(j = vector_number % 8) */
    ien_bit_num = vector & 0x00000007;

    /* Casting is valid because it matches the type to the right side or argument. */
    p_ier_addr = (uint8_t *)&ICU.IER[ier_reg_num].BYTE;

    /* Casting is valid because it matches the type to the right side or argument. */
    R_BSP_BIT_CLEAR(p_ier_addr, ien_bit_num);
} /* End of function R_BSP_InterruptRequestDisable() */

/***********************************************************************************************************************
* Function Name: bsp_interrupt_open
* Description  : Initialize callback function array.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void bsp_interrupt_open (void)
{
    uint32_t i;

    /* WAIT_LOOP */
    for (i = 0; i < BSP_INT_SRC_TOTAL_ITEMS; i++)
    {
        /* Casting is valid because it matches the type to the right side or argument. */
        g_bsp_vectors[i] = FIT_NO_FUNC;
    }

#ifdef BSP_MCU_SOFTWARE_CONFIGURABLE_INTERRUPT
    /* Initialize mapped interrupts. */
    bsp_mapped_interrupt_open();
#endif

#if (defined(BSP_CFG_SWINT_UNIT1_ENABLE) && (BSP_CFG_SWINT_UNIT1_ENABLE == 1))
    R_BSP_SoftwareInterruptOpen(BSP_SWINT_UNIT1);
#endif /* (defined(BSP_CFG_SWINT_UNIT1_ENABLE) && (BSP_CFG_SWINT_UNIT1_ENABLE == 1)) */
#if (defined(BSP_CFG_SWINT_UNIT2_ENABLE) && (BSP_CFG_SWINT_UNIT2_ENABLE == 1))
    R_BSP_SoftwareInterruptOpen(BSP_SWINT_UNIT2);
#endif /* (defined(BSP_CFG_SWINT_UNIT2_ENABLE) && (BSP_CFG_SWINT_UNIT2_ENABLE == 1)) */
} /* End of function bsp_interrupt_open() */

/**********************************************************************************************************************
 * Function Name: R_BSP_InterruptWrite
 ******************************************************************************************************************//**
 * @brief Registers a callback function for an interrupt.
 * @param[in] vector Which interrupt to register a callback for.
 * @param[in] callback Pointer to function to call when interrupt occurs.
 * @retval BSP_INT_SUCCESS Successful, callback has been registered.
 * @retval BSP_INT_ERR_INVALID_ARG Invalid function address input, any previous function has been unregistered.
 * @details This function registers a callback function for an interrupt. If FIT_NO_FUNC, NULL, or any other invalid 
 * function address is passed for the callback argument then any previously registered callbacks are unregistered.
 * If one of the interrupts that is handled by this code is triggered then the interrupt handler will query this code 
 * to see if a valid callback function is registered. If one is found then the callback function will be called.
 * If one is not found then the interrupt handler will clear the appropriate flag(s) and exit. If the user has a 
 * callback function registered and wishes to no longer handle the interrupt then the user should call this function 
 * again with FIT_NO_FUNC as the vector parameter.
 * @note Use of FIT_NO_FUNC is preferred over NULL since access to the address defined by FIT_NO_FUNC will cause a 
 * bus error which is easy for the user to catch. NULL typically resolves to 0 which is a valid address on RX MCUs.
 */
bsp_int_err_t R_BSP_InterruptWrite (bsp_int_src_t vector,  bsp_int_cb_t callback)
{
    bsp_int_err_t err;

    err = BSP_INT_SUCCESS;

    /* Check for valid address. */
    if (((uint32_t)callback == (uint32_t)NULL) || ((uint32_t)callback == (uint32_t)FIT_NO_FUNC))
    {
        /* Casting is valid because it matches the type to the right side or argument. */
        g_bsp_vectors[vector] = FIT_NO_FUNC;
    }
    else
    {
        g_bsp_vectors[vector] = callback;
    }

    return err;
} /* End of function R_BSP_InterruptWrite() */

/**********************************************************************************************************************
 * Function Name: R_BSP_InterruptRead
 ******************************************************************************************************************//**
 * @brief Gets the callback for an interrupt if one is registered.
 * @param[in] vector Which interrupt to read the callback for.
 * @param[out] callback Pointer to where to store callback address.
 * @retval BSP_INT_SUCCESS Successful, callback address has been returned.
 * @retval BSP_INT_ERR_NO_REGISTERED_CALLBACK No valid callback has been registered for this interrupt source.
 * @details This function returns the callback function address for an interrupt if one has been registered. If a 
 * callback function has not been registered then an error is returned and nothing is stored to the callback address.
 */
bsp_int_err_t R_BSP_InterruptRead (bsp_int_src_t vector, bsp_int_cb_t * callback)
{
    bsp_int_err_t err;

    err = BSP_INT_SUCCESS;

    /* Check for valid address. */
    if (((uint32_t)g_bsp_vectors[vector] == (uint32_t)NULL) || ((uint32_t)g_bsp_vectors[vector] == (uint32_t)FIT_NO_FUNC))
    {
        err = BSP_INT_ERR_NO_REGISTERED_CALLBACK;
    }
    else
    {
        *callback = g_bsp_vectors[vector];
    }

    return err;
} /* End of function R_BSP_InterruptRead() */

/**********************************************************************************************************************
 * Function Name: R_BSP_InterruptControl
 ******************************************************************************************************************//**
 * @brief Controls various interrupt operations.
 * @param[in] vector Which interrupt to control for.\n
 * If the interrupt control commands is the BSP_INT_CMD_FIT_INTERRUPT_ENABLE or the BSP_INT_CMD_FIT_INTERRUPT_DISABLE 
 * commands, set BSP_INT_SRC_EMPTY to "vector" because no arguments are used.
 * @param[in] cmd Interrupt control command.
 * @param[in,out] pdata Pointer to the argument for each interrupt control command. Typecasted to void*. See typedef 
 * defines of bsp_int_ctrl_t. \n
 * Most of the interrupt control commands do not need the argument and take FIT_NO_PTR for 
 * this parameter. If the interrupt control command is the BSP_INT_CMD_GROUP_INTERRUPT_ENABLE command, set the 
 * interrupt priority level for group interrupts as the argument. If the interrupt control command is the 
 * BSP_INT_CMD_FIT_INTERRUPT_DISABLE command, set the address of a variable for saving the current processor interrupt 
 * priority level in the argument. If the interrupt control command is the BSP_INT_CMD_FIT_INTERRUPT_ENABLE command, 
 * set the address of a variable used in the BSP_INT_CMD_FIT_INTERRUPT_DISABLE command.
 * @retval BSP_INT_SUCCESS Successful.
 * @retval BSP_INT_ERR_NO_REGISTERED_CALLBACK No valid callback has been registered for this interrupt source.
 * @retval BSP_INT_ERR_INVALID_ARG The command passed is invalid.
 * @retval BSP_INT_ERR_UNSUPPORTED This processing is not supported.
 * @retval BSP_INT_ERR_GROUP_STILL_ENABLED Group interrupt request remains enabled.
 * @retval BSP_INT_ERR_INVALID_IPL Illegal IPL value input.
 * @details This function controls the interrupt callback function call and enabling/disabling interrupts such as bus 
 * error interrupt, floating-point exception, NMI pin interrupt, and group interrupts, and enabling/disabling 
 * interrupts by controlling the Processor Interrupt Priority Level. When BSP_INT_CMD_GROUP_INTERRUPT_ENABLE is set as 
 * the interrupt control command, the interrupt request (IER) for group interrupts is enabled and also the interrupt 
 * priority level is set. The interrupt priority level set must be higher than the current level. When 
 * BSP_INT_CMD_GROUP_INTERRUPT_DISABLE is set as the interrupt control command, the interrupt request (IER) for group 
 * interrupts is disabled. Note that the interrupt request (IER) for group interrupts cannot be disabled as long as 
 * all interrupt requests (GEN) caused by grouped interrupt sources are disabled. When 
 * BSP_INT_CMD_FIT_INTERRUPT_DISABLE is set as the interrupt control command, the current processor interrupt priority 
 * level (IPL) is saved to the address specified by pdata as an argument, and disables interrupts by controlling the 
 * IPL. The value of IPL to be set is the value of BSP_CFG_FIT_IPL_MAX. When BSP_INT_CMD_FIT_INTERRUPT_ENABLE is set 
 * as the interrupt control command, the interrupt is enabled by setting the value stored in the address specified by 
 * pdata to IPL. These two commands are valid only in supervisor mode. When BSP_INT_CMD_FIT_INTERRUPT_DISABLE and 
 * BSP_INT_CMD_FIT_INTERRUPT_ENABLE commands are executed in user mode, Controlling IPL is not executed and an error 
 * code BSP_INT_ERR_UNSUPPORTED is returned.
 * @note BSP_INT_CMD_FIT_INTERRUPT_DISABLE and BSP_INT_CMD_FIT_INTERRUPT_ENABLE commands can be used to secure 
 * atomicity of critical sections. However, these commands are valid only in supervisor mode. When these commands are 
 * executed in user mode, atomicity is not to secure.\n
 * See Section 5.15 in the application note for more information.
 */
bsp_int_err_t R_BSP_InterruptControl (bsp_int_src_t vector, bsp_int_cmd_t cmd, void * pdata)
{
    bsp_int_err_t       err;
    bsp_int_cb_args_t   cb_args;

    err = BSP_INT_SUCCESS;

#ifdef BSP_MCU_GROUP_INTERRUPT
    /* nothing */
#else
    /* This code is only used to remove compiler info messages about these parameters not being used. */
    INTERNAL_NOT_USED(pdata);
#endif

    switch (cmd)
    {
        case (BSP_INT_CMD_CALL_CALLBACK):

            /* Casting is valid because it matches the type to the right side or argument. */
            if (((uint32_t)g_bsp_vectors[vector] != (uint32_t)NULL) && ((uint32_t)g_bsp_vectors[vector] != (uint32_t)FIT_NO_FUNC))
            {
                /* Fill in callback info. */
                cb_args.vector = vector;

                g_bsp_vectors[vector](&cb_args);
            }
            else
            {
                err = BSP_INT_ERR_NO_REGISTERED_CALLBACK;
            }
            break;

        case (BSP_INT_CMD_INTERRUPT_ENABLE):
            err = bsp_interrupt_enable_disable(vector, true);
            break;

        case (BSP_INT_CMD_INTERRUPT_DISABLE):
            err = bsp_interrupt_enable_disable(vector, false);
            break;

#ifdef BSP_MCU_GROUP_INTERRUPT
        case (BSP_INT_CMD_GROUP_INTERRUPT_ENABLE):

            /* Casting is valid because it matches the type to the right side or argument. */
            if(((uint32_t)NULL != (uint32_t)pdata) && ((uint32_t)FIT_NO_FUNC != (uint32_t)pdata))
            {
                /* Casting is valid because it matches the type to the right side or argument. */
                err = bsp_gr_int_enable_disable(vector, true, ((bsp_int_ctrl_t *)pdata)->ipl);
            }
            else
            {
                 err = BSP_INT_ERR_INVALID_ARG;
            }
            break;

        case (BSP_INT_CMD_GROUP_INTERRUPT_DISABLE):
            err = bsp_gr_int_enable_disable(vector, false, 0);
            break;
#endif

        case (BSP_INT_CMD_FIT_INTERRUPT_ENABLE):

            /* Casting is valid because it matches the type to the right side or argument. */
            err = bsp_fit_interrupts_control(true, (bsp_int_ctrl_t *)pdata);
            break;

        case (BSP_INT_CMD_FIT_INTERRUPT_DISABLE):

            /* Casting is valid because it matches the type to the right side or argument. */
            err = bsp_fit_interrupts_control(false, (bsp_int_ctrl_t *)pdata);
            break;

        default:
            err = BSP_INT_ERR_INVALID_ARG;
            break;
    }

    return err;
} /* End of function R_BSP_InterruptControl() */

/***********************************************************************************************************************
* Function Name: bsp_fit_interrupts_control
* Description  : 
* Arguments    : enable -
*                    Whether to enable or disable the interrupt.
*                pdata -
*                    Pointer to variable for saves ipl or restore ipl.
* Return Value : BSP_INT_SUCCESS -
*                    Interrupt enabled or disabled.
*                BSP_INT_ERR_INVALID_ARG -
*                    Invalid argument input.
*                BSP_INT_ERR_INVALID_IPL -
*                    Invalid IPL input.
*                BSP_INT_ERR_UNSUPPORTED -
*                    This processing is not supported. (Executed in user mode.)
***********************************************************************************************************************/
static bsp_int_err_t bsp_fit_interrupts_control (bool enable, bsp_int_ctrl_t * pdata)
{
    bsp_int_err_t       err;
    uint32_t            pmode;
    bool                ret;
    uint32_t            ipl_value;

    /* Casting is valid because it matches the type to the right side or argument. */
    if(((uint32_t)NULL != (uint32_t)pdata) && ((uint32_t)FIT_NO_FUNC != (uint32_t)pdata))
    {
        /* Read current processor mode. */
        pmode = (R_BSP_GET_PSW() & 0x00100000);

        /* Check current processor mode. */
        if (0 == pmode)
        {
            err = BSP_INT_SUCCESS;

            if (true == enable)
            {
                ipl_value = pdata->ipl;
            }
            else
            {
                 /* Get the current Processor Interrupt Priority Level (IPL) and save IPL value. */
                pdata->ipl = R_BSP_CpuInterruptLevelRead();

                /* Set IPL to the maximum value to disable all interrupts,
                 * so the scheduler can not be scheduled in critical region.
                 * Note: Please set this macro more than IPR for other FIT module interrupts. */
                ipl_value = BSP_CFG_FIT_IPL_MAX;
            }

            if (pdata->ipl < BSP_CFG_FIT_IPL_MAX)
            {
                ret = R_BSP_CpuInterruptLevelWrite(ipl_value);
                if (false == ret)
                {
                    err = BSP_INT_ERR_INVALID_IPL;
                }
            }
            else
            {
                err = BSP_INT_ERR_INVALID_IPL;
            }
        }
        else
        {
            err = BSP_INT_ERR_UNSUPPORTED;
        }
    }
    else
    {
        err = BSP_INT_ERR_INVALID_ARG;
    }

    return err;
} /* End of function bsp_fit_interrupts_control() */

#ifdef BSP_MCU_GROUP_INTERRUPT
/***********************************************************************************************************************
* Function Name: bsp_gr_int_enable_disable
* Description  : Either enables or disables a group interrupt. If a group interrupt is called multiple times to be
*                enabled then it will use the highest given IPL. A group interrupt will only be disabled when all
*                interrupt sources for that group are already disabled.
* Arguments    : vector -
*                    An interrupt source inside the group that is to be enabled/disabled.
*                enable -
*                    Whether to enable or disable the interrupt.
*                ipl -
*                    If enabling a group interrupt, what IPL to use.
* Return Value : BSP_INT_SUCCESS -
*                    Interrupt enabled or disabled.
*                BSP_INT_ERR_INVALID_ARG -
*                    Invalid IPL or vector
*                BSP_INT_ERR_GROUP_STILL_ENABLED -
*                    Not all group interrupts were disabled so group interrupt was not disabled.
***********************************************************************************************************************/
static bsp_int_err_t bsp_gr_int_enable_disable (bsp_int_src_t vector, bool enable, uint32_t ipl)
{
    bsp_int_err_t err = BSP_INT_SUCCESS;

#if BSP_CFG_PARAM_CHECKING_ENABLE == 1
    /* If interrupt is going to be enabled, verify that IPL is valid. */
    if ((true == enable) && ((BSP_MCU_IPL_MIN == ipl) || (ipl > BSP_MCU_IPL_MAX)))
    {
        return BSP_INT_ERR_INVALID_ARG;
    }
#endif

    if ((vector > BSP_INT_SRC_GR_INT_IE0_TOP) && (vector < BSP_INT_SRC_GR_INT_BE0_TOP))
    {
        /* Group IE0. */
#ifdef BSP_MCU_GROUP_INTERRUPT_IE0
        if (true == enable)
        {
            R_BSP_InterruptRequestDisable(VECT(ICU, GROUPIE0));

            /* Casting is valid because it matches the type to the right side or argument. */
            IR(ICU, GROUPIE0)  = 0;

            /* Casting is valid because it matches the type to the right side or argument. */
            IPR(ICU, GROUPIE0) = (uint8_t)((ipl > IPR(ICU, GROUPIE0)) ? ipl : IPR(ICU, GROUPIE0));
            R_BSP_InterruptRequestEnable(VECT(ICU, GROUPIE0));
        }
        else
        {
            /* Check to make sure all interrupt sources are already disabled for this group. */
            if (0 == ICU.GENIE0.LONG)
            {
                R_BSP_InterruptRequestDisable(VECT(ICU, GROUPIE0));

                /* Casting is valid because it matches the type to the right side or argument. */
                IPR(ICU, GROUPIE0) = 0;
            }
            else
            {
                err = BSP_INT_ERR_GROUP_STILL_ENABLED;
            }
        }
#else /* BSP_MCU_GROUP_INTERRUPT_IE0 */
        err = BSP_INT_ERR_INVALID_ARG;
#endif /* BSP_MCU_GROUP_INTERRUPT_IE0 */
    }
    else if ((vector > BSP_INT_SRC_GR_INT_BE0_TOP) && (vector < BSP_INT_SRC_GR_INT_BL0_TOP))
    {
        /* Group BE0. */
#ifdef BSP_MCU_GROUP_INTERRUPT_BE0
        if (true == enable)
        {
            R_BSP_InterruptRequestDisable(VECT(ICU, GROUPBE0));

            /* Casting is valid because it matches the type to the right side or argument. */
            IR(ICU, GROUPBE0)  = 0;

            /* Casting is valid because it matches the type to the right side or argument. */
            IPR(ICU, GROUPBE0) = (uint8_t)((ipl > IPR(ICU, GROUPBE0)) ? ipl : IPR(ICU, GROUPBE0));
            R_BSP_InterruptRequestEnable(VECT(ICU, GROUPBE0));
        }
        else
        {
            /* Check to make sure all interrupt sources are already disabled for this group. */
            if (0 == ICU.GENBE0.LONG)
            {
                R_BSP_InterruptRequestDisable(VECT(ICU, GROUPBE0));

                /* Casting is valid because it matches the type to the right side or argument. */
                IPR(ICU, GROUPBE0) = 0;
            }
            else
            {
                err = BSP_INT_ERR_GROUP_STILL_ENABLED;
            }
        }
#else /* BSP_MCU_GROUP_INTERRUPT_BE0 */
        err = BSP_INT_ERR_INVALID_ARG;
#endif /* BSP_MCU_GROUP_INTERRUPT_BE0 */
    }
    else if ((vector > BSP_INT_SRC_GR_INT_BL0_TOP) && (vector < BSP_INT_SRC_GR_INT_BL1_TOP))
    {
        /* Group BL0. */
#ifdef BSP_MCU_GROUP_INTERRUPT_BL0
        if (true == enable)
        {
            R_BSP_InterruptRequestDisable(VECT(ICU, GROUPBL0));

            /* Casting is valid because it matches the type to the right side or argument. */
            IR(ICU, GROUPBL0)  = 0;

            /* Casting is valid because it matches the type to the right side or argument. */
            IPR(ICU, GROUPBL0) = (uint8_t)((ipl > IPR(ICU, GROUPBL0)) ? ipl : IPR(ICU, GROUPBL0));
            R_BSP_InterruptRequestEnable(VECT(ICU, GROUPBL0));
        }
        else
        {
            /* Check to make sure all interrupt sources are already disabled for this group. */
            if (0 == ICU.GENBL0.LONG)
            {
                R_BSP_InterruptRequestDisable(VECT(ICU, GROUPBL0));

                /* Casting is valid because it matches the type to the right side or argument. */
                IPR(ICU, GROUPBL0) = 0;
            }
            else
            {
                err = BSP_INT_ERR_GROUP_STILL_ENABLED;
            }
        }
#else /* BSP_MCU_GROUP_INTERRUPT_BL0 */
        err = BSP_INT_ERR_INVALID_ARG;
#endif /* BSP_MCU_GROUP_INTERRUPT_BL0 */
    }
    else if ((vector > BSP_INT_SRC_GR_INT_BL1_TOP) && (vector < BSP_INT_SRC_GR_INT_BL2_TOP))
    {
        /* Group BL1. */
#ifdef BSP_MCU_GROUP_INTERRUPT_BL1
        if (true == enable)
        {
            R_BSP_InterruptRequestDisable(VECT(ICU, GROUPBL1));

            /* Casting is valid because it matches the type to the right side or argument. */
            IR(ICU, GROUPBL1)  = 0;

            /* Casting is valid because it matches the type to the right side or argument. */
            IPR(ICU, GROUPBL1) = (uint8_t)((ipl > IPR(ICU, GROUPBL1)) ? ipl : IPR(ICU, GROUPBL1));
            R_BSP_InterruptRequestEnable(VECT(ICU, GROUPBL1));
        }
        else
        {
            /* Check to make sure all interrupt sources are already disabled for this group. */
            if (0 == ICU.GENBL1.LONG)
            {
                R_BSP_InterruptRequestDisable(VECT(ICU, GROUPBL1));

                /* Casting is valid because it matches the type to the right side or argument. */
                IPR(ICU, GROUPBL1) = 0;
            }
            else
            {
                err = BSP_INT_ERR_GROUP_STILL_ENABLED;
            }
        }
#else /* BSP_MCU_GROUP_INTERRUPT_BL1 */
        err = BSP_INT_ERR_INVALID_ARG;
#endif /* BSP_MCU_GROUP_INTERRUPT_BL1 */
    }
    else if ((vector > BSP_INT_SRC_GR_INT_BL2_TOP) && (vector < BSP_INT_SRC_GR_INT_AL0_TOP))
    {
        /* Group BL2. */
#ifdef BSP_MCU_GROUP_INTERRUPT_BL2
        if (true == enable)
        {
            R_BSP_InterruptRequestDisable(VECT(ICU, GROUPBL2));

            /* Casting is valid because it matches the type to the right side or argument. */
            IR(ICU, GROUPBL2)  = 0;

            /* Casting is valid because it matches the type to the right side or argument. */
            IPR(ICU, GROUPBL2) = (uint8_t)((ipl > IPR(ICU, GROUPBL2)) ? ipl : IPR(ICU, GROUPBL2));
            R_BSP_InterruptRequestEnable(VECT(ICU, GROUPBL2));
        }
        else
        {
            /* Check to make sure all interrupt sources are already disabled for this group. */
            if (0 == ICU.GENBL2.LONG)
            {
                R_BSP_InterruptRequestDisable(VECT(ICU, GROUPBL2));

                /* Casting is valid because it matches the type to the right side or argument. */
                IPR(ICU, GROUPBL2) = 0;
            }
            else
            {
                err = BSP_INT_ERR_GROUP_STILL_ENABLED;
            }
        }
#else /* BSP_MCU_GROUP_INTERRUPT_BL2 */
        err = BSP_INT_ERR_INVALID_ARG;
#endif /* BSP_MCU_GROUP_INTERRUPT_BL2 */
    }
    else if ((vector > BSP_INT_SRC_GR_INT_AL0_TOP) && (vector < BSP_INT_SRC_GR_INT_AL1_TOP))
    {
        /* Group AL0. */
#ifdef BSP_MCU_GROUP_INTERRUPT_AL0
        if (true == enable)
        {
            R_BSP_InterruptRequestDisable(VECT(ICU, GROUPAL0));

            /* Casting is valid because it matches the type to the right side or argument. */
            IR(ICU, GROUPAL0)  = 0;

            /* Casting is valid because it matches the type to the right side or argument. */
            IPR(ICU, GROUPAL0) = (uint8_t)((ipl > IPR(ICU, GROUPAL0)) ? ipl : IPR(ICU, GROUPAL0));
            R_BSP_InterruptRequestEnable(VECT(ICU, GROUPAL0));
        }
        else
        {
            /* Check to make sure all interrupt sources are already disabled for this group. */
            if (0 == ICU.GENAL0.LONG)
            {
                R_BSP_InterruptRequestDisable(VECT(ICU, GROUPAL0));

                /* Casting is valid because it matches the type to the right side or argument. */
                IPR(ICU, GROUPAL0) = 0;
            }
            else
            {
                err = BSP_INT_ERR_GROUP_STILL_ENABLED;
            }
        }
#else /* BSP_MCU_GROUP_INTERRUPT_AL0 */
        err = BSP_INT_ERR_INVALID_ARG;
#endif /* BSP_MCU_GROUP_INTERRUPT_AL0 */
    }
    else if ((vector > BSP_INT_SRC_GR_INT_AL1_TOP) && (vector < BSP_INT_SRC_GR_INT_END))
    {
        /* Group AL1. */
#ifdef BSP_MCU_GROUP_INTERRUPT_AL1
        if (true == enable)
        {
            R_BSP_InterruptRequestDisable(VECT(ICU, GROUPAL1));

            /* Casting is valid because it matches the type to the right side or argument. */
            IR(ICU, GROUPAL1)  = 0;

            /* Casting is valid because it matches the type to the right side or argument. */
            IPR(ICU, GROUPAL1) = (uint8_t)((ipl > IPR(ICU, GROUPAL1)) ? ipl : IPR(ICU, GROUPAL1));
            R_BSP_InterruptRequestEnable(VECT(ICU, GROUPAL1));
        }
        else
        {
            /* Check to make sure all interrupt sources are already disabled for this group. */
            if (0 == ICU.GENAL1.LONG)
            {
                R_BSP_InterruptRequestDisable(VECT(ICU, GROUPAL1));

                /* Casting is valid because it matches the type to the right side or argument. */
                IPR(ICU, GROUPAL1) = 0;
            }
            else
            {
                err = BSP_INT_ERR_GROUP_STILL_ENABLED;
            }
        }
#else /* BSP_MCU_GROUP_INTERRUPT_AL1 */
        err = BSP_INT_ERR_INVALID_ARG;
#endif /* BSP_MCU_GROUP_INTERRUPT_AL1 */
    }
    else
    {
        /* Vector given was not part of a group. */
        err = BSP_INT_ERR_INVALID_ARG;
    }

    return err;
} /* End of function bsp_gr_int_enable_disable() */
#endif /* BSP_MCU_GROUP_INTERRUPT */

/* When using the user startup program, disable the following code. */
#if BSP_CFG_STARTUP_DISABLE == 0

#ifdef BSP_MCU_EXCEP_SUPERVISOR_INST_ISR
/***********************************************************************************************************************
* Function name: excep_supervisor_inst_isr
* Description  : Supervisor Instruction Violation ISR
* Arguments    : none
* Return Value : none
***********************************************************************************************************************/
R_BSP_ATTRIB_INTERRUPT void excep_supervisor_inst_isr(void)
{
    /* If user has registered a callback for this exception then call it. */
    R_BSP_InterruptControl(BSP_INT_SRC_EXC_SUPERVISOR_INSTR, BSP_INT_CMD_CALL_CALLBACK, FIT_NO_PTR);
} /* End of function excep_supervisor_inst_isr() */
#endif

#ifdef BSP_MCU_EXCEP_ACCESS_ISR
/***********************************************************************************************************************
* Function name: excep_access_isr
* Description  : Access exception ISR
* Arguments    : none
* Return Value : none
***********************************************************************************************************************/
R_BSP_ATTRIB_INTERRUPT void excep_access_isr(void)
{
    /* If user has registered a callback for this exception then call it. */
    R_BSP_InterruptControl(BSP_INT_SRC_EXC_ACCESS, BSP_INT_CMD_CALL_CALLBACK, FIT_NO_PTR);
} /* End of function excep_access_isr() */
#endif

#ifdef BSP_MCU_EXCEP_UNDEFINED_INST_ISR
/***********************************************************************************************************************
* Function name: excep_undefined_inst_isr
* Description  : Undefined instruction exception ISR
* Arguments    : none
* Return Value : none
***********************************************************************************************************************/
R_BSP_ATTRIB_INTERRUPT void excep_undefined_inst_isr(void)
{
    /* If user has registered a callback for this exception then call it. */
    R_BSP_InterruptControl(BSP_INT_SRC_EXC_UNDEFINED_INSTR, BSP_INT_CMD_CALL_CALLBACK, FIT_NO_PTR);
} /* End of function excep_undefined_inst_isr() */
#endif

#ifdef BSP_MCU_EXCEP_FLOATING_POINT_ISR
/***********************************************************************************************************************
* Function name: excep_floating_point_isr
* Description  : Floating point exception ISR
* Arguments    : none
* Return Value : none
***********************************************************************************************************************/
R_BSP_ATTRIB_INTERRUPT void excep_floating_point_isr(void)
{
#ifdef __FPU
    /* Used for reading FPSW register. */
    uint32_t tmp_fpsw;
#endif

    /* If user has registered a callback for this exception then call it. */
    R_BSP_InterruptControl(BSP_INT_SRC_EXC_FPU, BSP_INT_CMD_CALL_CALLBACK, FIT_NO_PTR);

#ifdef __FPU
    /* Get current FPSW. */
    tmp_fpsw = (uint32_t)R_BSP_GET_FPSW();

    /* Clear only the FPU exception flags. */
    R_BSP_SET_FPSW(tmp_fpsw & ((uint32_t)~BSP_PRV_FPU_CAUSE_FLAGS));
#endif
} /* End of function excep_floating_point_isr() */
#endif

#ifdef BSP_MCU_NON_MASKABLE_ISR
/***********************************************************************************************************************
* Function name: non_maskable_isr
* Description  : Non-maskable interrupt ISR
* Arguments    : none
* Return Value : none
***********************************************************************************************************************/
R_BSP_ATTRIB_INTERRUPT void non_maskable_isr(void)
{
    /* Determine what is the cause of this interrupt. */

#ifdef BSP_MCU_NMI_EXC_NMI_PIN
    /* EXC_NMI_PIN */
    if ((1 == ICU.NMISR.BIT.NMIST) && (1 == ICU.NMIER.BIT.NMIEN))
    {
        /* NMI pin interrupt is requested. */
        R_BSP_InterruptControl(BSP_INT_SRC_EXC_NMI_PIN, BSP_INT_CMD_CALL_CALLBACK, FIT_NO_PTR);

        /* Clear NMI pin interrupt flag. */
        ICU.NMICLR.BIT.NMICLR = 1;
    }
#endif

#ifdef BSP_MCU_NMI_OSC_STOP_DETECT
    /* OSC_STOP_DETECT */
    if ((1 == ICU.NMISR.BIT.OSTST) && (1 == ICU.NMIER.BIT.OSTEN))
    {
        /* Oscillation stop detection interrupt is requested. */
        R_BSP_InterruptControl(BSP_INT_SRC_OSC_STOP_DETECT, BSP_INT_CMD_CALL_CALLBACK, FIT_NO_PTR);

        /* Clear oscillation stop detect flag. */
        ICU.NMICLR.BIT.OSTCLR = 1;
    }
#endif

#ifdef BSP_MCU_NMI_WDT_ERROR
    /* WDT_ERROR */
    if ((1 == ICU.NMISR.BIT.WDTST) && (1 == ICU.NMIER.BIT.WDTEN))
    {
        /* WDT underflow/refresh error interrupt is requested. */
        R_BSP_InterruptControl(BSP_INT_SRC_WDT_ERROR, BSP_INT_CMD_CALL_CALLBACK, FIT_NO_PTR);

        /* Clear WDT flag. */
        ICU.NMICLR.BIT.WDTCLR = 1;
    }
#endif

#ifdef BSP_MCU_NMI_LVD
    /* LVD */
    if ((1 == ICU.NMISR.BIT.LVDST) && (1 == ICU.NMIER.BIT.LVDEN))
    {
        /* Voltage monitoring 1 interrupt is requested. */
        R_BSP_InterruptControl(BSP_INT_SRC_LVD1, BSP_INT_CMD_CALL_CALLBACK, FIT_NO_PTR);
    }
#endif

#ifdef BSP_MCU_NMI_IWDT_ERROR
    /* IWDT_ERROR */
    if ((1 == ICU.NMISR.BIT.IWDTST) && (1 == ICU.NMIER.BIT.IWDTEN))
    {
        /* IWDT underflow/refresh error interrupt is requested. */
        R_BSP_InterruptControl(BSP_INT_SRC_IWDT_ERROR, BSP_INT_CMD_CALL_CALLBACK, FIT_NO_PTR);

        /* Clear IWDT flag. */
        ICU.NMICLR.BIT.IWDTCLR = 1;
    }
#endif

#ifdef BSP_MCU_NMI_LVD1
    /* LVD1 */
    if ((1 == ICU.NMISR.BIT.LVD1ST) && (1 == ICU.NMIER.BIT.LVD1EN))
    {
        /* Voltage monitoring 1 interrupt is requested. */
        R_BSP_InterruptControl(BSP_INT_SRC_LVD1, BSP_INT_CMD_CALL_CALLBACK, FIT_NO_PTR);

        /* Clear LVD1 flag. */
        ICU.NMICLR.BIT.LVD1CLR = 1;
    }
#endif

#ifdef BSP_MCU_NMI_LVD2
    /* LVD2 */
    if ((1 == ICU.NMISR.BIT.LVD2ST) && (1 == ICU.NMIER.BIT.LVD2EN))
    {
        /* Voltage monitoring 1 interrupt is requested. */
        R_BSP_InterruptControl(BSP_INT_SRC_LVD2, BSP_INT_CMD_CALL_CALLBACK, FIT_NO_PTR);

        /* Clear LVD2 flag. */
        ICU.NMICLR.BIT.LVD2CLR = 1;
    }
#endif

#ifdef BSP_MCU_NMI_VBATT
    /* VBATT */
    if ((1 == ICU.NMISR.BIT.VBATST) && (1 == ICU.NMIER.BIT.VBATEN))
    {
        /* VBATT monitoring interrupt is requested. */
        R_BSP_InterruptControl(BSP_INT_SRC_VBATT, BSP_INT_CMD_CALL_CALLBACK, FIT_NO_PTR);

        /* Clear LVD2 flag. */
        ICU.NMICLR.BIT.VBATCLR = 1;
    }
#endif

#ifdef BSP_MCU_NMI_ECCRAM
    /* ECCRAM */
    if ((1 == ICU.NMISR.BIT.ECCRAMST) && (1 == ICU.NMIER.BIT.ECCRAMEN))
    {
        if(1 == ECCRAM.ECCRAM1STS.BIT.ECC1ERR)
        {
            /* ECCRAM Error interrupt is requested. */
            R_BSP_InterruptControl(BSP_INT_SRC_ECCRAM_1BIT, BSP_INT_CMD_CALL_CALLBACK, FIT_NO_PTR);

            /* Clear ECCRAM flags. */
            ECCRAM.ECCRAM1STS.BIT.ECC1ERR = 0;
        }

        if(1 == ECCRAM.ECCRAM2STS.BIT.ECC2ERR)
        {
            /* ECCRAM Error interrupt is requested. */
            R_BSP_InterruptControl(BSP_INT_SRC_ECCRAM_2BIT, BSP_INT_CMD_CALL_CALLBACK, FIT_NO_PTR);

            /* Clear ECCRAM flags. */
            ECCRAM.ECCRAM2STS.BIT.ECC2ERR = 0;
        }
    }
#endif

#ifdef BSP_MCU_NMI_RAM
    /* RAM */
    if ((1 == ICU.NMISR.BIT.RAMST) && (1 == ICU.NMIER.BIT.RAMEN))
    {
        /* Casting is valid because it matches the type to the right side or argument. */
        if(1 == RAM.RAMSTS.BIT.RAMERR)
        {
            /* RAM Error interrupt is requested. */
            R_BSP_InterruptControl(BSP_INT_SRC_RAM, BSP_INT_CMD_CALL_CALLBACK, FIT_NO_PTR);

            /* Clear RAM flags. */
            RAM.RAMSTS.BIT.RAMERR = 0;
        }
    #ifdef BSP_MCU_NMI_RAM_EXRAM

        /* Casting is valid because it matches the type to the right side or argument. */
        if(1 == RAM.EXRAMSTS.BIT.EXRAMERR)
        {
            /* Expansion RAM Error interrupt is requested. */
            R_BSP_InterruptControl(BSP_INT_SRC_EXRAM, BSP_INT_CMD_CALL_CALLBACK, FIT_NO_PTR);

            /* Clear Expansion RAM flags. */
            RAM.EXRAMSTS.BIT.EXRAMERR = 0;
        }
    #endif /* BSP_MCU_NMI_RAM_EXRAM */

    #ifdef BSP_MCU_NMI_RAM_ECCRAM

        /* Casting is valid because it matches the type to the right side or argument. */
        if(1 == RAM.ECCRAM1STS.BIT.ECC1ERR)
        {
            /* ECCRAM Error interrupt is requested. */
            R_BSP_InterruptControl(BSP_INT_SRC_ECCRAM_1BIT, BSP_INT_CMD_CALL_CALLBACK, FIT_NO_PTR);

            /* Clear ECCRAM flags. */
            RAM.ECCRAM1STS.BIT.ECC1ERR = 0;
        }

        /* Casting is valid because it matches the type to the right side or argument. */
        if(1 == RAM.ECCRAM2STS.BIT.ECC2ERR)
        {
            /* ECCRAM Error interrupt is requested. */
            R_BSP_InterruptControl(BSP_INT_SRC_ECCRAM_2BIT, BSP_INT_CMD_CALL_CALLBACK, FIT_NO_PTR);

            /* Clear ECCRAM flags. */
            RAM.ECCRAM2STS.BIT.ECC2ERR = 0;
        }
    #endif /* BSP_MCU_NMI_RAM_ECCRAM */
    }
#endif /* BSP_MCU_NMI_RAM */

#ifdef BSP_MCU_NMI_EXNMI
    /* EXNMI */
    if ((1 == ICU.NMISR.BIT.EXNMIST) && (1 == ICU.NMIER.BIT.EXNMIEN))
    {
    #ifdef BSP_MCU_NMI_EXNMI_RAM

        /* Casting is valid because it matches the type to the right side or argument. */
        if ((1 == ICU.EXNMISR.BIT.RAMST) && (1 == ICU.EXNMIER.BIT.RAMEN))
        {

            /* Casting is valid because it matches the type to the right side or argument. */
            if(1 == RAM.RAMSTS.BIT.RAMERR)
            {
                /* RAM Error interrupt is requested. */
                R_BSP_InterruptControl(BSP_INT_SRC_RAM, BSP_INT_CMD_CALL_CALLBACK, FIT_NO_PTR);

                /* Clear RAM flags. */
                RAM.RAMSTS.BIT.RAMERR = 0;
            }
        #ifdef BSP_MCU_NMI_EXNMI_RAM_EXRAM

            /* Casting is valid because it matches the type to the right side or argument. */
            if(1 == RAM.EXRAMSTS.BIT.EXRAMERR)
            {
                /* Expansion RAM Error interrupt is requested. */
                R_BSP_InterruptControl(BSP_INT_SRC_EXRAM, BSP_INT_CMD_CALL_CALLBACK, FIT_NO_PTR);

                /* Clear Expansion RAM flags. */
                RAM.EXRAMSTS.BIT.EXRAMERR = 0;
            }
        #endif /* BSP_MCU_NMI_EXNMI_RAM_EXRAM */

        #ifdef BSP_MCU_NMI_EXNMI_RAM_ECCRAM

            /* Casting is valid because it matches the type to the right side or argument. */
            if(1 == ECCRAM.ECCRAM1STS.BIT.ECC1ERR)
            {
                /* ECCRAM Error interrupt is requested. */
                R_BSP_InterruptControl(BSP_INT_SRC_ECCRAM_1BIT, BSP_INT_CMD_CALL_CALLBACK, FIT_NO_PTR);

                /* Clear ECCRAM flags. */
                ECCRAM.ECCRAM1STS.BIT.ECC1ERR = 0;
            }

            /* Casting is valid because it matches the type to the right side or argument. */
            if(1 == ECCRAM.ECCRAM2STS.BIT.ECC2ERR)
            {
                /* ECCRAM Error interrupt is requested. */
                R_BSP_InterruptControl(BSP_INT_SRC_ECCRAM_2BIT, BSP_INT_CMD_CALL_CALLBACK, FIT_NO_PTR);

                /* Clear ECCRAM flags. */
                ECCRAM.ECCRAM2STS.BIT.ECC2ERR = 0;
            }
        #endif /* BSP_MCU_NMI_EXNMI_RAM_ECCRAM */
        }
    #endif /* BSP_MCU_NMI_EXNMI_RAM */

    #ifdef BSP_MCU_NMI_EXNMI_DPFPUEX

    /* Casting is valid because it matches the type to the right side or argument. */
    if ((1 == ICU.EXNMISR.BIT.DPFPUST) && (1 == ICU.EXNMIER.BIT.DPFPUEN))
        {
            /* Double-Precision Floating-Point Exception interrupt is requested. */
            R_BSP_InterruptControl(BSP_INT_SRC_DPFPUEX, BSP_INT_CMD_CALL_CALLBACK, FIT_NO_PTR);

            /* Clear DPFPUST flag. */
            ICU.EXNMICLR.BIT.DPFPUCLR = 1;
        }
    #endif /* BSP_MCU_NMI_EXNMI_DPFPUEX */
    }
#endif /* BSP_MCU_NMI_EXNMI */

    /* WAIT_LOOP */
    while(1)
    {
        /* Infinite loop. Return from Non-maskable interrupt handlling routine is prohibited.
           Never use the non-maskable interrupt with an attempt to return to the program that was being executed at 
           the time of interrupt generation after the exception handling routine is ended.
         */
         R_BSP_NOP();
    }
} /* End of function non_maskable_isr() */
#endif /* BSP_MCU_NON_MASKABLE_ISR */

#ifdef BSP_MCU_UNDEFINED_INTERRUPT_SOURCE_ISR
/***********************************************************************************************************************
* Function name: undefined_interrupt_source_isr
* Description  : All undefined interrupt vectors point to this function.
*                Set a breakpoint in this function to determine which source is creating unwanted interrupts.
* Arguments    : none
* Return Value : none
***********************************************************************************************************************/
R_BSP_ATTRIB_INTERRUPT void undefined_interrupt_source_isr(void)
{
    /* If user has registered a callback for this exception then call it. */
    R_BSP_InterruptControl(BSP_INT_SRC_UNDEFINED_INTERRUPT, BSP_INT_CMD_CALL_CALLBACK, FIT_NO_PTR);
} /* End of function undefined_interrupt_source_isr() */
#endif

#ifdef BSP_MCU_BUS_ERROR_ISR
/***********************************************************************************************************************
* Function name: bus_error_isr
* Description  : By default, this demo code enables the Bus Error Interrupt. This interrupt will fire if the user tries 
*                to access code or data from one of the reserved areas in the memory map, including the areas covered 
*                by disabled chip selects. A nop() statement is included here as a convenient place to set a breakpoint 
*                during debugging and development, and further handling should be added by the user for their 
*                application.
* Arguments    : none
* Return value : none
***********************************************************************************************************************/
R_BSP_ATTRIB_INTERRUPT void bus_error_isr (void)
{
    /* Clear the bus error */
    BSC.BERCLR.BIT.STSCLR = 1;

    /* 
        To find the address that was accessed when the bus error occurred, read the register BSC.BERSR2.WORD.
        The upper 13 bits of this register contain the upper 13-bits of the offending address (in 512K byte units)
    */

    /* If user has registered a callback for this exception then call it. */
    R_BSP_InterruptControl(BSP_INT_SRC_BUS_ERROR, BSP_INT_CMD_CALL_CALLBACK, FIT_NO_PTR);
} /* End of function bus_error_isr() */
#endif

#endif /* BSP_CFG_STARTUP_DISABLE == 0 */

