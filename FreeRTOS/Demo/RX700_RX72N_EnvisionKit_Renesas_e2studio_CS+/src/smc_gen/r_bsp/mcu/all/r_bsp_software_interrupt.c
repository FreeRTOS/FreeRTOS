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
* Copyright (C) 2019 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/
/***********************************************************************************************************************
* File Name    : r_bsp_software_interrupt.c
* Description  : This module implements software interrupt specific functions.
***********************************************************************************************************************/
/**********************************************************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 08.10.2019 1.00     First Release
*         : 10.12.2019 1.01     Modified comment.
***********************************************************************************************************************/

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
#include "platform.h"

/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/
#define BSP_PRV_SWINT_TASK_BUFFER_MAX               (BSP_CFG_SWINT_TASK_BUFFER_NUMBER + 1)
#define BSP_PRV_SWINT_ACCESS_ACCEPTATION            (1)
#define BSP_PRV_SWINT_ACCESS_REJECTION              (0)
#define BSP_PRV_SWINT_ENABLE_NESTED_INTERRUPT       (1)
#define BSP_PRV_SWINT_DISABLE_NESTED_INTERRUPT      (0)

/***********************************************************************************************************************
Typedef definitions
***********************************************************************************************************************/

/***********************************************************************************************************************
Exported global variables (to be accessed by other files)
***********************************************************************************************************************/
#if (defined(BSP_CFG_SWINT_UNIT1_ENABLE) && (BSP_CFG_SWINT_UNIT1_ENABLE == 1)) || \
    (defined(BSP_CFG_SWINT_UNIT2_ENABLE) && (BSP_CFG_SWINT_UNIT2_ENABLE == 1))

st_bsp_swint_access_control_t g_bsp_swint_access_ctrl[BSP_SWINT_UNIT_MAX];

/***********************************************************************************************************************
Private global variables and functions
***********************************************************************************************************************/
/* Interrupt functions */
#if (defined(BSP_CFG_SWINT_UNIT1_ENABLE) && (BSP_CFG_SWINT_UNIT1_ENABLE == 1))
R_BSP_PRAGMA_STATIC_INTERRUPT(bsp_swint_isr, VECT(ICU, SWINT))
#endif /* (defined(BSP_CFG_SWINT_UNIT1_ENABLE) && (BSP_CFG_SWINT_UNIT1_ENABLE == 1)) */
#if (defined(BSP_CFG_SWINT_UNIT2_ENABLE) && (BSP_CFG_SWINT_UNIT2_ENABLE == 1))
R_BSP_PRAGMA_STATIC_INTERRUPT(bsp_swint2_isr, VECT(ICU, SWINT2))
#endif /* (defined(BSP_CFG_SWINT_UNIT2_ENABLE) && (BSP_CFG_SWINT_UNIT2_ENABLE == 1)) */

/* Functions */
static void bsp_swint_get_interrupt_information(e_bsp_swint_unit_t unit,  void * const p_args);
static void bsp_swint_enable_interrupt(e_bsp_swint_unit_t unit);
static void bsp_swint_disable_interrupt(e_bsp_swint_unit_t unit);
static e_bsp_swint_err_t bsp_swint_set_interrupt_priority(e_bsp_swint_unit_t unit,  void * const p_args);
static void bsp_swint_set_interrupt_request(e_bsp_swint_unit_t unit);
static void bsp_swint_clear_interrupt_request(e_bsp_swint_unit_t unit);
static void bsp_swint_enable_nested_interrupt(e_bsp_swint_unit_t unit);
static void bsp_swint_disable_nested_interrupt(e_bsp_swint_unit_t unit);
static e_bsp_swint_err_t bsp_swint_clear_task(e_bsp_swint_unit_t unit, void * const p_args);
static e_bsp_swint_err_t bsp_swint_clear_all_task(e_bsp_swint_unit_t unit);
static void bsp_swint_get_all_task_status(e_bsp_swint_unit_t unit, void * const p_args);
static bool bsp_swint_get_access_control(e_bsp_swint_unit_t unit, st_bsp_swint_access_control_t * const p_args);
static bool bsp_swint_release_access_control(e_bsp_swint_unit_t unit, st_bsp_swint_access_control_t * const p_args);
static void bsp_swint_execute_task(e_bsp_swint_unit_t unit);
static void bsp_swint_dummy_task(void * p_dummy_context);

/* Variables */
static st_bsp_swint_task_t s_bsp_swint_task[BSP_SWINT_UNIT_MAX][BSP_PRV_SWINT_TASK_BUFFER_MAX];
static uint8_t s_bsp_swint_buf_used[BSP_SWINT_UNIT_MAX];
static uint8_t s_bsp_swint_buf_top[BSP_SWINT_UNIT_MAX];
static uint8_t s_bsp_swint_buf_bottom[BSP_SWINT_UNIT_MAX];
static uint8_t s_bsp_swint_nested_int_status[BSP_SWINT_UNIT_MAX];

/**********************************************************************************************************************
 * Function Name: R_BSP_SoftwareInterruptOpen
 ******************************************************************************************************************//**
 * @brief This function initializes software interrupts.
 * @param[in] unit Software interrupt unit
 * @retval BSP_SWINT_SUCCESS Success.
 * @retval BSP_SWINT_ERR_INVALID_UNIT Invalid unit specified.
 * @retval BSP_SWINT_ERR_ALREADY_OPEN Failed to lock hardware.
 * @details This function locks the hardware, resets the access control status, clears the interrupt request (IR),
 * initializes the interrupt priority level (IPR), enables nested-interrupt status, initializes the task buffer, and 
 * enables interrupts (IEN).
 * @note This function is available only when use of software interrupts is enabled in a configuration macro.
 * This function is called automatically at BSP startup when the value of BSP_CFG_SWINT_UNITn_ENABLE in r_bsp_config.h 
 * is 1.
 */
e_bsp_swint_err_t R_BSP_SoftwareInterruptOpen(e_bsp_swint_unit_t unit)
{
    bool lock_ret;
    e_bsp_swint_err_t swint_ret;
    uint8_t buf_num;
    uint8_t swint_ipr;

    swint_ret = BSP_SWINT_SUCCESS;

    switch (unit)
    {
        /* Hardware Lock */
#if (defined(BSP_CFG_SWINT_UNIT1_ENABLE) && (BSP_CFG_SWINT_UNIT1_ENABLE == 1))
        case BSP_SWINT_UNIT1:
            lock_ret = R_BSP_HardwareLock(BSP_LOCK_SWINT);
            break;
#endif /* (defined(BSP_CFG_SWINT_UNIT1_ENABLE) && (BSP_CFG_SWINT_UNIT1_ENABLE == 1)) */

#if (defined(BSP_CFG_SWINT_UNIT2_ENABLE) && (BSP_CFG_SWINT_UNIT2_ENABLE == 1))
        case BSP_SWINT_UNIT2:
            lock_ret = R_BSP_HardwareLock(BSP_LOCK_SWINT2);
            break;
#endif /* (defined(BSP_CFG_SWINT_UNIT2_ENABLE) && (BSP_CFG_SWINT_UNIT2_ENABLE == 1)) */

        default:
            swint_ret = BSP_SWINT_ERR_INVALID_UNIT;
            break;
    }

    if (BSP_SWINT_SUCCESS == swint_ret)
    {
        if (true == lock_ret)
        {
            /* Reset Access Control Status */
            g_bsp_swint_access_ctrl[unit].status = BSP_PRV_SWINT_ACCESS_ACCEPTATION;

            /* Disable Interrupt(IEN) */
            R_BSP_SoftwareInterruptControl(unit, BSP_SWINT_CMD_DISABLE_INTERRUPT, FIT_NO_PTR);

            /* Clear Interrupt Request(IR) */
            R_BSP_SoftwareInterruptControl(unit, BSP_SWINT_CMD_CLEAR_INTERRUPT_REQUEST, FIT_NO_PTR);

            /* Set Interrupt Priority(IPR) */
            swint_ipr = BSP_CFG_SWINT_IPR_INITIAL_VALUE;
            R_BSP_SoftwareInterruptControl(unit, BSP_SWINT_CMD_SET_INTERRUPT_PRIORITY, &swint_ipr);

            /* Set Multiple Interrupt Status */
            s_bsp_swint_nested_int_status[unit] = BSP_PRV_SWINT_ENABLE_NESTED_INTERRUPT;

            /* Clear Task Buffer */
            for (buf_num = 0; buf_num < BSP_PRV_SWINT_TASK_BUFFER_MAX; buf_num++)
            {
                s_bsp_swint_task[unit][buf_num].status = BSP_SWINT_TASK_STATUS_NO_REQUEST;
                s_bsp_swint_task[unit][buf_num].p_taskAddr = bsp_swint_dummy_task;
                s_bsp_swint_task[unit][buf_num].p_context = FIT_NO_PTR;
            }

            /* Reset Task Buffer Position */
            s_bsp_swint_buf_top[unit] = 0;
            s_bsp_swint_buf_bottom[unit] = 0;
            s_bsp_swint_buf_used[unit] = 0;

            /* Enable Interrupt(IEN) */
            R_BSP_SoftwareInterruptControl(unit, BSP_SWINT_CMD_ENABLE_INTERRUPT, FIT_NO_PTR);
        }
        else
        {
            swint_ret = BSP_SWINT_ERR_ALREADY_OPEN;
        }
    }

    return swint_ret;
} /* End of function R_BSP_SoftwareInterruptOpen() */

/**********************************************************************************************************************
 * Function Name: R_BSP_SoftwareInterruptClose
 ******************************************************************************************************************//**
 * @brief This function terminates software interrupts.
 * @param[in] unit Software interrupt unit
 * @retval BSP_SWINT_SUCCESS Success.
 * @retval BSP_SWINT_ERR_INVALID_UNIT Invalid unit specified.
 * @retval BSP_SWINT_ERR_ALREADY_OPEN Failed to lock hardware.
 * @details This function unlocks the hardware, disables interrupts (IEN), clears the interrupt request (IR), 
 * initializes the task buffer, and disables nested-interrupt status.
 * @note This function is available only when use of software interrupts is enabled in a configuration macro. Use this 
 * function after the R_BSP_SoftwareInterruptOpen function has run.\n
 * If the R_BSP_SoftwareInterruptSetTask function or software interrupt function (bsp_swint_execute_task) is acquiring 
 * acces control rights and an interrupt is generated and this function is called within the interrupt, the task 
 * buffer may not be controlled correctly. If this function is used in an interrupt, clear the all task by the 
 * R_BSP_SoftwareInterruptControl function with the BSP_SWINT_CMD_CLEAR_ALL_TASK command before call this function.
 */
e_bsp_swint_err_t R_BSP_SoftwareInterruptClose(e_bsp_swint_unit_t unit)
{
    bool lock_ret;
    e_bsp_swint_err_t swint_ret;
    uint8_t buf_num;

    /* Check Unit */
    if (BSP_SWINT_UNIT_MAX > unit)
    {
        /* Disable Interrupt(IEN) */
        R_BSP_SoftwareInterruptControl(unit, BSP_SWINT_CMD_DISABLE_INTERRUPT, FIT_NO_PTR);

        /* Clear Interrupt Request(IR) */
        R_BSP_SoftwareInterruptControl(unit, BSP_SWINT_CMD_CLEAR_INTERRUPT_REQUEST, FIT_NO_PTR);

        /* Clear Task Buffer */
        for (buf_num = 0; buf_num < BSP_PRV_SWINT_TASK_BUFFER_MAX; buf_num++)
        {
            s_bsp_swint_task[unit][buf_num].status = BSP_SWINT_TASK_STATUS_NO_REQUEST;
            s_bsp_swint_task[unit][buf_num].p_taskAddr = bsp_swint_dummy_task;
            s_bsp_swint_task[unit][buf_num].p_context = FIT_NO_PTR;
        }

        /* Reset Task Buffer Position */
        s_bsp_swint_buf_top[unit] = 0;
        s_bsp_swint_buf_bottom[unit] = 0;
        s_bsp_swint_buf_used[unit] = 0;

        /* Clear Multiple Interrupt Status */
        s_bsp_swint_nested_int_status[unit] = BSP_PRV_SWINT_DISABLE_NESTED_INTERRUPT;

        switch (unit)
        {
            /* Hardware Lock */
#if (defined(BSP_CFG_SWINT_UNIT1_ENABLE) && (BSP_CFG_SWINT_UNIT1_ENABLE == 1))
            case BSP_SWINT_UNIT1:
                lock_ret = R_BSP_HardwareUnlock(BSP_LOCK_SWINT);
                break;
#endif /* (defined(BSP_CFG_SWINT_UNIT1_ENABLE) && (BSP_CFG_SWINT_UNIT1_ENABLE == 1)) */

#if (defined(BSP_CFG_SWINT_UNIT2_ENABLE) && (BSP_CFG_SWINT_UNIT2_ENABLE == 1))
            case BSP_SWINT_UNIT2:
                lock_ret = R_BSP_HardwareUnlock(BSP_LOCK_SWINT2);
                break;
#endif /* (defined(BSP_CFG_SWINT_UNIT2_ENABLE) && (BSP_CFG_SWINT_UNIT2_ENABLE == 1)) */

            default:

                /* Do nothing. */
                break;
        }

        if (true == lock_ret)
        {
            swint_ret = BSP_SWINT_SUCCESS;
        }
        else
        {
            swint_ret = BSP_SWINT_ERR_NOT_CLOSED;
        }
    }
    else
    {
        swint_ret = BSP_SWINT_ERR_INVALID_UNIT;
    }

    return swint_ret;
} /* End of function R_BSP_SoftwareInterruptClose() */

/**********************************************************************************************************************
 * Function Name: R_BSP_SoftwareInterruptSetTask
 ******************************************************************************************************************//**
 * @brief This function sets a task in the software interrupt task buffer.
 * @param[in] unit Software interrupt unit
 * @param[in] set_task Software interrupt task
 * @retval BSP_SWINT_SUCCESS Success.
 * @retval BSP_SWINT_ERR_INVALID_UNIT Invalid unit specified.
 * @retval BSP_SWINT_ERR_INVALID_TASK Invalid task pointer specified.
 * @retval BSP_SWINT_ERR_FULL_BUFFER Task buffer full.
 * @retval BSP_SWINT_ERR_ACCESS_REJECTION Failed to obtain access control right.
 * @details This function sets the task specified by an argument in the software interrupt task buffer. After setting 
 * the task, the software interrupt occurs. If the task buffer is full, the task is not set.
 * @note This function is available only when use of software interrupts is enabled in a configuration macro. Use this 
 * function after the R_BSP_SoftwareInterruptOpen function has run.\n
 * If the access control right cannot be obtained, provide a wait period and then call this function again. It is not 
 * possible to obtain the access control right during interrupt processing if the interrupt is generated in a state 
 * where other processing has the access control right. For this reason a deadlock will occur if polling is used in 
 * the interrupt processing to obtain the access control right.
 */
e_bsp_swint_err_t R_BSP_SoftwareInterruptSetTask(e_bsp_swint_unit_t unit, st_bsp_swint_task_t set_task)
{
    e_bsp_swint_err_t ret;
    st_bsp_swint_access_control_t access_control;

    /* Check Unit */
    if (BSP_SWINT_UNIT_MAX > unit)
    {
        /* Get Access Control */
        access_control.status = BSP_PRV_SWINT_ACCESS_REJECTION;
        if (true == bsp_swint_get_access_control(unit, &access_control))
        {
            /* Casting is valid because it matches the type to the right side or argument. */
            if (((uint32_t)FIT_NO_FUNC == (uint32_t)set_task.p_taskAddr) || ((uint32_t)NULL == (uint32_t)set_task.p_taskAddr))
            {
                ret = BSP_SWINT_ERR_INVALID_TASK;
            }
            else if (BSP_CFG_SWINT_TASK_BUFFER_NUMBER <= s_bsp_swint_buf_used[unit])
            {
                ret = BSP_SWINT_ERR_FULL_BUFFER;
            }
            else
            {
                if (BSP_CFG_SWINT_TASK_BUFFER_NUMBER <= s_bsp_swint_buf_top[unit])
                {
                    s_bsp_swint_buf_top[unit] = 0;
                }
                else
                {
                    s_bsp_swint_buf_top[unit]++;
                }

                s_bsp_swint_buf_used[unit]++;

                /* Set Task Buffer */
                s_bsp_swint_task[unit][s_bsp_swint_buf_top[unit]].status = BSP_SWINT_TASK_STATUS_REQUESTED;
                s_bsp_swint_task[unit][s_bsp_swint_buf_top[unit]].p_taskAddr = set_task.p_taskAddr;
                s_bsp_swint_task[unit][s_bsp_swint_buf_top[unit]].p_context = set_task.p_context;

                ret = BSP_SWINT_SUCCESS;
            }

            /* Release Access Control */
            bsp_swint_release_access_control(unit, &access_control);

            /* Set Interrupt Request(IR) */
            R_BSP_SoftwareInterruptControl(unit, BSP_SWINT_CMD_SET_INTERRUPT_REQUEST, FIT_NO_PTR);
        }
        else
        {
            ret = BSP_SWINT_ERR_ACCESS_REJECTION;
        }
    }
    else
    {
        ret = BSP_SWINT_ERR_INVALID_UNIT;
    }

    return ret;
} /* End of function R_BSP_SoftwareInterruptSetTask() */

/***********************************************************************************************************************
* Function Name: bsp_swint_get_interrupt_information
* Description  : Get the software interrupt information.
* Arguments    : unit - Unit number of software interrupt.
*                p_args - Pointer of setting parameter.
* Return Value : None.
***********************************************************************************************************************/
static void bsp_swint_get_interrupt_information(e_bsp_swint_unit_t unit,  void * const p_args)
{
    st_bsp_swint_int_info_t *p_swint_int_info;

    /* Casting is valid because it matches the type of the void type argument to the left. */
    p_swint_int_info = (st_bsp_swint_int_info_t *)p_args;

    switch (unit)
    {
        /* Get Interrupt Information */
#if (defined(BSP_CFG_SWINT_UNIT1_ENABLE) && (BSP_CFG_SWINT_UNIT1_ENABLE == 1))
        case BSP_SWINT_UNIT1:
            p_swint_int_info->ipr = IPR(ICU, SWINT);
            p_swint_int_info->ien = IEN(ICU, SWINT);
            p_swint_int_info->ir = IR(ICU, SWINT);
            p_swint_int_info->nested_int = s_bsp_swint_nested_int_status[unit];
            break;
#endif /* (defined(BSP_CFG_SWINT_UNIT1_ENABLE) && (BSP_CFG_SWINT_UNIT1_ENABLE == 1)) */

#if (defined(BSP_CFG_SWINT_UNIT2_ENABLE) && (BSP_CFG_SWINT_UNIT2_ENABLE == 1))
        case BSP_SWINT_UNIT2:
            p_swint_int_info->ipr = IPR(ICU, SWINT2);
            p_swint_int_info->ien = IEN(ICU, SWINT2);
            p_swint_int_info->ir = IR(ICU, SWINT2);
            p_swint_int_info->nested_int = s_bsp_swint_nested_int_status[unit];
            break;
#endif /* (defined(BSP_CFG_SWINT_UNIT2_ENABLE) && (BSP_CFG_SWINT_UNIT2_ENABLE == 1)) */

        default:

            /* Do nothing. */
            break;
    }
} /* End of function bsp_swint_get_interrupt_information() */

/***********************************************************************************************************************
* Function Name: bsp_swint_enable_interrupt
* Description  : Enable interrupt. (Set the IEN bit.)
* Arguments    : unit - Unit number of software interrupt.
* Return Value : None.
***********************************************************************************************************************/
static void bsp_swint_enable_interrupt(e_bsp_swint_unit_t unit)
{
    switch (unit)
    {
        /* Enable Interrupt */
#if (defined(BSP_CFG_SWINT_UNIT1_ENABLE) && (BSP_CFG_SWINT_UNIT1_ENABLE == 1))
        case BSP_SWINT_UNIT1:
            R_BSP_InterruptRequestEnable(VECT(ICU, SWINT));
            break;
#endif /* (defined(BSP_CFG_SWINT_UNIT1_ENABLE) && (BSP_CFG_SWINT_UNIT1_ENABLE == 1)) */

#if (defined(BSP_CFG_SWINT_UNIT2_ENABLE) && (BSP_CFG_SWINT_UNIT2_ENABLE == 1))
        case BSP_SWINT_UNIT2:
            R_BSP_InterruptRequestEnable(VECT(ICU, SWINT2));
            break;
#endif /* (defined(BSP_CFG_SWINT_UNIT2_ENABLE) && (BSP_CFG_SWINT_UNIT2_ENABLE == 1)) */

        default:

            /* Do nothing. */
            break;
    }
} /* End of function bsp_swint_enable_interrupt() */

/***********************************************************************************************************************
* Function Name: bsp_swint_disable_interrupt
* Description  : Disable interrupt. (Clear the IEN bit.)
* Arguments    : unit - Unit number of software interrupt.
* Return Value : None.
***********************************************************************************************************************/
static void bsp_swint_disable_interrupt(e_bsp_swint_unit_t unit)
{
    switch (unit)
    {
        /* Disable Interrupt */
#if (defined(BSP_CFG_SWINT_UNIT1_ENABLE) && (BSP_CFG_SWINT_UNIT1_ENABLE == 1))
        case BSP_SWINT_UNIT1:
            R_BSP_InterruptRequestDisable(VECT(ICU, SWINT));
            break;
#endif /* (defined(BSP_CFG_SWINT_UNIT1_ENABLE) && (BSP_CFG_SWINT_UNIT1_ENABLE == 1)) */

#if (defined(BSP_CFG_SWINT_UNIT2_ENABLE) && (BSP_CFG_SWINT_UNIT2_ENABLE == 1))
        case BSP_SWINT_UNIT2:
            R_BSP_InterruptRequestDisable(VECT(ICU, SWINT2));
            break;
#endif /* (defined(BSP_CFG_SWINT_UNIT2_ENABLE) && (BSP_CFG_SWINT_UNIT2_ENABLE == 1)) */

        default:

            /* Do nothing. */
            break;
    }
} /* End of function bsp_swint_disable_interrupt() */

/***********************************************************************************************************************
* Function Name: bsp_swint_set_interrupt_priority
* Description  : Set interrupt priority. (Set the IPR register.)
* Arguments    : unit - Unit number of software interrupt.
*                p_args - Pointer of setting parameter.
* Return Value : BSP_SWINT_SUCCESS - Operation successful.
*                BSP_SWINT_ERR_INVALID_IPR - Overflow interrupt priority.
***********************************************************************************************************************/
static e_bsp_swint_err_t bsp_swint_set_interrupt_priority(e_bsp_swint_unit_t unit,  void * const p_args)
{
    e_bsp_swint_err_t ret;
    uint8_t *p_swint_ipr;
    uint8_t ien;
    bsp_int_ctrl_t int_ctrl;

    /* Casting is valid because it matches the type of the void type argument to the left. */
    p_swint_ipr = (uint8_t *)p_args;

    /* Check Interrupt Priority */
    if (BSP_MCU_IPL_MAX < (*p_swint_ipr))
    {
        ret = BSP_SWINT_ERR_INVALID_IPR;
    }
    else
    {
        /* Set IPL to the maximum value to disable all interrupts*/
        R_BSP_InterruptControl(BSP_INT_SRC_EMPTY, BSP_INT_CMD_FIT_INTERRUPT_DISABLE, &int_ctrl);

        switch (unit)
        {
            /* Set Interrupt Priority */
#if (defined(BSP_CFG_SWINT_UNIT1_ENABLE) && (BSP_CFG_SWINT_UNIT1_ENABLE == 1))
            case BSP_SWINT_UNIT1:
                ien = IEN(ICU, SWINT);
                R_BSP_InterruptRequestDisable(VECT(ICU, SWINT));

                /* Casting is valid because it matches the type to the left side. */
                IPR(ICU, SWINT) = (uint8_t)*p_swint_ipr;

                if (1 == ien)
                {
                    R_BSP_InterruptRequestEnable(VECT(ICU, SWINT));
                }
                break;
#endif /* (defined(BSP_CFG_SWINT_UNIT1_ENABLE) && (BSP_CFG_SWINT_UNIT1_ENABLE == 1)) */

#if (defined(BSP_CFG_SWINT_UNIT2_ENABLE) && (BSP_CFG_SWINT_UNIT2_ENABLE == 1))
            case BSP_SWINT_UNIT2:
                ien = IEN(ICU, SWINT2);
                R_BSP_InterruptRequestDisable(VECT(ICU, SWINT2));

                /* Casting is valid because it matches the type to the left side. */
                IPR(ICU, SWINT2) = (uint8_t)*p_swint_ipr;

                if (1 == ien)
                {
                    R_BSP_InterruptRequestEnable(VECT(ICU, SWINT2));
                }
                break;
#endif /* (defined(BSP_CFG_SWINT_UNIT2_ENABLE) && (BSP_CFG_SWINT_UNIT2_ENABLE == 1)) */

            default:

                /* Do nothing. */
                break;
        }

        /* Restore the IPL */
        R_BSP_InterruptControl(BSP_INT_SRC_EMPTY, BSP_INT_CMD_FIT_INTERRUPT_ENABLE, &int_ctrl);

        ret = BSP_SWINT_SUCCESS;
    }

    return ret;
} /* End of function bsp_swint_set_interrupt_priority() */

/***********************************************************************************************************************
* Function Name: bsp_swint_set_interrupt_request
* Description  : Set interrupt request. (Set the SWINTR register.)
* Arguments    : unit - Unit number of software interrupt.
* Return Value : None.
***********************************************************************************************************************/
static void bsp_swint_set_interrupt_request(e_bsp_swint_unit_t unit)
{
    switch (unit)
    {
        /* Set Interrupt Request */
#if (defined(BSP_CFG_SWINT_UNIT1_ENABLE) && (BSP_CFG_SWINT_UNIT1_ENABLE == 1))
        case BSP_SWINT_UNIT1:
            ICU.SWINTR.BIT.SWINT = 1;
            break;
#endif /* (defined(BSP_CFG_SWINT_UNIT1_ENABLE) && (BSP_CFG_SWINT_UNIT1_ENABLE == 1)) */

#if (defined(BSP_CFG_SWINT_UNIT2_ENABLE) && (BSP_CFG_SWINT_UNIT2_ENABLE == 1))
        case BSP_SWINT_UNIT2:
            ICU.SWINT2R.BIT.SWINT2 = 1;
            break;
#endif /* (defined(BSP_CFG_SWINT_UNIT2_ENABLE) && (BSP_CFG_SWINT_UNIT2_ENABLE == 1)) */

        default:

            /* Do nothing. */
            break;
    }
} /* End of function bsp_swint_set_interrupt_request() */

/***********************************************************************************************************************
* Function Name: bsp_swint_clear_interrupt_request
* Description  : Clear interrupt request. (Clear the IR bit.)
* Arguments    : unit - Unit number of software interrupt.
* Return Value : None.
***********************************************************************************************************************/
static void bsp_swint_clear_interrupt_request(e_bsp_swint_unit_t unit)
{
    switch (unit)
    {
        /* Clear Interrupt Request */
#if (defined(BSP_CFG_SWINT_UNIT1_ENABLE) && (BSP_CFG_SWINT_UNIT1_ENABLE == 1))
        case BSP_SWINT_UNIT1:
            IR(ICU, SWINT) = 0;
            break;
#endif /* (defined(BSP_CFG_SWINT_UNIT1_ENABLE) && (BSP_CFG_SWINT_UNIT1_ENABLE == 1)) */

#if (defined(BSP_CFG_SWINT_UNIT2_ENABLE) && (BSP_CFG_SWINT_UNIT2_ENABLE == 1))
        case BSP_SWINT_UNIT2:
            IR(ICU, SWINT2) = 0;
            break;
#endif /* (defined(BSP_CFG_SWINT_UNIT2_ENABLE) && (BSP_CFG_SWINT_UNIT2_ENABLE == 1)) */

        default:

            /* Do nothing. */
            break;
    }
} /* End of function bsp_swint_clear_interrupt_request() */

/***********************************************************************************************************************
* Function Name: bsp_swint_enable_nested_interrupt
* Description  : Set nested interrupt status.
* Arguments    : unit - Unit number of software interrupt.
* Return Value : None.
***********************************************************************************************************************/
static void bsp_swint_enable_nested_interrupt(e_bsp_swint_unit_t unit)
{
    /* Set Multiple Interrupt Status */
    s_bsp_swint_nested_int_status[unit] = BSP_PRV_SWINT_ENABLE_NESTED_INTERRUPT;
} /* End of function bsp_swint_enable_nested_interrupt() */

/***********************************************************************************************************************
* Function Name: bsp_swint_disable_nested_interrupt
* Description  : Clear nested interrupt status.
* Arguments    : unit - Unit number of software interrupt.
* Return Value : None.
***********************************************************************************************************************/
static void bsp_swint_disable_nested_interrupt(e_bsp_swint_unit_t unit)
{
    /* Clear Multiple Interrupt Status */
    s_bsp_swint_nested_int_status[unit] = BSP_PRV_SWINT_DISABLE_NESTED_INTERRUPT;
} /* End of function bsp_swint_disable_nested_interrupt() */

/***********************************************************************************************************************
* Function Name: bsp_swint_clear_task
* Description  : Clear the task of software interrupt in the buffer.
* Arguments    : unit - Unit number of software interrupt.
*                p_args - Pointer of setting parameter.
* Return Value : BSP_SWINT_SUCCESS - Operation successful.
*                BSP_SWINT_ERR_ACCESS_REJECTION - Failed to get access.
*                BSP_SWINT_ERR_TASK_EXECUTING - Accessed during task execution.
*                BSP_SWINT_ERR_INVALID_BUFFER_NUMBER - Set invalid buffer number.
***********************************************************************************************************************/
static e_bsp_swint_err_t bsp_swint_clear_task(e_bsp_swint_unit_t unit, void * const p_args)
{
    e_bsp_swint_err_t ret;
    st_bsp_swint_task_buffer_t *p_swint_task_buffer;
    st_bsp_swint_access_control_t access_control;

    /* Get Access Control */
    access_control.status = BSP_PRV_SWINT_ACCESS_REJECTION;
    if (true == bsp_swint_get_access_control(unit, &access_control))
    {
        /* Casting is valid because it matches the type of the void type argument to the left. */
        p_swint_task_buffer = (st_bsp_swint_task_buffer_t *)p_args;

        if (BSP_PRV_SWINT_TASK_BUFFER_MAX > p_swint_task_buffer->number)
        {
            /* Clear Task Buffer */
            if (BSP_SWINT_TASK_STATUS_EXECUTING != s_bsp_swint_task[unit][p_swint_task_buffer->number].status)
            {
                s_bsp_swint_task[unit][p_swint_task_buffer->number].status = BSP_SWINT_TASK_STATUS_NO_REQUEST;
                s_bsp_swint_task[unit][p_swint_task_buffer->number].p_taskAddr = bsp_swint_dummy_task;
                s_bsp_swint_task[unit][p_swint_task_buffer->number].p_context = FIT_NO_PTR;
                ret = BSP_SWINT_SUCCESS;
            }
            else
            {
                ret = BSP_SWINT_ERR_TASK_EXECUTING;
            }
        }
        else
        {
            ret = BSP_SWINT_ERR_INVALID_BUFFER_NUMBER;
        }

        /* Release Access Control */
        bsp_swint_release_access_control(unit, &access_control);

        /* Set Interrupt Request(IR)
         * If a software interrupt is generated while this function has the access control right, the software 
         * interrupt cannot obtain the access control right and interrupt processing ends with the task remaining 
         * unexecuted. For this reason, after returning from a software interrupt the interrupt request is cleared 
         * regardless of whether a task has been set in the task buffer. To avoid it, setting of the interrupt 
         * request occurs in this timing.
         */
        R_BSP_SoftwareInterruptControl(unit, BSP_SWINT_CMD_SET_INTERRUPT_REQUEST, FIT_NO_PTR);
    }
    else
    {
        ret = BSP_SWINT_ERR_ACCESS_REJECTION;
    }

    return ret;
} /* End of function bsp_swint_clear_task() */

/***********************************************************************************************************************
* Function Name: bsp_swint_clear_all_task
* Description  : Clear the  all task of software interrupt in the buffer.
* Arguments    : unit - Unit number of software interrupt.
* Return Value : BSP_SWINT_SUCCESS - Operation successful.
*                BSP_SWINT_ERR_ACCESS_REJECTION - Failed to get access.
*                BSP_SWINT_ERR_TASK_EXECUTING - Accessed during task execution.
***********************************************************************************************************************/
static e_bsp_swint_err_t bsp_swint_clear_all_task(e_bsp_swint_unit_t unit)
{
    e_bsp_swint_err_t ret;
    uint8_t buf_num;
    st_bsp_swint_access_control_t access_control;

    /* Get Access Control */
    access_control.status = BSP_PRV_SWINT_ACCESS_REJECTION;
    if (true == bsp_swint_get_access_control(unit, &access_control))
    {
        ret = BSP_SWINT_SUCCESS;

        /* Check Task Status */
        for (buf_num = 0; buf_num < BSP_PRV_SWINT_TASK_BUFFER_MAX; buf_num++)
        {
            if (BSP_SWINT_TASK_STATUS_EXECUTING == s_bsp_swint_task[unit][buf_num].status)
            {
                ret = BSP_SWINT_ERR_TASK_EXECUTING;
                break;
            }
        }

        if (BSP_SWINT_SUCCESS == ret)
        {
            /* Clear ALL Task Buffer */
            for (buf_num = 0; buf_num < BSP_PRV_SWINT_TASK_BUFFER_MAX; buf_num++)
            {
                s_bsp_swint_task[unit][buf_num].status = BSP_SWINT_TASK_STATUS_NO_REQUEST;
                s_bsp_swint_task[unit][buf_num].p_taskAddr = bsp_swint_dummy_task;
                s_bsp_swint_task[unit][buf_num].p_context = FIT_NO_PTR;
            }

            /* Reset Task Buffer Position */
            s_bsp_swint_buf_top[unit] = 0;
            s_bsp_swint_buf_bottom[unit] = 0;
            s_bsp_swint_buf_used[unit] = 0;

            /* Release Access Control */
            bsp_swint_release_access_control(unit, &access_control);
        }
        else
        {
            /* Release Access Control */
            bsp_swint_release_access_control(unit, &access_control);

            /* Set Interrupt Request(IR)
             * If a software interrupt is generated while this function has the access control right, the software 
             * interrupt cannot obtain the access control right and interrupt processing ends with the task remaining 
             * unexecuted. For this reason, after returning from a software interrupt the interrupt request is cleared 
             * regardless of whether a task has been set in the task buffer. To avoid it, setting of the interrupt 
             * request occurs in this timing.
             */
            R_BSP_SoftwareInterruptControl(unit, BSP_SWINT_CMD_SET_INTERRUPT_REQUEST, FIT_NO_PTR);
        }
    }
    else
    {
        ret = BSP_SWINT_ERR_ACCESS_REJECTION;
    }

    return ret;
} /* End of function bsp_swint_clear_all_task() */

/***********************************************************************************************************************
* Function Name: bsp_swint_get_all_task_status
* Description  : Get the task status of software interrupt.
* Arguments    : unit - Unit number of software interrupt.
*                p_args - Pointer of setting parameter.
* Return Value : None.
***********************************************************************************************************************/
static void bsp_swint_get_all_task_status(e_bsp_swint_unit_t unit, void * const p_args)
{
    uint8_t buf_num;
    st_bsp_swint_task_t *p_swint_task;

    /* Casting is valid because it matches the type of the void type argument to the left. */
    p_swint_task = (st_bsp_swint_task_t *)p_args;

    /* Clear Task Status */
    for (buf_num = 0; buf_num < BSP_PRV_SWINT_TASK_BUFFER_MAX; buf_num++)
    {
        p_swint_task->status = s_bsp_swint_task[unit][buf_num].status;
        p_swint_task->p_taskAddr = s_bsp_swint_task[unit][buf_num].p_taskAddr;
        p_swint_task->p_context = s_bsp_swint_task[unit][buf_num].p_context;
        p_swint_task++;
    }
} /* End of function bsp_swint_get_all_task_status() */

/**********************************************************************************************************************
 * Function Name: R_BSP_SoftwareInterruptControl
 ******************************************************************************************************************//**
 * @brief This function controls software interrupts.
 * @param[in] unit Software interrupt unit
 * @param[in] cmd Software interrupt control command
 * @param[in, out] p_args Pointer to arguments for software interrupt control commands. Set the argument type to match 
 * each software interrupt control command. For commands that do not require arguments, use the setting FIT_NO_PTR.
 * @retval BSP_SWINT_SUCCESS Success.
 * @retval BSP_SWINT_ERR_INVALID_UNIT Invalid unit specified.
 * @retval BSP_SWINT_ERR_INVALID_IPR Invalid interrupt priority level specified.
 * @retval BSP_SWINT_ERR_INVALID_CMD Invalid command specified.
 * @retval BSP_SWINT_ERR_INVALID_BUFFER_NUMBER Invalid task buffer number specified.
 * @retval BSP_SWINT_ERR_TASK_EXECUTING Attempt to manipulate a task that is running.
 * @retval BSP_SWINT_ERR_ACCESS_REJECTION Failed to obtain access control right.
 * @details This function performs software interrupt control in response to commands. Refer the application note for 
 * the operation of each command.
 * @note This function is available only when use of software interrupts is enabled in a configuration macro. Use this 
 * function after the R_BSP_SoftwareInterruptOpen function has run.\n
 * Do not change the interrupt priority level (IPR) while a software interrupt is being processed.\n
 * When the BSP_SWINT_CMD_SET_INTERRUPT_PRIORITY command is run, interrupts are disabled temporarily in order to set 
 * the interrupt priority level (IPR).\n
 * If the access control right cannot be obtained, provide a wait period and then call this function again. It is not 
 * possible to obtain the access control right during interrupt processing if the interrupt is generated in a state 
 * where other processing has the access control right. For this reason a deadlock will occur if polling is used in 
 * the interrupt processing to obtain the access control right.\n
 * If a software interrupt is generated while this function has the access control right, the software interrupt 
 * cannot obtain the access control right and interrupt processing ends with the task remaining unexecuted. For this 
 * reason, after returning from a software interrupt the interrupt request is cleared regardless of whether a task has 
 * been set in the task buffer. To avoid this, setting of the interrupt request occurs at the end of the processing of 
 * the BSP_SWINT_CMD_CLEAR_TASK and BSP_SWINT_CMD_CLEAR_ALL_TASK commands. Nevertheless, since all task buffers are 
 * cleared when processing of the BSP_SWINT_CMD_CLEAR_ALL_TASK command completes successfully, the interrupt request 
 * is not set.
 */
e_bsp_swint_err_t R_BSP_SoftwareInterruptControl(e_bsp_swint_unit_t unit, e_bsp_swint_cmd_t const cmd, void * const p_args)
{
    e_bsp_swint_err_t ret;
    uint8_t *p_swint_buf_num;

    /* Check Unit */
    if (BSP_SWINT_UNIT_MAX > unit)
    {
        ret = BSP_SWINT_SUCCESS;

        /* Execute Command */
        switch (cmd)
        {
            case BSP_SWINT_CMD_GET_INTERRUPT_INFORMATION:
                bsp_swint_get_interrupt_information(unit, p_args);
                break;

            case BSP_SWINT_CMD_ENABLE_INTERRUPT:
                bsp_swint_enable_interrupt(unit);
                break;

            case BSP_SWINT_CMD_DISABLE_INTERRUPT:
                bsp_swint_disable_interrupt(unit);
                break;

            case BSP_SWINT_CMD_SET_INTERRUPT_PRIORITY:
                ret = bsp_swint_set_interrupt_priority(unit, p_args);
                break;

            case BSP_SWINT_CMD_SET_INTERRUPT_REQUEST:
                bsp_swint_set_interrupt_request(unit);
                break;

            case BSP_SWINT_CMD_CLEAR_INTERRUPT_REQUEST:
                bsp_swint_clear_interrupt_request(unit);
                break;

            case BSP_SWINT_CMD_ENABLE_NESTED_INTERRUPT:
                bsp_swint_enable_nested_interrupt(unit);
                break;

            case BSP_SWINT_CMD_DISABLE_NESTED_INTERRUPT:
                bsp_swint_disable_nested_interrupt(unit);
                break;

            case BSP_SWINT_CMD_CLEAR_TASK:
                ret = bsp_swint_clear_task(unit, p_args);
                break;

            case BSP_SWINT_CMD_CLEAR_ALL_TASK:
                ret = bsp_swint_clear_all_task(unit);
                break;

            case BSP_SWINT_CMD_GET_ALL_TASK_STATUS:
                bsp_swint_get_all_task_status(unit, p_args);
                break;

            case BSP_SWINT_CMD_GET_USED_BUFFER:

                /* Casting is valid because it matches the type of the void type argument to the left. */
                p_swint_buf_num = (uint8_t *)p_args;

                /* Casting is valid because it matches the type to the left side. */
                *p_swint_buf_num = (uint8_t)s_bsp_swint_buf_used[unit];
                break;

            case BSP_SWINT_CMD_GET_UNUSED_BUFFER:

                /* Casting is valid because it matches the type of the void type argument to the left. */
                p_swint_buf_num = (uint8_t *)p_args;

                /* Casting is valid because it matches the type to the left side. */
                *p_swint_buf_num = (uint8_t)(BSP_CFG_SWINT_TASK_BUFFER_NUMBER - s_bsp_swint_buf_used[unit]);
                break;

            default:
                ret = BSP_SWINT_ERR_INVALID_CMD;
                break;
        }
    }
    else
    {
        ret = BSP_SWINT_ERR_INVALID_UNIT;
    }

    return ret;
} /* End of function R_BSP_SoftwareInterruptControl() */

/***********************************************************************************************************************
* Function Name: bsp_swint_get_access_control
* Description  : Get access of software interrupt.
* Arguments    : unit - Unit number of software interrupt.
*                p_args - Pointer of setting parameter.
* Return Value : true - Get access.
*                false - Failed to get access.
***********************************************************************************************************************/
static bool bsp_swint_get_access_control(e_bsp_swint_unit_t unit, st_bsp_swint_access_control_t * const p_args)
{
    bool ret;

    /* Get Access */
    R_BSP_EXCHANGE(&g_bsp_swint_access_ctrl[unit].status, &p_args->status);

    if (BSP_PRV_SWINT_ACCESS_ACCEPTATION == p_args->status)
    {
        ret = true;
    }
    else
    {
        ret = false;
    }

    return ret;
} /* End of function bsp_swint_get_access_control() */

/***********************************************************************************************************************
* Function Name: bsp_swint_release_access_control
* Description  : Release access of software interrupt.
* Arguments    : unit - Unit number of software interrupt.
*                p_args - Pointer of setting parameter.
* Return Value : true - Release access.
*                false - Failed to release access.
***********************************************************************************************************************/
static bool bsp_swint_release_access_control(e_bsp_swint_unit_t unit, st_bsp_swint_access_control_t * const p_args)
{
    bool ret;

    /* Release access */
    R_BSP_EXCHANGE(&g_bsp_swint_access_ctrl[unit].status, &p_args->status);

    if (BSP_PRV_SWINT_ACCESS_ACCEPTATION == g_bsp_swint_access_ctrl[unit].status)
    {
        ret = true;
    }
    else
    {
        ret = false;
    }

    return ret;
} /* End of function bsp_swint_release_access_control() */

/***********************************************************************************************************************
* Function name: bsp_swint_dummy_task
* Description  : Dummy task.
* Arguments    : p_dummy_context - Dummy arguments.
* Return value : None.
***********************************************************************************************************************/
static void bsp_swint_dummy_task(void * p_dummy_context)
{
    R_BSP_NOP();
} /* End of function bsp_swint_dummy_task() */

/***********************************************************************************************************************
* Function name: bsp_swint_execute_task
* Description  : Execute task of software interrupt.
* Arguments    : unit - Unit number of software interrupt.
* Return value : None.
***********************************************************************************************************************/
static void bsp_swint_execute_task(e_bsp_swint_unit_t unit)
{
    st_bsp_swint_access_control_t access_control;

    /* Get Access Control */
    access_control.status = BSP_PRV_SWINT_ACCESS_REJECTION;
    if (true == bsp_swint_get_access_control(unit, &access_control))
    {
        /* Release Access Control */
        bsp_swint_release_access_control(unit, &access_control);

        /* Enable Multiple Interrupt */
        if (BSP_PRV_SWINT_ENABLE_NESTED_INTERRUPT == s_bsp_swint_nested_int_status[unit])
        {
            R_BSP_InterruptsEnable();
        }

        /* Get Access Control */
        access_control.status = BSP_PRV_SWINT_ACCESS_REJECTION;
        bsp_swint_get_access_control(unit, &access_control);

        /* WAIT_LOOP */
        while (0 != s_bsp_swint_buf_used[unit])
        {
            if (BSP_CFG_SWINT_TASK_BUFFER_NUMBER <= s_bsp_swint_buf_bottom[unit])
            {
                s_bsp_swint_buf_bottom[unit] = 0;
            }
            else
            {
                s_bsp_swint_buf_bottom[unit]++;
            }

            if (BSP_SWINT_TASK_STATUS_REQUESTED == s_bsp_swint_task[unit][s_bsp_swint_buf_bottom[unit]].status)
            {
                /* Change Task Status to "EXECUTING" */
                s_bsp_swint_task[unit][s_bsp_swint_buf_bottom[unit]].status = BSP_SWINT_TASK_STATUS_EXECUTING;

                /* Release Access Control */
                bsp_swint_release_access_control(unit, &access_control);

                /* Execute Task */
                s_bsp_swint_task[unit][s_bsp_swint_buf_bottom[unit]].p_taskAddr(s_bsp_swint_task[unit][s_bsp_swint_buf_bottom[unit]].p_context);

                /* Get Access Control */
                access_control.status = BSP_PRV_SWINT_ACCESS_REJECTION;
                bsp_swint_get_access_control(unit, &access_control);

                if (BSP_SWINT_TASK_STATUS_EXECUTING == s_bsp_swint_task[unit][s_bsp_swint_buf_bottom[unit]].status)
                {
                    /* Change Task Status to "COMPLETED" */
                    s_bsp_swint_task[unit][s_bsp_swint_buf_bottom[unit]].status = BSP_SWINT_TASK_STATUS_COMPLETED;
                }
            }

            if (0 != s_bsp_swint_buf_used[unit])
            {
                s_bsp_swint_buf_used[unit]--;
            }
        }

        /* Release Access Control */
        bsp_swint_release_access_control(unit, &access_control);
    }
} /* End of function bsp_swint_execute_task() */

#endif /* (BSP_CFG_SWINT_UNIT1_ENABLE == 1) || (BSP_CFG_SWINT_UNIT2_ENABLE == 1) */

#if (defined(BSP_CFG_SWINT_UNIT1_ENABLE) && (BSP_CFG_SWINT_UNIT1_ENABLE == 1))
/***********************************************************************************************************************
* Function name: bsp_swint_isr
* Description  : Software interrupt function. (Unit1)
* Arguments    : None.
* Return value : None.
***********************************************************************************************************************/
R_BSP_ATTRIB_STATIC_INTERRUPT void bsp_swint_isr(void)
{
    bsp_swint_execute_task(BSP_SWINT_UNIT1);
} /* End of function bsp_swint_isr() */
#endif /* (defined(BSP_CFG_SWINT_UNIT1_ENABLE) && (BSP_CFG_SWINT_UNIT1_ENABLE == 1)) */

#if (defined(BSP_CFG_SWINT_UNIT2_ENABLE) && (BSP_CFG_SWINT_UNIT2_ENABLE == 1))
/***********************************************************************************************************************
* Function name: bsp_swint2_isr
* Description  : Software interrupt function. (Unit2)
* Arguments    : None.
* Return value : None.
***********************************************************************************************************************/
R_BSP_ATTRIB_STATIC_INTERRUPT void bsp_swint2_isr(void)
{
    bsp_swint_execute_task(BSP_SWINT_UNIT2);
} /* End of function bsp_swint2_isr() */
#endif /* (defined(BSP_CFG_SWINT_UNIT2_ENABLE) && (BSP_CFG_SWINT_UNIT2_ENABLE == 1)) */

