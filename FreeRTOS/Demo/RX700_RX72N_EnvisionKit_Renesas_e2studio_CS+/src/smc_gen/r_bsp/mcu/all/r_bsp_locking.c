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
* File Name    : r_bsp_locking.c
* Description  : This implements a locking mechanism that can be used by all code. The locking is done atomically so
*                common resources can be accessed safely.
***********************************************************************************************************************/
/**********************************************************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 28.02.2019 2.00     Merged processing of all devices.
*                               Added support for GNUC and ICCRX.
*                               Fixed coding style.
*         : 26.07.2019 2.01     Modified comment of API function to Doxygen style.
*         : 10.12.2019 2.02     Modified comment.
***********************************************************************************************************************/

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
/* Platform configuration. */
#include "platform.h"

/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/

/***********************************************************************************************************************
Typedef definitions
***********************************************************************************************************************/

/***********************************************************************************************************************
Exported global variables (to be accessed by other files)
***********************************************************************************************************************/
 
/***********************************************************************************************************************
Private global variables and functions
***********************************************************************************************************************/

/**********************************************************************************************************************
 * Function Name: R_BSP_SoftwareLock
 ******************************************************************************************************************//**
 * @brief Attempts to reserve a lock.
 * @param[out] plock Pointer to lock structure with lock to try and acquire.
 * @retval true Successful, lock was available and acquired.
 * @retval false Failure, lock was already acquired and is not available.
 * @details This function implements an atomic locking mechanism. Locks can be used in numerous ways. Two common uses 
 * of locks are to protect critical sections of code and to protect against duplicate resource allocation.
 * For protecting critical sections of code the user would require that the code first obtain the critical section's 
 * lock before executing. An example of protecting against duplicate resource allocation would be if the user had two 
 * FIT modules that used the same peripheral. For example, the user may have one FIT module that uses the SCI 
 * peripheral in UART mode and another FIT module that uses the SCI peripheral in I2C mode. To make sure that both 
 * modules cannot use the same SCI channel, locks can be used.
 * Care should be taken when using locks as they do not provide advanced features one might expect from an RTOS
 * semaphore or mutex. If used improperly locks can lead to deadlock in the user's system.
 * Users can override the default locking mechanisms.
 */
bool R_BSP_SoftwareLock (BSP_CFG_USER_LOCKING_TYPE * const plock)
{
#if BSP_CFG_USER_LOCKING_ENABLED == 0
    bool ret = false;

    /* Variable used in trying to acquire lock. Using the xchg instruction makes this atomic */
    int32_t is_locked = true;
    
    /* This example uses the RX MCU's atomic xchg() instruction. plock->lock is the lock we are trying to reserve. 
       The way this works is that 'is_locked' gets the value of the plock->lock and plock->lock gets the value of 
       'is_locked' which we just set to 'true'. Basically this is an atomic 'swap' command. If the lock had not yet been
       reserved then its value would be 'false' and after the xchg() instruction finished 'is_locked' would have 
       'false'. If it had already been reserved then 'is_locked' would have 'true' after the xchg() instruction. Since 
       plock->lock was already 'true' and we just set it back to 'true' everything is ok. To see if we reserved the lock
       we just need to check the value of 'is_locked' after this instruction finishes. */

    /* Try to acquire semaphore to obtain lock */
    R_BSP_EXCHANGE(&is_locked, &plock->lock);
    
    /* Check to see if semaphore was successfully taken */
    if (false == is_locked)
    {        
        /* Lock obtained, return success. */
        ret = true;
    }
    else
    {
        /* Lock was not obtained, another task already has it. */
        R_BSP_NOP();
    }

    return ret;
#else
    /* User is going to handle the locking themselves. */
    return BSP_CFG_USER_LOCKING_SW_LOCK_FUNCTION(plock);
#endif
} /* End of function R_BSP_SoftwareLock() */

/**********************************************************************************************************************
 * Function Name: R_BSP_SoftwareUnlock
 ******************************************************************************************************************//**
 * @brief Releases a lock.
 * @param[out] plock Pointer to lock structure with lock to release.
 * @retval true Successful, lock was released. Or the lock has been already released.
 * @retval false Failure, lock could not be released.
 * @details This function releases a lock that was previously acquired using the R_BSP_SoftwareLock() function.
 */
bool R_BSP_SoftwareUnlock (BSP_CFG_USER_LOCKING_TYPE * const plock)
{
#if BSP_CFG_USER_LOCKING_ENABLED == 0
    /* Set lock back to unlocked. */
    plock->lock = false;

    return true;
#else
    /* User is going to handle the locking themselves. */
    return BSP_CFG_USER_LOCKING_SW_UNLOCK_FUNCTION(plock);
#endif
} /* End of function R_BSP_SoftwareUnlock() */


/**********************************************************************************************************************
 * Function Name: R_BSP_HardwareLock
 ******************************************************************************************************************//**
 * @brief Attempts to reserve a hardware peripheral lock.
 * @param[in] hw_index Index of lock to acquire from the hardware lock array.
 * @retval true Successful, lock was available and acquired.
 * @retval false Failure, lock was already acquired and is not available.
 * @details This function attempts to acquire the lock for a hardware resource of the MCU. Instead of sending in a 
 * pointer to a lock as with the R_BSP_SoftwareLock() function, the user sends in an index to an array that holds 1 
 * lock per MCU hardware resource. This array is shared amongst all FIT modules and user code therefore allowing 
 * multiple FIT modules (and user code) to use the same locks. The user can see the available hardware resources by 
 * looking at the mcu_lock_t enum in mcu_locks.h. These enum values are also the index into the hardware lock array.
 * The same atomic locking mechanisms from the R_BSP_SoftwareLock() function are used with this function as well.
 * @note Each entry in the mcu_lock_t enum in mcu_locks.h will be allocated a lock. On RX MCUs, each lock is required 
 * to be 4-bytes. If RAM space is an issue then the user can remove the entries from the mcu_lock_t enum they are not 
 * using. For example, if the user is not using the CRC peripheral then they could delete the BSP_LOCK_CRC entry. The 
 * user will save 4-bytes per deleted entry.
 */
bool R_BSP_HardwareLock (mcu_lock_t const hw_index)
{
#if BSP_CFG_USER_LOCKING_ENABLED == 0
    /* Pass actual lock to software lock function. */
    return R_BSP_SoftwareLock(&g_bsp_Locks[hw_index]);
#else
    /* User is going to handle the locking themselves. */
    return BSP_CFG_USER_LOCKING_HW_LOCK_FUNCTION(hw_index);
#endif
} /* End of function R_BSP_HardwareLock() */

/**********************************************************************************************************************
 * Function Name: R_BSP_HardwareUnlock
 ******************************************************************************************************************//**
 * @brief Releases a hardware peripheral lock.
 * @param[in] hw_index Index of lock to release from the hardware lock array.
 * @retval true Successful, lock was released.
 * @retval false Failure, lock could not be released.
 * @details This function attempts to release the lock for a hardware resource of the MCU that was previously acquired 
 * using the R_BSP_HardwareLock() function.
 * @note Each entry in the mcu_lock_t enum in mcu_locks.h will be allocated a lock. On RX MCUs, each lock is required 
 * to be 4-bytes. If RAM space is an issue then the user can remove the entries from the mcu_lock_t enum that they are 
 * not using. For example, if the user is not using the CRC peripheral then they could delete the BSP_LOCK_CRC entry. 
 * The user will save 4-bytes per deleted entry.
 */
bool R_BSP_HardwareUnlock (mcu_lock_t const hw_index)
{
#if BSP_CFG_USER_LOCKING_ENABLED == 0
    /* Pass actual lock to software unlock function. */
    return R_BSP_SoftwareUnlock(&g_bsp_Locks[hw_index]);
#else
    /* User is going to handle the locking themselves. */
    return BSP_CFG_USER_LOCKING_HW_UNLOCK_FUNCTION(hw_index);
#endif
} /* End of function R_BSP_HardwareUnlock() */

