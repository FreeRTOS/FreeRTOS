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
* File Name	   : locking.c
* Description  : This implements a locking mechanism that can be used by all code. The locking is done atomically so
*                common resources can be accessed safely.
***********************************************************************************************************************/
/**********************************************************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 07.03.2012 1.00     First Release
***********************************************************************************************************************/

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
/* Fixed-size integer typedefs. */
#include <stdint.h>
/* bool support. */
#include <stdbool.h>
/* Has intrinsic support. Includes xchg() which is used in this code. */
#include <machine.h>
/* Includes board and MCU related header files. */
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

/***********************************************************************************************************************
* Function Name: R_BSP_Lock
* Description  : Attempt to acquire the lock that has been sent in.
* Arguments    : plock -
*                    Pointer to lock structure with lock to try and acquire.
* Return Value : true -
*                    Lock was acquired.
*                false -
*                    Lock was not acquired.
***********************************************************************************************************************/
bool R_BSP_Lock(bsp_lock_t * plock)
{
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
    xchg(&is_locked, &plock->lock);
    
    /* Check to see if semaphore was successfully taken */
    if (is_locked == false)
    {        
        /* Lock obtained, return success. */
        ret = true;
    }
    else
    {
        /* Lock was not obtained, another task already has it. */
    }

    return ret;   
} /* End of function R_BSP_Lock() */


/***********************************************************************************************************************
* Function Name: R_BSP_Unlock
* Description  : Release hold on lock.
* Arguments    : plock -
*                    Pointer to lock structure with lock to release.
* Return Value : true -
*                    Lock was released.
*                false -
*                    Lock was not released.
***********************************************************************************************************************/
bool R_BSP_Unlock(bsp_lock_t * plock)
{
    /* Set lock back to unlocked. */
    plock->lock = false;

    return true;
} /* End of function R_BSP_Unlock() */


