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
 **********************************************************************************************************************/
/***********************************************************************************************************************
 * File Name    : freertos_object_init.c
 * Version      : 1.0
 * Description  :
 **********************************************************************************************************************/
/***********************************************************************************************************************
 * History : DD.MM.YYYY Version  Description
 *         : 07.12.2018 1.00     First Release
 **********************************************************************************************************************/

/***********************************************************************************************************************
 * Includes   <System Includes> , "Project Includes"
 **********************************************************************************************************************/
#include "FreeRTOS.h"
#include "freertos_start.h"
/***********************************************************************************************************************
 * Macro definitions
 **********************************************************************************************************************/

/***********************************************************************************************************************
 * Typedef definitions
 **********************************************************************************************************************/

/***********************************************************************************************************************
 * Private global variables and functions
 **********************************************************************************************************************/
void Kernel_Object_init (void);
void Object_init_manual (void);
/***********************************************************************************************************************
 * Function Name: Kernel_Object_init
 * Description  : This function initializes FreeRTOS objects.
 * Arguments    : None.
 * Return Value : None.
 **********************************************************************************************************************/
void Kernel_Object_init (void)
{
    /************** task creation ****************************/

    /************** semaphore creation ***********************/

    /************** queue creation ***************************/

    /************** software time creation **************************/

    /************** event groups creation ********************/

    /************** stream buffer creation *************************/

    /************** message buffer creation *********************/

} /* End of function Kernel_Object_init()*/

/***********************************************************************************************************************
 * Function Name : Object_init_manual
 * Description   : This function re-initializes FreeRTOS objects and should be called at runtime.
 * Arguments     : None.
 * Return value  : None.
 **********************************************************************************************************************/
void Object_init_manual (void)
{
    /************** task creation ****************************/
} /* End of function Object_init_manual()*/
