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
* File Name    : r_bsp_interrupts.h
* Description  : This module allows for callbacks to be registered for certain interrupts. 
*                And handle exception interrupts.
***********************************************************************************************************************/
/**********************************************************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 28.02.2019 1.00     First Release
***********************************************************************************************************************/

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
#include "platform.h"

/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/
/* Multiple inclusion prevention macro */
#ifndef INTERRUPTS_H
#define INTERRUPTS_H

/***********************************************************************************************************************
Typedef definitions
***********************************************************************************************************************/

/***********************************************************************************************************************
Exported global variables
***********************************************************************************************************************/

/***********************************************************************************************************************
Exported global functions (to be accessed by other files)
***********************************************************************************************************************/
void R_BSP_InterruptRequestEnable(uint32_t vector);
void R_BSP_InterruptRequestDisable(uint32_t vector);
bsp_int_err_t R_BSP_InterruptWrite(bsp_int_src_t vector,  bsp_int_cb_t callback);
bsp_int_err_t R_BSP_InterruptRead(bsp_int_src_t vector, bsp_int_cb_t * callback);
bsp_int_err_t R_BSP_InterruptControl(bsp_int_src_t vector, bsp_int_cmd_t cmd, void * pdata);

void bsp_interrupt_open(void); //r_bsp internal function. DO NOT CALL.

#ifdef BSP_MCU_EXCEP_SUPERVISOR_INST_ISR
R_BSP_PRAGMA_INTERRUPT_FUNCTION(excep_supervisor_inst_isr)
#endif
#ifdef BSP_MCU_EXCEP_ACCESS_ISR
R_BSP_PRAGMA_INTERRUPT_FUNCTION(excep_access_isr)
#endif
#ifdef BSP_MCU_EXCEP_UNDEFINED_INST_ISR
R_BSP_PRAGMA_INTERRUPT_FUNCTION(excep_undefined_inst_isr)
#endif
#ifdef BSP_MCU_EXCEP_FLOATING_POINT_ISR
R_BSP_PRAGMA_INTERRUPT_FUNCTION(excep_floating_point_isr)
#endif
#ifdef BSP_MCU_NON_MASKABLE_ISR
R_BSP_PRAGMA_INTERRUPT_FUNCTION(non_maskable_isr)
#endif
#ifdef BSP_MCU_UNDEFINED_INTERRUPT_SOURCE_ISR
R_BSP_PRAGMA_INTERRUPT_DEFAULT(undefined_interrupt_source_isr)
#endif
#ifdef BSP_MCU_BUS_ERROR_ISR
R_BSP_PRAGMA_INTERRUPT(bus_error_isr, VECT(BSC,BUSERR))
#endif

#endif  /* End of multiple inclusion prevention macro */

