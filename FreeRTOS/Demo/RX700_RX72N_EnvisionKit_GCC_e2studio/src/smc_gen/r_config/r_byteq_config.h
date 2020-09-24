/* Generated configuration header file - do not edit */
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
* File Name     : r_byteq_config.h
* Description   : Configures the byte queue memory allocation
************************************************************************************************************************
* History : DD.MM.YYYY Version Description  
*         : 24.07.2013 1.00     Initial Release
*         : 11.21.2014 1.20     Removed dependency to BSP
*         : 30.09.2015 1.50     Added dependency to BSP
*         : 01.06.2018 1.70     Changed the default value of the following macro definition.
*                                - BYTEQ_CFG_MAX_CTRL_BLKS - Changed the default value from 4 to 32.
***********************************************************************************************************************/
#ifndef BYTEQ_CONFIG_H
#define BYTEQ_CONFIG_H

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
#include "platform.h"

/***********************************************************************************************************************
Configuration Options
***********************************************************************************************************************/

/* SPECIFY WHETHER TO INCLUDE CODE FOR API PARAMETER CHECKING
   Available settings:
   BSP_CFG_PARAM_CHECKING_ENABLE:
       Utilizes the system default setting
   1:
       Includes parameter checking
   0:
       Compiles out parameter checking
*/
#define BYTEQ_CFG_PARAM_CHECKING_ENABLE     (BSP_CFG_PARAM_CHECKING_ENABLE)

/* SPECIFY IF SHOULD USE MALLOC() TO ALLOCATE MEMORY FOR QUEUE CONTROL BLOCKS */
#define BYTEQ_CFG_USE_HEAP_FOR_CTRL_BLKS    (0)

/* SPECIFY NUMBER OF STATIC QUEUE CONTROL BLOCKS TO SUPPORT */
/* valid only when BYTEQ_USE_HEAP_FOR_CTRL_BLKS is set to 0 */
#define BYTEQ_CFG_MAX_CTRL_BLKS             (32)


#endif /* BYTEQ_CONFIG_H */
