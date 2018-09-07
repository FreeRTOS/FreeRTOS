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
* Copyright (C) 2012 Renesas Electronics Corporation. All rights reserved.    
***********************************************************************************************************************/
/***********************************************************************************************************************
* File Name	   : vecttbl.h
* Device(s)    : RX111
* Description  : Has function prototypes for exception callback functions.
***********************************************************************************************************************/
/***********************************************************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 08.11.2012 1.20     Beta Release.
***********************************************************************************************************************/

#ifndef VECTTBL_HEADER_INC
#define VECTTBL_HEADER_INC

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
/* Fixed size integers. */
#include <stdint.h>
/* Used for nop(). */
#include <machine.h>
/* BSP configuration. */
#include "platform.h"

/***********************************************************************************************************************
Exported global functions (to be accessed by other files)
***********************************************************************************************************************/
#if defined(EXCEP_SUPERVISOR_ISR_CALLBACK)
void EXCEP_SUPERVISOR_ISR_CALLBACK(void);
#endif

#if defined(EXCEP_UNDEFINED_INSTR_ISR_CALLBACK)
void EXCEP_UNDEFINED_INSTR_ISR_CALLBACK(void);
#endif

#if defined(NMI_ISR_CALLBACK)
void NMI_ISR_CALLBACK(void);
#endif

#if defined(UNDEFINED_INT_ISR_CALLBACK)
void UNDEFINED_INT_ISR_CALLBACK(void);
#endif

#if defined(BUS_ERROR_ISR_CALLBACK)
void BUS_ERROR_ISR_CALLBACK(void);
#endif

#endif /* VECTTBL_HEADER_INC */
