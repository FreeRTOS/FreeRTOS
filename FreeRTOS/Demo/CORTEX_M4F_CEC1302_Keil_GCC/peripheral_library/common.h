/*
 **********************************************************************************
* © 2013 Microchip Technology Inc. and its subsidiaries.
* You may use this software and any derivatives exclusively with
* Microchip products.
* THIS SOFTWARE IS SUPPLIED BY MICROCHIP "AS IS".
* NO WARRANTIES, WHETHER EXPRESS, IMPLIED OR STATUTORY, APPLY TO THIS SOFTWARE,
* INCLUDING ANY IMPLIED WARRANTIES OF NON-INFRINGEMENT, MERCHANTABILITY,
* AND FITNESS FOR A PARTICULAR PURPOSE, OR ITS INTERACTION WITH MICROCHIP
* PRODUCTS, COMBINATION WITH ANY OTHER PRODUCTS, OR USE IN ANY APPLICATION.
* IN NO EVENT WILL MICROCHIP BE LIABLE FOR ANY INDIRECT, SPECIAL, PUNITIVE,
* INCIDENTAL OR CONSEQUENTIAL LOSS, DAMAGE, COST OR EXPENSE OF ANY KIND
* WHATSOEVER RELATED TO THE SOFTWARE, HOWEVER CAUSED, EVEN IF MICROCHIP HAS
* BEEN ADVISED OF THE POSSIBILITY OR THE DAMAGES ARE FORESEEABLE.
* TO THE FULLEST EXTENT ALLOWED BY LAW, MICROCHIP'S TOTAL LIABILITY ON ALL
* CLAIMS IN ANY WAY RELATED TO THIS SOFTWARE WILL NOT EXCEED THE AMOUNT OF
* FEES, IF ANY, THAT YOU HAVE PAID DIRECTLY TO MICROCHIP FOR THIS SOFTWARE.
* MICROCHIP PROVIDES THIS SOFTWARE CONDITIONALLY UPON YOUR ACCEPTANCE
* OF THESE TERMS.
 **********************************************************************************
 *  common.h
 *      This is the header file including common headers from various modules
 **********************************************************************************
 *  $Revision: #1 $  $DateTime: 2016/04/08 10:18:28 $  $    $
 *  Description: added ict module
 **********************************************************************************
 *  #xx
 **********************************************************************************
 * $File: //depot_pcs/FWEng/Release/projects/CEC1302_PLIB_CLIB/release5/Source/hw_blks/common/include/common.h $
 */

/*********************************************************************************/
/** @defgroup common common
 *  @{
 */

/** @file common.h
* \brief header file including common headers from various modules
* \author App Firmware Team
* 
**********************************************************************************/
#ifndef _COMMON_H_
#define _COMMON_H_

// Include common headers from various modules
// !!! The include order is important !!!
#include "cfg.h"
#include "platform.h"
#include "MCHP_CEC1302.h"
#include "ARM_REG.h"
/* Cortex-M4 processor and core peripherals */
#include "core_cm4.h" 

#include "defs.h"
#include "string.h"

#include "kernel.h"
#include "..\system\system.h"
#include "..\debug\trace.h"
#include "..\interrupt\irqhandler.h"
#include "..\timer\timer_app.h"

#include "cec1302_crypto_api.h"

#endif /*_COMMON_H_*/

/**   @}
 */


