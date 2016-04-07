/****************************************************************************
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
*/

/** @defgroup pwm pwm_c_wrapper
 *  @{
 */
/** @file pwm_c_wrapper.cpp
 \brief the pwm component C wrapper   
 This program is designed to allow the other C programs to be able to use this component

 There are entry points for all C wrapper API implementation

<b>Platform:</b> This is ARC-based component 

<b>Toolset:</b> Metaware IDE(8.5.1)
<b>Reference:</b> smsc_reusable_fw_requirement.doc */

/*******************************************************************************
 *  SMSC version control information (Perforce):
 *
 *  FILE:     $File: //depot_pcs/FWEng/Release/projects/CEC1302_CLIB/release2/Source/hw_blks/common/system/system.c $
 *  REVISION: $Revision: #1 $
 *  DATETIME: $DateTime: 2015/12/23 15:37:58 $
 *  AUTHOR:   $Author: akrishnan $
 *
 *  Revision history (latest first):
 *      #3  2011/05/09  martin_y    update to Metaware IDE(8.5.1) 
 *      #2  2011/03/25  martin_y    support FPGA build 058 apps
 *      #1  2011/03/23  martin_y    branch from MEC1618 sample code: MEC1618_evb_sample_code_build_0200
 ***********************************************************************************
 */
/* Imported Header File */
//#include    "common.h"
//#include    "build.h"
#include    <stdint.h>

#define ADDR_PCR_PROCESSOR_CLOCK_CONTROL    0x40080120
#define MMCR_PCR_PROCESSOR_CLOCK_CONTROL    (*(uint32_t *)(ADDR_PCR_PROCESSOR_CLOCK_CONTROL))
#define CPU_CLOCK_DIVIDER					1

/* The start up code is configured to use the following array as the stack used
by main(), which will then also get used by FreeRTOS interrupt handlers after 
the scheduler has been started. */
#warning If the array size is modified here then ulMainStackSize must also be modified in startup_ARMCM4.S.
volatile uint32_t ulMainStack[ 200 ];

/******************************************************************************/
/** system_set_ec_clock
* Set CPU speed
* @param void
* @return void
*******************************************************************************/

void system_set_ec_clock(void)
{

    /* Set ARC CPU Clock Divider to determine the CPU speed */
    /* Set divider to 8 for 8MHz operation, MCLK in silicon chip is 64MHz, CPU=MCLK/Divider */
    MMCR_PCR_PROCESSOR_CLOCK_CONTROL = CPU_CLOCK_DIVIDER;

} /* End system_set_ec_clock() */

