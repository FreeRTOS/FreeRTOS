/*****************************************************************************
* © 2015 Microchip Technology Inc. and its subsidiaries.
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
******************************************************************************

Version Control Information (Perforce)
******************************************************************************
$Revision: #1 $ 
$DateTime: 2016/09/22 08:03:49 $ 
$Author: pramans $
Last Change:	Initial Draft
******************************************************************************/
/** @file interrupt_nvic_perphl.c
* \brief Interrupt NVIC Peripheral Source File
* \author jvasanth
* 
* This file implements the NVIC peripheral functions  
******************************************************************************/

/** @defgroup Interrupt
 *  @{
 */

#include "common_lib.h"
#include "interrupt.h"

/* ------------------------------------------------------------------------------- */
/*                  NVIC Functions                                                 */
/* ------------------------------------------------------------------------------- */

/**  Enable/Disable the NVIC IRQ in the NVIC interrupt controller
 * @param nvic_num : NVIC number (see enum IRQn_Type)
 * @param en_flag : 1 = Enable the NVIC IRQ, 0 = Disable the NVIC IRQ 
 */
void p_interrupt_nvic_enable(IRQn_Type nvic_num, uint8_t en_flag)
{	
	if (en_flag) {
        NVIC_EnableIRQ(nvic_num);
    } else {
        NVIC_DisableIRQ(nvic_num);
    }
    __DSB();	
}

/**  ecia_nvic_clr_en - Clear all NVIC external enables */ 
void p_interrupt_nvic_extEnables_clr(void)
{
    uint32_t i, m;
    
    m = (uint32_t)(MAX_IRQn) >> 5;
    if ( (uint32_t)(MAX_IRQn) & 0x1Ful ) { m++; }
		
    for ( i = 0ul; i < m ; i++ ) 
    {
        NVIC->ICER[i] = 0xfffffffful;        
    }
}

/** Clear all NVIC external enables and pending bits */
void p_interrupt_nvic_enpend_clr(void)
{
    uint32_t i, m;

    // Clear NVIC enables & pending status
    m = (uint32_t)(MAX_IRQn) >> 5;
    if ( (uint32_t)(MAX_IRQn) & 0x1Ful ) { m++; }
		
    for ( i = 0ul; i < m ; i++ ) 
    {
        NVIC->ICER[i] = 0xfffffffful;
        NVIC->ICPR[i] = 0xfffffffful;
    }    
}

/** Set NVIC external priorities to POR value */
void p_interrupt_nvic_priorities_default_set(void)
{
    uint32_t i;
    // Set POR default NVIC priority (highest)
    for ( i = 0ul; i < (uint32_t)MAX_IRQn; i++ ) {
        NVIC->IP[i] = 0u;
    }
}

/** Set NVIC external priorities to specified priority (0 - 7)
 * @param zero-based 3-bit priority value: 0=highest, 7=lowest.
 * @note NVIC highest priority is the value 0, lowest is all 1's.
 * Each external interrupt has an 8-bit register and the priority 
 * is left justified in the registers. MECxxx implements 8 priority 
 * levels or bits [7:5] in the register. Lowest priority = 0xE0
 */
void p_interrupt_nvic_priorities_set(uint8_t new_pri)
{
    uint16_t i;
    
    for ( i = 0ul; i < MAX_IRQn; i++ ) {
        NVIC_SetPriority((IRQn_Type)i, new_pri);
    }
}


/* end interrupt_nvic_perphl.c */
/**   @}
 */
