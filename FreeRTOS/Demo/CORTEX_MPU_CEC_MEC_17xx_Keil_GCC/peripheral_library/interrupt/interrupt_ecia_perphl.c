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
/** @file interrupt_ecia_perphl.c
* \brief Interrupt ECIA Peripheral Source File
* \author jvasanth
* 
* This file implements the ECIA peripheral functions  
******************************************************************************/

/** @defgroup Interrupt
 *  @{
 */

#include "common_lib.h"
#include "interrupt.h"

#define ECIA	((INTS_Type               *) INTS_BASE)
#define	ECS		((EC_REG_BANK_Type *)   EC_REG_BANK_BASE)

/* ------------------------------------------------------------------------------- */
/*   Operations on GIRQ Block Enable Set, Enable Clear and Status Register         */
/* ------------------------------------------------------------------------------- */

/** Enable specified GIRQ in ECIA block
 * @param girq_id - enum MEC_GIRQ_IDS 
 */
void p_interrupt_ecia_block_enable_set(uint8_t girq_id)
{
    if ( girq_id < (MEC_GIRQ_ID_MAX) ) {
        ECIA->BLOCK_ENABLE_SET = (1ul << ((girq_id + 8) & 0x1Fu));
    }
}

/** Enable GIRQs in ECIA Block 
 * @param girq_bitmask - Bitmask of GIRQs to be enabled in ECIA Block  
 */
void p_interrupt_ecia_block_enable_bitmask_set(uint32_t girq_bitmask)
{    
    ECIA->BLOCK_ENABLE_SET = girq_bitmask;    
}

/** Check if specified GIRQ block enabled or not
 * @param girq_id - enum MEC_GIRQ_IDS 
 * @return retVal - 1 if the particular GIRQ block enabled, else 0
 */
uint8_t p_interrupt_ecia_block_enable_get(uint8_t girq_id)
{
    uint8_t retVal;
    
    retVal = 0;
    if ( girq_id < (MEC_GIRQ_ID_MAX) ) 
    {        
        if ((ECIA->BLOCK_ENABLE_SET) & (1ul << ((girq_id + 8) & 0x1Fu)))
        {
           retVal = 1; 
        }
    }
    return retVal;
}

/** Set all GIRQ block enables */
void p_interrupt_ecia_block_enable_all_set(void)
{    
    ECIA->BLOCK_ENABLE_SET = 0xfffffffful; 
}

/** Clear specified GIRQ in ECIA Block 
 * @param girq_id - enum MEC_GIRQ_IDS 
 */
void p_interrupt_ecia_block_enable_clr(uint8_t girq_id)
{
    if ( girq_id < (MEC_GIRQ_ID_MAX) ) {
        ECIA->BLOCK_ENABLE_CLEAR = (1ul << ((girq_id + 8) & 0x1Fu));
    }
}

/** Clear GIRQs in ECIA Block 
 * @param girq_bitmask - Bitmask of GIRQs to be cleared in ECIA Block  
 */
void p_interrupt_ecia_block_enable_bitmask_clr(uint32_t girq_bitmask)
{    
    ECIA->BLOCK_ENABLE_CLEAR = girq_bitmask;    
}

/** p_interrupt_ecia_block_enable_all_clr - Clears all GIRQ block enables */
 void p_interrupt_ecia_block_enable_all_clr(void)
{    
    ECIA->BLOCK_ENABLE_CLEAR = 0xfffffffful; 
}

/** Get status of GIRQ in ECIA Block
 * @param girq_id - enum MEC_GIRQ_IDS  
 * @return 0 if status bit not set; else non-zero value
 */
uint32_t p_interrupt_ecia_block_irq_status_get(uint8_t girq_id)
{ 	
    uint32_t retVal;

    retVal = ECIA->BLOCK_IRQ_VECTOR & (1ul << ((girq_id + 8) & 0x1Fu));

    return retVal;		
}

/** Reads the Block IRQ Vector Register
  * @return 32-bit value
 */
uint32_t p_interrupt_ecia_block_irq_all_status_get(void)
{ 	
    uint32_t retVal;

    retVal = ECIA->BLOCK_IRQ_VECTOR;

    return retVal;		
}


/* ------------------------------------------------------------------------------- */
/*   Operations on GIRQx Source, Enable, Result and Enable Registers               */
/* ------------------------------------------------------------------------------- */

/** Clear specified interrupt source bit in GIRQx
 * @param girq_id - enum MEC_GIRQ_IDS
 * @param bitnum -[0, 31]
 */
void p_interrupt_ecia_girq_source_clr(int16_t girq_id, uint8_t bitnum)
{
	  __IO uint32_t *girq_source = (uint32_t*)ECIA;
		  
    if ( girq_id < (MEC_GIRQ_ID_MAX) ) {
			/* Each GIRQ has 5 32bit fields: SRC, ENABLE_SET, ENABLE_CLR, RESULT & RESERVED
			 * please refer INTS_Type in MCHP_device_internal.h
			 * Based on the girq id calculate the offset in the structure INTS_Type
			 * 
			 * BASED ON THE STRUCTURE DEFINITION OF INTS_Type ALL FIELDS ARE ALIGNED ON
			 * 32 BIT BOUNDARY, FOLLOWING WILL NOT WORK IF THIS SCHEME CHANGES
			*/
			  girq_source += (5 * girq_id);
        *girq_source |= (1ul << (bitnum & 0x1Fu));
    }
}

/** Read the specified interrupt source bit in GIRQx
 * @param girq_id - enum MEC_GIRQ_IDS
 * @param bitnum -[0, 31]
 * @return 0 if source bit not set; else non-zero value
 */
uint32_t p_interrupt_ecia_girq_source_get(int16_t girq_id, uint8_t bitnum)
{
    uint32_t retVal;
	  __IO uint32_t *girq_source = (uint32_t*)ECIA;
	
    retVal = 0;
    if ( girq_id < (MEC_GIRQ_ID_MAX) ) {
			/* Each GIRQ has 5 32bit fields: SRC, ENABLE_SET, ENABLE_CLR, RESULT & RESERVED
			 * please refer INTS_Type in MCHP_device_internal.h
			 * Based on the girq id calculate the offset in the structure INTS_Type
			 * 
			 * BASED ON THE STRUCTURE DEFINITION OF INTS_Type ALL FIELDS ARE ALIGNED ON
			 * 32 BIT BOUNDARY, FOLLOWING WILL NOT WORK IF THIS SCHEME CHANGES
			*/
			  girq_source += (5 * girq_id);			
        retVal = (*girq_source & (1ul << (bitnum & 0x1Fu)));
    }		
    return retVal;
}

/** Enable the specified interrupt in GIRQx
 * girq_id - enum MEC_GIRQ_IDS
 * bitnum = [0, 31]
 */
void p_interrupt_ecia_girq_enable_set(uint16_t girq_id, uint8_t bitnum)
{
	  __IO uint32_t *girq_enable_set = (uint32_t*)(&(ECIA->GIRQ08_EN_SET));
	
    if ( girq_id < (MEC_GIRQ_ID_MAX) ) {
			/* Each GIRQ has 5 32bit fields: SRC, ENABLE_SET, ENABLE_CLR, RESULT & RESERVED
			 * please refer INTS_Type in MCHP_device_internal.h
			 * Based on the girq id calculate the offset in the structure INTS_Type
			 * 
			 * BASED ON THE STRUCTURE DEFINITION OF INTS_Type ALL FIELDS ARE ALIGNED ON
			 * 32 BIT BOUNDARY, FOLLOWING WILL NOT WORK IF THIS SCHEME CHANGES
			*/
			  girq_enable_set += (5 * girq_id);			
        *girq_enable_set |= (1ul << (bitnum & 0x1Fu));
    }
}

/** Disable the specified interrupt in GIRQx
 * girq_id - enum MEC_GIRQ_IDS
 * bitnum = [0, 31]
 */
void p_interrupt_ecia_girq_enable_clr(uint16_t girq_id, uint8_t bitnum)
{
	  __IO uint32_t *girq_enable_clr = (uint32_t*)(&(ECIA->GIRQ08_EN_CLR));
	
    if ( girq_id < (MEC_GIRQ_ID_MAX) ) {
			/* Each GIRQ has 5 32bit fields: SRC, ENABLE_SET, ENABLE_CLR, RESULT & RESERVED
			 * please refer INTS_Type in MCHP_device_internal.h
			 * Based on the girq id calculate the offset in the structure INTS_Type
			 * 
			 * BASED ON THE STRUCTURE DEFINITION OF INTS_Type ALL FIELDS ARE ALIGNED ON
			 * 32 BIT BOUNDARY, FOLLOWING WILL NOT WORK IF THIS SCHEME CHANGES
			*/
			  girq_enable_clr += (5 * girq_id);			
        *girq_enable_clr |= (1ul << (bitnum & 0x1Fu));
    }
}

/** Read the status of the specified interrupt in GIRQx
 * girq_id - enum MEC_GIRQ_IDS
 * bitnum = [0, 31]
 * @return 0 if enable bit not set; else non-zero value
 */
uint32_t p_interrupt_ecia_girq_enable_get(uint16_t girq_id, uint8_t bitnum)
{
    uint32_t retVal;
	  __IO uint32_t *girq_enable_set = (uint32_t*)(&(ECIA->GIRQ08_EN_SET));

    retVal = 0;
    if ( girq_id < (MEC_GIRQ_ID_MAX) ) {
			/* Each GIRQ has 5 32bit fields: SRC, ENABLE_SET, ENABLE_CLR, RESULT & RESERVED
			 * please refer INTS_Type in MCHP_device_internal.h
			 * Based on the girq id calculate the offset in the structure INTS_Type
			 * 
			 * BASED ON THE STRUCTURE DEFINITION OF INTS_Type ALL FIELDS ARE ALIGNED ON
			 * 32 BIT BOUNDARY, FOLLOWING WILL NOT WORK IF THIS SCHEME CHANGES
			*/
			  girq_enable_set += (5 * girq_id);			
        retVal = (*girq_enable_set  & (1ul << (bitnum & 0x1Fu)));
    }
    return retVal;
}

/** Read the result bit of the interrupt in GIRQx
 * @param girq_id - enum MEC_GIRQ_IDS
 * @param bitnum -[0, 31]
 * @return 0 if enable bit not set; else non-zero value
 */
uint32_t p_interrupt_ecia_girq_result_get(int16_t girq_id, uint8_t bitnum)
{
    uint32_t retVal;
	  __IO uint32_t *girq_result = (uint32_t*)(&(ECIA->GIRQ08_RESULT));
	
    retVal = 0;
    if ( girq_id < (MEC_GIRQ_ID_MAX) ) {
			/* Each GIRQ has 5 32bit fields: SRC, ENABLE_SET, ENABLE_CLR, RESULT & RESERVED
			 * please refer INTS_Type in MCHP_device_internal.h
			 * Based on the girq id calculate the offset in the structure INTS_Type
			 * 
			 * BASED ON THE STRUCTURE DEFINITION OF INTS_Type ALL FIELDS ARE ALIGNED ON
			 * 32 BIT BOUNDARY, FOLLOWING WILL NOT WORK IF THIS SCHEME CHANGES
			*/
			  girq_result += (5 * girq_id);			
        retVal = (*girq_result & (1ul << (bitnum & 0x1Fu)));
    }
		
    return retVal;
}

/* ------------------------------------------------------------------------------- */
/*                         Operations on all GIRQs                                 */
/* ------------------------------------------------------------------------------- */

/** Clear all aggregator GIRQn status registers */
void p_interrupt_ecia_girqs_source_reset(void)
{
    uint16_t i;
	  __IO uint32_t *girq_source = (uint32_t*)ECIA;

    for ( i = 0u; i < (MEC_GIRQ_ID_MAX); i++ ) {
			/* Each GIRQ has 5 32bit fields: SRC, ENABLE_SET, ENABLE_CLR, RESULT & RESERVED
			 * please refer INTS_Type in MCHP_device_internal.h
			 * Based on the girq id calculate the offset in the structure INTS_Type
			 * 
			 * BASED ON THE STRUCTURE DEFINITION OF INTS_Type ALL FIELDS ARE ALIGNED ON
			 * 32 BIT BOUNDARY, FOLLOWING WILL NOT WORK IF THIS SCHEME CHANGES
			*/
			  girq_source += 5;			
        *girq_source = 0xfffffffful;
    }    
}

/** Clear all aggregator GIRQn enables */
 void p_interrupt_ecia_girqs_enable_reset(void)
{
    uint16_t i;
	  __IO uint32_t *girq_enable_clr = (uint32_t*)(&(ECIA->GIRQ08_EN_CLR));

    for ( i = 0u; i < (MEC_GIRQ_ID_MAX); i++ ) {
			/* Each GIRQ has 5 32bit fields: SRC, ENABLE_SET, ENABLE_CLR, RESULT & RESERVED
			 * please refer INTS_Type in MCHP_device_internal.h
			 * Based on the girq id calculate the offset in the structure INTS_Type
			 * 
			 * BASED ON THE STRUCTURE DEFINITION OF INTS_Type ALL FIELDS ARE ALIGNED ON
			 * 32 BIT BOUNDARY, FOLLOWING WILL NOT WORK IF THIS SCHEME CHANGES
			*/
			  girq_enable_clr += 5;				
        *girq_enable_clr = 0xfffffffful;
    }    
}

/* ------------------------------------------------------------------------------- */
/*                  Function to set interrupt control                              */
/* ------------------------------------------------------------------------------- */

/** Set interrupt control 
 * @param nvic_en_flag : 0 = Alternate NVIC disabled, 1 = Alternate NVIC enabled
 */
void p_interrupt_control_set(uint8_t nvic_en_flag)
{		
    ECS->INTERRUPT_CONTROL = nvic_en_flag;
}

/** Read interrupt control 
 * @return uint8_t - 0 = Alternate NVIC disabled, 1 = Alternate NVIC enabled
 */
uint8_t p_interrupt_control_get(void)
{		
    return (ECS->INTERRUPT_CONTROL & 0x1);
}

/* end interrupt_ecia_perphl.c */
/**   @}
 */
