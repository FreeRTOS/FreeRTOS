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
Last Change: Renamed ecia_init to interrupt_init
******************************************************************************/
/** @file interrupt_api.c
* \brief Interrupt APIs Source File
* \author jvasanth
* 
* This file implements the Interrupt Source file  
******************************************************************************/

/** @defgroup Interrupt
 *  @{
 */
 
#include "common_lib.h"
#include "interrupt.h"
#include "..\pcr\pcr.h"

static uint8_t interrupt_is_girq_direct(uint8_t girq_num);

/* ------------------------------------------------------------------------------- */
/*                  NVIC,ECIA Routing Policy for Direct Mode                       */
/* ------------------------------------------------------------------------------- */
/* In Direct Mode, some interrupts could be configured to be used as aggregated.
 * Configuration:
 *      1. Always set ECS Interrupt Direct enable bit.         
 *      2. If GIRQn aggregated set Block Enable bit.
 *      3. If GIRQn direct then clear Block Enable bit and enable individual NVIC inputs.
 *  Switching issues:
 *  Aggregate enable/disable requires set/clear single GIRQn bit in GIRQ Block En/Clr registers.
 *  Also requires set/clear of individual NVIC Enables.
 *  
 * Note: interrupt_is_girq_direct() internal function uses this policy to detect 
 * if any interrupt is configured as direct or aggregated
*/

/** Initialize EC Interrupt Aggregator
 * @param mode 1 - Direct Map mode, 0 - Fully Aggregated Mode 
 * @param girq_bitmask - BitMask of GIRQ to be configured as aggregated 
 *                     This parameter is only applicable in direct mode.
 * @note All GPIO's and wake capable sources are always 
 * aggregated! GPIO's interrupts will still work in direct mode.
 * Block wakes are not be routed to the processor in direct 
 * mode. 
 * Note2: This function disables and enables global interrupt 
 */
void interrupt_init(uint8_t mode, uint32_t girq_bitmask)
{
    uint32_t isave;
	
    isave = __get_PRIMASK();
    __disable_irq();
		
    //Clear Sleep for Interrupt block
    pcr_sleep_enable(PCR_INT, 0);

    interrupt_mode_set(mode);

    p_interrupt_ecia_girqs_enable_reset();        
    
    p_interrupt_nvic_enpend_clr();
	
    p_interrupt_nvic_priorities_default_set();
    
    if (mode)
    {//If direct mode, enable specific GIRQs to be aggregated
        p_interrupt_ecia_block_enable_bitmask_set(girq_bitmask);
    }
       
    if (!isave) {
        __enable_irq();
    }
}

/** Set interrupt routing mode to aggregated or direct. 
 * @param mode 1 = Direct (except GPIO & wake), 0 = All Aggregated 
 * @note In direct mode, one could enable certain GIRQs as aggregated using 
 * p_interrupt_ecia_block_enable_set function
 */
void interrupt_mode_set(uint8_t mode)
{
    if (mode) 
	{
		p_interrupt_ecia_block_enable_all_clr();        
    } 
	else 
	{
		p_interrupt_ecia_block_enable_all_set();        
    }
		
    p_interrupt_control_set(mode);
}

/** Clears all individual interrupts Enables and Source in ECIA,
 *  and Clears all NVIC external enables and pending bits  
 */
void interrupt_reset(void)
{	
    p_interrupt_ecia_girqs_enable_reset();
    p_interrupt_ecia_girqs_source_reset();	

    p_interrupt_nvic_enpend_clr();
}

/** Enables interrupt for a device 
 * @param dev_iroute - source IROUTING information  
 * @note This function disables and enables global interrupt 
 */
void interrupt_device_enable(uint32_t dev_iroute)
{
    uint32_t isave;
    IRQn_Type nvic_num;
    uint8_t girq_num;
    uint8_t ia_bitpos;
    
    girq_num = (uint8_t)(dev_iroute >> (ECIA_GIRQ_ID_BITPOS)) & 0x1Fu;
    ia_bitpos = (uint8_t)(dev_iroute >> (ECIA_GIRQ_BIT_BITPOS)) & 0x1Fu;    
    
    if (interrupt_is_girq_direct(girq_num)) 
    { // GIRQ is hooked direct        
        nvic_num = (IRQn_Type)((dev_iroute >> (ECIA_NVIC_ID_BITPOS)) & 0xFFul);
    } 
    else 
    { // GIRQ is aggregated        
        nvic_num = (IRQn_Type)((dev_iroute >> (ECIA_IA_NVIC_ID_BITPOS)) & 0xFFul);
    }
    
    isave = __get_PRIMASK();
    __disable_irq();

    NVIC_EnableIRQ(nvic_num);
    p_interrupt_ecia_girq_enable_set(girq_num, ia_bitpos);    
    __DSB();        				        

    if (!isave) {
        __enable_irq();
    }
}


/** Disables interrupt for a device
 * @param dev_iroute - source IROUTING information  
 * @note This function disables and enables global interrupt 
 */
void interrupt_device_disable(uint32_t dev_iroute)
{
    uint32_t isave;
    IRQn_Type nvic_num;
    uint8_t girq_num;
    uint8_t ia_bitpos;

    girq_num = (uint8_t)(dev_iroute >> (ECIA_GIRQ_ID_BITPOS)) & 0x1Fu;
    ia_bitpos = (uint8_t)(dev_iroute >> (ECIA_GIRQ_BIT_BITPOS)) & 0x1Fu;    
    
    isave = __get_PRIMASK();
    __disable_irq();
    
    if (interrupt_is_girq_direct(girq_num)) 
    { // GIRQ is hooked direct        
        nvic_num = (IRQn_Type)((dev_iroute >> (ECIA_NVIC_ID_BITPOS)) & 0xFFul);
        NVIC_DisableIRQ(nvic_num);
    }   
        
    p_interrupt_ecia_girq_enable_clr(girq_num, ia_bitpos);    
    __DSB();        				        

    if (!isave) {
        __enable_irq();
    }
}

/** ecia_is_girq_direct - Return true if GIRQn sources can be directly 
 * connected to the NVIC - based on ECS->INTERRUPT_CONTROL and GIRQ block enable
 * @param girq_num - enum MEC_GIRQ_IDS
 * @return 1 if GIRQn sources can be directly routed to the NVIC, else 0
 */
static uint8_t interrupt_is_girq_direct(uint8_t girq_num)
{    
    uint32_t bpos;
    uint8_t retVal;
    uint8_t girq_block_enabled;
    
    retVal = 0;
    
    bpos = (girq_num & 0x1Fu) + 8u;
    
    if ((ECIA_GIRQ_DIRECT_BITMAP) & (1ul << bpos)) 
    {        
        if (p_interrupt_control_get())                
        {// direct NVIC enabled
           
            girq_block_enabled = p_interrupt_ecia_block_enable_get(girq_num);
            
            if (!girq_block_enabled)
            {
                retVal = 1;
            }
        }
    }
    return retVal;
}


/* ------------------------------------------------------------------------------- */
/*                  ECIA APIs using device IROUTE() as input                       */ 
/* ------------------------------------------------------------------------------- */

/** Clear Source in the ECIA for the device  
 * @param devi - device IROUTING value  
 */
void interrupt_device_ecia_source_clear(const uint32_t dev_iroute)
{    
    uint8_t girq_num;
    uint8_t ia_bit_pos;
    
    girq_num = (uint8_t)(dev_iroute >> (ECIA_GIRQ_ID_BITPOS)) & 0x1Fu;
    ia_bit_pos = (uint8_t)(dev_iroute >> (ECIA_GIRQ_BIT_BITPOS)) & 0x1Fu;           
            
    p_interrupt_ecia_girq_source_clr(girq_num, ia_bit_pos);        
    __DSB();
}

/** Get the Source bit in the ECIA for the device  
 * @param devi - device IROUTING value  
 * @return 0 if source bit not set; else non-zero value
 */
uint32_t interrupt_device_ecia_source_get(const uint32_t dev_iroute)
{    
    uint8_t girq_num;
    uint8_t ia_bit_pos;
    uint8_t retVal;
    
    girq_num = (uint8_t)(dev_iroute >> (ECIA_GIRQ_ID_BITPOS)) & 0x1Fu;
    ia_bit_pos = (uint8_t)(dev_iroute >> (ECIA_GIRQ_BIT_BITPOS)) & 0x1Fu;           
            
    retVal = p_interrupt_ecia_girq_source_get(girq_num, ia_bit_pos);        
    return retVal;
}

/** Get the Result bit in the ECIA for the device  
 * @param devi - device IROUTING value  
 * @return 0 if result bit not set; else non-zero value
 */
uint32_t interrupt_device_ecia_result_get(const uint32_t dev_iroute)
{    
    uint8_t girq_num;
    uint8_t ia_bit_pos;
    uint8_t retVal;
    
    girq_num = (uint8_t)(dev_iroute >> (ECIA_GIRQ_ID_BITPOS)) & 0x1Fu;
    ia_bit_pos = (uint8_t)(dev_iroute >> (ECIA_GIRQ_BIT_BITPOS)) & 0x1Fu;           
            
    retVal = p_interrupt_ecia_girq_result_get(girq_num, ia_bit_pos);        
    return retVal;
}

/* ------------------------------------------------------------------------------- */
/*                  NVIC APIs using device IROUTE() as input                       */ 
/* ------------------------------------------------------------------------------- */
/* Note that if the device interrupt is aggregated, then these APIs would affect the 
 * NVIC corresponding to the aggregated GIRQ 
 */

/**  Enable/Disable the NVIC (in the NVIC controller) for the device
 * @param dev_iroute : source IROUTING information (encoded in a uint32_t)
 * @param en_flag : 1 = Enable the NVIC IRQ, 0 = Disable the NVIC IRQ 
 * @note 1. Recommended to use interrupt_device_enable, interrupt_device_disable
 * to enable/disable interrupts for the device, since those APIs configure ECIA as well
 * 2. This function disables and enables global interrupt    
 */
void interrupt_device_nvic_enable(uint32_t dev_iroute, uint8_t en_flag)
{
    uint32_t isave;
    IRQn_Type nvic_num;
		
    if (p_interrupt_control_get())        
    { // direct				
        nvic_num = (IRQn_Type)((dev_iroute >> (ECIA_NVIC_ID_BITPOS)) & 0xFFul);						
    } 
    else // fully aggregated
    {				
        nvic_num = (IRQn_Type)((dev_iroute >> (ECIA_IA_NVIC_ID_BITPOS)) & 0xFFul);
    }
    
    isave = __get_PRIMASK();
    __disable_irq();
    
    p_interrupt_nvic_enable(nvic_num, en_flag);		
   
    if (!isave) {
        __enable_irq();
    }
}


/** Set NVIC priority for specified peripheral interrupt 
 * @param dev_iroute - source IROUTING information (encoded in a uint32_t)
 * @param nvic_pri - NVIC Priority
 * @note If ECIA is in aggregated mode, the priority affects all interrupt 
 * sources in the GIRQ. 
 */
void interrupt_device_nvic_priority_set(const uint32_t dev_iroute, const uint8_t nvic_pri)
{
    IRQn_Type nvic_num;
	
    if (p_interrupt_control_get())        
    { // direct				
        nvic_num = (IRQn_Type)((dev_iroute >> (ECIA_NVIC_ID_BITPOS)) & 0xFFul);						
    } 
    else // fully aggregated
    {				
        nvic_num = (IRQn_Type)((dev_iroute >> (ECIA_IA_NVIC_ID_BITPOS)) & 0xFFul);
    }
		
    NVIC_SetPriority(nvic_num, (uint32_t)nvic_pri);
}

/** Return NVIC priority for the device's interrupt
 * @param dev_iroute - source IROUTING information 
 * @return uint32_t  NVIC priority 
 */
uint32_t interrupt_device_nvic_priority_get(const uint32_t dev_iroute)
{
    IRQn_Type nvic_num;
	uint32_t nvic_priority;
    
    if (p_interrupt_control_get())        
    { // direct				
        nvic_num = (IRQn_Type)((dev_iroute >> (ECIA_NVIC_ID_BITPOS)) & 0xFFul);						
    } 
    else // fully aggregated
    {				
        nvic_num = (IRQn_Type)((dev_iroute >> (ECIA_IA_NVIC_ID_BITPOS)) & 0xFFul);
    }
    
    nvic_priority = NVIC_GetPriority(nvic_num);
		
    return nvic_priority;
}


/** Return NVIC pending for the device
 * @param dev_iroute - source IROUTING information 
 * @return uint8_t 0(not pending), 1 (pending in NVIC) 
 *  
 */
uint8_t interrupt_device_nvic_pending_get(const uint32_t dev_iroute)
{
    IRQn_Type nvic_num;
    uint8_t nvic_pending;
    
    if (p_interrupt_control_get())        
    { // direct				
        nvic_num = (IRQn_Type)((dev_iroute >> (ECIA_NVIC_ID_BITPOS)) & 0xFFul);						
    } 
    else // fully aggregated
    {				
        nvic_num = (IRQn_Type)((dev_iroute >> (ECIA_IA_NVIC_ID_BITPOS)) & 0xFFul);
    }
    
    nvic_pending = (uint8_t)(NVIC_GetPendingIRQ(nvic_num));
		
    return nvic_pending;
}


/** Set NVIC pending for interrupt source
 * @param dev_iroute - source IROUTING information   
 */
void interrupt_device_nvic_pending_set(const uint32_t dev_iroute)
{
    IRQn_Type nvic_num;    
    
    if (p_interrupt_control_get())        
    { // direct				
        nvic_num = (IRQn_Type)((dev_iroute >> (ECIA_NVIC_ID_BITPOS)) & 0xFFul);						
    } 
    else // fully aggregated
    {				
        nvic_num = (IRQn_Type)((dev_iroute >> (ECIA_IA_NVIC_ID_BITPOS)) & 0xFFul);
    }
    
    NVIC_SetPendingIRQ(nvic_num);   
}

/** Clears NVIC pending for interrupt source
 * @param dev_iroute - source IROUTING information 
 * @return uint8_t 0(not pending), 1 (pending in NVIC) - before clear 
 * @note This function disables and enables global interrupt  
 */
uint8_t interrupt_device_nvic_pending_clear(const uint32_t dev_iroute)
{
    uint32_t was_masked;
    IRQn_Type nvic_num;
    uint8_t pending;
    
    if (p_interrupt_control_get())        
    { // direct				
        nvic_num = (IRQn_Type)((dev_iroute >> (ECIA_NVIC_ID_BITPOS)) & 0xFFul);						
    } 
    else // fully aggregated
    {				
        nvic_num = (IRQn_Type)((dev_iroute >> (ECIA_IA_NVIC_ID_BITPOS)) & 0xFFul);
    }
    
    was_masked = __get_PRIMASK();
    __disable_irq();
    
    pending = (uint8_t)(NVIC_GetPendingIRQ(nvic_num));

    NVIC_ClearPendingIRQ(nvic_num);
    __DSB();
    
    if (!was_masked) {
        __enable_irq();
    }
		
    return pending;
}

/* ------------------------------------------------------------------------------- */

/* end interrupt_api.c */
/**   @}
 */
