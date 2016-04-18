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
$DateTime: 2016/04/08 10:18:28 $ 
$Author: pramans $
Last Change:	Updated for tabs
******************************************************************************/
/** @file pcr_api.c
* \brief Power, Clocks, and Resets API Source file
* \author jvasanth
* 
* This file implements the PCR APIs  
******************************************************************************/

/** @defgroup PCR
 *  @{
 */

#include "common_lib.h"
#include "pcr.h"


/* ------------------------------------------------------------------------------- */
/*  Functions to program Sleep Enable, CLK Reqd Status, Reset Enable for a block   */
/* ------------------------------------------------------------------------------- */

/** Sets or Clears block specific bit in PCR Sleep Enable Register
 * @param pcr_block_id - pcr block id encoded using PCRx_REGS_BIT 
 * @param set_clr_flag - Flag to set (1) or clear (0) bit in the PCR Sleep Enable Register
 */
void pcr_sleep_enable(uint32_t pcr_block_id, uint8_t set_clr_flag)
{
    uint32_t bit_mask;
    uint8_t pcr_reg_id;	
 
    bit_mask = 1UL<<(pcr_block_id & 0xFFu);
    pcr_reg_id = (uint8_t)((pcr_block_id >> PCRx_REGS_POS_SLEEP_ENABLE) & 0xFFu);

    p_pcr_reg_update(pcr_reg_id, bit_mask, set_clr_flag);	
}


/** Get Clock Required Status for the block
 * @param pcr_block_id - pcr block id encoded using PCRx_REGS_BIT 
 * @return uint8_t - 1 if Clock Required Status set, else 0
 */
uint8_t pcr_clock_reqd_status_get(uint32_t pcr_block_id)
{
    uint32_t bit_mask;
    uint8_t pcr_reg_id, retVal;	
 
    bit_mask = 1UL<<(pcr_block_id & 0xFFu);
    pcr_reg_id = (uint8_t)((pcr_block_id >> PCRx_REGS_POS_CLK_REQD_STS) & 0xFFu);

    retVal = 0;
    if (p_pcr_reg_get(pcr_reg_id, bit_mask))
    {
        retVal = 1;
    }
    
    return retVal;
}

/** Sets or Clears Reset Enable register bit for the block
 * @param pcr_block_id - pcr block id encoded using PCRx_REGS_BIT 
 * @param set_clr_flag - Flag to set (1) or clear (0) bit in the PCR Reset Enable Register
 */
void pcr_reset_enable(uint32_t pcr_block_id, uint8_t set_clr_flag)
{
    uint32_t bit_mask;
    uint8_t pcr_reg_id;	
 
    bit_mask = 1UL<<(pcr_block_id & 0xFFu);
    pcr_reg_id = (uint8_t)((pcr_block_id >> PCRx_REGS_POS_RESET_ENABLE) & 0xFFu);

    p_pcr_reg_update(pcr_reg_id, bit_mask, set_clr_flag);					
}


/* ------------------------------------------------------------------------------- */
/*                  Functions for entering low power modes                         */
/* ------------------------------------------------------------------------------- */

/** Instructs all blocks to sleep by setting the Sleep Enable bits */
void pcr_all_blocks_sleep(void)
{
	p_pcr_reg_write(PCR_REG_CHIP_SLEEP_ENABLE, 0xFFFFFFFF);
	p_pcr_reg_write(PCR_REG_EC_SLEEP_ENABLE, 0xFFFFFFFF);
	p_pcr_reg_write(PCR_REG_HOST_SLEEP_ENABLE, 0xFFFFFFFF);
	p_pcr_reg_write(PCR_REG_EC_SLEEP_ENABLE_2, 0xFFFFFFFF);		
}

/** Clears the Sleep Enable bits for all blocks */
 void pcr_all_blocks_wake(void)
{
	p_pcr_reg_write(PCR_REG_CHIP_SLEEP_ENABLE, 0);
	p_pcr_reg_write(PCR_REG_EC_SLEEP_ENABLE, 0);
	p_pcr_reg_write(PCR_REG_HOST_SLEEP_ENABLE, 0);
	p_pcr_reg_write(PCR_REG_EC_SLEEP_ENABLE_2, 0);		
}

/** Programs required sleep mode in System Sleep Control Register
 * @param sleep_mode - see enum SYSTEM_SLEEP_MODES
 */
void pcr_system_sleep(uint8_t sleep_mode)
{
    p_pcr_system_sleep_ctrl_write(sleep_mode);
}


/* end pcr_api.c */
/**   @}
 */
