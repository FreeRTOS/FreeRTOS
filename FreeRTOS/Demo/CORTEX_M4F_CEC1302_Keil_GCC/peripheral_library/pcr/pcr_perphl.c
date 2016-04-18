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
/** @file pcr_perphl.c
* \brief Power, Clocks, and Resets Peripheral Source file
* \author jvasanth
* 
* This file implements the PCR Peripheral functions  
******************************************************************************/

/** @defgroup PCR
 *  @{
 */

#include "common_lib.h"
#include "pcr.h"

/* ---------------------------------------------------------------------- */
/* Generic functions to program and read 32-bit values from PCR Registers */
/* ---------------------------------------------------------------------- */
/** Writes 32-bit value in the PCR Register
 * @param pcr_reg_id - pcr register id 
 * @param value - 32-bit value
 */
void p_pcr_reg_write(uint8_t pcr_reg_id, uint32_t value)
{
    __IO uint32_t *pPCR_Reg;

    pPCR_Reg = (uint32_t *)(PCR_BASE);		

    pPCR_Reg += pcr_reg_id;

    *pPCR_Reg = value;			
}

/** Reads 32-bit value from the PCR Register
 * @param pcr_reg_id - pcr register id 
 * @return value - 32-bit value
 */
uint32_t p_pcr_reg_read(uint8_t pcr_reg_id)
{
    __IO uint32_t *pPCR_Reg;
    uint32_t retVal;

    pPCR_Reg = (uint32_t *)(PCR_BASE);		

    pPCR_Reg += pcr_reg_id;	

    retVal = *pPCR_Reg;

    return retVal;
}

/* ---------------------------------------------------------------------- */
/*          Functions to set, clr and get bits in PCR Registers           */
/* ---------------------------------------------------------------------- */

/** Sets bits in a PCR Register
 * @param pcr_reg_id - pcr register id 
 * @param bit_mask - Bit mask of bits to set 
 */
void p_pcr_reg_set(uint8_t pcr_reg_id, uint32_t bit_mask)
{
    __IO uint32_t *pPCR_Reg;

    pPCR_Reg = (uint32_t *)(PCR_BASE);		

    pPCR_Reg += pcr_reg_id;

    *pPCR_Reg |= bit_mask;			
}

/** Clears bits in a PCR Register
 * @param pcr_reg_id - pcr register id 
 * @param bit_mask - Bit mask of bits to clear 
 */
void p_pcr_reg_clr(uint8_t pcr_reg_id, uint32_t bit_mask)
{
    __IO uint32_t *pPCR_Reg;

    pPCR_Reg = (uint32_t *)(PCR_BASE);		

    pPCR_Reg += pcr_reg_id;

    *pPCR_Reg &= ~bit_mask;			
}

/** Read bits in a PCR Register
 * @param pcr_reg_id - pcr register id 
 * @param bit_mask - Bit mask of bits to read 
 * @return value - 32-bit value
 */
uint32_t p_pcr_reg_get(uint8_t pcr_reg_id, uint32_t bit_mask)
{
    __IO uint32_t *pPCR_Reg;
    uint32_t retVal;

    pPCR_Reg = (uint32_t *)(PCR_BASE);		

    pPCR_Reg += pcr_reg_id;		

    retVal = (*pPCR_Reg) & bit_mask;

    return retVal;
}

/** Sets or Clears bits in a PCR Register - Helper Function
 * @param pcr_reg_id - pcr register id 
 * @param bit_mask - Bit mask of bits to set or clear
 * @param set_clr_flag - Flag to set (1) or clear (0) bits in the PCR Register
 */
void p_pcr_reg_update(uint8_t pcr_reg_id, uint32_t bit_mask, uint8_t set_clr_flag)
{
    if (set_clr_flag)
    {
            p_pcr_reg_set(pcr_reg_id, bit_mask);
    }
    else
    {
            p_pcr_reg_clr(pcr_reg_id, bit_mask);
    }        
}

/* ---------------------------------------------------------------------- */
/*          Functions to operate on System Sleep Control Register         */
/* ---------------------------------------------------------------------- */

/**
 * Sets/Clears the Ring oscillator power down bit 
 *         in System Sleep Control Register
 * @param set_clr_flag - 1 - Sets the bit, 0 - clears the bit
 */
void p_pcr_system_sleep_ctrl_ring_osc_power_down(uint8_t set_clr_flag)
{
	__IO uint32_t *pPCR_Reg;		
		
    pPCR_Reg = (uint32_t *)(PCR_BASE)	+ PCR_REG_SYSTEM_SLEEP_CTRL;

    if (set_clr_flag)
    {
            *pPCR_Reg |= PCR_SYS_SLP_CTRL_RING_OSC_PWR_DOWN_BITMASK;			
    }
    else
    {
        *pPCR_Reg &= ~PCR_SYS_SLP_CTRL_RING_OSC_PWR_DOWN_BITMASK;			
    }
}

/** Sets/Clears the Ring oscillator output gate bit 
 *         in System Sleep Control Register
 * @param set_clr_flag - 1 - Sets the bit, 0 - clears the bit
 */
void p_pcr_system_sleep_ctrl_ring_osc_output_gate(uint8_t set_clr_flag)
{
	__IO uint32_t *pPCR_Reg;		
		
    pPCR_Reg = (uint32_t *)(PCR_BASE)	+ PCR_REG_SYSTEM_SLEEP_CTRL;

    if (set_clr_flag)
    {
            *pPCR_Reg |= PCR_SYS_SLP_CTRL_RING_OSC_OUTPUT_GATE_BITMASK;			
    }
    else
    {
        *pPCR_Reg &= ~PCR_SYS_SLP_CTRL_RING_OSC_OUTPUT_GATE_BITMASK;			
    }
}

/** Sets/Clears the Core regulator standby bit 
 *         in System Sleep Control Register
 * @param set_clr_flag - 1 - Sets the bit, 0 - clears the bit
 */
void p_pcr_system_sleep_ctrl_core_regulator_stdby(uint8_t set_clr_flag)
{
	__IO uint32_t *pPCR_Reg;		
		
    pPCR_Reg = (uint32_t *)(PCR_BASE)	+ PCR_REG_SYSTEM_SLEEP_CTRL;

    if (set_clr_flag)
    {
            *pPCR_Reg |= PCR_SYS_SLP_CTRL_CORE_REGLTOR_STDBY_BITMASK;			
    }
    else
    {
        *pPCR_Reg &= ~PCR_SYS_SLP_CTRL_CORE_REGLTOR_STDBY_BITMASK;			
    }
}

/** Writes required sleep mode in System Sleep Control Register
 * @param sleep_value - System Sleep control value - [D2, D1, D0]
 */
void p_pcr_system_sleep_ctrl_write(uint8_t sleep_value)
{
    __IO uint32_t *pPCR_Reg;		
    
    pPCR_Reg = (uint32_t *)(PCR_BASE)	+ PCR_REG_SYSTEM_SLEEP_CTRL;	

    *pPCR_Reg = (sleep_value & 0x7);		
}

/** Reads the System Sleep Control PCR Register
 * @return value - byte 0 of the system sleep control PCR register
 */
uint8_t p_pcr_system_sleep_ctrl_read(void)
{
    __IO uint32_t *pPCR_Reg;
    uint8_t retVal;
    
    pPCR_Reg = (uint32_t *)(PCR_BASE)	+ PCR_REG_SYSTEM_SLEEP_CTRL;		

    retVal = (uint8_t)((*pPCR_Reg) & 0xFF);

    return retVal;
}



/* ---------------------------------------------------------------------- */
/*          Function to program to CLK Divide Value                       */
/* ---------------------------------------------------------------------- */

/** Writes the clock divide value in the Processor Clock Control Register
 * @param clk_divide_value - clk divide values, valid values in enum PROCESSOR_CLK_DIVIDE_VALUE
 */
void p_pcr_processor_clk_ctrl_write(uint8_t clk_divide_value)
{
    __IO uint32_t *pPCR_Reg;		

    pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_REG_PROCESSOR_CLK_CTRL;		

    *pPCR_Reg = (clk_divide_value & 0xFF);	
	
}

/* ---------------------------------------------------------------------- */
/*          Function to program the slow clock divide value           */
/* ---------------------------------------------------------------------- */

/** Write the slow clock divide value in the Slow Clock Control Register
 * @param slow_clk_divide_value - slow clk divide value
 */
void p_pcr_slow_clk_ctrl_write(uint8_t slow_clk_divide_value)
{
    __IO uint32_t *pPCR_Reg;		

    pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_REG_SLOW_CLK_CTRL;		

    *pPCR_Reg = (slow_clk_divide_value & 0x3FF);	

}

/* ---------------------------------------------------------------------- */
/*          Function to read the Oscillator Lock Status                   */
/* ---------------------------------------------------------------------- */

/** Reads the Oscillator Lock status bit in the Oscillator ID Register
 * @return 1 if Oscillator Lock Status bit is set, else 0
 */
uint8_t p_pcr_oscillator_lock_sts_get(void)
{
    __IO uint32_t *pPCR_Reg;
    uint8_t retVal;

    pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_REG_OSCILLATOR_ID;	

    retVal = 0;
    if (*pPCR_Reg & PCR_OSCILLATOR_LOCK_STATUS_BITMASK)
    {
            retVal = 1;
    }
    
    return retVal;
	
}

/* ---------------------------------------------------------------------- */
/*  Functions to read various power status in Chip Sub-System register    */
/* ---------------------------------------------------------------------- */

/** Reads the VCC Reset Status bit 
 *        in the Chip Subsystem Power Reset Status Register
 * @return 1 if VCC Reset Status bit is set, else 0
 */
uint8_t p_pcr_chip_subsystem_vcc_reset_sts_get(void)
{
    __IO uint32_t *pPCR_Reg;
    uint8_t retVal;

    pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_REG_CHIP_SUBSYSTEM_PWR_RESET_STS;	

    retVal = 0;
    if (*pPCR_Reg & PCR_CHIP_SUBSYSTEM_VCC_RESET_STS_BITMASK)
    {
            retVal = 1;
    }
    
    return retVal;	
}

/** Reads the SIO Reset Status bit 
 *        in the Chip Subsystem Power Reset Status Register
 * @return 1 if SIO Reset Status bit is set, else 0
 */
uint8_t p_pcr_chip_subsystem_sio_reset_sts_get(void)
{
    __IO uint32_t *pPCR_Reg;
    uint8_t retVal;

    pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_REG_CHIP_SUBSYSTEM_PWR_RESET_STS;	

    retVal = 0;
    if (*pPCR_Reg & PCR_CHIP_SUBSYSTEM_SIO_RESET_STS_BITMASK)
    {
            retVal = 1;
    }
    
    return retVal;	
}

/** Reads the VBAT Reset Status bit 
 *        in the Chip Subsystem Power Reset Status Register
 * @return 1 if VBAT Reset Status bit is set, else 0
 */
uint8_t p_pcr_chip_subsystem_vbat_reset_sts_get(void)
{
    __IO uint32_t *pPCR_Reg;
    uint8_t retVal;

    pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_REG_CHIP_SUBSYSTEM_PWR_RESET_STS;	

    retVal = 0;
    if (*pPCR_Reg & PCR_CHIP_SUBSYSTEM_VBAT_RESET_STS_BITMASK)
    {
            retVal = 1;
    }
    
    return retVal;	
}

/** Clears the VBAT Reset Status bit 
 *        in the Chip Subsystem Power Reset Status Register 
 */
void p_pcr_chip_subsystem_vbat_reset_sts_clr(void)
{
    __IO uint32_t *pPCR_Reg;		

    pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_REG_CHIP_SUBSYSTEM_PWR_RESET_STS;

    // Write to clear
    *pPCR_Reg = PCR_CHIP_SUBSYSTEM_VBAT_RESET_STS_BITMASK;
	
}

/** Reads the VCC1 Reset Status bit 
 *        in the Chip Subsystem Power Reset Status Register
 * @return 1 if VCC1 Reset Status bit is set, else 0
 */
uint8_t p_pcr_chip_subsystem_vcc1_reset_sts_get(void)
{
    __IO uint32_t *pPCR_Reg;
    uint8_t retVal;

    pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_REG_CHIP_SUBSYSTEM_PWR_RESET_STS;	

    retVal = 0;
    if (*pPCR_Reg & PCR_CHIP_SUBSYSTEM_VCC1_RESET_STS_BITMASK)
    {
            retVal = 1;
    }
    
    return retVal;	
}

/** Clears the VCC1 Reset Status bit 
 *        in the Chip Subsystem Power Reset Status Register 
 */
void p_pcr_chip_subsystem_vcc1_reset_sts_clr(void)
{
    __IO uint32_t *pPCR_Reg;		

    pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_REG_CHIP_SUBSYSTEM_PWR_RESET_STS;

    // Write to clear
    *pPCR_Reg = PCR_CHIP_SUBSYSTEM_VCC1_RESET_STS_BITMASK;
	
}

/** Reads the 32K_ACTIVE status bit 
 *        in the Chip Subsystem Power Reset Status Register
 * @return 1 if 32_ACTIVE bit is set, else 0
 */
uint8_t p_pcr_chip_subsystem_32K_active_sts_get(void)
{
    __IO uint32_t *pPCR_Reg;
    uint8_t retVal;

    pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_REG_CHIP_SUBSYSTEM_PWR_RESET_STS;	

    retVal = 0;
    if (*pPCR_Reg & PCR_CHIP_SUBSYSTEM_32K_ACTIVE_STS_BITMASK)
    {
            retVal = 1;
    }
    
    return retVal;	
}

/** Reads the PCICLK_ACTIVE status bit 
 *        in the Chip Subsystem Power Reset Status Register
 * @return 1 if CICLK_ACTIVE bit is set, else 0
 */
uint8_t p_pcr_chip_subsystem_pciclk_active_sts_get(void)
{
    __IO uint32_t *pPCR_Reg;
    uint8_t retVal;

    pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_REG_CHIP_SUBSYSTEM_PWR_RESET_STS;	

    retVal = 0;
    if (*pPCR_Reg & PCR_CHIP_SUBSYSTEM_PCICLK_ACTIVE_STS_BITMASK)
    {
            retVal = 1;
    }		
    return retVal;	
}

/* ---------------------------------------------------------------------- */
/*           Functions for Power Reset Control Register                   */
/* ---------------------------------------------------------------------- */

/** Reads the iRESET_OUT bit in the Power Reset Control Register
 * @return 1 if iRESET_OUT bit is set, else 0
 */
uint8_t p_pcr_iReset_Out_get(void)
{
    __IO uint32_t *pPCR_Reg;
    uint8_t retVal;

    pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_REG_PWR_RESET_CTRL;	

    retVal = 0;
    if (*pPCR_Reg & PCR_iRESET_OUT_BITMASK)
    {
            retVal = 1;
    }
    
    return retVal;
	
}

/** Sets/Clears the iRESET_OUT bit in the Power Reset Control Register
 * @param 1 Set iRESET_OUT bit; 0 - Clear the bit
 */
void p_pcr_iReset_Out(uint8_t set_clr_flag)
{
    __IO uint32_t *pPCR_Reg;		

    pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_REG_PWR_RESET_CTRL;

    *pPCR_Reg	 = (set_clr_flag & 0x1);		
}


/* end pcr_perphl.c */
/**   @}
 */
