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


/** Writes required sleep mode in System Sleep Control Register
 * @param sleep_value - System Sleep control value (Heavy/Light/Sleep All)
 */
void p_pcr_system_sleep_ctrl_write(uint8_t sleep_value)
{
    __IO uint32_t *pPCR_Reg;
	
   /* Check for valid value */
   if ((sleep_value == SYSTEM_LIGHT_SLEEP) || 
		    (sleep_value == SYSTEM_LIGHT_SLEEP) ||
	       (sleep_value == SYSTEM_LIGHT_SLEEP))
	 {    
			pPCR_Reg = (uint32_t *)(PCR_BASE)	+ PCR_REG_SYSTEM_SLEEP_CTRL;	

			*pPCR_Reg = (sleep_value & 0x7);		
	 }
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

   /* Check for valid value */
   if (((clk_divide_value >= PCR_CPU_CLK_DIVIDE_1) && 
		    (clk_divide_value <= PCR_CPU_CLK_DIVIDE_4)) ||
	       (clk_divide_value == PCR_CPU_CLK_DIVIDE_16) ||
	        (clk_divide_value == PCR_CPU_CLK_DIVIDE_48))
	 {	
			pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_REG_PROCESSOR_CLK_CTRL;		

			*pPCR_Reg = (clk_divide_value & 0xFF);
	 }
	
}

/** Writes the clock divide value in the Processor Clock Control Register
 * @param none
 * @ return value - clk divide value, valid values in enum PROCESSOR_CLK_DIVIDE_VALUE
 */
uint8_t p_pcr_processor_clk_ctrl_read(void)
{
    __IO uint32_t *pPCR_Reg;
    uint8_t retVal;	

    pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_REG_PROCESSOR_CLK_CTRL;		

	  retVal = ((uint8_t)((*pPCR_Reg) & 0xFF));
	
    return retVal;
	
}

/* ---------------------------------------------------------------------- */
/*          Function to program the slow clock divide value           */
/* ---------------------------------------------------------------------- */

/** Write the slow clock divide value in the Slow Clock Control Register
 * @param slow_clk_divide_value - slow clk divide value
 */
void p_pcr_slow_clk_ctrl_write(uint16_t slow_clk_divide_value)
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


/** Reads the Oscillator ID Register
 * @return oscillator ID value
 */
uint16_t p_pcr_oscillator_id_reg_read(void)
{
    __IO uint32_t *pPCR_Reg;
    uint16_t retVal;

    pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_REG_OSCILLATOR_ID;	

    retVal = ((uint16_t)((*pPCR_Reg) & 0x1FFu));
    
    return retVal;
	
}

/* ---------------------------------------------------------------------- */
/*  Functions to read various power status in Power Reset register    */
/* ---------------------------------------------------------------------- */

/** Reads the VCC PWRGD Status bit 
 *        in the Power Reset Status Register
 * @return 1 if VCC PWRGD Status bit is set, else 0
 */
uint8_t p_pcr_pwr_reset_vcc_pwrdg_sts_get(void)
{
    __IO uint32_t *pPCR_Reg;
    uint8_t retVal;

    pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_REG_PWR_RESET_STS;	

    retVal = 0;
    if (*pPCR_Reg & PCR_PWR_RESET_STS_VCC_PWRGD_RESET_STS_BITMASK)
    {
            retVal = 1;
    }
    
    return retVal;	
}

/** Reads the Host Reset Status bit 
 *        in the Power Reset Status Register
 * @return 1 if Host Reset Status bit is set, else 0
 */
uint8_t p_pcr_pwr_reset_host_reset_sts_get(void)
{
    __IO uint32_t *pPCR_Reg;
    uint8_t retVal;

    pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_REG_PWR_RESET_STS;	

    retVal = 0;
    if (*pPCR_Reg & PCR_PWR_RESET_STS_HOST_RESET_STS_BITMASK)
    {
            retVal = 1;
    }
    
    return retVal;	
}

/** Reads the VBAT Reset Status bit 
 *        in the Power Reset Status Register
 * @return 1 if VBAT Reset Status bit is set, else 0
 */
uint8_t p_pcr_pwr_reset_vbat_reset_sts_get(void)
{
    __IO uint32_t *pPCR_Reg;
    uint8_t retVal;

    pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_REG_PWR_RESET_STS;	

    retVal = 0;
    if (*pPCR_Reg & PCR_PWR_RESET_STS_VBAT_RESET_STS_BITMASK)
    {
            retVal = 1;
    }
    
    return retVal;	
}

/** Clears the VBAT Reset Status bit 
 *        in the Power Reset Status Register 
 */
void p_pcr_pwr_reset_vbat_reset_sts_clr(void)
{
    __IO uint32_t *pPCR_Reg;		

    pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_REG_PWR_RESET_STS;

    // Write to clear
    *pPCR_Reg |= PCR_PWR_RESET_STS_VBAT_RESET_STS_BITMASK;
	
}

/** Reads the VTR Reset Status bit 
 *        in the Power Reset Status Register
 * @return 1 if VTR Reset Status bit is set, else 0
 */
uint8_t p_pcr_pwr_reset_vtr_reset_sts_get(void)
{
    __IO uint32_t *pPCR_Reg;
    uint8_t retVal;

    pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_REG_PWR_RESET_STS;	

    retVal = 0;
    if (*pPCR_Reg & PCR_PWR_RESET_STS_VTR_RESET_STS_BITMASK)
    {
            retVal = 1;
    }
    
    return retVal;	
}

/** Clears the VTR Reset Status bit 
 *        in the Power Reset Status Register 
 */
void p_pcr_pwr_reset_vtr_reset_sts_clr(void)
{
    __IO uint32_t *pPCR_Reg;		

    pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_REG_PWR_RESET_STS;

    // Write to clear
    *pPCR_Reg |= PCR_PWR_RESET_STS_VTR_RESET_STS_BITMASK;
	
}

/** Reads the JTAG Reset Status bit 
 *        in the Power Reset Status Register
 * @return 1 if JTAG Reset Status bit is set, else 0
 */
uint8_t p_pcr_pwr_reset_jtag_reset_sts_get(void)
{
    __IO uint32_t *pPCR_Reg;
    uint8_t retVal;

    pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_REG_PWR_RESET_STS;	

    retVal = 0;
    if (*pPCR_Reg & PCR_PWR_RESET_STS_JTAG_RESET_STS_BITMASK)
    {
            retVal = 1;
    }
    
    return retVal;	
}

/** Clears the JTAG Reset Status bit 
 *        in the Power Reset Status Register 
 */
void p_pcr_pwr_reset_jtag_reset_sts_clr(void)
{
    __IO uint32_t *pPCR_Reg;		

    pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_REG_PWR_RESET_STS;

    // Write to clear
    *pPCR_Reg |= PCR_PWR_RESET_STS_JTAG_RESET_STS_BITMASK;
	
}

/** Reads the 32K_ACTIVE status bit 
 *        in the Chip Subsystem Power Reset Status Register
 * @return 1 if 32_ACTIVE bit is set, else 0
 */
uint8_t p_pcr_pwr_reset_32K_active_sts_get(void)
{
    __IO uint32_t *pPCR_Reg;
    uint8_t retVal;

    pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_REG_PWR_RESET_STS;	

    retVal = 0;
    if (*pPCR_Reg & PCR_PWR_RESET_STS_32K_ACTIVE_STS_BITMASK)
    {
            retVal = 1;
    }
    
    return retVal;	
}

/** Reads the PCICLK_ACTIVE status bit 
 *        in the Power Reset Status Register
 * @return 1 if PCICLK_ACTIVE bit is set, else 0
 */
uint8_t p_pcr_pwr_reset_pciclk_active_sts_get(void)
{
    __IO uint32_t *pPCR_Reg;
    uint8_t retVal;

    pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_REG_PWR_RESET_STS;	

    retVal = 0;
    if (*pPCR_Reg & PCR_PWR_RESET_STS_PCICLK_ACTIVE_STS_BITMASK)
    {
            retVal = 1;
    }		
    return retVal;	
}

/** Reads the ESPI status bit 
 *        in the Power Reset Status Register
 * @return 1 if ESPICLK_ACTIVE bit is set, else 0
 */
uint8_t p_pcr_pwr_reset_espiclk_active_sts_get(void)
{
    __IO uint32_t *pPCR_Reg;
    uint8_t retVal;

    pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_REG_PWR_RESET_STS;	

    retVal = 0;
    if (*pPCR_Reg & PCR_PWR_RESET_STS_ESPICLK_ACTIVE_STS_BITMASK)
    {
            retVal = 1;
    }		
    return retVal;	
}

/** Reads the Power status reg
 * @return Power Status Reg value
 */
uint16_t p_pcr_pwr_reset_sts_get(void)
{
    __IO uint32_t *pPCR_Reg;
    uint16_t retVal;

    pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_REG_PWR_RESET_STS;	

    retVal = (uint16_t)((*pPCR_Reg) & 0xFFF);
	
	  return (retVal);    
}

/* ---------------------------------------------------------------------- */
/*           Functions for Power Reset Control Register                   */
/* ---------------------------------------------------------------------- */

/** Reads the Power Reset Control Register
 * @return Power Reset Control Register value
 */
uint16_t p_pcr_pwr_reset_ctrl_read(void)
{
    __IO uint32_t *pPCR_Reg;
    uint16_t retVal;

    pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_REG_PWR_RESET_CTRL;	

    retVal = (uint16_t)((*pPCR_Reg) & 0x1FFUL);    
    
    return retVal;	
}

/** Set the PWR_INV bit in the Power Reset Control Register
 * @param set_clr value 1 or 0
 * @return none
 */
void p_pcr_pwr_reset_ctrl_pwr_inv_set_clr(uint8_t set_clr)
{
    __IO uint32_t *pPCR_Reg;    

    pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_REG_PWR_RESET_CTRL;	

	  if (set_clr)
		{
        *pPCR_Reg |= (PCR_PWR_RESET_CTRL_PWR_INV_BITMASK);
		}
		else
		{
		    *pPCR_Reg &= ~(PCR_PWR_RESET_CTRL_PWR_INV_BITMASK);
		}
}

/** Set the HOST RESET SELECT bit in the Power Reset Control Register
 * @param set_clr value 1 or 0
 * @return none
 */
void p_pcr_pwr_reset_ctrl_host_rst_set_clr(uint8_t set_clr)
{
    __IO uint32_t *pPCR_Reg;    

    pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_REG_PWR_RESET_CTRL;	

	  if (set_clr)
		{
        *pPCR_Reg |= (PCR_PWR_RESET_CTRL_HOST_RST_SELECT_BITMASK);       
		}
		else
		{
        *pPCR_Reg &= ~(PCR_PWR_RESET_CTRL_HOST_RST_SELECT_BITMASK);       			
		}
}


/* ---------------------------------------------------------------------- */
/*           Functions for System Reset Register                   */
/* ---------------------------------------------------------------------- */
/** Set the SOFT_SYS_RESET bit in the System Reset Register
 * @param none
 * @return none
 */
void p_pcr_system_reset_set()
{
    __IO uint32_t *pPCR_Reg;    

    pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_REG_SYSTEM_RESET;	

    *pPCR_Reg |= (1<<8);       
}

/* ---------------------------------------------------------------------- */
/*           Functions for PKE Clock Register                   */
/* ---------------------------------------------------------------------- */
/** Set the value in PKE CLOCK Register
 * @param PKE Clock value 
 * @return none
 */
void p_pcr_pke_clock_write(uint8_t pke_clk_val)
{
    __IO uint32_t *pPCR_Reg;    

    pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_TEST0;	

    *pPCR_Reg = pke_clk_val;
}

/** Read the value in PKE CLOCK Register
 * @none 
 * @return PKE Clock value 
 */
uint8_t p_pcr_pke_clock_read(void)
{
    __IO uint32_t *pPCR_Reg;    

    pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_TEST0;	

    return ((uint8_t)(*pPCR_Reg & 0xFF));
}

/* ---------------------------------------------------------------------- */
/*           Functions for Oscillator calibration Register                   */
/* ---------------------------------------------------------------------- */
/** Set the value in Oscillator calibration Register
 * @param Oscillator calibration value 
 * @return none
 */
void p_pcr_osc_cal_write(uint8_t osc_cal_val)
{
    __IO uint32_t *pPCR_Reg;    

    pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_TEST1;	

    *pPCR_Reg = osc_cal_val;
}

/** Read the value in Osc cal Register
 * @none 
 * @return Osc cal value 
 */
uint8_t p_pcr_osc_cal_read(void)
{
    __IO uint32_t *pPCR_Reg;    

    pPCR_Reg = (uint32_t *)(PCR_BASE) + PCR_TEST1;	

    return ((uint8_t)(*pPCR_Reg & 0xFF));
}

/* end pcr_perphl.c */
/**   @}
 */
