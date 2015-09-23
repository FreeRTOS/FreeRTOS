/*******************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only
* intended for use with Renesas products. No other uses are authorized. This
* software is owned by Renesas Electronics Corporation and is protected under
* all applicable laws, including copyright laws.
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING
* THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, INCLUDING BUT NOT
* LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE
* AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED.
* TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS
* ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE
* FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR
* ANY REASON RELATED TO THIS SOFTWARE, EVEN IF RENESAS OR ITS AFFILIATES HAVE
* BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software
* and to discontinue the availability of this software. By using this software,
* you agree to the additional terms and conditions found by accessing the
* following link:
* http://www.renesas.com/disclaimer
*
* Copyright (C) 2014 Renesas Electronics Corporation. All rights reserved.
*******************************************************************************/
/*******************************************************************************
* System Name  : RZ/T1 Init program
* File Name    : r_ecm.c
* Version      : 0.1
* Device       : R7S9100xx
* Abstract     : API for ECM function
* Tool-Chain   : IAR Embedded Workbench Ver.7.20
* OS           : not use
* H/W Platform : Renesas Starter Kit for RZ/T1(Preliminary)
* Description  : ECM API of RZ/T1
* Limitation   : LOCO operation is necessary for clearing ERROROUT# pin.
*******************************************************************************/
/*******************************************************************************
* History      : DD.MM.YYYY Version  Description
*              :                     First Release
*******************************************************************************/

/*******************************************************************************
Includes <System Includes> , "Project Includes"
*******************************************************************************/
#include <stdint.h>
#include <Renesas/ior7s910017.h>
#include "r_system.h"
#include "r_ecm.h"
#include "r_reset.h"
#include "r_icu_init.h"

/*******************************************************************************
Macro definitions
*******************************************************************************/
#define ECM_CMT0_CLOCK_PCLKD_32 (1)
#define ECM_CMT0_CMI0_ENABLE    (1)
#define ECM_CMT0_CONST_15_us    (0x22)
#define ECM_CMT0_START          (1)
#define ECM_CMT0_STOP           (0)

#define ECM_CMT_REG_CLEAR (0x0000)

/*******************************************************************************
Typedef definitions
*******************************************************************************/



/*******************************************************************************
Imported global variables and functions (from other files)
*******************************************************************************/


/*******************************************************************************
Exported global variables and functions (to be accessed by other files)
*******************************************************************************/



/*******************************************************************************
Private variables and functions
*******************************************************************************/
static uint32_t *g_pcmd_reg_adrr[ECM_TYPE_MAX] = 
{
    (uint32_t *) &ECMM.ECMMPCMD0.LONG,
    (uint32_t *) &ECMC.ECMCPCMD0.LONG,
    (uint32_t *) &ECM.ECMPCMD1.LONG
};

/*******************************************************************************
* Function Name : R_ECM_Init
* Description   : Initialize ECM function.
*                   - Clear all error source
*                   - Clear ERROROUT# pin output to in-active (High) level.
* Arguments    : none
* Return Value : none
*******************************************************************************/
void R_ECM_Init(void)
{
    volatile uint8_t result;
      
    /* Clear all error source (ECMESSTC0, ECMESSTC1, ECMESSTC2) */   
    result = R_ECM_Write_Reg32(ECM_COMMON, &(ECM.ECMESSTC0.LONG), 0xDFFFFFF7); 
    result = R_ECM_Write_Reg32(ECM_COMMON, &(ECM.ECMESSTC1.LONG), 0x000001FF);       
    result = R_ECM_Write_Reg32(ECM_COMMON, &(ECM.ECMESSTC2.LONG), 0x70000000);  
    
    /* Mask all error source (ECMEMK0, ECMEMK1, ECMEMK2) for clearing ERROROUT# */
    result = R_ECM_Write_Reg32(ECM_COMMON, &(ECM.ECMEMK0.LONG), 0xDFFFFFF7); 
    result = R_ECM_Write_Reg32(ECM_COMMON, &(ECM.ECMEMK1.LONG), 0x000001FF); 
    result = R_ECM_Write_Reg32(ECM_COMMON, &(ECM.ECMEMK2.LONG), 0x30000000); 
      
    /* Mask ECM maskable, non-maskable interrupt and ECM reset of ECM compare match
       error (ECMMICFG2, ECMNMICFG2, ECMIRCFG2) */
    result = R_ECM_Write_Reg32(ECM_COMMON, &(ECM.ECMMICFG2.LONG), 0x00000000); 
    result = R_ECM_Write_Reg32(ECM_COMMON, &(ECM.ECMNMICFG2.LONG), 0x00000000); 
    result = R_ECM_Write_Reg32(ECM_COMMON, &(ECM.ECMIRCFG2.LONG), 0x00000000); 
    
    /* Clear ERROROUT# pin output to in-active (High) level */
    result = R_ECM_Write_Reg8(ECM_MASTER, &(ECMM.ECMMECLR.BYTE), 0x01);
    result = R_ECM_Write_Reg8(ECM_CHECKER, &(ECMC.ECMCECLR.BYTE), 0x01);
    
    /* Wait 15us for ECM compare error stabilization */
    R_ECM_CompareError_Wait();
    
    /* Clear ECM compare error (ECMESSTC2) again */
    result = R_ECM_Write_Reg32(ECM_COMMON, &(ECM.ECMESSTC2.LONG), 0x10000000);
    
    /* Initialize the all error mask settings (ECMEMK0, ECMEMK1, ECMEMK2) */
    result = R_ECM_Write_Reg32(ECM_COMMON, &(ECM.ECMEMK0.LONG), 0x00000000);
    result = R_ECM_Write_Reg32(ECM_COMMON, &(ECM.ECMEMK1.LONG), 0x00000000);
    result = R_ECM_Write_Reg32(ECM_COMMON, &(ECM.ECMEMK2.LONG), 0x00000000);
          
}

/*******************************************************************************
 End of function R_ECM_Init
*******************************************************************************/

/*******************************************************************************
* Function Name : R_ECM_CompareError_Wait
* Description   : Wait about 15 us for ECM compare error stabilizeation by using CMT0 
* Arguments    : none
* Return Value : none
*******************************************************************************/
void R_ECM_CompareError_Wait(void)
{
    /* Enables writing to the registers related to Reset and Low-Power function */
    r_rst_write_enable();
    
    /* Release from the CMT0 module-stop state  */
    MSTP(CMT0) = 0;
    
    /* Disables writing to the registers related to Reset and Low-Power function */
    r_rst_write_disable();
   
    /* Set CMT0 to 100us interval operation */
    CMT0.CMCR.BIT.CKS = ECM_CMT0_CLOCK_PCLKD_32;  // Count clock = PCLKD/32
    CMT0.CMCR.BIT.CMIE = ECM_CMT0_CMI0_ENABLE;    // Enable CMI0 interrupt
    CMT0.CMCNT = ECM_CMT_REG_CLEAR;              // Clear CMCNT counter
    CMT0.CMCOR = ECM_CMT0_CONST_15_us;           // Set constant value for 15us
    
    
    /* Set IRQ21(CMI0) for polloing sequence */
    VIC.IEC0.BIT.IEC21 = ICU_IEC_MASK_SET;    // Mask IRQ21 interrupt
    VIC.PLS0.BIT.PLS21 = ICU_TYPE_EDGE;       // Set EDGE type interrupt
    VIC.PIC0.BIT.PIC21 = ICU_PIC_EDGE_CLEAR;  // Clear interrupt detection edge
    
    /* Enable IRQ interrupt (Clear CPSR.I bit to 0) */
    asm("cpsie i");   // Clear CPSR.I bit to 0 
    asm("isb");       // Ensuring Context-changing    
       
    /* Start CMT0 count */
    CMT.CMSTR0.BIT.STR0 = ECM_CMT0_START;
 
    /* Wait for 15us (IRQ21 is generated) */
    while ( ! (VIC.RAIS0.BIT.RAI21) )
    {
        /* Wait */   
    }
             
    /* Stop CMT0 count */
    CMT.CMSTR0.BIT.STR0 = ECM_CMT0_STOP;
    
    /* Initialize CMT0 settings and clear interrupt detection edge */
    CMT0.CMCR.WORD = ECM_CMT_REG_CLEAR;
    CMT0.CMCNT = ECM_CMT_REG_CLEAR;
    CMT0.CMCOR = ECM_CMT_REG_CLEAR;
    CMT.CMSTR0.WORD = ECM_CMT_REG_CLEAR;
    
    VIC.PIC0.BIT.PIC21 = ICU_PIC_EDGE_CLEAR;  // Clear interrupt detection edge
    

    /* Disable IRQ interrupt (Set CPSR.I bit to 1) */
    asm("cpsid i");
    asm("isb");

    /* Enables writing to the registers related to Reset and Low-Power function */
    r_rst_write_enable();
    
    /* Set CMT0 to module-stop state */
    MSTP(CMT0) = 1;
    
    /* Disables writing to the registers related to Reset and Low-Power function */
    r_rst_write_disable();

}

/*******************************************************************************
 End of function R_ECM_CompareError_Wait
*******************************************************************************/


/*******************************************************************************
* Function Name : R_ECM_Write_Reg8
* Description   : Writing the special sequence for 8-bit ECM protected register 
* Arguments    :  reg_type
*                     The type of ECM register (ECM_MASETR, ECM_CHECKER, ECM_COMMON)
*                 *reg                 
*                     The address of ECM protected register
*                 value
*                     The 8-bit value of writing to protected register
* Return Value : none
*******************************************************************************/
uint8_t R_ECM_Write_Reg8( uint8_t reg_type, volatile unsigned char *reg, uint8_t value)
{
    uint8_t result;  
    volatile uint8_t  dummy_8;
    volatile uint32_t dummy_32;
    
    /* Special write sequence */
    *g_pcmd_reg_adrr[reg_type] = ECM_COMMAND_KEY;  // Write fixed value
    dummy_32 = *g_pcmd_reg_adrr[reg_type];
   
    *reg = value;     // Write expected value
    *reg = ~value;    // Write inversed value of the expected value
    *reg = value;     // Write expected value
    dummy_8 = *reg;  
    
   /* Check the ECMPS register whether special sequence is success or failure
           result = 0 : Special sequence is success.
                  = 1 : Special sequence is failure.                          */ 
    result = ECM.ECMPS.BYTE;  
    
    return result;  
    
}
/*******************************************************************************
 End of function R_ECM_Write_Reg8
*******************************************************************************/

/*******************************************************************************
* Function Name : R_ECM_Write_Reg32
* Description   : Writing the special sequence for 32-bit ECM protected register 
* Arguments    :  reg_type
*                     The type of ECM register (ECM_MASETR, ECM_CHECKER, ECM_COMMON)
*                 *reg                 
*                     The address of ECM protected register
*                 value
*                     The 32-bit value of writing to protected register
* Return Value : none
*******************************************************************************/
uint8_t R_ECM_Write_Reg32( uint8_t reg_type, volatile unsigned long *reg, uint32_t value)
{
    uint8_t result;  
    volatile uint32_t dummy_32;
    
    /* Special write sequence */
    *g_pcmd_reg_adrr[reg_type] = ECM_COMMAND_KEY;  // Write fixed value
    dummy_32 = *g_pcmd_reg_adrr[reg_type];
   
    *reg = value;     // Write expected value
    *reg = ~value;    // Write inversed value of the expected value
    *reg = value;     // Write expected value
    dummy_32 = *reg;  
    
   /* Check the ECMPS register whether special sequence is success or failure
           result = 0 : Special sequence is success.
                  = 1 : Special sequence is failure.                          */ 
    result = ECM.ECMPS.BYTE;  
    
    return result;  
    
}
/*******************************************************************************
 End of function R_ECM_Write_Reg32
*******************************************************************************/
  
/* End of File */


