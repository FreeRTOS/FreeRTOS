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
* File Name    : loader_init2.c
* Version      : 0.1
* Device       : R7S9100xx
* Abstract     : Loader program 2
* Tool-Chain   : IAR Embedded Workbench Ver.7.20
* OS           : not use
* H/W Platform : Renesas Starter Kit for RZ/T1(Preliminary)
* Description  : Initialize the peripheral settings of RZ/T1
* Limitation   : none
*******************************************************************************/
/*******************************************************************************
* History      : DD.MM.YYYY Version  Description
*              :                     First Release
*******************************************************************************/
#ifdef __ICCARM__

#pragma section="VECTOR_RBLOCK"
#pragma section="VECTOR_WBLOCK"
#pragma section="USER_PRG_RBLOCK"
#pragma section="USER_PRG_WBLOCK"
#pragma section="USER_DATA_RBLOCK"
#pragma section="USER_DATA_WBLOCK"

#endif  // __ICCARM__

/*******************************************************************************
Includes <System Includes> , "Project Includes"
*******************************************************************************/
#include <stdint.h>
#include <Renesas/ior7s910017.h>
#include "r_system.h"
#include "r_reset.h"
#include "r_cpg.h"
#include "r_atcm_init.h"
#include "r_port.h"
#include "r_mpc.h"
#include "r_ecm.h"


/*******************************************************************************
Macro definitions
*******************************************************************************/

/*******************************************************************************
Typedef definitions
*******************************************************************************/

/*******************************************************************************
Imported global variables and functions (from other files)
*******************************************************************************/
extern int _main(void);
extern void bus_init(void);
extern void set_low_vec(void);
extern void cache_init(void);
extern void __iar_data_init3(void);

/*******************************************************************************
Exported global variables and functions (to be accessed by other files)
*******************************************************************************/

/*******************************************************************************
Private variables and functions
*******************************************************************************/
void loader_init2(void);
void reset_check(void);
void cpg_init(void);

/*******************************************************************************
* Function Name : loader_init2
* Description   : Initialize sysytem by loader program 2
* Arguments    : none
* Return Value : none
*******************************************************************************/
void loader_init2(void)
{ 
    /* Check the reset source */
    reset_check();
  
    /* Set CPU clock and LOCO clock */
    cpg_init();
    
    /* Set ATCM access wait to 1-wait with optimization */
    /* Caution: ATCM_WAIT_0 is permitted if CPUCLK = 150MHz or 300MHz.
                ATCM_WAIT_1_OPT is permitted if CPUCLK = 450MHz or 600MHz.*/
    R_ATCM_WaitSet(ATCM_WAIT_1_OPT);
     
    /* Copy the variable data */
    __iar_data_init3();

    /* Initialize I1, D1 Cache and MPU setting */
    cache_init();
    
    /* Set RZ/T1 to Low-vector (SCTLR.V = 0) */
    set_low_vec();  
                
    /* Jump to _main() */
    _main();

}

/*******************************************************************************
 End of function loader_init2
*******************************************************************************/

/*******************************************************************************
* Function Name : reset_check
* Description   : Check the reset source and execute the each sequence.
*                 When error source number 35 is generated, set P77 pin to High.
* Arguments    : none
* Return Value : none
*******************************************************************************/
void reset_check(void)
{
    volatile uint8_t result;
    volatile uint32_t dummy;
    
    /* Check the reset status flag and execute the each sequence */
    if (RST_SOURCE_ECM == SYSTEM.RSTSR0.LONG) // ECM reset is generated
    {
        /* Clear reset status flag */ 
        r_rst_write_enable();              // Enable writing to the RSTSR0 register
        SYSTEM.RSTSR0.LONG = 0x00000000;  // Clear reset factor flag
        r_rst_write_disable();             // Disable writing to the RSTSR0 register
        
        /* Please coding the User program */ 
        
    }
    else if (RST_SOURCE_SWR1 == SYSTEM.RSTSR0.LONG) // Software reset 1 is generated
    {
        /* Clear reset status flag */ 
        r_rst_write_enable();              // Enable writing to the RSTSR0 register
        SYSTEM.RSTSR0.LONG = 0x00000000;  // Clear reset factor flag
        r_rst_write_disable();             // Disable writing to the RSTSR0 register
        
        /* Please coding the User program */  
        
    }
    else if (RST_SOURCE_RES == SYSTEM.RSTSR0.LONG) // RES# pin reset is generated
    {
        /* Clear reset status flag */ 
        r_rst_write_enable();              // Enable writing to the RSTSR0 register
        SYSTEM.RSTSR0.LONG = 0x00000000;  // Clear reset factor flag
        r_rst_write_disable();             // Disable writing to the RSTSR0 register
        
        /* Please coding the User program */    
        
    }
    else // Any reset is not generated
    {        
        /* Please coding the User program */  
    }

}

/*******************************************************************************
 End of function reset_check
*******************************************************************************/

/*******************************************************************************
* Function Name : cpg_init
* Description   : Set CPU clock and LOCO clock by CPG function
* Arguments    : none
* Return Value : none
*******************************************************************************/
void cpg_init(void)
{
    volatile uint32_t dummy; 
      
    /* Enables writing to the registers related to CPG function */
    R_CPG_WriteEnable();
    
    /* Enables LOCO clock operation */
    SYSTEM.LOCOCR.BIT.LCSTP = CPG_LOCO_ENABLE;
    
    /* Set CPUCLK to 450MHz, and dummy read at three times */
    SYSTEM.PLL1CR.LONG = CPG_CPUCLK_450_MHz;
    dummy = SYSTEM.PLL1CR.LONG;
    dummy = SYSTEM.PLL1CR.LONG;
    dummy = SYSTEM.PLL1CR.LONG;
     
    /* Enables PLL1 operation */
    SYSTEM.PLL1CR2.LONG = CPG_PLL1_ON;    
    
    /* Disables writing to the registers related to CPG function */
    R_CPG_WriteDisable(); 
    
    /* Wait about 100us for PLL1 (and LOCO) stabilization */
    R_CPG_PLL_Wait();

    /* Enables writing to the registers related to CPG function */
    R_CPG_WriteEnable();  
     
    /* Selects the PLL1 as clock source */
    SYSTEM.SCKCR2.LONG = CPG_SELECT_PLL1;
    
    /* Disables writing to the registers related to CPG function */
    R_CPG_WriteDisable();
  
}

/*******************************************************************************
 End of function cpg_init
*******************************************************************************/


/* End of File */


