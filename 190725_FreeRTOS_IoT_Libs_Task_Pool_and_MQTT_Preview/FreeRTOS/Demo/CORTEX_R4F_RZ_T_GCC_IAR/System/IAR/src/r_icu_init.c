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
* File Name    : r_icu_init.c
* Version      : 0.1
* Device       : R7S9100xx
* Abstract     : API for ICU init
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

/*******************************************************************************
Includes <System Includes> , "Project Includes"
*******************************************************************************/
#include <stdint.h>
#include <Renesas/ior7s910017.h>
#include "r_icu_init.h"
#include "r_system.h"
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

/*******************************************************************************
Private variables and functions
*******************************************************************************/
#ifdef __ICCARM__
#pragma type_attribute=__irq __arm 
#endif  // __ICCARM__
void R_IRQ9_isr(void);



/*******************************************************************************
* Function Name: R_ICU_Disable
* Description  : Disable IRQ interrupt 
* Arguments    : vec_num
                     Vector interrupt number (1 to 294).
* Return Value : none
*******************************************************************************/
void R_ICU_Disable(uint32_t vec_num)
{
    /* Define IECn register address pointer */
    volatile uint32_t *p_iec_base;

    /* Variable to specify register suffix */
    uint32_t reg_num;  // IECn (n = reg_num)  
    uint32_t bit_num;  // IECn.IECm (m = bit_num)
    
    /* Calcurate register address and register suffix number */
    if ( 255 >= vec_num )  // Vector number : 1 to 255 
    {
        /* Set each pointer base address as IEC0 */
        /* Casting the pointer to a (uint32_t *) is valid because this pointer 
           will reference 32 bit I/O register address */
        p_iec_base = (uint32_t*)&(VIC.IEC0.LONG);
        
        /* Calcurate register suffix number */
        reg_num = vec_num / 32;  // IECn (n = reg_num) 
        bit_num = vec_num % 32;  // IECn.IECm (m = bit_num)
    }
    else  // Vector number : 256 to 294
    {
        /* Set each pointer address as IEC8 */
        /* Casting the pointer to a (uint32_t *) is valid because this pointer 
           will reference 32 bit I/O register address */
        p_iec_base = (uint32_t*)&(VIC.IEC8.LONG);
                         
        /* Calcurate register suffix number. And subtract 8 from reg_num  
        because IEC8 is base address in this case */
        reg_num = (vec_num / 32) - 8;  // IECn (n = 8 + reg_num)
        bit_num = (vec_num % 32);  // IECn.IECm (m = bit_num) 
    }
        
    /* Set interrupt enable clear register (disable interrupt) */
    p_iec_base += reg_num;  // Specify IECn register address
    *p_iec_base |= ( 1 << bit_num );  // Set IECn.IECm bit
        
}
/*******************************************************************************
 End of function R_ICU_Disable
*******************************************************************************/

/*******************************************************************************
* Function Name: R_ICU_Enable
* Description  : Enable IRQ interrupt 
* Arguments    : vec_num
                     Vector interrupt number (1 to 294).
* Return Value : none
*******************************************************************************/
void R_ICU_Enable(uint32_t vec_num)
{
    /* Define IENn register address pointer */
    volatile uint32_t *p_ien_base;
    
    /* Variable to specify register suffix */
    uint32_t reg_num;  // IENn (n = reg_num)  
    uint32_t bit_num;  // IENn.IENm (m = bit_num)
    

    /* Calcurate register address and register suffix number */
    if ( 255 >= vec_num )  // Vector number : 1 to 255 
    {
        /* Set each pointer base address as IEN0 */
        /* Casting the pointer to a (uint32_t *) is valid because this pointer 
           will reference 32 bit I/O register address */
        p_ien_base = (uint32_t*)&(VIC.IEN0.LONG);
        
        /* Calcurate register suffix number */
        reg_num = vec_num / 32;  // IENn (n = reg_num) 
        bit_num = vec_num % 32;  // IENn.IENm (m = bit_num)
    }
    else  // Vector number : 256 to 294
    {
        /* Set each pointer address as IEN8 */
        /* Casting the pointer to a (uint32_t *) is valid because this pointer 
           will reference 32 bit I/O register address */
        p_ien_base = (uint32_t*)&(VIC.IEN8.LONG);
                         
        /* Calcurate register suffix number. And subtract 8 from reg_num  
        because IEN8 is base address in this case */
        reg_num = (vec_num / 32) - 8;  // IENn (n = 8 + reg_num)
        bit_num = (vec_num % 32);  // IENn.IENm (m = bit_num) 
    }
        
    /* Set interrupt enable register (enable interrupt) */
    p_ien_base += reg_num;  // Specify IENn register address
    *p_ien_base |= ( 1 << bit_num );  // Set IENn.IENm bit
        
}
/*******************************************************************************
 End of function R_ICU_Enable
*******************************************************************************/

/*******************************************************************************
* Function Name: R_ICU_ExtPinInit
* Description  : Initialize external interrupt pin setting.
* Arguments    : pin_num
                     External interrupt pin number (0 to 15).
                 detect
                     Interrupt pin detection sense (Low, Fall, Rise, RIse&Fall).
                 dnf_set
                     Setting of degital noise filter 
* Return Value : none
*******************************************************************************/
void R_ICU_ExtPinInit(uint16_t pin_num, uint8_t detect, uint32_t dnf_set)
{
    /* Define IRQCRn register address pointer */
    /* Casting the pointer to a (void *) is valid because this pointer will
    reference 32 bit I/O register address */
    volatile uint32_t *p_irqcr_base = (void *)(&(ICU.IRQCR0.LONG));
  
    /* Disable digital noise filter (Clear IRQFLTEn bit (n = pin_num))*/
    ICU.IRQFLTE.LONG &= (0x0000FFFF & ~( 1 << pin_num ));
     
    /* Set IRQ detection sense */
    p_irqcr_base += pin_num;  // Specify IRQCRn register address
    *p_irqcr_base = detect;  // Set IRQCRn.IRQMD[1:0]            
    
    /* Set digital noise filter and enable */
    if ( ICU_DNF_NO_USE != dnf_set )
    {
        /* Set digital noise filter */
        ICU.IRQFLTC.LONG &= ~( 3 << ( pin_num * 2 ) );  // Clear FCLKSELn[1:0]
        ICU.IRQFLTC.LONG |= (dnf_set << ( pin_num * 2)); // Set FCLKSELn[1:0] to dnf_set value
     
        /* Enable digital noise filter */
        ICU.IRQFLTE.LONG |= ( 1 << pin_num );
    }

}
/*******************************************************************************
 End of function R_ICU_ExtPinInit
*******************************************************************************/


/*******************************************************************************
* Function Name: R_ICU_Regist
* Description  : Registration interrupt controller setting.
* Arguments    : vec_num
                     Vector interrupt number (1 to 294).
                 type
                     IRQ detection type(Level or Edge).
                 priority
                     IRQ priority level ( Vector number 1 to 255 : 0 to 15, 
                                          Vector number 256 to 294 : 16 to 31)
                 isr_addr
                     Interrupt service routine address
* Return Value : none
*******************************************************************************/
void R_ICU_Regist(uint32_t vec_num, uint32_t type, uint32_t priority, uint32_t isr_addr)
{
    /* Define PLSn, PRLn, VADn and PICn registers address pointer */
    volatile uint32_t *p_pls_base;
    volatile uint32_t *p_prl_base;    
    volatile uint32_t *p_vad_base;
    volatile uint32_t *p_pic_base;
    
    /* Variable to specify register suffix */
    uint32_t reg_num;  // PLSn, PICn (n = reg_num)  
    uint32_t bit_num;  // PLSn.PLSm, PICn.PICm (m = bit_num)
    

    /* Calcurate register address and register suffix number */
    if ( 255 >= vec_num )  // Vector number : 1 to 255 
    {
        /* Set each pointer base address as PLS0, PRL1, VAD1 and PIC0 */
        /* Casting the pointer to a (uint32_t *) is valid because this pointer 
           will reference 32 bit I/O register address */
        p_pls_base = (uint32_t*)&(VIC.PLS0.LONG);
        p_prl_base = (uint32_t*)&(VIC.PRL1.LONG);    
        p_vad_base = (uint32_t*)&(VIC.VAD1.LONG);
        p_pic_base = (uint32_t*)&(VIC.PIC0.LONG); 
        
        /* Calcurate register suffix number */
        reg_num = vec_num / 32;  // PLSn, PICn (n = reg_num) 
        bit_num = vec_num % 32;  // PLSn.PLSm, PICn.PICm (m = bit_num)
    }
    else  // Vector number : 256 to 294
    {
        /* Set each pointer address as PLS8, PRL256, VAD256 and PIC8 */
        /* Casting the pointer to a (uint32_t *) is valid because this pointer 
           will reference 32 bit I/O register address */
        p_pls_base = (uint32_t*)&(VIC.PLS8.LONG);
        p_prl_base = (uint32_t*)&(VIC.PRL256.LONG);    
        p_vad_base = (uint32_t*)&(VIC.VAD256.LONG);
        p_pic_base = (uint32_t*)&(VIC.PIC8.LONG);
                         
        /* Calcurate register suffix number. And subtract 8 from reg_num  
        because PLS8 and PIC8 are base address in this case */
        reg_num = (vec_num / 32) - 8;  // PLSn, PICn (n = 8 + reg_num)
        bit_num = (vec_num % 32);  // PLSn.PLSm, PICn.PICm (m = bit_num) 
        vec_num -= 255;  // Offset (PRLn and VADn base is changed (eg. VAD1 to VAD256)
    }
    
    /* Set interrupt detection type (Level or Edge) by PLSn */
    p_pls_base += reg_num;  // Specify PLSn register address
    *p_pls_base &= ~( 1 << bit_num );  // Clear PLSn.PLSm bit
    *p_pls_base |= ( type << bit_num );  // Set PLSn.PLSm bit to type value
      
    /* Set interrupt priority level (0 to 15) or (16 to 31) */
    p_prl_base += ( vec_num - 1 );  // Specify PRLn register address
    *p_prl_base = priority; // Set PRLn to priority value
      
    /* Set interrupt service routine address */
    p_vad_base += ( vec_num - 1 );  // Specify VADn register address
    *p_vad_base = isr_addr;  // Set VADn to isr_addr value

    /* Clear interrupt edge detection (edge type only)*/     
    if ( ICU_TYPE_EDGE == type )
    {
        p_pic_base += reg_num;  // Specify PICn register address
        *p_pic_base |= ( 1 << bit_num );  // Set PICn.PICm bit to 1
    }

}

/*******************************************************************************
 End of function R_ICU_Regist
*******************************************************************************/

/*******************************************************************************
* Function Name: R_IRQ9_isr
* Description  : Interrupt service routine of IRQ9 (IRQ5 pin interrupt).
*                Toggle the P56 output level (LED1)
* Arguments    : none
* Return Value : none
*******************************************************************************/
#ifdef __ICCARM__
#pragma type_attribute=__irq __arm 
#endif  // __ICCARM__
void R_IRQ9_isr(void)
{
    /* Clear interrupt edge detection */  
    VIC.PIC0.BIT.PIC9 = ICU_PIC_EDGE_CLEAR; 
  
    /* Toggle the P56 output level(LED1) */
    PORT5.PODR.BIT.B6 ^= 1;
        
    /* End interrupt sequence (dummy writing to HVA0 register) */
    VIC.HVA0.LONG = 0x00000000;
  
}

/*******************************************************************************
 End of function R_IRQ9_isr
*******************************************************************************/


/* End of File */
