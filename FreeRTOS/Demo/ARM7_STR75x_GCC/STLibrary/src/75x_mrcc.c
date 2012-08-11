/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_mrcc.c
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006
* Description        : This file provides all the MRCC software functions.
********************************************************************************
* History:
* 07/17/2006 : V1.0
* 03/10/2006 : V0.1
********************************************************************************
* THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
* WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
* AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT,
* INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE
* CONTENT OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING
* INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/

/* Includes ------------------------------------------------------------------*/
#include "75x_mrcc.h"

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
#define MRCC_FLAG_Mask    0x1F    /* MRCC Flag Mask */

/* MRCC_PWRCTRL mask bits */
#define MRCC_LP_Set_Mask             0x00000001
#define MRCC_LP_Reset_Mask           0xFFFFFFFE
#define MRCC_SWRESET_Mask            0x00000002
#define MRCC_WFI_Mask                0x00000004
#define MRCC_STANDBY_Mask            0x00000006
#define MRCC_LPMC_Reset_Mask         0xFFFFFFF9
#define MRCC_LPDONE_Reset_Mask       0xFFFFFF7F
#define MRCC_LPPARAM_Reset_Mask      0xFFFF1FFF
#define MRCC_WFIParam_Reset_Mask     0xFFFF1FEF
#define MRCC_CKRTCSEL_Set_Mask       0x03000000
#define MRCC_CKRTCSEL_Reset_Mask     0xFCFFFFFF
#define MRCC_CKRTCOK_Mask            0x08000000
#define MRCC_LPOSCEN_Mask            0x10000000
#define MRCC_OSC32KEN_Mask           0x20000000
            
/* MRCC_CLKCTL mask bits */
#define MRCC_PPRESC_Set_Mask        0x00000003
#define MRCC_PPRESC_Reset_Mask      0xFFFFFFFC
#define MRCC_PPRESC2_Mask           0x00000004
#define MRCC_HPRESC_Set_Mask        0x00000018
#define MRCC_HPRESC_Reset_Mask      0xFFFFFFE7
#define MRCC_MCOS_Reset_Mask        0xFFFFFF3F
#define MRCC_XTDIV2_Set_Mask        0x00008000
#define MRCC_XTDIV2_Reset_Mask      0xFFFF7FFF
#define MRCC_OSC4MBYP_Set_Mask      0x00010000
#define MRCC_OSC4MBYP_Reset_Mask    0xFFFEFFFF
#define MRCC_OSC4MOFF_Set_Mask      0x00020000  
#define MRCC_OSC4MOFF_Reset_Mask    0xFFFDFFFF
#define MRCC_NCKDF_Set_Mask         0x00040000
#define MRCC_NCKDF_Reset_Mask       0xFFFBFFFF
#define MRCC_CKOSCSEL_Set_Mask      0x00200000
#define MRCC_CKOSCSEL_Reset_Mask    0xFFDFFFFF
#define MRCC_CKUSBSEL_Mask          0x00400000
#define MRCC_CKSEL_Set_Mask         0x00800000
#define MRCC_CKSEL_Reset_Mask       0xFF7FFFFF
#define MRCC_CKSEL_CKOSCSEL_Mask    0x00A00000
#define MRCC_PLLEN_Set_Mask         0x01000000
#define MRCC_PLLEN_Reset_Mask       0xFEFFFFFF
#define MRCC_PLL2EN_Set_Mask        0x02000000
#define MRCC_PLL2EN_Reset_Mask      0xFDFFFFFF
#define MRCC_MX_Set_Mask            0x18000000
#define MRCC_MX_Reset_Mask          0xE7FFFFFF
#define MRCC_LOCK_Mask              0x80000000
#define MRCC_PLLEN_LOCK_Mask        0x81000000

/* Typical Value of the OSC4M in Hz */
#define OSC4M_Value    4000000   

/* Typical Value of the OSC4M divided by 128 (used to clock the RTC) in Hz */
#define OSC4M_Div128_Value    31250
   
/* Typical Value of the OS32K Oscillator Frequency in Hz */
#define OSC32K_Value    32768     

/* Typical Reset Value of the Internal LPOSC Oscillator Frequency in Hz */
#define LPOSC_Value    245000   

/* Typical Reset Value of the Internal FREEOSC Oscillator Frequency in Hz */
#define FREEOSC_Value    5000000 

/* Time out for OSC4M start up */
#define OSC4MStartUp_TimeOut   0xFE

/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
static ErrorStatus SetCKSYS_FREEOSC(void);
static ErrorStatus SetCKSYS_OSC4M(u32 PLL_State);
static ErrorStatus SetCKSYS_OSC4MPLL(u32 PLL_Mul);
static ErrorStatus SetCKSYS_RTC(u32 PLL_State);
static void WriteLPBit(void);
static void WriteCKOSCSELBit(void);

/* Private functions ---------------------------------------------------------*/

/*******************************************************************************
* Function Name  : MRCC_DeInit
* Description    : Deinitializes the MRCC peripheral registers to their default
*                  reset values. 
*                   - Depending on the system clock state, some bits in MRCC_CLKCTL
*                     register can’t be reset.
*                   - The OSC32K, LPOSC and RTC clock selection configuration 
*                     bits in MRCC_PWRCTRL register are not cleared by this  
*                     function. To reset those bits, use the dedicated functions 
*                     available within this driver.
*                   - The MRCC_RFSR, MRCC_BKP0 and MRCC_BKP1 registers are not
*                     reset by this function.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void MRCC_DeInit(void)
{
  /* Try to clear NCKDF bit */
  MRCC->CLKCTL &= MRCC_NCKDF_Reset_Mask;

  if((MRCC->CLKCTL & MRCC_NCKDF_Set_Mask) != RESET)
  {/* No clock detected on OSC4M */

    /* Reset LOCKIE, LOCKIF, CKUSBSEL, NCKDIE, OSC4MOFF, OSC4MBYP, MCOS[1:0], 
       MCOP, HPRESC[1:0], PPRES[2:0] bits */
    MRCC->CLKCTL &= 0x9FB40000;
     
    if((MRCC->CLKCTL & MRCC_CKOSCSEL_Set_Mask) != RESET)
    { 
      /* Clear CKOSCSEL bit --------------------------------------------------*/         
      /* Execute CKOSCSEL bit writing sequence */
      WriteCKOSCSELBit();
    }
  }
  else
  {/* Clock present on OSC4M */

    if((MRCC->CLKCTL & MRCC_CKOSCSEL_Set_Mask) != RESET)
    { 
      /* Reset CKSEL bit */
      MRCC->CLKCTL &= MRCC_CKSEL_Reset_Mask;

      /* Clear CKOSCSEL bit --------------------------------------------------*/
      /* Execute CKOSCSEL bit writing sequence */
      WriteCKOSCSELBit();
    }

    if((MRCC->CLKCTL & MRCC_CKSEL_Set_Mask) == RESET)
    {
      /* Set CKSEL bit */
      MRCC->CLKCTL |= MRCC_CKSEL_Set_Mask;  
    }

    /* Disable PLL */
    MRCC->CLKCTL &= MRCC_PLLEN_Reset_Mask;

    /* Reset LOCKIE, LOCKIF, MX[1:0], CKUSBSEL, NCKDIE, MCOS[1:0], MCOP,
       HPRESC[1:0], PPRES[2:0] bits */
    MRCC->CLKCTL &= 0x87B70000;

    /* Reset CKSEL bit */
    MRCC->CLKCTL &= MRCC_CKSEL_Reset_Mask;

    /* Reset OSC4MOFF and OSC4MBYP bits */
    MRCC->CLKCTL &= 0xFFFCFFFF;   
  }

  /* Reset RTCM, EN33V, LP_PARAM[15:13], WFI_FLASH_EN, LPMC_DBG and LPMC[1:0] bits */
  MRCC->PWRCTRL &= 0xFBFE1FE1;
  
  /* Reset PCLKEN register bits */
  MRCC->PCLKEN = 0x00;
  
  /* Reset PSWRES register bits */
  MRCC->PSWRES = 0x00;  

  /* Clear NCKDF bit */
  MRCC->CLKCTL &= MRCC_NCKDF_Reset_Mask; 
}

/*******************************************************************************
* Function Name  : MRCC_XTDIV2Config
* Description    : Enables or disables the oscillator divider by 2. This function
*                  must not be used when the PLL is enabled.
* Input          : - MRCC_XTDIV2: specifies the new state of the oscillator 
*                    divider by 2.
*                    This parameter can be one of the following values:
*                          - MRCC_XTDIV2_Disable: oscillator divider by 2 disbaled
*                          - MRCC_XTDIV2_Enable: oscillator divider by 2 enbaled
* Output         : None
* Return         : None
*******************************************************************************/
void MRCC_XTDIV2Config(u32 MRCC_XTDIV2)
{
  if(MRCC_XTDIV2 == MRCC_XTDIV2_Enable)
  {
    MRCC->CLKCTL |= MRCC_XTDIV2_Enable;
  }
  else
  {
    MRCC->CLKCTL &= MRCC_XTDIV2_Disable;
  }  
}

/*******************************************************************************
* Function Name  : MRCC_CKSYSConfig
* Description    : Configures the system clock (CK_SYS).
* Input          : - MRCC_CKSYS: specifies the clock source used as system clock.
*                    This parameter can be one of the following values:
*                          - MRCC_CKSYS_FREEOSC
*                          - MRCC_CKSYS_OSC4M
*                          - MRCC_CKSYS_OSC4MPLL
*                          - MRCC_CKSYS_RTC (RTC clock source must be previously
*                            configured using MRCC_CKRTCConfig() function)
*                : - MRCC_PLL: specifies the PLL configuration.
*                    This parameter can be one of the following values:
*                          - MRCC_PLL_Disabled: PLL disabled
*                          - MRCC_PLL_NoChange: No change on PLL configuration
*                          - MRCC_PLL_Mul_12: Multiplication by 12
*                          - MRCC_PLL_Mul_14: Multiplication by 14
*                          - MRCC_PLL_Mul_15: Multiplication by 15
*                          - MRCC_PLL_Mul_16: Multiplication by 16
* Output         : None
* Return         : An ErrorStatus enumuration value:
*                         - SUCCESS: Clock configuration succeeded
*                         - ERROR: Clock configuration failed
*******************************************************************************/
ErrorStatus MRCC_CKSYSConfig(u32 MRCC_CKSYS, u32 MRCC_PLL)
{
  ErrorStatus Status = ERROR;

  switch(MRCC_CKSYS)
  {
    case MRCC_CKSYS_FREEOSC:
      if((MRCC_PLL == MRCC_PLL_Disabled) || (MRCC_PLL == MRCC_PLL_NoChange))
      {
        Status = SetCKSYS_FREEOSC();
      }
      break;

    case MRCC_CKSYS_OSC4M:
      if((MRCC_PLL == MRCC_PLL_Disabled) || (MRCC_PLL == MRCC_PLL_NoChange))
      {
        Status = SetCKSYS_OSC4M(MRCC_PLL);
      }
      break;

    case MRCC_CKSYS_OSC4MPLL:
      if((MRCC_PLL == MRCC_PLL_Mul_12) || (MRCC_PLL == MRCC_PLL_Mul_14) ||
         (MRCC_PLL == MRCC_PLL_Mul_15) || (MRCC_PLL == MRCC_PLL_Mul_16))
      {
        Status = SetCKSYS_OSC4MPLL(MRCC_PLL);
      }
      break;

    case MRCC_CKSYS_RTC:
      if((MRCC_PLL == MRCC_PLL_Disabled) || (MRCC_PLL == MRCC_PLL_NoChange))
      {    
        Status = SetCKSYS_RTC(MRCC_PLL);
      }
      break;

    default:
      Status = ERROR;
      break;
  }
  return Status;
}

/*******************************************************************************
* Function Name  : MRCC_HCLKConfig
* Description    : Configures the AHB clock (HCLK).
* Input          : - MRCC_HCLK: defines the AHB clock. This clock is derived
*                    from the system clock(CK_SYS).
*                    This parameter can be one of the following values:
*                          - MRCC_CKSYS_Div1: AHB clock = CK_SYS
*                          - MRCC_CKSYS_Div2: AHB clock = CK_SYS/2
*                          - MRCC_CKSYS_Div4: AHB clock = CK_SYS/4
*                          - MRCC_CKSYS_Div8: AHB clock = CK_SYS/8
* Output         : None
* Return         : None
*******************************************************************************/
void MRCC_HCLKConfig(u32 MRCC_HCLK)
{
  u32 Temp = 0;
  
  /* Clear HPRESC[1:0] bits */
  Temp = MRCC->CLKCTL & MRCC_HPRESC_Reset_Mask;
  
  /* Set HPRESC[1:0] bits according to MRCC_HCLK value */
  Temp |= MRCC_HCLK;
  
  /* Store the new value */
  MRCC->CLKCTL = Temp;  
}

/*******************************************************************************
* Function Name  : MRCC_CKTIMConfig
* Description    : Configures the TIM clock (CK_TIM).
* Input          : - MRCC_CKTIM: defines the TIM clock. This clock is derived
*                    from the AHB clock(HCLK).
*                    This parameter can be one of the following values:
*                          - MRCC_HCLK_Div1: TIM clock = HCLK
*                          - MRCC_HCLK_Div2: TIM clock = HCLK/2
*                          - MRCC_HCLK_Div4: TIM clock = HCLK/4
*                          - MRCC_HCLK_Div8: TIM clock = HCLK/8
* Output         : None
* Return         : None
*******************************************************************************/
void MRCC_CKTIMConfig(u32 MRCC_CKTIM)
{
  u32 Temp = 0;
  
  /* Clear PPRESC[1:0] bits */
  Temp = MRCC->CLKCTL & MRCC_PPRESC_Reset_Mask;
  
  /* Set PPRESC[1:0] bits according to MRCC_CKTIM value */
  Temp |= MRCC_CKTIM;
  
  /* Store the new value */
  MRCC->CLKCTL = Temp;
}

/*******************************************************************************
* Function Name  : MRCC_PCLKConfig
* Description    : Configures the APB clock (PCLK).
* Input          : - MRCC_PCLK: defines the APB clock. This clock is derived 
*                    from the TIM clock(CK_TIM).
*                    This parameter can be one of the following values:
*                          - MRCC_CKTIM_Div1: APB clock = CKTIM
*                          - MRCC_CKTIM_Div2: APB clock = CKTIM/2
* Output         : None
* Return         : None
*******************************************************************************/
void MRCC_PCLKConfig(u32 MRCC_PCLK)
{
  if(MRCC_PCLK == MRCC_CKTIM_Div2)
  {
    MRCC->CLKCTL |= MRCC_CKTIM_Div2;
  }
  else
  {
    MRCC->CLKCTL &= MRCC_CKTIM_Div1;
  }
}

/*******************************************************************************
* Function Name  : MRCC_CKRTCConfig
* Description    : Configures the RTC clock (CK_RTC).
* Input          : - MRCC_CKRTC: specifies the clock source to be used as RTC
*                    clock.
*                    This parameter can be one of the following values:
*                          - MRCC_CKRTC_OSC4M_Div128
*                          - MRCC_CKRTC_OSC32K (OSC32K must be previously enabled
*                            using MRCC_OSC32KConfig() function)
*                          - MRCC_CKRTC_LPOSC (LPOSC must be previously enabled
*                            using MRCC_LPOSCConfig() function)
* Output         : None
* Return         : An ErrorStatus enumuration value:
*                         - SUCCESS: Clock configuration succeeded
*                         - ERROR: Clock configuration failed
*******************************************************************************/
ErrorStatus MRCC_CKRTCConfig(u32 MRCC_CKRTC)
{
  u32 Tmp = 0;

  if(((MRCC->CLKCTL & MRCC_CKOSCSEL_Set_Mask) != RESET) &&
     ((MRCC->CLKCTL & MRCC_CKSEL_Set_Mask) != RESET))
  { 
    /* CK_RTC used as CK_SYS clock source */
    return ERROR;
  }
  else
  {    
    /* Clear CKRTCSEL[1:0] bits */
    Tmp = MRCC->PWRCTRL & MRCC_CKRTCSEL_Reset_Mask;

    /* Set CKRTCSEL[1:0] bits according to MRCC_CKRTC value */
    Tmp |= MRCC_CKRTC;

    /* Store the new value */
    MRCC->PWRCTRL = Tmp;       
  }

  return SUCCESS;
}

/*******************************************************************************
* Function Name  : MRCC_CKUSBConfig
* Description    : Configures the USB clock(CK_USB).
* Input          : - MRCC_CKUSB: specifies the clock source to be used as USB
*                    clock.
*                    This parameter can be one of the following values:
*                          - MRCC_CKUSB_Internal(CK_PLL2 enabled)
*                          - MRCC_CKUSB_External(CK_PLL2 disabled)
* Output         : None
* Return         : An ErrorStatus enumuration value:
*                         - SUCCESS: Clock configuration succeeded
*                         - ERROR: Clock configuration failed
*******************************************************************************/
ErrorStatus MRCC_CKUSBConfig(u32 MRCC_CKUSB)
{
  if(MRCC_CKUSB == MRCC_CKUSB_External)
  {
    /* Disable CK_PLL2 */
    MRCC->CLKCTL &= MRCC_PLL2EN_Reset_Mask;

    /* External USB clock selected */
    MRCC->CLKCTL |= MRCC_CKUSB_External;
  }
  else
  {
    if((MRCC->CLKCTL & MRCC_PLLEN_LOCK_Mask) != RESET)
    { /* PLL enabled and locked */
      
      /* Enable CK_PLL2 */
      MRCC->CLKCTL |= MRCC_PLL2EN_Set_Mask;

      /* Internal USB clock selected */
      MRCC->CLKCTL &= MRCC_CKUSB_Internal;
    }
    else
    {
      /* PLL not enabled */
      return ERROR;
    }
  }

  return SUCCESS;  
}

/*******************************************************************************
* Function Name  : MRCC_ITConfig
* Description    : Enables or disables the specified MRCC interrupts.
* Input          : - MRCC_IT: specifies the MRCC interrupts sources to be
*                    enabled or disabled. This parameter can be any combination
*                    of the following values:
*                          - MRCC_IT_LOCK: PLL lock interrupt
*                          - MRCC_IT_NCKD: No Clock detected interrupt
*                  - NewState: new state of the MRCC interrupts.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void MRCC_ITConfig(u32 MRCC_IT, FunctionalState NewState)
{
  if(NewState == ENABLE)
  {
    MRCC->CLKCTL |= MRCC_IT;
  }
  else
  {
    MRCC->CLKCTL &= ~MRCC_IT;
  }
}

/*******************************************************************************
* Function Name  : MRCC_PeripheralClockConfig
* Description    : Enables or disables the specified peripheral clock.
* Input          : - MRCC_Peripheral: specifies the peripheral to gates its
*                    clock. More than one peripheral can be selected using
*                    the “|” operator.
*                  - NewState: new state of the specified peripheral clock.
*                    This parameter can be one of the following values:
*                          - ENABLE: the selected peripheral clock is enabled
*                          - DISABLE: the selected peripheral clock is disabled
* Output         : None
* Return         : None
*******************************************************************************/
void MRCC_PeripheralClockConfig(u32 MRCC_Peripheral, FunctionalState NewState)
{
  if(NewState == ENABLE)
  {
    MRCC->PCLKEN |= MRCC_Peripheral;
  }
  else
  {
    MRCC->PCLKEN &= ~MRCC_Peripheral;
  }
}

/*******************************************************************************
* Function Name  : MRCC_PeripheralSWResetConfig
* Description    : Forces or releases peripheral software reset.
* Input          : - MRCC_Peripheral: specifies the peripheral to reset. More
*                    than one peripheral can be selected using the “|” operator.
*                  - NewState: new state of the specified peripheral software
*                    reset. This parameter can be one of the following values:
*                          - ENABLE: the selected peripheral is kept under reset
*                          - DISABLE: the selected peripheral exits from reset
* Output         : None
* Return         : None
*******************************************************************************/
void MRCC_PeripheralSWResetConfig(u32 MRCC_Peripheral, FunctionalState NewState)
{
  if(NewState == ENABLE)
  {
    MRCC->PSWRES |= MRCC_Peripheral;
  }
  else
  {
    MRCC->PSWRES &= ~MRCC_Peripheral;
  }
}

/*******************************************************************************
* Function Name  : MRCC_GetClocksStatus
* Description    : Returns the status and frequencies of different on chip clocks.
*                  Don’t use this function when CK_SYS is clocked by an external
*                  clock source (OSC4M bypassed).
* Input          : - MRCC_ClocksStatus: pointer to a MRCC_ClocksTypeDef structure
*                    which will hold the clocks information.
* Output         : None
* Return         : None
*******************************************************************************/
void MRCC_GetClocksStatus(MRCC_ClocksTypeDef*  MRCC_ClocksStatus)
{
  u32 PLLMul = 0;
  u32 Temp = 0;
  u32 Presc = 0;

  /* Get the Status of PLL */
  if((MRCC->CLKCTL & MRCC_PLLEN_Set_Mask) == RESET)  
  {
    MRCC_ClocksStatus->PLL_Status = OFF;
  }
  else
  {
    MRCC_ClocksStatus->PLL_Status = ON;
  }
  
  /* Get the Status of OSC4M */
  if((MRCC->CLKCTL & MRCC_OSC4MOFF_Set_Mask) == RESET)  
  {
    MRCC_ClocksStatus->OSC4M_Status = ON;
  }
  else
  {
    MRCC_ClocksStatus->OSC4M_Status = OFF;
  }  
  
  /* Get the Status of LPOSC */
  if((MRCC->PWRCTRL & MRCC_LPOSCEN_Mask) == RESET)  
  {
    MRCC_ClocksStatus->LPOSC_Status = OFF;
  }
  else
  {
    MRCC_ClocksStatus->LPOSC_Status = ON;
  }  
  
  /* Get the Status of OSC32K */
  if((MRCC->PWRCTRL & MRCC_OSC32KEN_Mask) == RESET)  
  {
    MRCC_ClocksStatus->OSC32K_Status = OFF;
  }
  else
  {
    MRCC_ClocksStatus->OSC32K_Status = ON;
  } 
    
/* Get CKU_SB source ---------------------------------------------------------*/  
  if((MRCC->CLKCTL & MRCC_CKUSBSEL_Mask) != RESET)
  {
    MRCC_ClocksStatus->CKUSB_Source = External;    
  }
  else
  {  
    if((MRCC->CLKCTL & MRCC_PLL2EN_Set_Mask) != RESET)
    {
      MRCC_ClocksStatus->CKUSB_Source = Internal;
    
    }
    else 
    {
      MRCC_ClocksStatus->CKUSB_Source = Disabled;    
    }
  }

/* Get CK_RTC source ---------------------------------------------------------*/ 
  Temp = MRCC->PWRCTRL & MRCC_CKRTCSEL_Set_Mask;
  Temp = Temp >> 24;
    
  switch(Temp)
  {
    case 0x00:
      MRCC_ClocksStatus->CKRTC_Source = Disabled;
      break;

    case 0x01:
      MRCC_ClocksStatus->CKRTC_Source = OSC4M_Div128;
      break;

    case 0x02:
      MRCC_ClocksStatus->CKRTC_Source = OSC32K;
      break;
        
    case 0x03:
      MRCC_ClocksStatus->CKRTC_Source = LPOSC;              
      break;
        
    default:
      MRCC_ClocksStatus->CKRTC_Source = Disabled;
      break;          
  }
      
/* Get CK_SYS source ---------------------------------------------------------*/   
  if((MRCC->CLKCTL & MRCC_CKSEL_Set_Mask) != RESET)
  {/* CK_OSC used as CK_SYS clock source */
    
    if((MRCC->CLKCTL & MRCC_CKOSCSEL_Set_Mask) != RESET)
    { /* CK_RTC used as CK_OSC clock source */
      MRCC_ClocksStatus->CKSYS_Source = CKRTC;
      
      if(MRCC_ClocksStatus->CKRTC_Source == OSC32K)
      {
        /* CK_SYS clock frequency */
        MRCC_ClocksStatus->CKSYS_Frequency = OSC32K_Value;         
      }         
      else if(MRCC_ClocksStatus->CKRTC_Source == LPOSC)

      {
        /* CK_SYS clock frequency */
        MRCC_ClocksStatus->CKSYS_Frequency = LPOSC_Value;             
      }
      else if(MRCC_ClocksStatus->CKRTC_Source == OSC4M_Div128)

      {
        /* CK_SYS clock frequency */
        MRCC_ClocksStatus->CKSYS_Frequency = OSC4M_Div128_Value;             
      }
    }
    else
    { /* OSC4M used as CK_OSC clock source */
      MRCC_ClocksStatus->CKSYS_Source = OSC4M; 
    
      if((MRCC->CLKCTL & MRCC_XTDIV2_Set_Mask) != RESET)
      {
        /* CK_SYS clock frequency */
        MRCC_ClocksStatus->CKSYS_Frequency = Main_Oscillator >> 1;
      }
      else
      {
        /* CK_SYS clock frequency */
        MRCC_ClocksStatus->CKSYS_Frequency = Main_Oscillator;
      }          
    }
  }     
  else
  {/* CK_PLL1 used as CK_SYS clock */
    
    if(MRCC_ClocksStatus->PLL_Status == OFF)
    { /* FREEOSC used as CK_PLL1 clock source */
      MRCC_ClocksStatus->CKSYS_Source = FREEOSC; 
      
      /* CK_SYS clock frequency */
      MRCC_ClocksStatus->CKSYS_Frequency = FREEOSC_Value;               
    }
    else
    { /* OSC4M followed by PLL used as CK_PLL1 clock source */
      MRCC_ClocksStatus->CKSYS_Source = OSC4MPLL;
                    
      /* Get PLL factor ------------------------------------------------------*/
      Temp = MRCC->CLKCTL & MRCC_MX_Set_Mask;
      Temp = Temp >> 27;
    
      switch(Temp)
      {
        case 0x00:
          PLLMul = 16;
          break;

        case 0x01:
          PLLMul = 15;
          break;

        case 0x02:
          PLLMul = 14;
          break;
        
        case 0x03:
          PLLMul = 12;
          break;
        
        default:
          PLLMul = 16;
          break;          
      } 
      
      /* CK_SYS clock frequency */
      MRCC_ClocksStatus->CKSYS_Frequency = OSC4M_Value * PLLMul;     
    }
  }

/* Compute HCLK, CKTIM and PCLK clocks frequencies ---------------------------*/    
  /* Get HCLK prescaler */
  Presc = MRCC->CLKCTL & MRCC_HPRESC_Set_Mask;
  Presc = Presc >> 3;
  /* HCLK clock frequency */
  MRCC_ClocksStatus->HCLK_Frequency = MRCC_ClocksStatus->CKSYS_Frequency >> Presc;

  /* Get CK_TIM prescaler */
  Presc = MRCC->CLKCTL & MRCC_PPRESC_Set_Mask;
  /* CK_TIM clock frequency */
  MRCC_ClocksStatus->CKTIM_Frequency = MRCC_ClocksStatus->HCLK_Frequency >> Presc;
 
  /* Get PCLK prescaler */
  Presc = MRCC->CLKCTL & MRCC_PPRESC2_Mask;
  Presc = Presc >> 2;
  /* PCLK clock frequency */
  MRCC_ClocksStatus->PCLK_Frequency = MRCC_ClocksStatus->CKTIM_Frequency >> Presc;
}

/*******************************************************************************
* Function Name  : MRCC_LPMC_DBGonfig
* Description    : Enables or disables the Low Power Debug Mode.
* Input          : - MRCC_LPDM: specifies the LPDM new state value.
*                    This parameter can be one of the following values:
*                          - MRCC_LPDM_Disable
*                          - MRCC_LPDM_Enable
* Output         : None
* Return         : None
*******************************************************************************/
void MRCC_LPMC_DBGConfig(u32 MRCC_LPDM)
{
  if(MRCC_LPDM == MRCC_LPDM_Enable)
  {
    MRCC->PWRCTRL |= MRCC_LPDM_Enable;
  }
  else
  {
    MRCC->PWRCTRL &= MRCC_LPDM_Disable;
  }
}

/*******************************************************************************
* Function Name  : MRCC_EnterWFIMode
* Description    : Enters WFI mode.
*                  If the Flash is used in Burst mode, it must be kept enabled
*                  in WFI mode(use MRCC_WFIParam_FLASHOn as parameter)
* Input          : - MRCC_WFIParam: specifies the WFI mode control parameters.
*                    This parameter can be one of the following values:
*                          - MRCC_WFIParam_FLASHPowerDown(DMA not allowed during WFI)
*                          - MRCC_WFIParam_FLASHOn(DMA allowed during WFI)
*                          - MRCC_WFIParam_FLASHOff(DMA not allowed during WFI)
* Output         : None
* Return         : None
*******************************************************************************/
void MRCC_EnterWFIMode(u32 MRCC_WFIParam)
{
/* Low Power mode configuration ----------------------------------------------*/
  /* Clear LPMC[1:0] bits */
   MRCC->PWRCTRL &= MRCC_LPMC_Reset_Mask;

  /* Select WFI mode */
  MRCC->PWRCTRL |= MRCC_WFI_Mask;

/* Low Power mode control parameters configuration ---------------------------*/
  /* Clear LP_PARAM[15:13] and WFI_FLASH_EN bits */
  MRCC->PWRCTRL &= MRCC_WFIParam_Reset_Mask;
  
  if(MRCC_WFIParam != MRCC_WFIParam_FLASHPowerDown)
  {
    /* Set LP_PARAM[15:13] and WFI_FLASH_EN bits according to MRCC_WFIParam value */
    MRCC->PWRCTRL |= MRCC_WFIParam;
  }
    
/* Execute the Low Power bit writing sequence --------------------------------*/
  WriteLPBit();
}

/*******************************************************************************
* Function Name  : MRCC_EnterSTOPMode
* Description    : Enters STOP mode.
* Input          : - MRCC_STOPParam: specifies the STOP mode control parameters.
*                    This parameter can be one of the following values:
*                          - MRCC_STOPParam_Default (OSC4M On, FLASH On, MVREG On)
*                          - MRCC_STOPParam_OSC4MOff
*                          - MRCC_STOPParam_FLASHOff
*                          - MRCC_STOPParam_MVREGOff
* Output         : None
* Return         : None
*******************************************************************************/
void MRCC_EnterSTOPMode(u32 MRCC_STOPParam)
{
/* Low Power mode configuration ----------------------------------------------*/
  /* Clear LPMC[1:0] bits (STOP mode is selected) */
   MRCC->PWRCTRL &= MRCC_LPMC_Reset_Mask;

/* Low Power mode control parameters configuration ---------------------------*/
  /* Clear LP_PARAM[15:13] bits */
  MRCC->PWRCTRL &= MRCC_LPPARAM_Reset_Mask;
  
  if(MRCC_STOPParam != MRCC_STOPParam_Default)
  {
    /* Set LP_PARAM[15:13] bits according to MRCC_STOPParam value */
    MRCC->PWRCTRL |= MRCC_STOPParam;
  }

/* Execute the Low Power bit writing sequence --------------------------------*/
  WriteLPBit();
}

/*******************************************************************************
* Function Name  : MRCC_EnterSTANDBYMode
* Description    : Enters STANDBY mode.
*                  Make sure that WKPF flag is cleared before using this function.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void MRCC_EnterSTANDBYMode(void)
{
/* Low Power mode configuration ----------------------------------------------*/
  /* Clear LPMC[1:0] bits */
   MRCC->PWRCTRL &= MRCC_LPMC_Reset_Mask;

  /* Select STANDBY mode */
  MRCC->PWRCTRL |= MRCC_STANDBY_Mask;

/* Execute the Low Power bit writing sequence --------------------------------*/
  WriteLPBit();
}

/*******************************************************************************
* Function Name  : MRCC_GenerateSWReset
* Description    : Generates a system software reset.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void MRCC_GenerateSWReset(void)
{
/* Low Power mode configuration ----------------------------------------------*/
  /* Clear LPMC[1:0] bits */
  MRCC->PWRCTRL &= MRCC_LPMC_Reset_Mask;

  /* Select software reset */
  MRCC->PWRCTRL |= MRCC_SWRESET_Mask;

/* Execute the Low Power bit writing sequence --------------------------------*/
  WriteLPBit();
}

/*******************************************************************************
* Function Name  : MRCC_WriteBackupRegister
* Description    : Writes user data to the specified backup register.
* Input          : - MRCC_BKP: specifies the backup register.
*                    This parameter can be one of the following values:
*                          - MRCC_BKP0
*                          - MRCC_BKP1
*                  - Data: data to write.
* Output         : None
* Return         : None
*******************************************************************************/
void MRCC_WriteBackupRegister(MRCC_BKPReg MRCC_BKP, u32 Data)
{
  if(MRCC_BKP == MRCC_BKP0)
  {
    MRCC->BKP0 = Data;
  }
  else
  {
    MRCC->BKP1 = Data;
  }
}

/*******************************************************************************
* Function Name  : MRCC_ReadBackupRegister
* Description    : Reads data from the specified backup register.
* Input          : - MRCC_BKP: specifies the backup register.
*                    This parameter can be one of the following values:
*                          - MRCC_BKP0
*                          - MRCC_BKP1
* Output         : None
* Return         : The content of the specified backup register.
*******************************************************************************/
u32 MRCC_ReadBackupRegister(MRCC_BKPReg MRCC_BKP)
{
  if(MRCC_BKP == MRCC_BKP0)
  {
    return(MRCC->BKP0);
  }
  else
  {
    return(MRCC->BKP1);
  }
}

/*******************************************************************************
* Function Name  : MRCC_IOVoltageRangeConfig
* Description    : Configures the I/O pins voltage range.
* Input          : - MRCC_IOVoltageRange: specifies the I/O pins voltage range.
*                    This parameter can be one of the following values:
*                          - MRCC_IOVoltageRange_5V
*                          - MRCC_IOVoltageRange_3V3
* Output         : None
* Return         : None
*******************************************************************************/
void MRCC_IOVoltageRangeConfig(u32 MRCC_IOVoltageRange)
{
  if(MRCC_IOVoltageRange == MRCC_IOVoltageRange_3V3)
  {
    MRCC->PWRCTRL |= MRCC_IOVoltageRange_3V3;
  }
  else
  {
    MRCC->PWRCTRL &= MRCC_IOVoltageRange_5V;
  }
}

/*******************************************************************************
* Function Name  : MRCC_MCOConfig
* Description    : Selects the clock source to output on MCO pin (P0.1).
*                  To output the clock, the associated alternate function must
*                  be enabled in the I/O port controller.
* Input          : - MRCC_MCO: specifies the clock source to output.
*                    This parameter can be one of the following values:
*                          - MRCC_MCO_HCLK
*                          - MRCC_MCO_PCLK
*                          - MRCC_MCO_OSC4M
*                          - MRCC_MCO_CKPLL2
*                  - MRCC_MCOPrescaler: specifies if prescaler, divide by 1 or 2,
*                    is applied to this clock before outputting it to MCO pin.
*                    This parameter can be one of the following values:
*                          - MRCC_MCOPrescaler_1
*                          - MRCC_MCOPrescaler_2
* Output         : None
* Return         : None
*******************************************************************************/
void MRCC_MCOConfig(u32 MRCC_MCO, u32 MCO_MCOPrescaler)
{
  u32 Temp = 0;
/* MCO prescaler configuration -----------------------------------------------*/
  if(MCO_MCOPrescaler == MRCC_MCOPrescaler_2)
  {
    MRCC->CLKCTL |= MRCC_MCOPrescaler_2;
  }
  else
  {
    MRCC->CLKCTL &= MRCC_MCOPrescaler_1;
  }

/* MCO selection configuration -----------------------------------------------*/

  /* Clear MCOS[1:0] bits */
  Temp = MRCC->CLKCTL & MRCC_MCOS_Reset_Mask;

  /* Set MCOS[1:0] bits according to MRCC_MCO value */
  Temp |= MRCC_MCO;
  
  /* Store the new value */
  MRCC->CLKCTL = Temp;
}

/*******************************************************************************
* Function Name  : MRCC_OSC4MConfig
* Description    : Configures the 4MHz main oscillator (OSC4M).
*                  This function must be used when the CK_SYS is not clocked
*                  by the OSC4M and the PLL is not enabled.
* Input          : - MRCC_OSC4M: specifies the new state of the OSC4M oscillator.
*                    This parameter can be one of the following values:
*                          - MRCC_OSC4M_Default: OSC4M enabled, bypass disabled
*                          - MRCC_OSC4M_Disable: OSC4M disabled
*                          - MRCC_OSC4M_Bypass:  OSC4M bypassed
* Output         : None
* Return         : An ErrorStatus enumuration value:
*                         - SUCCESS: Clock configuration succeeded
*                         - ERROR: Clock configuration failed
*******************************************************************************/
ErrorStatus MRCC_OSC4MConfig(u32 MRCC_OSC4M)
{
  ErrorStatus Status = SUCCESS;

/* If CK_SYS is driven by OSC4M or the PLL is enabled, exit ------------------*/           
  if(((MRCC->CLKCTL & MRCC_CKSEL_CKOSCSEL_Mask) == MRCC_CKSEL_Set_Mask) ||    
     (((MRCC->CLKCTL & MRCC_CKSEL_CKOSCSEL_Mask) == MRCC_CKSEL_CKOSCSEL_Mask) &&
     ((MRCC->PWRCTRL & MRCC_CKRTCSEL_Reset_Mask) != RESET))||
     ((MRCC->CLKCTL & MRCC_PLLEN_Set_Mask) != RESET))
  {
    Status = ERROR;
  }
/* Else configure the OSC4MOFF and OSC4MBYP bits -----------------------------*/   
  else
  {  
    switch(MRCC_OSC4M)
    {
      case MRCC_OSC4M_Default:
        MRCC->CLKCTL &= MRCC_OSC4MOFF_Reset_Mask & MRCC_OSC4MBYP_Reset_Mask;
        break;
      
      case MRCC_OSC4M_Disable:
        MRCC->CLKCTL &= MRCC_OSC4MBYP_Reset_Mask;
        MRCC->CLKCTL |= MRCC_OSC4MOFF_Set_Mask;
        break;
        
      case MRCC_OSC4M_Bypass:
        MRCC->CLKCTL &= MRCC_OSC4MOFF_Reset_Mask;
        MRCC->CLKCTL |= MRCC_OSC4MBYP_Set_Mask;
        break;        
      
      default:
        Status =  ERROR;
        break;      
    }
  }  
  
  return Status; 
}

/*******************************************************************************
* Function Name  : MRCC_OSC32KConfig
* Description    : Configures the OSC32K oscillator.
*                  This function must be used when the CK_SYS is not clocked by
*                  the CK_RTC.
* Input          : - MRCC_OSC32K: specifies the new state of the OSC32K oscillator.
*                    This parameter can be one of the following values:
*                          - MRCC_OSC32K_Disable: OSC32K disabled
*                          - MRCC_OSC32K_Enable: OSC32K enabled
*                  - MRCC_OSC32KBypass: specifies if the OSC32K oscillator is
*                    bypassed or not.
*                    This parameter can be one of the following values:
*                          - MRCC_OSC32KBypass_Disable: OSC32K selected
*                          - MRCC_OSC32KBypass_Enable: OSC32K bypassed                          
* Output         : None
* Return         : An ErrorStatus enumuration value:
*                         - SUCCESS: Clock configuration succeeded
*                         - ERROR: Clock configuration failed
*******************************************************************************/
ErrorStatus MRCC_OSC32KConfig(u32 MRCC_OSC32K, u32 MRCC_OSC32KBypass)
{ 
/* If CK_SYS is driven by CK_RTC, exit ---------------------------------------*/     
  if(((MRCC->CLKCTL & MRCC_CKSEL_Set_Mask) != RESET) &&
      ((MRCC->CLKCTL & MRCC_CKOSCSEL_Set_Mask) != RESET))
  {
    return ERROR;
  }
/* Else configure the OSC32KEN and OSC32KBYP bits ----------------------------*/ 
  else
  { 
    /* Configure OSC32KEN bit */
    if(MRCC_OSC32K == MRCC_OSC32K_Enable)
    {
      MRCC->PWRCTRL |= MRCC_OSC32K_Enable;
    }
    else
    {
      MRCC->PWRCTRL &= MRCC_OSC32K_Disable;
    }
    
    /* Configure OSC32KBYP bit */
    if(MRCC_OSC32KBypass == MRCC_OSC32KBypass_Enable)
    {
      MRCC->PWRCTRL |= MRCC_OSC32KBypass_Enable;
    }
    else
    {
      MRCC->PWRCTRL &= MRCC_OSC32KBypass_Disable;
    }   
     
    return SUCCESS;   
  }
}

/*******************************************************************************
* Function Name  : MRCC_LPOSCConfig
* Description    : Enables or disables the LPOSC oscillator.
*                  This function must be used when the CK_SYS is not clocked by
*                  the CK_RTC.
* Input          : - MRCC_LPOSC: specifies the new state of the LPOSC oscillator.
*                    This parameter can be one of the following values:
*                          - MRCC_LPOSC_Disable: LPOSC disabled
*                          - MRCC_LPOSC_Enable: LPOSC enabled
* Output         : None
* Return         : An ErrorStatus enumuration value:
*                         - SUCCESS: Clock configuration succeeded
*                         - ERROR: Clock configuration failed
*******************************************************************************/
ErrorStatus MRCC_LPOSCConfig(u32 MRCC_LPOSC)
{
/* If CK_SYS is driven by CK_RTC or LPOSC is used as CK_RTC clock source, exit*/      
  if((((MRCC->CLKCTL & MRCC_CKSEL_Set_Mask) != RESET) &&
     ((MRCC->CLKCTL & MRCC_CKOSCSEL_Set_Mask) != RESET)) ||
     ((MRCC->PWRCTRL & MRCC_CKRTCSEL_Set_Mask) == MRCC_CKRTC_LPOSC)) 
  {
    return ERROR;
  }
/* Else configure the LPOSCEN bit --------------------------------------------*/  
  else
  {   
    if(MRCC_LPOSC == MRCC_LPOSC_Enable)
    {
      MRCC->PWRCTRL |= MRCC_LPOSC_Enable;
    }
    else
    {
      MRCC->PWRCTRL &= MRCC_LPOSC_Disable;
    }

    return SUCCESS;
  }     
}

/*******************************************************************************
* Function Name  : MRCC_RTCMConfig
* Description    : Enables or disables RTC clock measurement.
* Input          : - MRCC_RTCM: specifies whether CK_RTC is connected to TB 
*                    timer IC1 or not.
*                    This parameter can be one of the following values:
*                          - MRCC_RTCM_Disable: CK_RTC not connected to TB timer IC1
*                          - MRCC_RTCM_Enable: CK_RTC connected to TB timer IC1
* Output         : None
* Return         : None
*******************************************************************************/
void MRCC_RTCMConfig(u32 MRCC_RTCM)
{
  if(MRCC_RTCM == MRCC_RTCM_Enable)
  {
    MRCC->PWRCTRL |= MRCC_RTCM_Enable;
  }
  else
  {
    MRCC->PWRCTRL &= MRCC_RTCM_Disable;
  }  
}

/*******************************************************************************
* Function Name  : MRCC_SetBuilderCounter
* Description    : Sets the builder counter value which defines the delay for
*                  the 4MHz main oscillator (OSC4M) clock to be stabilized.
* Input          : - BuilderCounter: defines the delay for the OSC4M oscillator
*                    clock to be stabilized.
* Output         : None
* Return         : None
*******************************************************************************/
void MRCC_SetBuilderCounter(u8 BuilderCounter)
{ 
  *(u8 *) 0x60000026 = BuilderCounter;
}

/*******************************************************************************
* Function Name  : MRCC_GetCKSYSCounter
* Description    : Gets the result of the delay applied to CK_SYS before
*                  starting the CPU.
* Input          : None
* Output         : None
* Return         : SCOUNT value.
*******************************************************************************/
u16 MRCC_GetCKSYSCounter(void)
{
  return((u16)(MRCC->RFSR & 0x0FFF));
}

/*******************************************************************************
* Function Name  : MRCC_GetFlagStatus
* Description    : Checks whether the specified MRCC flag is set or not.
* Input          : - MRCC_FLAG: specifies the flag to check.
*                    This parameter can be one of the following values:
*                          - MRCC_FLAG_LOCK: PLL Locked flag
*                          - MRCC_FLAG_LOCKIF: PLL Lock Interrupt status flag
*                          - MRCC_FLAG_CKSEL: CK_SYS source staus flag
*                          - MRCC_FLAG_CKOSCSEL: CK_OSC clock source staus flag
*                          - MRCC_FLAG_NCKD: No Clock Detected flag
*                          - MRCC_FLAG_SWR: Software Reset flag
*                          - MRCC_FLAG_WDGR: Watchdog Reset flag
*                          - MRCC_FLAG_EXTR: External Reset flag
*                          - MRCC_FLAG_WKP: Wake-Up flag
*                          - MRCC_FLAG_STDB: STANDBY flag
*                          - MRCC_FLAG_BCOUNT:   Builder Counter Flag
*                          - MRCC_FLAG_OSC32KRDY: Oscillator 32K Ready
*                          - MRCC_FLAG_CKRTCOK: CK_RTC OK
*                          - MRCC_FLAG_LPDONE: Low Power Bit Sequence has been performed
*                          - MRCC_FLAG_LP: Low Power Mode Entry
* Output         : None
* Return         : The new state of MRCC_FLAG (SET or RESET).
*******************************************************************************/
FlagStatus MRCC_GetFlagStatus(u8 MRCC_FLAG)
{
  u32 MRCCReg = 0, FlagPos = 0;
  u32 StatusReg = 0;

  /* Get the MRCC register index */
  MRCCReg = MRCC_FLAG >> 5;

  /* Get the flag position */
  FlagPos = MRCC_FLAG & MRCC_FLAG_Mask;

  if(MRCCReg == 1) /* The flag to check is in CLKCTL register */
  {
    StatusReg = MRCC->CLKCTL;
  }
  else if (MRCCReg == 2) /* The flag to check is in RFSR register */
  {
    StatusReg = MRCC->RFSR;
  }
  else if(MRCCReg == 3) /* The flag to check is in PWRCTRL register */
  {
    StatusReg = MRCC->PWRCTRL;
  }
  
  if((StatusReg & (1 << FlagPos))!= RESET)
  {
    return SET;
  }
  else
  {
    return RESET;
  }
}

/*******************************************************************************
* Function Name  : MRCC_ClearFlag
* Description    : Clears the MRCC’s pending flags.
* Input          : - MRCC_FLAG: specifies the flag to clear.
*                    This parameter can be one of the following values:
*                          - MRCC_FLAG_NCKD: No Clock Detected flag
*                          - MRCC_FLAG_SWR: Software Reset flag
*                          - MRCC_FLAG_WDGR: Watchdog Reset flag
*                          - MRCC_FLAG_EXTR: External Reset flag
*                          - MRCC_FLAG_WKP: Wake-Up flag
*                          - MRCC_FLAG_STDB: STANDBY flag
*                          - MRCC_FLAG_LPDONE: Low Power Bit Sequence has been performed
* Output         : None
* Return         : None
*******************************************************************************/
void MRCC_ClearFlag(u8 MRCC_FLAG)
{
  u32 MRCCReg = 0, FlagPos = 0;

  /* Get the MRCC register index */
  MRCCReg = MRCC_FLAG >> 5;

  /* Get the flag position */
  FlagPos = MRCC_FLAG & MRCC_FLAG_Mask;

  if(MRCCReg == 1) /* The flag to clear is in CLKCTL register */
  {
    MRCC->CLKCTL &= ~(1 << FlagPos);
  }
  else if (MRCCReg == 2) /* The flag to clear is in RFSR register */
  {
    MRCC->RFSR &= ~(1 << FlagPos);
  }
  else if(MRCCReg == 3) /* The flag to clear is in PWRCTRL register */
  {
    MRCC->PWRCTRL &= ~(1 << FlagPos);
  }
}

/*******************************************************************************
* Function Name  : MRCC_GetITStatus
* Description    : Checks whether the specified MRCC interrupt has occurred or not.
* Input          : - MRCC_IT: specifies the MRCC interrupt source to check.
*                    This parameter can be one of the following values:
*                          - MRCC_IT_LOCK: PLL lock interrupt
*                          - MRCC_IT_NCKD: No Clock detected interrupt
* Output         : None
* Return         : The new state of MRCC_IT (SET or RESET).
*******************************************************************************/
ITStatus MRCC_GetITStatus(u32 MRCC_IT)
{
  /* Check the specified interrupt pending bit */
  if((MRCC->CLKCTL & (MRCC_IT >> 1)) != RESET)
  {
    return SET;
  }
  else
  {
    return RESET;
  }
}

/*******************************************************************************
* Function Name  : MRCC_ClearITPendingBit
* Description    : Clears the MRCC’s interrupt pending bits.
* Input          : - MRCC_IT: specifies the interrupt pending bit to clear.
*                    This parameter can be any combination of the following
*                    values:
*                          - MRCC_IT_LOCK: PLL lock interrupt
*                          - MRCC_IT_NCKD: No Clock detected interrupt
* Output         : None
* Return         : None
*******************************************************************************/
void MRCC_ClearITPendingBit(u32 MRCC_IT)
{
  /* Clear the specified interrupt pending bit */
  MRCC->CLKCTL &= ~(MRCC_IT >> 1);
}

/*******************************************************************************
* Function Name  : MRCC_WaitForOSC4MStartUp
* Description    : Waits for OSC4M start-up.
* Input          : None
* Output         : None
* Return         : An ErrorStatus enumuration value:
*                         - SUCCESS: OSC4M oscillator is stable and ready to use
*                         - ERROR: no clock is detected on OSC4M
*******************************************************************************/
ErrorStatus MRCC_WaitForOSC4MStartUp(void)
{
  u32 StartUpCounter = 0;

  do
  {
    /* Clear No Clock Detected flag */
    if(MRCC_GetFlagStatus(MRCC_FLAG_NCKD) != RESET)
    {
      MRCC_ClearFlag(MRCC_FLAG_NCKD);
    }

    StartUpCounter++;

  }while((MRCC_GetFlagStatus(MRCC_FLAG_BCOUNT) == RESET)&&
         (StartUpCounter != OSC4MStartUp_TimeOut));
  
  if(MRCC_GetFlagStatus(MRCC_FLAG_BCOUNT) != RESET)
  {
    return SUCCESS;
  }
  else
  {
    return ERROR;
  }  
}

/*******************************************************************************
* Function Name  : SetCKSYS_FREEOSC
* Description    : Selects FREEOSC as CK_SYS clock source.
* Input          : None
* Output         : None
* Return         : An ErrorStatus enumuration value:
*                         - SUCCESS: Clock configuration succeeded
*                         - ERROR: Clock configuration failed
*******************************************************************************/
static ErrorStatus SetCKSYS_FREEOSC(void)
{
  /* Check if the PLL is enabled */
  if((MRCC->CLKCTL & MRCC_PLLEN_Set_Mask) != RESET)
  {  
    if((MRCC->CLKCTL & MRCC_CKSEL_Set_Mask) == RESET)
    { /* CK_PLL1 used as Ck_SYS clock source*/

      if((MRCC->CLKCTL & MRCC_CKOSCSEL_Set_Mask) != RESET)
      {/* Check if CK_RTC source clock is present*/ 
        if((MRCC->PWRCTRL & MRCC_CKRTCSEL_Set_Mask) == RESET) 
        {
          /* CK_RTC disabled*/
          return ERROR;
        }
      }
      
      /* Select CK_OSC as CK_SYS clock source */
      MRCC->CLKCTL |= MRCC_CKSEL_Set_Mask;
    }  
    
    /* Disable PLL */
    MRCC->CLKCTL &= MRCC_PLLEN_Reset_Mask;
  }

  /* Select CK_PLL1 as CK_SYS clock source */
  MRCC->CLKCTL &= MRCC_CKSEL_Reset_Mask;

  if((MRCC->CLKCTL & MRCC_CKSEL_Set_Mask) == RESET)
  {
    return SUCCESS;
  }
  else
  {
    return ERROR;
  }
}

/*******************************************************************************
* Function Name  : SetCKSYS_OSC4M
* Description    : Selects 4MHz main oscillator (OSC4M) as CK_SYS clock source.
* Input          : PLL_State: specifies the PLL state.
* Output         : None
* Return         : An ErrorStatus enumuration value:
*                         - SUCCESS: Clock configuration succeeded
*                         - ERROR: Clock configuration failed
*******************************************************************************/
static ErrorStatus SetCKSYS_OSC4M(u32 PLL_State)
{
/* If OSC4M is not present, exit ---------------------------------------------*/      
  if(((MRCC->CLKCTL & MRCC_NCKDF_Set_Mask) != RESET) || 
     ((MRCC->CLKCTL & MRCC_OSC4MOFF_Set_Mask) != RESET) ) 
  {
    /* OSC4M disabled or OSC4M clock is not present*/
    return ERROR;
  }

/* Else configure CKSEL and CKOSCSEL bits ------------------------------------*/          
  if((MRCC->CLKCTL & MRCC_CKOSCSEL_Set_Mask) != RESET)
  { /* CK_RTC used as CK_OSC clock */   
  
    if((MRCC->CLKCTL & MRCC_CKSEL_Set_Mask) != RESET) 
    {
      /* Select CK_PLL1 as CK_SYS clock source */
      MRCC->CLKCTL &= MRCC_CKSEL_Reset_Mask;
    }
    
    /* Clear CKOSCSEL bit ----------------------------------------------------*/
    /* Execute CKOSCSEL bit writing sequence */
    WriteCKOSCSELBit();

    /* Check if CKOSCSEL is set to 0 */
    if((MRCC->CLKCTL & MRCC_CKOSCSEL_Set_Mask) != RESET)
    {
      return ERROR;
    }
  }  
 
  /* Select CK_OSC as CK_SYS clock source */
  MRCC->CLKCTL |= MRCC_CKSEL_Set_Mask;

  if((MRCC->CLKCTL & MRCC_CKSEL_Set_Mask) != RESET)
  {
    if(PLL_State == MRCC_PLL_Disabled)
    {
      /* Disable PLL */
      MRCC->CLKCTL &= MRCC_PLLEN_Reset_Mask;
    }
    
    return SUCCESS;
  }
  else
  {
    return ERROR;
  }  
}

/*******************************************************************************
* Function Name  : SetCKSYS_OSC4MPLL
* Description    : Selects 4MHz main oscillator (OSC4M) followed by PLL as
*                  CK_SYS clock source.
* Input          : PLL_Mul: specifies the PLL factor.
* Output         : None
* Return         : An ErrorStatus enumuration value:
*                         - SUCCESS: Clock configuration succeeded
*                         - ERROR: Clock configuration failed
*******************************************************************************/
static ErrorStatus SetCKSYS_OSC4MPLL(u32 PLL_Mul)
{
  /* Check if 4MHz main oscillator clock is present */
  if(((MRCC->CLKCTL & MRCC_NCKDF_Set_Mask) == RESET) && 
     ((MRCC->CLKCTL & MRCC_OSC4MOFF_Set_Mask) == RESET)) 
  {    
    if(((MRCC->CLKCTL & MRCC_PLLEN_Set_Mask) != RESET) &&
       ((MRCC->CLKCTL & MRCC_MX_Set_Mask) == PLL_Mul))
    {
      /* Select CK_PLL1 as CK_SYS clock source */
      MRCC->CLKCTL &= MRCC_CKSEL_Reset_Mask;

      if((MRCC->CLKCTL & MRCC_CKSEL_Set_Mask) == RESET)
      {
        return SUCCESS;
      }
      else
      {
        return ERROR;
      }
    }
    else
    {
      /* If CK_RTC is selected as CK_OSC clock source */
      if((MRCC->CLKCTL & MRCC_CKOSCSEL_Set_Mask) != RESET)
      {
        if((MRCC->CLKCTL & MRCC_CKSEL_Set_Mask) != RESET)
        {
          /* Clear CKSEL bit */
          MRCC->CLKCTL &= MRCC_CKSEL_Reset_Mask;
        }

        /* Clear CKOSCSEL bit ------------------------------------------------*/
        /* Execute CKOSCSEL bit writing sequence */
        WriteCKOSCSELBit();
      
        /* Check if CKOSCSEL is set to 0 */
        if((MRCC->CLKCTL & MRCC_CKOSCSEL_Set_Mask) != RESET)
        {
          return ERROR;
        }
      }

      /* Select CK_OSC as CK_SYS clock source */
      MRCC->CLKCTL |= MRCC_CKSEL_Set_Mask;

      /* Disable PLL */
      MRCC->CLKCTL &= MRCC_PLLEN_Reset_Mask;

      /* Configure PLL factor */
      if(PLL_Mul == MRCC_PLL_Mul_16)
      {
        MRCC->CLKCTL &= MRCC_MX_Reset_Mask;
      }
      else if((PLL_Mul == MRCC_PLL_Mul_15) || (PLL_Mul == MRCC_PLL_Mul_14) ||
            (PLL_Mul == MRCC_PLL_Mul_12))
      {
        /* Clear MX[1:0] bits */
        MRCC->CLKCTL &= MRCC_MX_Reset_Mask;
        /* Set MX[1:0] bits according to PLL_Mul value */
        MRCC->CLKCTL |= PLL_Mul;
      }
       
      if(Main_Oscillator == 4000000)
      {/* 4 MHz external Quartz oscillator used as main oscillator */
        /* Disable Oscillator Divider by 2 */
        MRCC->CLKCTL &= MRCC_XTDIV2_Reset_Mask;
      }
      else if(Main_Oscillator == 8000000)
      {/* 8 MHz external Quartz oscillator used as main oscillator */
        /* Enable Oscillator Divider by 2 */
        MRCC->CLKCTL |= MRCC_XTDIV2_Set_Mask;
      }

      /* Enable PLL */
      MRCC->CLKCTL |= MRCC_PLLEN_Set_Mask;
   
      /* Wait until the PLL is locked */
      while((MRCC->CLKCTL & MRCC_LOCK_Mask) == RESET)
      {
        /* If OSC4M clock disapear or the PLL is disabled, exit */
        if(((MRCC->CLKCTL & MRCC_NCKDF_Set_Mask) != RESET) ||
           ((MRCC->CLKCTL & MRCC_PLLEN_Set_Mask) == RESET))       
        {
          return ERROR;
        }
      }

      /* Select CK_PLL1 as CK_SYS clock source */
      MRCC->CLKCTL &= MRCC_CKSEL_Reset_Mask;

      if((MRCC->CLKCTL & MRCC_CKSEL_Set_Mask) == RESET)
      {
        return SUCCESS;
      }
      else
      {
        return ERROR;
      }
    }
  }
  else 
  {
    /* OSC4M disabled or OSC4M clock is not present*/
    return ERROR;
  }
}

/*******************************************************************************
* Function Name  : SetCKSYS_RTC
* Description    : Selects RTC clock (CK_RTC) as CK_SYS clock source.
* Input          : PLL_State: specifies the PLL state.
* Output         : None
* Return         : An ErrorStatus enumuration value:
*                         - SUCCESS: Clock configuration succeeded
*                         - ERROR: Clock configuration failed
*******************************************************************************/
static ErrorStatus SetCKSYS_RTC(u32 PLL_State)
{
  /* Check if CK_RTC clock is enabled and ready to use */
  if(((MRCC->PWRCTRL & MRCC_CKRTCSEL_Set_Mask) != RESET)||
     ((MRCC->CLKCTL & MRCC_CKRTCOK_Mask) == RESET))
  {
/* Configure CK_RTC as Ck_SYS clock source -----------------------------------*/
    if((MRCC->CLKCTL & MRCC_CKOSCSEL_Set_Mask) == RESET)
    { 
      /* Select CK_PLL1 as CK_SYS clock source */
      MRCC->CLKCTL &= MRCC_CKSEL_Reset_Mask;
    
      /* Set CKOSCSEL bit ----------------------------------------------------*/
      /* Execute CKOSCSEL bit writing sequence */
      WriteCKOSCSELBit();
      
      /* Check if CKOSCSEL is set to 1 */
      if((MRCC->CLKCTL & MRCC_CKOSCSEL_Set_Mask) == RESET)
      {
         return ERROR;
      }
    }
    
    /* Select CK_OSC as CK_SYS clock source */
    MRCC->CLKCTL |= MRCC_CKSEL_Set_Mask;          
    
    if((MRCC->CLKCTL & MRCC_CKSEL_Set_Mask) != RESET)
    {
      if(PLL_State == MRCC_PLL_Disabled)
      {
        /* Disable PLL */
        MRCC->CLKCTL &= MRCC_PLLEN_Reset_Mask;
      }
    
      return SUCCESS;
    }
    else
    {
      return ERROR;
    }    
  }
  else
  {      
    /* CK_RTC disabled */
    return ERROR;
  }  
}

/*******************************************************************************
* Function Name  : WriteLPBit
* Description    : Executes the Low Power bit writing sequence.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
static void WriteLPBit(void)
{
  u32 Tmp = 0, Tmp1 = 0, Tmp2 = 0;

  /* Clear LP_DONE flag */
  MRCC->PWRCTRL &= MRCC_LPDONE_Reset_Mask;

  Tmp = MRCC->PWRCTRL;
  Tmp1 = Tmp | MRCC_LP_Set_Mask;
  Tmp2 = Tmp & MRCC_LP_Reset_Mask;

  /* Set LP bit */
  MRCC->PWRCTRL = Tmp1;

  /* Set LP bit */
  MRCC->PWRCTRL = Tmp1;

  /* Reset LP bit */
  MRCC->PWRCTRL = Tmp2;

  /* Set LP bit */
  MRCC->PWRCTRL = Tmp1;

  /* Read LP bit*/
  Tmp = MRCC->PWRCTRL;  
}

/*******************************************************************************
* Function Name  : WriteCKOSCSELBit
* Description    : Executes the CKOSCSEL bit writing sequence.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
static void WriteCKOSCSELBit(void)
{
  u32 Tmp = 0, Tmp1 = 0, Tmp2 = 0;

  Tmp = MRCC->CLKCTL;
  Tmp1 = Tmp | MRCC_CKOSCSEL_Set_Mask;
  Tmp2 = Tmp & MRCC_CKOSCSEL_Reset_Mask;

  /* Set CKOSCSEL bit */
  MRCC->CLKCTL = Tmp1;

  /* Set CKOSCSEL bit */
  MRCC->CLKCTL = Tmp1;

  /* Reset CKOSCSEL bit */
  MRCC->CLKCTL = Tmp2;

  /* Set CKOSCSEL bit */
  MRCC->CLKCTL = Tmp1;
  
  /* Read CKOSCSEL bit */
  Tmp = MRCC->CLKCTL;
}
/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
