/******************** (C) COPYRIGHT 2007 STMicroelectronics ********************
* File Name          : stm32f10x_tim1.c
* Author             : MCD Application Team
* Date First Issued  : 09/29/2006
* Description        : This file provides all the TIM1 software functions.
********************************************************************************
* History:
* 04/02/2007: V0.2
* mm/dd/yyyy: V0.1
* 09/29/2006: V0.01
********************************************************************************
* THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
* WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
* AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT,
* INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE
* CONTENT OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING
* INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/

/* Includes ------------------------------------------------------------------*/
#include "stm32f10x_tim1.h"
#include "stm32f10x_rcc.h"

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/

/* ------------ TIM1 registers bit address in the alias region ----------- */
#define TIM1_OFFSET    (TIM1_BASE - PERIPH_BASE)

/* --- TIM1 CR1 Register ---*/
/* Alias word address of CEN bit */
#define CR1_OFFSET        (TIM1_OFFSET + 0x00)
#define CEN_BitNumber     0x00
#define CR1_CEN_BB        (PERIPH_BB_BASE + (CR1_OFFSET * 32) + (CEN_BitNumber * 4))

/* Alias word address of UDIS bit */
#define UDIS_BitNumber    0x01
#define CR1_UDIS_BB       (PERIPH_BB_BASE + (CR1_OFFSET * 32) + (UDIS_BitNumber * 4))

/* Alias word address of URS bit */
#define URS_BitNumber     0x02
#define CR1_URS_BB        (PERIPH_BB_BASE + (CR1_OFFSET * 32) + (URS_BitNumber * 4))

/* Alias word address of OPM bit */
#define OPM_BitNumber     0x03
#define CR1_OPM_BB        (PERIPH_BB_BASE + (CR1_OFFSET * 32) + (OPM_BitNumber * 4))

/* Alias word address of ARPE bit */
#define ARPE_BitNumber    0x07
#define CR1_ARPE_BB       (PERIPH_BB_BASE + (CR1_OFFSET * 32) + (ARPE_BitNumber * 4))

/* --- TIM1 CR2 Register --- */
/* Alias word address of CCPC bit */
#define CR2_OFFSET        (TIM1_OFFSET + 0x04)
#define CCPC_BitNumber    0x00
#define CR2_CCPC_BB       (PERIPH_BB_BASE + (CR2_OFFSET * 32) + (CCPC_BitNumber * 4))

/* Alias word address of CCUS bit */
#define CCUS_BitNumber    0x02
#define CR2_CCUS_BB       (PERIPH_BB_BASE + (CR2_OFFSET * 32) + (CCUS_BitNumber * 4))

/* Alias word address of CCDS bit */
#define CCDS_BitNumber    0x03
#define CR2_CCDS_BB       (PERIPH_BB_BASE + (CR2_OFFSET * 32) + (CCDS_BitNumber * 4))

/* Alias word address of TI1S bit */
#define TI1S_BitNumber    0x07
#define CR2_TI1S_BB       (PERIPH_BB_BASE + (CR2_OFFSET * 32) + (TI1S_BitNumber * 4))

/* Alias word address of OIS1 bit */
#define OIS1_BitNumber    0x08
#define CR2_OIS1_BB       (PERIPH_BB_BASE + (CR2_OFFSET * 32) + (OIS1_BitNumber * 4))

/* Alias word address of OIS1N bit */
#define OIS1N_BitNumber   0x09
#define CR2_OIS1N_BB      (PERIPH_BB_BASE + (CR2_OFFSET * 32) + (OIS1N_BitNumber * 4))

/* Alias word address of OIS2 bit */
#define OIS2_BitNumber    0x0A
#define CR2_OIS2_BB      (PERIPH_BB_BASE + (CR2_OFFSET * 32) + (OIS2_BitNumber * 4))

/* Alias word address of OIS2N bit */
#define OIS2N_BitNumber   0x0B
#define CR2_OIS2N_BB      (PERIPH_BB_BASE + (CR2_OFFSET * 32) + (OIS2N_BitNumber * 4))

/* Alias word address of OIS3 bit */
#define OIS3_BitNumber    0x0C
#define CR2_OIS3_BB       (PERIPH_BB_BASE + (CR2_OFFSET * 32) + (OIS3_BitNumber * 4))

/* Alias word address of OIS3N bit */
#define OIS3N_BitNumber   0x0D
#define CR2_OIS3N_BB      (PERIPH_BB_BASE + (CR2_OFFSET * 32) + (OIS3N_BitNumber * 4))

/* Alias word address of OIS4 bit */
#define OIS4_BitNumber    0x0E
#define CR2_OIS4_BB       (PERIPH_BB_BASE + (CR2_OFFSET * 32) + (OIS4_BitNumber * 4))

/* --- TIM1 SMCR Register --- */
/* Alias word address of MSM bit */
#define SMCR_OFFSET       (TIM1_OFFSET + 0x08)
#define MSM_BitNumber     0x07
#define SMCR_MSM_BB       (PERIPH_BB_BASE + (SMCR_OFFSET * 32) + (MSM_BitNumber * 4))

/* Alias word address of ECE bit */
#define ECE_BitNumber     0x0E
#define SMCR_ECE_BB       (PERIPH_BB_BASE + (SMCR_OFFSET * 32) + (ECE_BitNumber * 4))

/* --- TIM1 EGR Register --- */
/* Alias word address of UG bit */
#define EGR_OFFSET        (TIM1_OFFSET + 0x14)
#define UG_BitNumber      0x00
#define EGR_UG_BB         (PERIPH_BB_BASE + (EGR_OFFSET * 32) + (UG_BitNumber * 4))

/* --- TIM1 CCER Register --- */
/* Alias word address of CC1E bit */
#define CCER_OFFSET       (TIM1_OFFSET + 0x20)
#define CC1E_BitNumber    0x00
#define CCER_CC1E_BB      (PERIPH_BB_BASE + (CCER_OFFSET * 32) + (CC1E_BitNumber * 4))

/* Alias word address of CC1P bit */
#define CC1P_BitNumber    0x01
#define CCER_CC1P_BB      (PERIPH_BB_BASE + (CCER_OFFSET * 32) + (CC1P_BitNumber * 4))

/* Alias word address of CC1NE bit */
#define CC1NE_BitNumber   0x02
#define CCER_CC1NE_BB     (PERIPH_BB_BASE + (CCER_OFFSET * 32) + (CC1NE_BitNumber * 4))

/* Alias word address of CC1NP bit */
#define CC1NP_BitNumber   0x03
#define CCER_CC1NP_BB     (PERIPH_BB_BASE + (CCER_OFFSET * 32) + (CC1NP_BitNumber * 4))

/* Alias word address of CC2E bit */
#define CC2E_BitNumber    0x04
#define CCER_CC2E_BB      (PERIPH_BB_BASE + (CCER_OFFSET * 32) + (CC2E_BitNumber * 4))

/* Alias word address of CC2P bit */
#define CC2P_BitNumber    0x05
#define CCER_CC2P_BB      (PERIPH_BB_BASE + (CCER_OFFSET * 32) + (CC2P_BitNumber * 4))

/* Alias word address of CC2NE bit */
#define CC2NE_BitNumber   0x06
#define CCER_CC2NE_BB     (PERIPH_BB_BASE + (CCER_OFFSET * 32) + (CC2NE_BitNumber * 4))

/* Alias word address of CC2NP bit */
#define CC2NP_BitNumber   0x07
#define CCER_CC2NP_BB     (PERIPH_BB_BASE + (CCER_OFFSET * 32) + (CC2NP_BitNumber * 4))

/* Alias word address of CC3E bit */
#define CC3E_BitNumber    0x08
#define CCER_CC3E_BB      (PERIPH_BB_BASE + (CCER_OFFSET * 32) + (CC3E_BitNumber * 4))

/* Alias word address of CC3P bit */
#define CC3P_BitNumber    0x09
#define CCER_CC3P_BB      (PERIPH_BB_BASE + (CCER_OFFSET * 32) + (CC3P_BitNumber * 4))

/* Alias word address of CC3NE bit */
#define CC3NE_BitNumber   0x0A
#define CCER_CC3NE_BB     (PERIPH_BB_BASE + (CCER_OFFSET * 32) + (CC3NE_BitNumber * 4))

/* Alias word address of CC3NP bit */
#define CC3NP_BitNumber   0x0B
#define CCER_CC3NP_BB     (PERIPH_BB_BASE + (CCER_OFFSET * 32) + (CC3NP_BitNumber * 4))

/* Alias word address of CC4E bit */
#define CC4E_BitNumber    0x0C
#define CCER_CC4E_BB      (PERIPH_BB_BASE + (CCER_OFFSET * 32) + (CC4E_BitNumber * 4))

/* Alias word address of CC4P bit */
#define CC4P_BitNumber    0x0D
#define CCER_CC4P_BB      (PERIPH_BB_BASE + (CCER_OFFSET * 32) + (CC4P_BitNumber * 4))

/* --- TIM1 BDTR Register --- */
/* Alias word address of MOE bit */
#define BDTR_OFFSET       (TIM1_OFFSET + 0x44)
#define MOE_BitNumber     0x0F
#define BDTR_MOE_BB       (PERIPH_BB_BASE + (BDTR_OFFSET * 32) + (MOE_BitNumber * 4))

/* --- TIM1 CCMR1 Register --- */
/* Alias word address of OC1FE bit */
#define CCMR1_OFFSET      (TIM1_OFFSET + 0x18)
#define OC1FE_BitNumber   0x02
#define CCMR1_OC1FE_BB    (PERIPH_BB_BASE + (CCMR1_OFFSET * 32) + (OC1FE_BitNumber * 4))

/* Alias word address of OC1PE bit */
#define OC1PE_BitNumber   0x03
#define CCMR1_OC1PE_BB    (PERIPH_BB_BASE + (CCMR1_OFFSET * 32) + (OC1PE_BitNumber * 4))

/* Alias word address of OC2FE bit */
#define OC2FE_BitNumber   0x0A
#define CCMR1_OC2FE_BB    (PERIPH_BB_BASE + (CCMR1_OFFSET * 32) + (OC2FE_BitNumber * 4))

/* Alias word address of OC2PE bit */
#define OC2PE_BitNumber   0x0B
#define CCMR1_OC2PE_BB    (PERIPH_BB_BASE + (CCMR1_OFFSET * 32) + (OC2PE_BitNumber * 4))

/* --- TIM1 CCMR2 Register ---- */
/* Alias word address of OC3FE bit */
#define CCMR2_OFFSET      (TIM1_OFFSET + 0x1C)
#define OC3FE_BitNumber   0x02
#define CCMR2_OC3FE_BB    (PERIPH_BB_BASE + (CCMR2_OFFSET * 32) + (OC3FE_BitNumber * 4))

/* Alias word address of OC3PE bit */
#define OC3PE_BitNumber   0x03
#define CCMR2_OC3PE_BB    (PERIPH_BB_BASE + (CCMR2_OFFSET * 32) + (OC3PE_BitNumber * 4))

/* Alias word address of OC4FE bit */
#define OC4FE_BitNumber   0x0A
#define CCMR2_OC4FE_BB    (PERIPH_BB_BASE + (CCMR2_OFFSET * 32) + (OC4FE_BitNumber * 4))

/* Alias word address of OC4PE bit */
#define OC4PE_BitNumber   0x0B
#define CCMR2_OC4PE_BB    (PERIPH_BB_BASE + (CCMR2_OFFSET * 32) + (OC4PE_BitNumber * 4))

/* --------------------- TIM1 registers bit mask ------------------------- */
/* TIM1 CR1 Mask */
#define CR1_CounterMode_Mask                ((u16)0x039F)
#define CR1_CKD_Mask                        ((u16)0x00FF)

/* TIM1 CR2 Mask */
#define CR2_MMS_Mask                        ((u16)0x0080)

/* TIM1 SMCR Mask */
#define SMCR_SMS_Mask                       ((u16)0xFFF0)
#define SMCR_ETR_Mask                       ((u16)0x40F7)
#define SMCR_TS_Mask                        ((u16)0xFF87)
#define SMCR_ECE_Set                        ((u16)0x0001)

/* TIM1 CCMRx Mask */
#define CCMR_CC13S_Mask                     ((u16)0xFFFC)
#define CCMR_CC24S_Mask                     ((u16)0xFCFF)
#define CCMR_TI13Direct_Set                 ((u16)0x0001)
#define CCMR_TI24Direct_Set                 ((u16)0x0100)
#define CCMR_OCM13_Mask                     ((u16)0x7F0F)
#define CCMR_OCM24_Mask                     ((u16)0x0F7F)
#define CCMR_IC13PSC_Mask                   ((u16)0xFFF3)
#define CCMR_IC24PSC_Mask                   ((u16)0xF3FF)
#define CCMR_IC13F_Mask                     ((u16)0xFF0F)
#define CCMR_IC24F_Mask                     ((u16)0x0FFF)
#define OC13Mode_Mask		                ((u16)0xFF00)
#define OC24Mode_Mask		                ((u16)0x00FF)

/* TIM1 CCER Set/Reset Bit */
#define CCER_CCE_Set                        ((u16)0x0001)
#define CCER_CCE_Reset                      ((u16)0x0000)

/* TIM1 DMA Mask */
#define DCR_DMA_Mask                        ((u16)0x0000)

/* TIM1 private Masks */
#define TIM1_Period_Reset_Mask               ((u16)0xFFFF)
#define TIM1_Prescaler_Reset_Mask            ((u16)0x0000)
#define TIM1_RepetitionCounter_Reset_Mask    ((u16)0x0000)
#define TIM1_Pulse_Reset_Mask                ((u16)0x0000)
#define TIM1_ICFilter_Mask                   ((u8)0x00)
#define TIM1_DeadTime_Reset_Mask             ((u16)0x0000)

/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
static void ETR_Config(u16 TIM1_ExtTRGPrescaler, u16 TIM1_ExtTRGPolarity,
                       u16 ExtTRGFilter);
static void TI1_Config(u16 TIM1_ICPolarity, u16 TIM1_ICSelection,
                       u8 TIM1_ICFilter);
static void TI2_Config(u16 TIM1_ICPolarity, u16 TIM1_ICSelection,
                       u8 TIM1_ICFilter);
static void TI3_Config(u16 TIM1_ICPolarity, u16 TIM1_ICSelection,
                       u8 TIM1_ICFilter);
static void TI4_Config(u16 TIM1_ICPolarity, u16 TIM1_ICSelection,
                       u8 TIM1_ICFilter);

/*******************************************************************************
* Function Name  : TIM1_DeInit
* Description    : Deinitializes the TIM1 peripheral registers to their default
*                  reset values.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_DeInit(void)
{
  RCC_APB2PeriphResetCmd(RCC_APB2Periph_TIM1, ENABLE);
  RCC_APB2PeriphResetCmd(RCC_APB2Periph_TIM1, DISABLE);
}

/*******************************************************************************
* Function Name  : TIM1_TimeBaseInit
* Description    : Initializes the TIM1 Time Base Unit according to the specified
*                  parameters in the TIM1_TimeBaseInitStruct.
* Input          : - TIM1_TimeBaseInitStruct: pointer to a TIM1_TimeBaseInitTypeDef
*                    structure that contains the configuration information for
*                    the specified TIM1 peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_TimeBaseInit(TIM1_TimeBaseInitTypeDef* TIM1_TimeBaseInitStruct)
{
 /* Check the parameters */
  assert(IS_TIM1_COUNTER_MODE(TIM1_TimeBaseInitStruct->TIM1_CounterMode));
  assert(IS_TIM1_CKD_DIV(TIM1_TimeBaseInitStruct->TIM1_ClockDivision));

  /* Set the Autoreload value */
  TIM1->ARR = TIM1_TimeBaseInitStruct->TIM1_Period ;

  /* Set the Prescaler value */
  TIM1->PSC = TIM1_TimeBaseInitStruct->TIM1_Prescaler;

  /* Select the Counter Mode and set the clock division */
  TIM1->CR1 &= CR1_CKD_Mask & CR1_CounterMode_Mask;
  TIM1->CR1 |= (u32)TIM1_TimeBaseInitStruct->TIM1_ClockDivision |
               TIM1_TimeBaseInitStruct->TIM1_CounterMode;

  /* Set the Repetition Counter value */
  TIM1->RCR = TIM1_TimeBaseInitStruct->TIM1_RepetitionCounter;
}

/*******************************************************************************
* Function Name  : TIM1_OC1Init
* Description    : Initializes the TIM1 Channel1 according to the specified
*                  parameters in the TIM1_OCInitStruct.
* Input          : - TIM1_OCInitStruct: pointer to a TIM1_OCInitTypeDef structure that
*                    contains the configuration information for the TIM1 peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_OC1Init(TIM1_OCInitTypeDef* TIM1_OCInitStruct)
{
  u16 tmpccmr = 0;

  /* Check the parameters */
  assert(IS_TIM1_OC_MODE(TIM1_OCInitStruct->TIM1_OCMode));
  assert(IS_TIM1_OUTPUT_STATE(TIM1_OCInitStruct->TIM1_OutputState));
  assert(IS_TIM1_OUTPUTN_STATE(TIM1_OCInitStruct->TIM1_OutputNState));
  assert(IS_TIM1_OC_POLARITY(TIM1_OCInitStruct->TIM1_OCPolarity));
  assert(IS_TIM1_OCN_POLARITY(TIM1_OCInitStruct->TIM1_OCNPolarity));
  assert(IS_TIM1_OCIDLE_STATE(TIM1_OCInitStruct->TIM1_OCIdleState));
  assert(IS_TIM1_OCNIDLE_STATE(TIM1_OCInitStruct->TIM1_OCNIdleState)); 

  tmpccmr = TIM1->CCMR1;

  /* Disable the Channel 1: Reset the CCE Bit */
  *(vu32 *) CCER_CC1E_BB = CCER_CCE_Reset;

  /* Reset the Output Compare Bits */
   tmpccmr &= OC13Mode_Mask;

  /* Set the Ouput Compare Mode */
  tmpccmr |= TIM1_OCInitStruct->TIM1_OCMode;

  TIM1->CCMR1 = tmpccmr;

  /* Set the Output State */
  *(vu32 *) CCER_CC1E_BB = TIM1_OCInitStruct->TIM1_OutputState;

  /* Set the Output N State */
  *(vu32 *) CCER_CC1NE_BB = TIM1_OCInitStruct->TIM1_OutputNState;

  /* Set the Output Polarity */
  *(vu32 *) CCER_CC1P_BB = TIM1_OCInitStruct->TIM1_OCPolarity;

  /* Set the Output N Polarity */
  *(vu32 *) CCER_CC1NP_BB = TIM1_OCInitStruct->TIM1_OCNPolarity;

  /* Set the Output Idle state */
  *(vu32 *) CR2_OIS1_BB = TIM1_OCInitStruct->TIM1_OCIdleState;

  /* Set the Output N Idle state */
  *(vu32 *) CR2_OIS1N_BB = TIM1_OCInitStruct->TIM1_OCNIdleState;

  /* Set the Pulse value */
  TIM1->CCR1 = TIM1_OCInitStruct->TIM1_Pulse;
}

/*******************************************************************************
* Function Name  : TIM1_OC2Init
* Description    : Initializes the TIM1 Channel2 according to the specified
*                  parameters in the TIM1_OCInitStruct.
* Input          : - TIM1_OCInitStruct: pointer to a TIM1_OCInitTypeDef structure that
*                    contains the configuration information for the TIM1 peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_OC2Init(TIM1_OCInitTypeDef* TIM1_OCInitStruct)
{
  u32 tmpccmr = 0;

  /* Check the parameters */
  assert(IS_TIM1_OC_MODE(TIM1_OCInitStruct->TIM1_OCMode));
  assert(IS_TIM1_OUTPUT_STATE(TIM1_OCInitStruct->TIM1_OutputState));
  assert(IS_TIM1_OUTPUTN_STATE(TIM1_OCInitStruct->TIM1_OutputNState));
  assert(IS_TIM1_OC_POLARITY(TIM1_OCInitStruct->TIM1_OCPolarity));
  assert(IS_TIM1_OCN_POLARITY(TIM1_OCInitStruct->TIM1_OCNPolarity));
  assert(IS_TIM1_OCIDLE_STATE(TIM1_OCInitStruct->TIM1_OCIdleState));
  assert(IS_TIM1_OCNIDLE_STATE(TIM1_OCInitStruct->TIM1_OCNIdleState));

  tmpccmr = TIM1->CCMR1;

  /* Disable the Channel 2: Reset the CCE Bit */
  *(vu32 *) CCER_CC2E_BB = CCER_CCE_Reset;

  /* Reset the Output Compare Bits */
   tmpccmr &= OC24Mode_Mask;

  /* Set the Ouput Compare Mode */
  tmpccmr |= (u32)TIM1_OCInitStruct->TIM1_OCMode << 8;

  TIM1->CCMR1 = (u16)tmpccmr;

  /* Set the Output State */
  *(vu32 *) CCER_CC2E_BB = TIM1_OCInitStruct->TIM1_OutputState;

  /* Set the Output N State */
  *(vu32 *) CCER_CC2NE_BB = TIM1_OCInitStruct->TIM1_OutputNState;

  /* Set the Output Polarity */
  *(vu32 *) CCER_CC2P_BB = TIM1_OCInitStruct->TIM1_OCPolarity;

  /* Set the Output N Polarity */
  *(vu32 *) CCER_CC2NP_BB = TIM1_OCInitStruct->TIM1_OCNPolarity;

  /* Set the Output Idle state */
  *(vu32 *) CR2_OIS2_BB = TIM1_OCInitStruct->TIM1_OCIdleState;

  /* Set the Output N Idle state */
  *(vu32 *) CR2_OIS2N_BB = TIM1_OCInitStruct->TIM1_OCNIdleState;

  /* Set the Pulse value */
  TIM1->CCR2 = TIM1_OCInitStruct->TIM1_Pulse;
}

/*******************************************************************************
* Function Name  : TIM1_OC3Init
* Description    : Initializes the TIM1 Channel3 according to the specified
*                  parameters in the TIM1_OCInitStruct.
* Input          : - TIM1_OCInitStruct: pointer to a TIM1_OCInitTypeDef structure that
*                    contains the configuration information for the TIM1 peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_OC3Init(TIM1_OCInitTypeDef* TIM1_OCInitStruct)
{
  u16 tmpccmr = 0;

  /* Check the parameters */
  assert(IS_TIM1_OC_MODE(TIM1_OCInitStruct->TIM1_OCMode));
  assert(IS_TIM1_OUTPUT_STATE(TIM1_OCInitStruct->TIM1_OutputState));
  assert(IS_TIM1_OUTPUTN_STATE(TIM1_OCInitStruct->TIM1_OutputNState));
  assert(IS_TIM1_OC_POLARITY(TIM1_OCInitStruct->TIM1_OCPolarity));
  assert(IS_TIM1_OCN_POLARITY(TIM1_OCInitStruct->TIM1_OCNPolarity));
  assert(IS_TIM1_OCIDLE_STATE(TIM1_OCInitStruct->TIM1_OCIdleState));
  assert(IS_TIM1_OCNIDLE_STATE(TIM1_OCInitStruct->TIM1_OCNIdleState));

  tmpccmr = TIM1->CCMR2;

  /* Disable the Channel 3: Reset the CCE Bit */
  *(vu32 *) CCER_CC3E_BB = CCER_CCE_Reset;

  /* Reset the Output Compare Bits */
   tmpccmr &= OC13Mode_Mask;

  /* Set the Ouput Compare Mode */
  tmpccmr |= TIM1_OCInitStruct->TIM1_OCMode;

  TIM1->CCMR2 = tmpccmr;

  /* Set the Output State */
  *(vu32 *) CCER_CC3E_BB = TIM1_OCInitStruct->TIM1_OutputState;

  /* Set the Output N State */
  *(vu32 *) CCER_CC3NE_BB = TIM1_OCInitStruct->TIM1_OutputNState;

  /* Set the Output Polarity */
  *(vu32 *) CCER_CC3P_BB = TIM1_OCInitStruct->TIM1_OCPolarity;

  /* Set the Output N Polarity */
  *(vu32 *) CCER_CC3NP_BB = TIM1_OCInitStruct->TIM1_OCNPolarity;

  /* Set the Output Idle state */
  *(vu32 *) CR2_OIS3_BB = TIM1_OCInitStruct->TIM1_OCIdleState;

  /* Set the Output N Idle state */
  *(vu32 *) CR2_OIS3N_BB = TIM1_OCInitStruct->TIM1_OCNIdleState;

  /* Set the Pulse value */
  TIM1->CCR3 = TIM1_OCInitStruct->TIM1_Pulse;
}

/*******************************************************************************
* Function Name  : TIM1_OC4Init
* Description    : Initializes the TIM1 Channel4 according to the specified
*                  parameters in the TIM1_OCInitStruct.
* Input          : - TIM1_OCInitStruct: pointer to a TIM1_OCInitTypeDef structure that
*                    contains the configuration information for the TIM1 peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_OC4Init(TIM1_OCInitTypeDef* TIM1_OCInitStruct)
{
  u32 tmpccmr = 0;

  /* Check the parameters */
  assert(IS_TIM1_OC_MODE(TIM1_OCInitStruct->TIM1_OCMode));
  assert(IS_TIM1_OUTPUT_STATE(TIM1_OCInitStruct->TIM1_OutputState));
  assert(IS_TIM1_OC_POLARITY(TIM1_OCInitStruct->TIM1_OCPolarity));
  assert(IS_TIM1_OCIDLE_STATE(TIM1_OCInitStruct->TIM1_OCIdleState));

  tmpccmr = TIM1->CCMR2;

  /* Disable the Channel 4: Reset the CCE Bit */
  *(vu32 *) CCER_CC4E_BB = CCER_CCE_Reset;

  /* Reset the Output Compare Bits */
   tmpccmr &= OC24Mode_Mask;

  /* Set the Ouput Compare Mode */
  tmpccmr |= (u32)TIM1_OCInitStruct->TIM1_OCMode << 8;

  TIM1->CCMR2 = (u16)tmpccmr;

  /* Set the Output State */
  *(vu32 *) CCER_CC4E_BB = TIM1_OCInitStruct->TIM1_OutputState;

  /* Set the Output Polarity */
  *(vu32 *) CCER_CC4P_BB = TIM1_OCInitStruct->TIM1_OCPolarity;

  /* Set the Output Idle state */
  *(vu32 *) CR2_OIS4_BB = TIM1_OCInitStruct->TIM1_OCIdleState;

  /* Set the Pulse value */
  TIM1->CCR4 = TIM1_OCInitStruct->TIM1_Pulse;
}

/*******************************************************************************
* Function Name  : TIM1_BDTRConfig
* Description    : Configures the: Break feature, dead time, Lock level, the OSSI,
*                  the OSSR State and the AOE(automatic output enable).
* Input          : - TIM1_BDTRInitStruct: pointer to a TIM1_BDTRInitTypeDef
*                    structure that contains the BDTR Register configuration
*                    information for the TIM1 peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_BDTRConfig(TIM1_BDTRInitTypeDef *TIM1_BDTRInitStruct)
{
  u16 tmpbdtr = 0;

  /* Check the parameters */
  assert(IS_TIM1_OSSR_STATE(TIM1_BDTRInitStruct->TIM1_OSSRState));
  assert(IS_TIM1_OSSI_STATE(TIM1_BDTRInitStruct->TIM1_OSSIState));
  assert(IS_TIM1_LOCK_LEVEL(TIM1_BDTRInitStruct->TIM1_LOCKLevel));
  assert(IS_TIM1_BREAK_STATE(TIM1_BDTRInitStruct->TIM1_Break));
  assert(IS_TIM1_BREAK_POLARITY(TIM1_BDTRInitStruct->TIM1_BreakPolarity));
  assert(IS_TIM1_AUTOMATIC_OUTPUT_STATE(TIM1_BDTRInitStruct->TIM1_AutomaticOutput));

  tmpbdtr = TIM1->BDTR;

  /* Set the Lock level, the Break enable Bit and the Ploarity, the OSSR State,
     the OSSI State, the dead time value and the Automatic Output Enable Bit */

  tmpbdtr = (u32)TIM1_BDTRInitStruct->TIM1_OSSRState | TIM1_BDTRInitStruct->TIM1_OSSIState |
             TIM1_BDTRInitStruct->TIM1_LOCKLevel | TIM1_BDTRInitStruct->TIM1_DeadTime |
			 TIM1_BDTRInitStruct->TIM1_Break | TIM1_BDTRInitStruct->TIM1_BreakPolarity |
             TIM1_BDTRInitStruct->TIM1_AutomaticOutput;

  TIM1->BDTR = tmpbdtr;
}

/*******************************************************************************
* Function Name  : TIM1_ICInit
* Description    : Initializes the TIM1 peripheral according to the specified
*                  parameters in the TIM1_ICInitStruct.
* Input          : - TIM1_ICInitStruct: pointer to a TIM1_ICInitTypeDef structure
*                    that contains the configuration information for the specified
*                    TIM1 peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_ICInit(TIM1_ICInitTypeDef* TIM1_ICInitStruct)
{
  /* Check the parameters */
  assert(IS_TIM1_CHANNEL(TIM1_ICInitStruct->TIM1_Channel));
  assert(IS_TIM1_IC_POLARITY(TIM1_ICInitStruct->TIM1_ICPolarity));
  assert(IS_TIM1_IC_SELECTION(TIM1_ICInitStruct->TIM1_ICSelection));
  assert(IS_TIM1_IC_PRESCALER(TIM1_ICInitStruct->TIM1_ICPrescaler));
  assert(IS_TIM1_IC_FILTER(TIM1_ICInitStruct->TIM1_ICFilter));

  if (TIM1_ICInitStruct->TIM1_Channel == TIM1_Channel_1)
  {
    /* TI1 Configuration */
    TI1_Config(TIM1_ICInitStruct->TIM1_ICPolarity,
               TIM1_ICInitStruct->TIM1_ICSelection,
               TIM1_ICInitStruct->TIM1_ICFilter);

    /* Set the Input Capture Prescaler value */
    TIM1_SetIC1Prescaler(TIM1_ICInitStruct->TIM1_ICPrescaler);
  }
  else if (TIM1_ICInitStruct->TIM1_Channel == TIM1_Channel_2)
  {
    /* TI2 Configuration */
    TI2_Config(TIM1_ICInitStruct->TIM1_ICPolarity,
               TIM1_ICInitStruct->TIM1_ICSelection,
               TIM1_ICInitStruct->TIM1_ICFilter);

    /* Set the Input Capture Prescaler value */
    TIM1_SetIC2Prescaler(TIM1_ICInitStruct->TIM1_ICPrescaler);
  }
  else if (TIM1_ICInitStruct->TIM1_Channel == TIM1_Channel_3)
  {
    /* TI3 Configuration */
    TI3_Config(TIM1_ICInitStruct->TIM1_ICPolarity,
               TIM1_ICInitStruct->TIM1_ICSelection,
               TIM1_ICInitStruct->TIM1_ICFilter);

    /* Set the Input Capture Prescaler value */
    TIM1_SetIC3Prescaler(TIM1_ICInitStruct->TIM1_ICPrescaler);
  }
  else
  {
    /* TI4 Configuration */
    TI4_Config(TIM1_ICInitStruct->TIM1_ICPolarity,
               TIM1_ICInitStruct->TIM1_ICSelection,
               TIM1_ICInitStruct->TIM1_ICFilter);

    /* Set the Input Capture Prescaler value */
    TIM1_SetIC4Prescaler(TIM1_ICInitStruct->TIM1_ICPrescaler);
  }
}

/*******************************************************************************
* Function Name  : TIM1_PWMIConfig
* Description    : Configures the TIM1 peripheral in PWM Input Mode according 
*                  to the specified parameters in the TIM1_ICInitStruct.
* Input          : - TIM1_ICInitStruct: pointer to a TIM1_ICInitTypeDef structure
*                    that contains the configuration information for the specified
*                    TIM1 peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_PWMIConfig(TIM1_ICInitTypeDef* TIM1_ICInitStruct)
{
  u8 ICPolarity = TIM1_ICPolarity_Rising;
  u8 ICSelection = TIM1_ICSelection_DirectTI;

  /* Check the parameters */
  assert(IS_TIM1_PWMI_CHANNEL(TIM1_ICInitStruct->TIM1_Channel));
  assert(IS_TIM1_IC_POLARITY(TIM1_ICInitStruct->TIM1_ICPolarity));
  assert(IS_TIM1_IC_SELECTION(TIM1_ICInitStruct->TIM1_ICSelection));
  assert(IS_TIM1_IC_PRESCALER(TIM1_ICInitStruct->TIM1_ICPrescaler));

  /* Select the Opposite Input Polarity */
  if (TIM1_ICInitStruct->TIM1_ICPolarity == TIM1_ICPolarity_Rising)
  {
    ICPolarity = TIM1_ICPolarity_Falling;
  }
  else
  {
    ICPolarity = TIM1_ICPolarity_Rising;
  }

  /* Select the Opposite Input */
  if (TIM1_ICInitStruct->TIM1_ICSelection == TIM1_ICSelection_DirectTI)
  {
    ICSelection = TIM1_ICSelection_IndirectTI;
  }
  else
  {
    ICSelection = TIM1_ICSelection_DirectTI;
  }

  if (TIM1_ICInitStruct->TIM1_Channel == TIM1_Channel_1)
  {
    /* TI1 Configuration */
    TI1_Config(TIM1_ICInitStruct->TIM1_ICPolarity, TIM1_ICInitStruct->TIM1_ICSelection,
               TIM1_ICInitStruct->TIM1_ICFilter);

    /* Set the Input Capture Prescaler value */
    TIM1_SetIC1Prescaler(TIM1_ICInitStruct->TIM1_ICPrescaler);

    /* TI2 Configuration */
    TI2_Config(ICPolarity, ICSelection, TIM1_ICInitStruct->TIM1_ICFilter);

    /* Set the Input Capture Prescaler value */
    TIM1_SetIC2Prescaler(TIM1_ICInitStruct->TIM1_ICPrescaler);
  }
  else
  {	 
    /* TI2 Configuration */
    TI2_Config(TIM1_ICInitStruct->TIM1_ICPolarity, TIM1_ICInitStruct->TIM1_ICSelection,
               TIM1_ICInitStruct->TIM1_ICFilter);

    /* Set the Input Capture Prescaler value */
    TIM1_SetIC2Prescaler(TIM1_ICInitStruct->TIM1_ICPrescaler);

    /* TI1 Configuration */
    TI1_Config(ICPolarity, ICSelection, TIM1_ICInitStruct->TIM1_ICFilter);

    /* Set the Input Capture Prescaler value */
    TIM1_SetIC1Prescaler(TIM1_ICInitStruct->TIM1_ICPrescaler);
  }
}
/*******************************************************************************
* Function Name  : TIM1_OCStructInit
* Description    : Fills each TIM1_OCInitStruct member with its default value.
* Input          : - TIM1_OCInitStruct : pointer to a TIM1_OCInitTypeDef structure
*                    which will be initialized.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_OCStructInit(TIM1_OCInitTypeDef* TIM1_OCInitStruct)
{
  /* Set the default configuration */
  TIM1_OCInitStruct->TIM1_OCMode = TIM1_OCMode_Timing;
  TIM1_OCInitStruct->TIM1_OutputState = TIM1_OutputState_Disable;
  TIM1_OCInitStruct->TIM1_OutputNState = TIM1_OutputNState_Disable;
  TIM1_OCInitStruct->TIM1_Pulse = TIM1_Pulse_Reset_Mask;
  TIM1_OCInitStruct->TIM1_OCPolarity = TIM1_OCPolarity_High;
  TIM1_OCInitStruct->TIM1_OCNPolarity = TIM1_OCPolarity_High;
  TIM1_OCInitStruct->TIM1_OCIdleState = TIM1_OCIdleState_Reset;
  TIM1_OCInitStruct->TIM1_OCNIdleState = TIM1_OCNIdleState_Reset;
}

/*******************************************************************************
* Function Name  : TIM1_ICStructInit
* Description    : Fills each TIM1_ICInitStruct member with its default value.
* Input          : - TIM1_ICInitStruct : pointer to a TIM1_ICInitTypeDef structure
*                    which will be initialized.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_ICStructInit(TIM1_ICInitTypeDef* TIM1_ICInitStruct)
{
  /* Set the default configuration */
  TIM1_ICInitStruct->TIM1_Channel = TIM1_Channel_1;
  TIM1_ICInitStruct->TIM1_ICSelection = TIM1_ICSelection_DirectTI;
  TIM1_ICInitStruct->TIM1_ICPolarity = TIM1_ICPolarity_Rising;
  TIM1_ICInitStruct->TIM1_ICPrescaler = TIM1_ICPSC_DIV1;
  TIM1_ICInitStruct->TIM1_ICFilter = TIM1_ICFilter_Mask;
}

/*******************************************************************************
* Function Name  : TIM1_TimeBaseStructInit
* Description    : Fills each TIM1_TimeBaseInitStruct member with its default value.
* Input          : - TIM1_TimeBaseInitStruct : pointer to a TIM1_TimeBaseInitTypeDef
*                    structure which will be initialized.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_TimeBaseStructInit(TIM1_TimeBaseInitTypeDef* TIM1_TimeBaseInitStruct)
{
  /* Set the default configuration */
  TIM1_TimeBaseInitStruct->TIM1_Period = TIM1_Period_Reset_Mask;
  TIM1_TimeBaseInitStruct->TIM1_Prescaler = TIM1_Prescaler_Reset_Mask;
  TIM1_TimeBaseInitStruct->TIM1_ClockDivision = TIM1_CKD_DIV1;
  TIM1_TimeBaseInitStruct->TIM1_CounterMode = TIM1_CounterMode_Up;
  TIM1_TimeBaseInitStruct->TIM1_RepetitionCounter = TIM1_RepetitionCounter_Reset_Mask;
}

/*******************************************************************************
* Function Name  : TIM1_BDTRStructInit
* Description    : Fills each TIM1_BDTRInitStruct member with its default value.
* Input          : - TIM1_BDTRInitStruct : pointer to a TIM1_BDTRInitTypeDef
*                    structure which will be initialized.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_BDTRStructInit(TIM1_BDTRInitTypeDef* TIM1_BDTRInitStruct)
{
  /* Set the default configuration */
  TIM1_BDTRInitStruct->TIM1_OSSRState = TIM1_OSSRState_Disable;
  TIM1_BDTRInitStruct->TIM1_OSSIState = TIM1_OSSIState_Disable;
  TIM1_BDTRInitStruct->TIM1_LOCKLevel = TIM1_LOCKLevel_OFF;
  TIM1_BDTRInitStruct->TIM1_DeadTime = TIM1_DeadTime_Reset_Mask;
  TIM1_BDTRInitStruct->TIM1_Break = TIM1_Break_Disable;
  TIM1_BDTRInitStruct->TIM1_BreakPolarity = TIM1_BreakPolarity_Low;
  TIM1_BDTRInitStruct->TIM1_AutomaticOutput = TIM1_AutomaticOutput_Disable;
}

/*******************************************************************************
* Function Name  : TIM1_Cmd
* Description    : Enables or disables the TIM1 peripheral.
* Input          : - Newstate: new state of the TIM1 peripheral.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_Cmd(FunctionalState NewState)
{
  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(NewState));

  /* set or Reset the CEN Bit */
  *(vu32 *) CR1_CEN_BB = (u16)NewState;
}

/*******************************************************************************
* Function Name  : TIM1_CtrlPWMOutputs
* Description    : Enables or disables the TIM1 peripheral Main Outputs.
* Input          : - Newstate: new state of the TIM1 peripheral Main Outputs.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_CtrlPWMOutputs(FunctionalState Newstate)
{
  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(Newstate));

  /* Set or Reset the MOE Bit */
  *(vu32 *) BDTR_MOE_BB = (u16)Newstate;
}

/*******************************************************************************
* Function Name  : TIM1_ITConfig
* Description    : Enables or disables the specified TIM1 interrupts.
* Input          : - TIM1_IT: specifies the TIM1 interrupts sources to be enabled
*                    or disabled.
*                    This parameter can be any combination of the following values:
*                       - TIM1_IT_Update: TIM1 update Interrupt source
*                       - TIM1_IT_CC1: TIM1 Capture Compare 1 Interrupt source
*                       - TIM1_IT_CC2: TIM1 Capture Compare 2 Interrupt source
*                       - TIM1_IT_CC3: TIM1 Capture Compare 3 Interrupt source
*                       - TIM1_IT_CC4: TIM1 Capture Compare 4 Interrupt source
*                       - TIM1_IT_CCUpdate: TIM1 Capture Compare Update Interrupt
*                         source
*                       - TIM1_IT_Trigger: TIM1 Trigger Interrupt source
*                       - TIM1_IT_Break: TIM1 Break Interrupt source
*                  - Newstate: new state of the TIM1 interrupts.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_ITConfig(u16 TIM1_IT, FunctionalState NewState)
{
  /* Check the parameters */
  assert(IS_TIM1_IT(TIM1_IT));
  assert(IS_FUNCTIONAL_STATE(NewState));

  if (NewState == ENABLE)
  {
    /* Enable the Interrupt sources */
    TIM1->DIER |= TIM1_IT;
  }
  else
  {
    /* Disable the Interrupt sources */
    TIM1->DIER &= (u16)~TIM1_IT;
  }
}

/*******************************************************************************
* Function Name  : TIM1_DMAConfig
* Description    : Configures the TIM1’s DMA interface.
* Input          : - TIM1_DMABase: DMA Base address.
*                    This parameter can be one of the following values:
*                       - TIM1_DMABase_CR1, TIM1_DMABase_CR2, TIM1_DMABase_SMCR,
*                         TIM1_DMABase_DIER, TIM1_DMABase_SR, TIM1_DMABase_EGR,
*                         TIM1_DMABase_CCMR1, TIM1_DMABase_CCMR2, TIM1_DMABase_CCER,
*                         TIM1_DMABase_CNT, TIM1_DMABase_PSC, TIM1_DMABase_ARR,
*                         TIM1_DMABase_RCR, TIM1_DMABase_CCR1, TIM1_DMABase_CCR2,
*                         TIM1_DMABase_CCR3, TIM1_DMABase_CCR4, TIM1_DMABase_BDTR,
*                         TIM1_DMABase_DCR.
*                   - TIM1_DMABurstLength: DMA Burst length.
*                     This parameter can be one value between:
*                     TIM1_DMABurstLength_1Byte and TIM1_DMABurstLength_18Bytes.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_DMAConfig(u16 TIM1_DMABase, u16 TIM1_DMABurstLength)
{
  u32 tmpdcr = 0;

  /* Check the parameters */
  assert(IS_TIM1_DMA_BASE(TIM1_DMABase));
  assert(IS_TIM1_DMA_LENGTH(TIM1_DMABurstLength));

  tmpdcr = TIM1->DCR;

  /* Reset the DBA and the DBL Bits */
  tmpdcr &= DCR_DMA_Mask;

  /* Set the DMA Base and the DMA Burst Length */
  tmpdcr |= TIM1_DMABase | TIM1_DMABurstLength;

  TIM1->DCR = (u16)tmpdcr;
}

/*******************************************************************************
* Function Name  : TIM1_DMACmd
* Description    : Enables or disables the TIM1’s DMA Requests.
* Input          : - TIM1_DMASources: specifies the DMA Request sources.
*                    This parameter can be any combination of the following values:
*                       - TIM1_DMA_Update: TIM1 update Interrupt source
*                       - TIM1_DMA_CC1: TIM1 Capture Compare 1 DMA source
*                       - TIM1_DMA_CC2: TIM1 Capture Compare 2 DMA source
*                       - TIM1_DMA_CC3: TIM1 Capture Compare 3 DMA source
*                       - TIM1_DMA_CC4: TIM1 Capture Compare 4 DMA source
*                       - TIM1_DMA_COM: TIM1 Capture Compare Update DMA
*                         source
*                       - TIM1_DMA_Trigger: TIM1 Trigger DMA source
*                  - Newstate: new state of the DMA Request sources.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_DMACmd(u16 TIM1_DMASource, FunctionalState Newstate)
{
  u32 tmpdier = 0;

  /* Check the parameters */
  assert(IS_TIM1_DMA_SOURCE(TIM1_DMASource));
  assert(IS_FUNCTIONAL_STATE(Newstate));

  tmpdier = TIM1->DIER;

  if (Newstate == ENABLE)
  {
    /* Enable the DMA sources */
    tmpdier |= TIM1_DMASource;
  }
  else
  {
    /* Disable the DMA sources */
    tmpdier &= (u16)~TIM1_DMASource;
  }
  TIM1->DIER = (u16)tmpdier;
}

/*******************************************************************************
* Function Name  : TIM1_InternalClockConfig
* Description    : Configures the TIM1 interrnal Clock
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_InternalClockConfig(void)
{
  /* Disable slave mode to clock the prescaler directly with the internal clock */
  TIM1->SMCR &=  SMCR_SMS_Mask;
}
/*******************************************************************************
* Function Name  : TIM1_ETRClockMode1Config
* Description    : Configures the TIM1 External clock Mode1
* Input          : - TIM1_ExtTRGPrescaler: The external Trigger Prescaler.
*                    It can be one of the following values:
*                       - TIM1_ExtTRGPSC_OFF
*                       - TIM1_ExtTRGPSC_DIV2
*                       - TIM1_ExtTRGPSC_DIV4
*                       - TIM1_ExtTRGPSC_DIV8.
*                  - TIM1_ExtTRGPolarity: The external Trigger Polarity.
*                    It can be one of the following values:
*                       - TIM1_ExtTRGPolarity_Inverted
*                       - TIM1_ExtTRGPolarity_NonInverted
*                  - ExtTRGFilter: External Trigger Filter.
*                    This parameter must be a value between 0x00 and 0x0F
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_ETRClockMode1Config(u16 TIM1_ExtTRGPrescaler, u16 TIM1_ExtTRGPolarity,
                             u16 ExtTRGFilter)
{
  /* Check the parameters */
  assert(IS_TIM1_EXT_PRESCALER(TIM1_ExtTRGPrescaler));
  assert(IS_TIM1_EXT_POLARITY(TIM1_ExtTRGPolarity));

  /* Configure the ETR Clock source */
  ETR_Config(TIM1_ExtTRGPrescaler, TIM1_ExtTRGPolarity, ExtTRGFilter);

  /* Select the External clock mode1 */
  TIM1->SMCR &= SMCR_SMS_Mask;
  TIM1->SMCR |= TIM1_SlaveMode_External1;
  
  /* Select the Trigger selection : ETRF */
  TIM1->SMCR &= SMCR_TS_Mask;
  TIM1->SMCR |= TIM1_TS_ETRF;
}

/*******************************************************************************
* Function Name  : TIM1_ETRClockMode2Config
* Description    : Configures the TIM1 External clock Mode2
* Input          : - TIM1_ExtTRGPrescaler: The external Trigger Prescaler.
*                    It can be one of the following values:
*                       - TIM1_ExtTRGPSC_OFF
*                       - TIM1_ExtTRGPSC_DIV2
*                       - TIM1_ExtTRGPSC_DIV4
*                       - TIM1_ExtTRGPSC_DIV8
*                  - TIM1_ExtTRGPolarity: The external Trigger Polarity.
*                    It can be one of the following values:
*                       - TIM1_ExtTRGPolarity_Inverted
*                       - TIM1_ExtTRGPolarity_NonInverted
*                  - ExtTRGFilter: External Trigger Filter.
*                    This parameter must be a value between 0x00 and 0x0F
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_ETRClockMode2Config(u16 TIM1_ExtTRGPrescaler, u16 TIM1_ExtTRGPolarity,
                             u16 ExtTRGFilter)
{
  /* Check the parameters */
  assert(IS_TIM1_EXT_PRESCALER(TIM1_ExtTRGPrescaler));
  assert(IS_TIM1_EXT_POLARITY(TIM1_ExtTRGPolarity));

  /* Configure the ETR Clock source */
  ETR_Config(TIM1_ExtTRGPrescaler, TIM1_ExtTRGPolarity, ExtTRGFilter);

  /* Enable the External clock mode2 */
  *(vu32 *) SMCR_ECE_BB = SMCR_ECE_Set;
}

/*******************************************************************************
* Function Name  : TIM1_ITRxExternalClockConfig
* Description    : Configures the TIM1 Internal Trigger as External Clock
* Input          : - TIM1_ITRSource: Internal Trigger source.
*                    This parameter can be one of the following values:
*                       - TIM1_TS_ITR0: Internal Trigger 0
*                       - TIM1_TS_ITR1: Internal Trigger 1
*                       - TIM1_TS_ITR2: Internal Trigger 2
*                       - TIM1_TS_ITR3: Internal Trigger 3
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_ITRxExternalClockConfig(u16 TIM1_InputTriggerSource)
{
  /* Check the parameters */
  assert(IS_TIM1_INTERNAL_TRIGGER_SELECTION(TIM1_InputTriggerSource));
  
  /* Select the Internal Trigger */
  TIM1_SelectInputTrigger(TIM1_InputTriggerSource);

  /* Select the External clock mode1 */
  TIM1->SMCR |= TIM1_SlaveMode_External1;
}

/*******************************************************************************
* Function Name  : TIM1_TIxExternalClockConfig
* Description    : Configures the TIM1 Trigger as External Clock
* Input          : - TIM1_TIxExternalCLKSource: Trigger source.
*                    This parameter can be one of the following values:
*                       - TIM1_TS_TI1F_ED: TI1 Edge Detector
*                       - TIM1_TS_TI1FP1: Filtered TIM1 Input 1
*                       - TIM1_TS_TI2FP2: Filtered TIM1 Input 2
*                  - TIM1_ICPolarity: specifies the TIx Polarity.
*                    This parameter can be:
*                       - TIM1_ICPolarity_Rising
*                       - TIM1_ICPolarity_Falling
*                   - ICFilter : specifies the filter value.
*                     This parameter must be a value between 0x0 and 0xF.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_TIxExternalClockConfig(u16 TIM1_TIxExternalCLKSource,
                                u16 TIM1_ICPolarity, u8 ICFilter)
{
  /* Check the parameters */
  assert(IS_TIM1_TIX_TRIGGER_SELECTION(TIM1_TIxExternalCLKSource));
  assert(IS_TIM1_IC_POLARITY(TIM1_ICPolarity));
  assert(IS_TIM1_IC_FILTER(ICFilter));

  /* Configure the TIM1 Input Clock Source */
  if (TIM1_TIxExternalCLKSource == TIM1_TIxExternalCLK1Source_TI2)
  {
    TI2_Config(TIM1_ICPolarity, TIM1_ICSelection_DirectTI, ICFilter);
  }
  else
  {
    TI1_Config(TIM1_ICPolarity, TIM1_ICSelection_DirectTI, ICFilter);
  }

  /* Select the Trigger source */
  TIM1_SelectInputTrigger(TIM1_TIxExternalCLKSource);

  /* Select the External clock mode1 */
  TIM1->SMCR |= TIM1_SlaveMode_External1;
}
/*******************************************************************************
* Function Name  : TIM1_SelectInputTrigger
* Description    : Selects the TIM1 Input Trigger source
* Input          : - TIM1_InputTriggerSource: The Trigger source.
*                    This parameter can be one of the following values:
*                       - TIM1_TS_ITR0: Internal Trigger 0
*                       - TIM1_TS_ITR1: Internal Trigger 1
*                       - TIM1_TS_ITR2: Internal Trigger 2
*                       - TIM1_TS_ITR3: Internal Trigger 3
*                       - TIM1_TS_TI1F_ED: TI1 Edge Detector
*                       - TIM1_TS_TI1FP1: Filtered Timer Input 1
*                       - TIM1_TS_TI2FP2: Filtered Timer Input 2
*                       - TIM1_TS_ETRF: External Trigger input
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_SelectInputTrigger(u16 TIM1_InputTriggerSource)
{
  u32 tmpsmcr = 0;

  /* Check the parameters */
  assert(IS_TIM1_TRIGGER_SELECTION(TIM1_InputTriggerSource));

  tmpsmcr = TIM1->SMCR;

  /* Select the Tgigger Source */
  tmpsmcr &= SMCR_TS_Mask;
  tmpsmcr |= TIM1_InputTriggerSource;

  TIM1->SMCR = (u16)tmpsmcr;
}

/*******************************************************************************
* Function Name  : TIM1_UpdateDisableConfig
* Description    : Enables or Disables the TIM1 Update event.
* Input          : - Newstate: new state of the TIM1 peripheral Preload register
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_UpdateDisableConfig(FunctionalState Newstate)
{
  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(Newstate));

  /* Set or Reset the UDIS Bit */
  *(vu32 *) CR1_UDIS_BB = (u16)Newstate;
}

/*******************************************************************************
* Function Name  : TIM1_UpdateRequestConfig
* Description    : Selects the TIM1 Update Request Interrupt source.
* Input          : - TIM1_UpdateSource: specifies the Update source.
*                    This parameter can be one of the following values:
*                       - TIM1_UpdateSource_Regular
*                       - TIM1_UpdateSource_Global
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_UpdateRequestConfig(u8 TIM1_UpdateSource)
{
  /* Check the parameters */
  assert(IS_TIM1_UPDATE_SOURCE(TIM1_UpdateSource));

  /* Set or Reset the URS Bit */
  *(vu32 *) CR1_URS_BB = TIM1_UpdateSource;
}

/*******************************************************************************
* Function Name  : TIM1_SelectHallSensor
* Description    : Enables or disables the TIM1’s Hall sensor interface.
* Input          : - Newstate: new state of the TIM1 Hall sensor interface
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_SelectHallSensor(FunctionalState Newstate)
{
  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(Newstate));

  /* Set or Reset the TI1S Bit */
  *(vu32 *) CR2_TI1S_BB = (u16)Newstate;
}

/*******************************************************************************
* Function Name  : TIM1_SelectOPM
* Description    : Enables or disables the TIM1’s One Pulse Mode.
* Input          : - TIM1_OPMode: specifies the OPM Mode to be used.
*                    This parameter can be one of the following values:
*                    - TIM1_OPMode_Single
*                    - TIM1_OPMode_Repetitive
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_SelectOnePulseMode(u16 TIM1_OPMode)
{
  /* Check the parameters */
  assert(IS_TIM1_OPM_MODE(TIM1_OPMode));

  /* Set or Reset the OPM Bit */
  *(vu32 *) CR1_OPM_BB = TIM1_OPMode;
}

/*******************************************************************************
* Function Name  : TIM1_SelectOutputTrigger
* Description    : Selects the TIM1 Trigger Output Mode.
* Input          : - TIM1_TRGOSource: specifies the Trigger Output source.
*                    This paramter can be one of the following values:
*                       - TIM1_TRGOSource_Reset
*                       - TIM1_TRGOSource_Enable
*                       - TIM1_TRGOSource_Update
*                       - TIM1_TRGOSource_OC1
*                       - TIM1_TRGOSource_OC1Ref
*                       - TIM1_TRGOSource_OC2Ref
*                       - TIM1_TRGOSource_OC3Ref
*                       - TIM1_TRGOSource_OC4Ref
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_SelectOutputTrigger(u16 TIM1_TRGOSource)
{
  u32 tmpcr2 = 0;

  /* Check the parameters */
  assert(IS_TIM1_TRGO_SOURCE(TIM1_TRGOSource));

  tmpcr2 = TIM1->CR2;

  /* Reset the MMS Bits */
  tmpcr2 &= CR2_MMS_Mask;

  /* Select the TRGO source */
  tmpcr2 |=  TIM1_TRGOSource;

  TIM1->CR2 = (u16)tmpcr2;
}

/*******************************************************************************
* Function Name  : TIM1_SelectSlaveMode
* Description    : Selects the TIM1 Slave Mode.
* Input          : - TIM1_SlaveMode: specifies the TIM1 Slave Mode.
*                    This paramter can be one of the following values:
*                       - TIM1_SlaveMode_Reset
*                       - TIM1_SlaveMode_Gated
*                       - TIM1_SlaveMode_Trigger
*                       - TIM1_SlaveMode_External1
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_SelectSlaveMode(u16 TIM1_SlaveMode)
{
  u32 tmpsmcr = 0;

  /* Check the parameters */
  assert(IS_TIM1_SLAVE_MODE(TIM1_SlaveMode));

  tmpsmcr = TIM1->SMCR;

  /* Reset the SMS Bits */
  tmpsmcr &= SMCR_SMS_Mask;

  /* Select the Slave Mode */
  tmpsmcr |= TIM1_SlaveMode;

  TIM1->SMCR = (u16)tmpsmcr;
}

/*******************************************************************************
* Function Name  : TIM1_SelectMasterSlaveMode
* Description    : Sets or Resets the TIM1 Master/Slave Mode.
* Input          : - TIM1_MasterSlaveMode: specifies the TIM1 Master Slave Mode.
*                    This paramter can be one of the following values:
*                       - TIM1_MasterSlaveMode_Enable: synchronization between
*                         the current timer and its slaves (through TRGO).
*                       - TIM1_MasterSlaveMode_Disable: No action
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_SelectMasterSlaveMode(u16 TIM1_MasterSlaveMode)
{
  /* Check the parameters */
  assert(IS_TIM1_MSM_STATE(TIM1_MasterSlaveMode));

  /* Set or Reset the MSM Bit */
  *(vu32 *) SMCR_MSM_BB = TIM1_MasterSlaveMode;
}

/*******************************************************************************
* Function Name  : TIM1_EncoderInterfaceConfig
* Description    : Configures the TIM1 Encoder Interface.
* Input          : - TIM1_EncoderMode: specifies the TIM1 Encoder Mode.
*                    This parameter can be one of the following values:
*                       - TIM1_EncoderMode_TI1: Counter counts on TI1FP1 edge
*                         depending on TI2FP2 level.
*                       - TIM1_EncoderMode_TI2: Counter counts on TI2FP2 edge
*                         depending on TI1FP1 level.
*                       - TIM1_EncoderMode_TI12: Counter counts on both TI1FP1 and
*                         TI2FP2 edges depending on the level of the other input.
*                  - TIM1_IC1Polarity: specifies the IC1 Polarity
*                    This parmeter can be one of the following values:
*                       - TIM1_ICPolarity_Falling
*                       - TIM1_ICPolarity_Rising
*                  - TIM1_IC2Polarity: specifies the IC2 Polarity
*                    This parmeter can be one of the following values:
*                       - TIM1_ICPolarity_Falling
*                       - TIM1_ICPolarity_Rising
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_EncoderInterfaceConfig(u16 TIM1_EncoderMode, u16 TIM1_IC1Polarity,
                                u16 TIM1_IC2Polarity)
{
  u32 tmpsmcr = 0;
  u32 tmpccmr1 = 0;

  /* Check the parameters */
  assert(IS_TIM1_ENCODER_MODE(TIM1_EncoderMode));
  assert(IS_TIM1_IC_POLARITY(TIM1_IC1Polarity));
  assert(IS_TIM1_IC_POLARITY(TIM1_IC2Polarity));

  tmpsmcr = TIM1->SMCR;
  tmpccmr1 = TIM1->CCMR1;

  /* Set the encoder Mode */
  tmpsmcr &= SMCR_SMS_Mask;
  tmpsmcr |= TIM1_EncoderMode;

  /* Select the Capture Compare 1 and the Capture Compare 2 as input */
  tmpccmr1 &= CCMR_CC13S_Mask & CCMR_CC24S_Mask;
  tmpccmr1 |= CCMR_TI13Direct_Set | CCMR_TI24Direct_Set;

  /* Set the TI1 and the TI2 Polarities */
  *(vu32 *) CCER_CC1P_BB = TIM1_IC1Polarity;
  *(vu32 *) CCER_CC2P_BB = TIM1_IC2Polarity;

  TIM1->SMCR = (u16)tmpsmcr;

  TIM1->CCMR1 = (u16)tmpccmr1;
}

/*******************************************************************************
* Function Name  : TIM1_PrescalerConfig
* Description    : Configures the TIM1 Prescaler.
* Input          : - Prescaler: specifies the Prescaler Register value
*                  - TIM1_PSCReloadMode: specifies the TIM1 Prescaler Reload mode.
*                    This parmeter can be one of the following values:
*                       - TIM1_PSCReloadMode_Update: The Prescaler is loaded at
*                         the update event.
*                       - TIM1_PSCReloadMode_Immediate: The Prescaler is loaded
*                         immediatly.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_PrescalerConfig(u16 Prescaler, u16 TIM1_PSCReloadMode)
{
  /* Check the parameters */
  assert(IS_TIM1_PRESCALER_RELOAD(TIM1_PSCReloadMode));

  /* Set the Prescaler value */
  TIM1->PSC = Prescaler;

  /* Set or reset the UG Bit */
  *(vu32 *) EGR_UG_BB = TIM1_PSCReloadMode;
}
/*******************************************************************************
* Function Name  : TIM1_CounterModeConfig
* Description    : Specifies the TIM1 Counter Mode to be used.
* Input          : - TIM1_CounterMode: specifies the Counter Mode to be used
*                    This parameter can be one of the following values:
*                       - TIM1_CounterMode_Up: TIM1 Up Counting Mode
*                       - TIM1_CounterMode_Down: TIM1 Down Counting Mode
*                       - TIM1_CounterMode_CenterAligned1: TIM1 Center Aligned Mode1
*                       - TIM1_CounterMode_CenterAligned2: TIM1 Center Aligned Mode2
*                       - TIM1_CounterMode_CenterAligned3: TIM1 Center Aligned Mode3
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_CounterModeConfig(u16 TIM1_CounterMode)
{
  u32 tmpcr1 = 0;

  /* Check the parameters */
  assert(IS_TIM1_COUNTER_MODE(TIM1_CounterMode));

  tmpcr1 = TIM1->CR1;

  /* Reset the CMS and DIR Bits */
  tmpcr1 &= CR1_CounterMode_Mask;

  /* Set the Counter Mode */
  tmpcr1 |= TIM1_CounterMode;

  TIM1->CR1 = (u16)tmpcr1;
}

/*******************************************************************************
* Function Name  : TIM1_ForcedOC1Config
* Description    : Forces the TIM1 Channel1 output waveform to active or inactive 
*                  level.
* Input          : - TIM1_ForcedAction: specifies the forced Action to be set to
*                    the output waveform.
*                    This parameter can be one of the following values:
*                       - TIM1_ForcedAction_Active: Force active level on OC1REF
*                       - TIM1_ForcedAction_InActive: Force inactive level on
*                         OC1REF.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_ForcedOC1Config(u16 TIM1_ForcedAction)
{
  u32 tmpccmr1 = 0;

  /* Check the parameters */
  assert(IS_TIM1_FORCED_ACTION(TIM1_ForcedAction));

  tmpccmr1 = TIM1->CCMR1;

  /* Reset the OCM Bits */
  tmpccmr1 &= CCMR_OCM13_Mask;

  /* Configure The Forced output Mode */
  tmpccmr1 |= TIM1_ForcedAction;

  TIM1->CCMR1 = (u16)tmpccmr1;
}

/*******************************************************************************
* Function Name  : TIM1_ForcedOC2Config
* Description    : Forces the TIM1 Channel2 output waveform to active or inactive 
*                  level.
* Input          : - TIM1_ForcedAction: specifies the forced Action to be set to
*                    the output waveform.
*                    This parameter can be one of the following values:
*                       - TIM1_ForcedAction_Active: Force active level on OC2REF
*                       - TIM1_ForcedAction_InActive: Force inactive level on
*                         OC2REF.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_ForcedOC2Config(u16 TIM1_ForcedAction)
{
  u32 tmpccmr1 = 0;

  /* Check the parameters */
  assert(IS_TIM1_FORCED_ACTION(TIM1_ForcedAction));

  tmpccmr1 = TIM1->CCMR1;

  /* Reset the OCM Bits */
  tmpccmr1 &= CCMR_OCM24_Mask;

  /* Configure The Forced output Mode */
  tmpccmr1 |= (u32)TIM1_ForcedAction << 8;

  TIM1->CCMR1 = (u16)tmpccmr1;
}

/*******************************************************************************
* Function Name  : TIM1_ForcedOC3Config
* Description    : Forces the TIM1 Channel3 output waveform to active or inactive 
*                  level.
* Input          : - TIM1_ForcedAction: specifies the forced Action to be set to
*                    the output waveform.
*                    This parameter can be one of the following values:
*                       - TIM1_ForcedAction_Active: Force active level on OC3REF
*                       - TIM1_ForcedAction_InActive: Force inactive level on
*                         OC3REF.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_ForcedOC3Config(u16 TIM1_ForcedAction)
{
  u32 tmpccmr2 = 0;

  /* Check the parameters */
  assert(IS_TIM1_FORCED_ACTION(TIM1_ForcedAction));

  tmpccmr2 = TIM1->CCMR2;

  /* Reset the OCM Bits */
  tmpccmr2 &= CCMR_OCM13_Mask;

  /* Configure The Forced output Mode */
  tmpccmr2 |= TIM1_ForcedAction;

  TIM1->CCMR2 = (u16)tmpccmr2;
}

/*******************************************************************************
* Function Name  : TIM1_ForcedOC4Config
* Description    : Forces the TIM1 Channel4 output waveform to active or inactive 
*                  level.
* Input          : - TIM1_ForcedAction: specifies the forced Action to be set to
*                    the output waveform.
*                    This parameter can be one of the following values:
*                       - TIM1_ForcedAction_Active: Force active level on OC4REF
*                       - TIM1_ForcedAction_InActive: Force inactive level on
*                         OC4REF.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_ForcedOC4Config(u16 TIM1_ForcedAction)
{
  u32 tmpccmr2 = 0;

  /* Check the parameters */
  assert(IS_TIM1_FORCED_ACTION(TIM1_ForcedAction));

  tmpccmr2 = TIM1->CCMR1;

  /* Reset the OCM Bits */
  tmpccmr2 &= CCMR_OCM24_Mask;

  /* Configure The Forced output Mode */
  tmpccmr2 |= (u16)((u16)TIM1_ForcedAction << 8);

  TIM1->CCMR2 = (u16)tmpccmr2;
}

/*******************************************************************************
* Function Name  : TIM1_ARRPreloadConfig
* Description    : Enables or disables TIM1 peripheral Preload register on ARR.
* Input          : - Newstate: new state of the TIM1 peripheral Preload register
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_ARRPreloadConfig(FunctionalState Newstate)
{
  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(Newstate));

  /* Set or Reset the ARPE Bit */
  *(vu32 *) CR1_ARPE_BB = (u16)Newstate;
}

/*******************************************************************************
* Function Name  : TIM1_SelectCOM
* Description    : Selects the TIM1 peripheral Commutation event.
* Input          : - Newstate: new state of the Commutation event.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_SelectCOM(FunctionalState Newstate)
{
  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(Newstate));

  /* Set or Reset the CCUS Bit */
  *(vu32 *) CR2_CCUS_BB = (u16)Newstate;
}

/*******************************************************************************
* Function Name  : TIM1_SelectCCDMA
* Description    : Selects the TIM1 peripheral Capture Compare DMA source.
* Input          : - Newstate: new state of the Capture Compare DMA source
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_SelectCCDMA(FunctionalState Newstate)
{
  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(Newstate));

  /* Set or Reset the CCDS Bit */
  *(vu32 *) CR2_CCDS_BB = (u16)Newstate;
}

/*******************************************************************************
* Function Name  : TIM1_CCPreloadControl
* Description    : Sets or Resets the TIM1 peripheral Capture Compare Preload 
*                  Control bit.
* Input          : - Newstate: new state of the Capture Compare Preload Control bit
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_CCPreloadControl(FunctionalState Newstate)
{
  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(Newstate));

  /* Set or Reset the CCPC Bit */
  *(vu32 *) CR2_CCPC_BB = (u16)Newstate;
}

/*******************************************************************************
* Function Name  : TIM1_OC1PreloadConfig
* Description    : Enables or disables the TIM1 peripheral Preload Register on CCR1.
* Input          : - TIM1_OCPreload: new state of the Capture Compare Preload
*                    register.
*                    This parameter can be one of the following values:
*                       - TIM1_OCPreload_Enable
*                       - TIM1_OCPreload_Disable
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_OC1PreloadConfig(u16 TIM1_OCPreload)
{
  /* Check the parameters */
  assert(IS_TIM1_OCPRELOAD_STATE(TIM1_OCPreload));

  /* Set or Reset the OC1PE Bit */
  *(vu32 *) CCMR1_OC1PE_BB = (u16)TIM1_OCPreload;
}

/*******************************************************************************
* Function Name  : TIM1_OC2PreloadConfig
* Description    : Enables or disables the TIM1 peripheral Preload Register on CCR2.
* Input          : - TIM1_OCPreload: new state of the Capture Compare Preload
*                    register.
*                    This parameter can be one of the following values:
*                       - TIM1_OCPreload_Enable
*                       - TIM1_OCPreload_Disable
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_OC2PreloadConfig(u16 TIM1_OCPreload)
{
  /* Check the parameters */
  assert(IS_TIM1_OCPRELOAD_STATE(TIM1_OCPreload));

  /* Set or Reset the OC2PE Bit */
  *(vu32 *) CCMR1_OC2PE_BB = (u16)TIM1_OCPreload;
}

/*******************************************************************************
* Function Name  : TIM1_OC3PreloadConfig
* Description    : Enables or disables the TIM1 peripheral Preload Register on CCR3.
* Input          : - TIM1_OCPreload: new state of the Capture Compare Preload
*                    register.
*                    This parameter can be one of the following values:
*                       - TIM1_OCPreload_Enable
*                       - TIM1_OCPreload_Disable
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_OC3PreloadConfig(u16 TIM1_OCPreload)
{
  /* Check the parameters */
  assert(IS_TIM1_OCPRELOAD_STATE(TIM1_OCPreload));

  /* Set or Reset the OC3PE Bit */
  *(vu32 *) CCMR2_OC3PE_BB = (u16)TIM1_OCPreload;
}

/*******************************************************************************
* Function Name  : TIM1_OC4PreloadConfig
* Description    : Enables or disables the TIM1 peripheral Preload Register on CCR4.
* Input          : - TIM1_OCPreload: new state of the Capture Compare Preload
*                    register.
*                    This parameter can be one of the following values:
*                       - TIM1_OCPreload_Enable
*                       - TIM1_OCPreload_Disable
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_OC4PreloadConfig(u16 TIM1_OCPreload)
{
  /* Check the parameters */
  assert(IS_TIM1_OCPRELOAD_STATE(TIM1_OCPreload));

  /* Set or Reset the OC4PE Bit */
  *(vu32 *) CCMR2_OC4PE_BB = (u16)TIM1_OCPreload;
}

/*******************************************************************************
* Function Name  : TIM1_OC1FastConfig
* Description    : Configures the TIM1 Capture Compare 1 Fast feature.
* Input          : - TIM1_OCFast: new state of the Output Compare Fast Enable bit.
*                    This parameter can be one of the following values:
*                       - TIM1_OCFast_Enable
*                       - TIM1_OCFast_Disable
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_OC1FastConfig(u16 TIM1_OCFast)
{
  /* Check the parameters */
  assert(IS_TIM1_OCFAST_STATE(TIM1_OCFast));

  /* Set or Reset the OC1FE Bit */
  *(vu32 *) CCMR1_OC1FE_BB = (u16)TIM1_OCFast;
}

/*******************************************************************************
* Function Name  : TIM1_OC2FastConfig
* Description    : Configures the TIM1 Capture Compare Fast feature.
* Input          : - TIM1_OCFast: new state of the Output Compare Fast Enable bit.
*                    This parameter can be one of the following values:
*                       - TIM1_OCFast_Enable
*                       - TIM1_OCFast_Disable
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_OC2FastConfig(u16 TIM1_OCFast)
{
  /* Check the parameters */
  assert(IS_TIM1_OCFAST_STATE(TIM1_OCFast));

  /* Set or Reset the OC2FE Bit */
  *(vu32 *) CCMR1_OC2FE_BB = (u16)TIM1_OCFast;
}

/*******************************************************************************
* Function Name  : TIM1_OC3FastConfig
* Description    : Configures the TIM1 Capture Compare Fast feature.
* Input          : - TIM1_OCFast: new state of the Output Compare Fast Enable bit.
*                    This parameter can be one of the following values:
*                       - TIM1_OCFast_Enable
*                       - TIM1_OCFast_Disable
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_OC3FastConfig(u16 TIM1_OCFast)
{
  /* Check the parameters */
  assert(IS_TIM1_OCFAST_STATE(TIM1_OCFast));

  /* Set or Reset the OC3FE Bit */
  *(vu32 *) CCMR2_OC3FE_BB = (u16)TIM1_OCFast;
}

/*******************************************************************************
* Function Name  : TIM1_OC4FastConfig
* Description    : Configures the TIM1 Capture Compare Fast feature.
* Input          : - TIM1_OCFast: new state of the Output Compare Fast Enable bit.
*                    This parameter can be one of the following values:
*                       - TIM1_OCFast_Enable
*                       - TIM1_OCFast_Disable
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_OC4FastConfig(u16 TIM1_OCFast)
{
  /* Check the parameters */
  assert(IS_TIM1_OCFAST_STATE(TIM1_OCFast));

  /* Set or Reset the OC4FE Bit */
  *(vu32 *) CCMR2_OC4FE_BB = (u16)TIM1_OCFast;
}

/*******************************************************************************
* Function Name  : TIM1_GenerateEvent
* Description    : Configures the TIM1 event to be generate by software.
* Input          : - TIM1_EventSource: specifies the event source.
*                    This parameter can be one or more of the following values:
*                       - TIM1_EventSource_Update: TIM1 update Event source
*                       - TIM1_EventSource_CC1: TIM1 Capture Compare 1 Event source
*                       - TIM1_EventSource_CC2: TIM1 Capture Compare 2 Event source
*                       - TIM1_EventSource_CC3: TIM1 Capture Compare 3 Event source
*                       - TIM1_EventSource_CC4: TIM1 Capture Compare 4 Event source
*                       - TIM1_EventSource_COM: TIM1 COM Event source
*                       - TIM1_EventSource_Trigger: TIM1 Trigger Event source
*                       - TIM1_EventSourceBreak: TIM1 Break Event source
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_GenerateEvent(u16 TIM1_EventSource)
{
  /* Check the parameters */
  assert(IS_TIM1_EVENT_SOURCE(TIM1_EventSource));

  /* Set the event sources */
  TIM1->EGR |= TIM1_EventSource;
}

/*******************************************************************************
* Function Name  : TIM1_OC1PolarityConfig
* Description    : Configures the TIM1 Channel 1 polarity.
* Input          : - TIM1_OCPolarity: specifies the OC1 Polarity
*                    This parmeter can be one of the following values:
*                       - TIM1_OCPolarity_High: Output Compare active high
*                       - TIM1_OCPolarity_Low: Output Compare active low
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_OC1PolarityConfig(u16 TIM1_OCPolarity)
{
  /* Check the parameters */
  assert(IS_TIM1_OC_POLARITY(TIM1_OCPolarity));

  /* Set or Reset the CC1P Bit */
  *(vu32 *) CCER_CC1P_BB = (u16)TIM1_OCPolarity;
}

/*******************************************************************************
* Function Name  : TIM1_OC1NPolarityConfig
* Description    : Configures the TIM1 Channel 1N polarity.
* Input          : - TIM1_OCPolarity: specifies the OC1N Polarity
*                    This parmeter can be one of the following values:
*                       - TIM1_OCPolarity_High: Output Compare active high
*                       - TIM1_OCPolarity_Low: Output Compare active low
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_OC1NPolarityConfig(u16 TIM1_OCPolarity)
{
  /* Check the parameters */
  assert(IS_TIM1_OC_POLARITY(TIM1_OCPolarity));

  /* Set or Reset the CC3P Bit */
  *(vu32 *) CCER_CC1NP_BB = (u16)TIM1_OCPolarity;
}

/*******************************************************************************
* Function Name  : TIM1_OC2PolarityConfig
* Description    : Configures the TIM1 Channel 2 polarity.
* Input          : - TIM1_OCPolarity: specifies the OC2 Polarity
*                    This parmeter can be one of the following values:
*                       - TIM1_OCPolarity_High: Output Compare active high
*                       - TIM1_OCPolarity_Low: Output Compare active low
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_OC2PolarityConfig(u16 TIM1_OCPolarity)
{
  /* Check the parameters */
  assert(IS_TIM1_OC_POLARITY(TIM1_OCPolarity));

  /* Set or Reset the CC2P Bit */
  *(vu32 *) CCER_CC2P_BB = (u16)TIM1_OCPolarity;
}

/*******************************************************************************
* Function Name  : TIM1_OC2NPolarityConfig
* Description    : Configures the TIM1 Channel 2N polarity.
* Input          : - TIM1_OCPolarity: specifies the OC2N Polarity
*                    This parmeter can be one of the following values:
*                       - TIM1_OCPolarity_High: Output Compare active high
*                       - TIM1_OCPolarity_Low: Output Compare active low
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_OC2NPolarityConfig(u16 TIM1_OCPolarity)
{
  /* Check the parameters */
  assert(IS_TIM1_OC_POLARITY(TIM1_OCPolarity));

  /* Set or Reset the CC3P Bit */
  *(vu32 *) CCER_CC2NP_BB = (u16)TIM1_OCPolarity;
}

/*******************************************************************************
* Function Name  : TIM1_OC3PolarityConfig
* Description    : Configures the TIM1 Channel 3 polarity.
* Input          : - TIM1_OCPolarity: specifies the OC3 Polarity
*                    This parmeter can be one of the following values:
*                       - TIM1_OCPolarity_High: Output Compare active high
*                       - TIM1_OCPolarity_Low: Output Compare active low
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_OC3PolarityConfig(u16 TIM1_OCPolarity)
{
  /* Check the parameters */
  assert(IS_TIM1_OC_POLARITY(TIM1_OCPolarity));

  /* Set or Reset the CC3P Bit */
  *(vu32 *) CCER_CC3P_BB = (u16)TIM1_OCPolarity;
}

/*******************************************************************************
* Function Name  : TIM1_OC3NPolarityConfig
* Description    : Configures the TIM1 Channel 3N polarity.
* Input          : - TIM1_OCPolarity: specifies the OC3N Polarity
*                    This parmeter can be one of the following values:
*                       - TIM1_OCPolarity_High: Output Compare active high
*                       - TIM1_OCPolarity_Low: Output Compare active low
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_OC3NPolarityConfig(u16 TIM1_OCPolarity)
{
  /* Check the parameters */
  assert(IS_TIM1_OC_POLARITY(TIM1_OCPolarity));

  /* Set or Reset the CC3P Bit */
  *(vu32 *) CCER_CC3NP_BB = (u16)TIM1_OCPolarity;
}

/*******************************************************************************
* Function Name  : TIM1_OC4PolarityConfig
* Description    : Configures the TIM1 Channel 4 polarity.
* Input          : - TIM1_OCPolarity: specifies the OC4 Polarity
*                    This parmeter can be one of the following values:
*                       - TIM1_OCPolarity_High: Output Compare active high
*                       - TIM1_OCPolarity_Low: Output Compare active low
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_OC4PolarityConfig(u16 TIM1_OCPolarity)
{
  /* Check the parameters */
  assert(IS_TIM1_OC_POLARITY(TIM1_OCPolarity));

  /* Set or Reset the CC4P Bit */
  *(vu32 *) CCER_CC4P_BB = (u16)TIM1_OCPolarity;
}

/*******************************************************************************
* Function Name  : TIM1_CCxCmd
* Description    : Enables or disables the TIM1 Capture Compare Channel x.
* Input          : - TIM1_Channel: specifies the TIM1 Channel
*                    This parmeter can be one of the following values:
*                       - TIM1_Channel1: TIM1 Channel1
*                       - TIM1_Channel2: TIM1 Channel2
*                       - TIM1_Channel3: TIM1 Channel3
*                       - TIM1_Channel4: TIM1 Channel4
*                 - Newstate: specifies the TIM1 Channel CCxE bit new state.
*                   This parameter can be: ENABLE or DISABLE. 
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_CCxCmd(u16 TIM1_Channel, FunctionalState Newstate)
{
  /* Check the parameters */
  assert(IS_TIM1_CHANNEL(TIM1_Channel));
  assert(IS_FUNCTIONAL_STATE(Newstate));

  if(TIM1_Channel == TIM1_Channel_1)
  {
    /* Set or Reset the CC1E Bit */
    *(vu32 *) CCER_CC1E_BB = (u16)Newstate;  
  }
  else if(TIM1_Channel == TIM1_Channel_2)
  {
    /* Set or Reset the CC2E Bit */
    *(vu32 *) CCER_CC2E_BB = (u16)Newstate;
  }
  else if(TIM1_Channel == TIM1_Channel_3)
  {
    /* Set or Reset the CC3E Bit */
    *(vu32 *) CCER_CC3E_BB = (u16)Newstate;
  }
  else
  {
    /* Set or Reset the CC4E Bit */
    *(vu32 *) CCER_CC4E_BB = (u16)Newstate;
  }
}

/*******************************************************************************
* Function Name  : TIM1_CCxNCmd
* Description    : Enables or disables the TIM1 Capture Compare Channel xN.
* Input          : - TIM1_Channel: specifies the TIM1 Channel
*                    This parmeter can be one of the following values:
*                       - TIM1_Channel1: TIM1 Channel1
*                       - TIM1_Channel2: TIM1 Channel2
*                       - TIM1_Channel3: TIM1 Channel3
*                 - Newstate: specifies the TIM1 Channel CCxNE bit new state.
*                   This parameter can be: ENABLE or DISABLE. 
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_CCxNCmd(u16 TIM1_Channel, FunctionalState Newstate)
{
  /* Check the parameters */
  assert(IS_TIM1_COMPLEMENTARY_CHANNEL(TIM1_Channel));
  assert(IS_FUNCTIONAL_STATE(Newstate));

  if(TIM1_Channel == TIM1_Channel_1)
  {
    /* Set or Reset the CC1NE Bit */
    *(vu32 *) CCER_CC1NE_BB = (u16)Newstate;  
  }
  else if(TIM1_Channel == TIM1_Channel_2)
  {
    /* Set or Reset the CC2NE Bit */
    *(vu32 *) CCER_CC2NE_BB = (u16)Newstate;
  }
  else 
  {
    /* Set or Reset the CC3NE Bit */
    *(vu32 *) CCER_CC3NE_BB = (u16)Newstate;
  }
}

/*******************************************************************************
* Function Name  : TIM1_SelectOCxM
* Description    : Selects the TIM1 Ouput Compare Mode.
*                  This function disables the selected channel before changing 
*                  the Ouput Compare Mode. User has to enable this channel using
*                  TIM1_CCxCmd and TIM1_CCxNCmd functions.
* Input          : - TIM1_Channel: specifies the TIM1 Channel
*                    This parmeter can be one of the following values:
*                       - TIM1_Channel1: TIM1 Channel1
*                       - TIM1_Channel2: TIM1 Channel2
*                       - TIM1_Channel3: TIM1 Channel3
*                       - TIM1_Channel4: TIM1 Channel4
*                  - TIM1_OCMode: specifies the TIM1 Output Compare Mode.
*                    This paramter can be one of the following values:
*                       - TIM1_OCMode_Timing
*                       - TIM1_OCMode_Active
*                       - TIM1_OCMode_Toggle
*                       - TIM1_OCMode_PWM1
*                       - TIM1_OCMode_PWM2
*                       - TIM1_ForcedAction_Active
*                       - TIM1_ForcedAction_InActive
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_SelectOCxM(u16 TIM1_Channel, u16 TIM1_OCMode)
{
  /* Check the parameters */
  assert(IS_TIM1_CHANNEL(TIM1_Channel));
  assert(IS_TIM1_OCM(TIM1_OCMode));

  if(TIM1_Channel == TIM1_Channel_1)
  {
    /* Disable the Channel 1: Reset the CCE Bit */
    *(vu32 *) CCER_CC1E_BB = CCER_CCE_Reset;

    /* Reset the Output Compare Bits */
    TIM1->CCMR1 &= OC13Mode_Mask;

    /* Set the Ouput Compare Mode */
    TIM1->CCMR1 |= TIM1_OCMode;
  }
  else if(TIM1_Channel == TIM1_Channel_2)
  {
    /* Disable the Channel 2: Reset the CCE Bit */
    *(vu32 *) CCER_CC2E_BB = CCER_CCE_Reset;

    /* Reset the Output Compare Bits */
    TIM1->CCMR1 &= OC24Mode_Mask;

    /* Set the Ouput Compare Mode */
    TIM1->CCMR1 |= (u16)((u16)TIM1_OCMode << 8);
  }
  else if(TIM1_Channel == TIM1_Channel_3)
  {
    /* Disable the Channel 3: Reset the CCE Bit */
    *(vu32 *) CCER_CC3E_BB = CCER_CCE_Reset;

    /* Reset the Output Compare Bits */
    TIM1->CCMR2 &= OC13Mode_Mask;

    /* Set the Ouput Compare Mode */
    TIM1->CCMR2 |= TIM1_OCMode;
  }
  else
  {
    /* Disable the Channel 4: Reset the CCE Bit */
    *(vu32 *) CCER_CC4E_BB = CCER_CCE_Reset;

    /* Reset the Output Compare Bits */
    TIM1->CCMR2 &= OC24Mode_Mask;

    /* Set the Ouput Compare Mode */
    TIM1->CCMR2 |= (u16)((u16)TIM1_OCMode << 8);
  }
}

/*******************************************************************************
* Function Name  : TIM1_SetAutoreload
* Description    : Sets the TIM1 Autoreload Register value.
* Input          : - Autoreload: specifies the Autoreload register new value.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_SetAutoreload(u16 Autoreload)
{
  /* Set the Autoreload Register value */
  TIM1->ARR = Autoreload;
}

/*******************************************************************************
* Function Name  : TIM1_SetCompare1
* Description    : Sets the TIM1 Capture Compare1 Register value.
* Input          : - Compare1: specifies the Capture Compare1 register new value.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_SetCompare1(u16 Compare1)
{
  /* Set the Capture Compare1 Register value */
  TIM1->CCR1 = Compare1;
}

/*******************************************************************************
* Function Name  : TIM1_SetCompare2
* Description    : Sets the TIM1 Capture Compare2 Register value.
* Input          : - Compare2: specifies the Capture Compare2 register new value.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_SetCompare2(u16 Compare2)
{
  /* Set the Capture Compare2 Register value */
  TIM1->CCR2 = Compare2;
}

/*******************************************************************************
* Function Name  : TIM1_SetCompare3
* Description    : Sets the TIM1 Capture Compare3 Register value.
* Input          : - Compare3: specifies the Capture Compare3 register new value.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_SetCompare3(u16 Compare3)
{
  /* Set the Capture Compare3 Register value */
  TIM1->CCR3 = Compare3;
}

/*******************************************************************************
* Function Name  : TIM1_SetCompare4
* Description    : Sets the TIM1 Capture Compare4 Register value.
* Input          : - Compare4: specifies the Capture Compare4 register new value.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_SetCompare4(u16 Compare4)
{
  /* Set the Capture Compare4 Register value */
  TIM1->CCR4 = Compare4;
}

/*******************************************************************************
* Function Name  : TIM1_SetIC1Prescaler
* Description    : Sets the TIM1 Input Capture 1 prescaler.
* Input          : - TIM1_IC1Prescaler: specifies the Input Capture prescaler
*                    new value.
*                    This parameter can be one of the following values:
*                       - TIM1_ICPSC_DIV1: no prescaler
*                       - TIM1_ICPSC_DIV2: capture is done once every 2 events
*                       - TIM1_ICPSC_DIV4: capture is done once every 4 events
*                       - TIM1_ICPSC_DIV8: capture is done once every 8 events
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_SetIC1Prescaler(u16 TIM1_IC1Prescaler)
{
  u32 tmpccmr1 = 0;
  
  /* Check the parameters */
  assert(IS_TIM1_IC_PRESCALER(TIM1_IC1Prescaler));

  tmpccmr1 = TIM1->CCMR1;

  /* Reset the IC1PSC Bits */
  tmpccmr1 &= CCMR_IC13PSC_Mask;

  /* Set the IC1PSC value */
  tmpccmr1 |= TIM1_IC1Prescaler;

  TIM1->CCMR1 = (u16)tmpccmr1;
}

/*******************************************************************************
* Function Name  : TIM1_SetIC2Prescaler
* Description    : Sets the TIM1 Input Capture 2 prescaler.
* Input          : - TIM1_IC2Prescaler: specifies the Input Capture prescaler
*                    new value.
*                    This parameter can be one of the following values:
*                       - TIM1_ICPSC_DIV1: no prescaler
*                       - TIM1_ICPSC_DIV2: capture is done once every 2 events
*                       - TIM1_ICPSC_DIV4: capture is done once every 4 events
*                       - TIM1_ICPSC_DIV8: capture is done once every 8 events
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_SetIC2Prescaler(u16 TIM1_IC2Prescaler)
{
  u32 tmpccmr1 = 0;

  /* Check the parameters */
  assert(IS_TIM1_IC_PRESCALER(TIM1_IC2Prescaler));

  tmpccmr1 = TIM1->CCMR1;

  /* Reset the IC2PSC Bits */
  tmpccmr1 &= CCMR_IC24PSC_Mask;

  /* Set the IC2PSC value */
  tmpccmr1 |= (u16)((u16)TIM1_IC2Prescaler << 8);

  TIM1->CCMR1 = (u16)tmpccmr1;
}

/*******************************************************************************
* Function Name  : TIM1_SetIC3Prescaler
* Description    : Sets the TIM1 Input Capture 3 prescaler.
* Input          : - TIM1_IC3Prescaler: specifies the Input Capture prescaler
*                    new value.
*                    This parameter can be one of the following values:
*                       - TIM1_ICPSC_DIV1: no prescaler
*                       - TIM1_ICPSC_DIV2: capture is done once every 2 events
*                       - TIM1_ICPSC_DIV4: capture is done once every 4 events
*                       - TIM1_ICPSC_DIV8: capture is done once every 8 events
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_SetIC3Prescaler(u16 TIM1_IC3Prescaler)
{
  u32 tmpccmr2 = 0;

  /* Check the parameters */
  assert(IS_TIM1_IC_PRESCALER(TIM1_IC3Prescaler));

  tmpccmr2 = TIM1->CCMR2;

  /* Reset the IC3PSC Bits */
  tmpccmr2 &= CCMR_IC13PSC_Mask;

  /* Set the IC3PSC value */
  tmpccmr2 |= TIM1_IC3Prescaler;

  TIM1->CCMR2 = (u16)tmpccmr2;
}

/*******************************************************************************
* Function Name  : TIM1_SetIC4Prescaler
* Description    : Sets the TIM1 Input Capture 4 prescaler.
* Input          : - TIM1_IC4Prescaler: specifies the Input Capture prescaler
*                    new value.
*                    This parameter can be one of the following values:
*                       - TIM1_ICPSC_DIV1: no prescaler
*                       - TIM1_ICPSC_DIV2: capture is done once every 2 events
*                       - TIM1_ICPSC_DIV4: capture is done once every 4 events
*                       - TIM1_ICPSC_DIV8: capture is done once every 8 events
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_SetIC4Prescaler(u16 TIM1_IC4Prescaler)
{
  u32 tmpccmr2 = 0;

  /* Check the parameters */
  assert(IS_TIM1_IC_PRESCALER(TIM1_IC4Prescaler));

  tmpccmr2 = TIM1->CCMR2;

  /* Reset the IC4PSC Bits */
  tmpccmr2 &= CCMR_IC24PSC_Mask;

  /* Set the IC4PSC value */
  tmpccmr2 |= (u16)((u16)TIM1_IC4Prescaler << 8);

  TIM1->CCMR2 = (u16)tmpccmr2;
}

/*******************************************************************************
* Function Name  : TIM1_SetClockDivision
* Description    : Sets the TIM1 Clock Division value.
* Input          : - TIM1_CKD: specifies the clock division value.
*                    This parameter can be one of the following value:
*                       - TIM1_CKD_DIV1: TDTS = Tck_tim
*                       - TIM1_CKD_DIV2: TDTS = 2*Tck_tim
*                       - TIM1_CKD_DIV4: TDTS = 4*Tck_tim
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_SetClockDivision(u16 TIM1_CKD)
{
  u32 tmpcr1 = 0;

  /* Check the parameters */
  assert(IS_TIM1_CKD_DIV(TIM1_CKD));

  tmpcr1 = TIM1->CR1;

  /* Reset the CKD Bits */
  tmpcr1 &= CR1_CKD_Mask;

  /* Set the CKD value */
  tmpcr1 |= TIM1_CKD;

  TIM1->CR1 = (u16)tmpcr1;
}

/*******************************************************************************
* Function Name  : TIM1_GetCapture1
* Description    : Gets the TIM1 Input Capture 1 value.
* Input          : None
* Output         : None
* Return         : Capture Compare 1 Register value.
*******************************************************************************/
u16 TIM1_GetCapture1(void)
{
  /* Get the Capture 1 Register value */
  return TIM1->CCR1;
}

/*******************************************************************************
* Function Name  : TIM1_GetCapture2
* Description    : Gets the TIM1 Input Capture 2 value.
* Input          : None
* Output         : None
* Return         : Capture Compare 2 Register value.
*******************************************************************************/
u16 TIM1_GetCapture2(void)
{
  /* Get the Capture 2 Register value */
  return TIM1->CCR2;
}

/*******************************************************************************
* Function Name  : TIM1_GetCapture3
* Description    : Gets the TIM1 Input Capture 3 value.
* Input          : None
* Output         : None
* Return         : Capture Compare 3 Register value.
*******************************************************************************/
u16 TIM1_GetCapture3(void)
{
  /* Get the Capture 3 Register value */
  return TIM1->CCR3;
}

/*******************************************************************************
* Function Name  : TIM1_GetCapture4
* Description    : Gets the TIM1 Input Capture 4 value.
* Input          : None
* Output         : None
* Return         : Capture Compare 4 Register value.
*******************************************************************************/
u16 TIM1_GetCapture4(void)
{
  /* Get the Capture 4 Register value */
  return TIM1->CCR4;
}

/*******************************************************************************
* Function Name  : TIM1_GetCounter
* Description    : Gets the TIM1 Counter value.
* Input          : None
* Output         : None
* Return         : Counter Register value.
*******************************************************************************/
u16 TIM1_GetCounter(void)
{
  /* Get the Counter Register value */
  return TIM1->CNT;
}

/*******************************************************************************
* Function Name  : TIM1_GetPrescaler
* Description    : Gets the TIM1 Prescaler value.
* Input          : None
* Output         : None
* Return         : Prescaler Register value.
*******************************************************************************/
u16 TIM1_GetPrescaler(void)
{
  /* Get the Prescaler Register value */
  return TIM1->PSC;
}

/*******************************************************************************
* Function Name  : TIM1_GetFlagStatus
* Description    : Checks whether the specified TIM1 flag is set or not.
* Input          : - TIM1_FLAG: specifies the flag to check.
*                    This parameter can be one of the following values:
*                       - TIM1_FLAG_Update: TIM1 update Flag
*                       - TIM1_FLAG_CC1: TIM1 Capture Compare 1 Flag
*                       - TIM1_FLAG_CC2: TIM1 Capture Compare 2 Flag
*                       - TIM1_FLAG_CC3: TIM1 Capture Compare 3 Flag
*                       - TIM1_FLAG_CC4: TIM1 Capture Compare 4 Flag
*                       - TIM1_FLAG_COM: TIM1 Commutation Flag
*                       - TIM1_FLAG_Trigger: TIM1 Trigger Flag
*                       - TIM1_FLAG_Break: TIM1 Break Flag
*                       - TIM1_FLAG_CC1OF: TIM1 Capture Compare 1 overcapture Flag
*                       - TIM1_FLAG_CC2OF: TIM1 Capture Compare 2 overcapture Flag
*                       - TIM1_FLAG_CC3OF: TIM1 Capture Compare 3 overcapture Flag
*                       - TIM1_FLAG_CC4OF: TIM1 Capture Compare 4 overcapture Flag
* Output         : None
* Return         : The new state of TIM1_FLAG (SET or RESET).
*******************************************************************************/
FlagStatus TIM1_GetFlagStatus(u16 TIM1_FLAG)
{
  FlagStatus bitstatus = RESET;

  /* Check the parameters */
  assert(IS_TIM1_GET_FLAG(TIM1_FLAG));

  if ((TIM1->SR & TIM1_FLAG) != (u16)RESET )
  {
    bitstatus = SET;
  }
  else
  {
    bitstatus = RESET;
  }
  return bitstatus;
}

/*******************************************************************************
* Function Name  : TIM1_ClearFlag
* Description    : Clears the TIM1’s pending flags.
* Input          : - TIM1_FLAG: specifies the flag to clear.
*                    This parameter can be any combination of the following values:
*                       - TIM1_FLAG_Update: TIM1 update Flag
*                       - TIM1_FLAG_CC1: TIM1 Capture Compare 1 Flag
*                       - TIM1_FLAG_CC2: TIM1 Capture Compare 2 Flag
*                       - TIM1_FLAG_CC3: TIM1 Capture Compare 3 Flag
*                       - TIM1_FLAG_CC4: TIM1 Capture Compare 4 Flag
*                       - TIM1_FLAG_COM: TIM1 Commutation Flag
*                       - TIM1_FLAG_Trigger: TIM1 Trigger Flag
*                       - TIM1_FLAG_Break: TIM1 Break Flag
*                       - TIM1_FLAG_CC1OF: TIM1 Capture Compare 1 overcapture Flag
*                       - TIM1_FLAG_CC2OF: TIM1 Capture Compare 2 overcapture Flag
*                       - TIM1_FLAG_CC3OF: TIM1 Capture Compare 3 overcapture Flag
*                       - TIM1_FLAG_CC4OF: TIM1 Capture Compare 4 overcapture Flag
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_ClearFlag(u16 TIM1_FLAG)
{
  /* Check the parameters */
  assert(IS_TIM1_CLEAR_FLAG(TIM1_FLAG));

  /* Clear the flags */
  TIM1->SR &= (u16)~TIM1_FLAG;
}

/*******************************************************************************
* Function Name  : TIM1_GetITStatus
* Description    : Checks whether the TIM1 interrupt has occurred or not.
* Input          : - TIM1_IT: specifies the TIM1 interrupt source to check.
*                    This parameter can be one of the following values:
*                       - TIM1_IT_Update: TIM1 update Interrupt source
*                       - TIM1_IT_CC1: TIM1 Capture Compare 1 Interrupt source
*                       - TIM1_IT_CC2: TIM1 Capture Compare 2 Interrupt source
*                       - TIM1_IT_CC3: TIM1 Capture Compare 3 Interrupt source
*                       - TIM1_IT_CC4: TIM1 Capture Compare 4 Interrupt source
*                       - TIM1_IT_COM: TIM1 Commutation Interrupt
*                         source
*                       - TIM1_IT_Trigger: TIM1 Trigger Interrupt source
*                       - TIM1_IT_Break: TIM1 Break Interrupt source
* Output         : None
* Return         : The new state of the TIM1_IT(SET or RESET).
*******************************************************************************/
ITStatus TIM1_GetITStatus(u16 TIM1_IT)
{
  ITStatus bitstatus = RESET;
  
  u16 TIM1_itStatus = 0x0, TIM1_itEnable = 0x0;

  /* Check the parameters */
  assert(IS_TIM1_GET_IT(TIM1_IT));
  
  TIM1_itStatus = TIM1->SR & TIM1_IT;
  
  TIM1_itEnable = TIM1->DIER & TIM1_IT;

  if ((TIM1_itStatus != (u16)RESET ) && (TIM1_itEnable != (u16)RESET ))
  {
    bitstatus = SET;
  }
  else
  {
    bitstatus = RESET;
  }
  return bitstatus;
}

/*******************************************************************************
* Function Name  : TIM1_ClearITPendingBit
* Description    : Clears the TIM1's interrupt pending bits.
* Input          : - TIM1_IT: specifies the pending bit to clear.
*                    This parameter can be any combination of the following values:
*                       - TIM1_IT_Update: TIM1 update Interrupt source
*                       - TIM1_IT_CC1: TIM1 Capture Compare 1 Interrupt source
*                       - TIM1_IT_CC2: TIM1 Capture Compare 2 Interrupt source
*                       - TIM1_IT_CC3: TIM1 Capture Compare 3 Interrupt source
*                       - TIM1_IT_CC4: TIM1 Capture Compare 4 Interrupt source
*                       - TIM1_IT_COM: TIM1 Commutation Interrupt
*                         source
*                       - TIM1_IT_Trigger: TIM1 Trigger Interrupt source
*                       - TIM1_IT_Break: TIM1 Break Interrupt source
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_ClearITPendingBit(u16 TIM1_IT)
{
  /* Check the parameters */
  assert(IS_TIM1_IT(TIM1_IT));

  /* Clear the IT pending Bit */
  TIM1->SR &= (u16)~TIM1_IT;
}

/*******************************************************************************
* Function Name  : TI1_Config
* Description    : Configure the TI1 as Input.
* Input          : - TIM1_ICPolarity : The Input Polarity.
*                    This parameter can be one of the following values:
*                       - TIM1_ICPolarity_Rising
*                       - TIM1_ICPolarity_Falling
*                  - TIM1_ICSelection: specifies the input to be used.
*                    This parameter can be one of the following values:
*                       - TIM1_ICSelection_DirectTI: TIM1 Input 1 is selected to
*                         be connected to IC1.
*                       - TIM1_ICSelection_IndirectTI: TIM1 Input 1 is selected to
*                         be connected to IC2.
*                       - TIM1_ICSelection_TRGI:TIM1 Input 1 is selected to be
*                         connected to TRGI.
*                  - TIM1_ICFilter: Specifies the Input Capture Filter.
*                    This parameter must be a value between 0x00 and 0x0F.
* Output         : None
* Return         : None
*******************************************************************************/
static void TI1_Config(u16 TIM1_ICPolarity, u16 TIM1_ICSelection,
                       u8 TIM1_ICFilter)
{
  u32 tmpccmr1 = 0;

  tmpccmr1 = TIM1->CCMR1;

  /* Disable the Channel 1: Reset the CCE Bit */
  *(vu32 *) CCER_CC1E_BB = CCER_CCE_Reset;

  /* Select the Input and set the filter */
  tmpccmr1 &= CCMR_CC13S_Mask & CCMR_IC13F_Mask;
  tmpccmr1 |= (u16)TIM1_ICSelection | (u16)((u16)TIM1_ICFilter << 4);

  TIM1->CCMR1 = (u16)tmpccmr1;

  /* Select the Polarity */
  *(vu32 *) CCER_CC1P_BB = TIM1_ICPolarity;

  /* Set the CCE Bit */
  *(vu32 *) CCER_CC1E_BB = CCER_CCE_Set;
}

/*******************************************************************************
* Function Name  : TI2_Config
* Description    : Configure the TI2 as Input.
* Input          : - TIM1_ICPolarity : The Input Polarity.
*                    This parameter can be one of the following values:
*                       - TIM1_ICPolarity_Rising
*                       - TIM1_ICPolarity_Falling
*                  - TIM1_ICSelection: specifies the input to be used.
*                    This parameter can be one of the following values:
*                       - TIM1_ICSelection_DirectTI: TIM1 Input 2 is selected to
*                         be connected to IC2.
*                       - TIM1_ICSelection_IndirectTI: TIM1 Input 2 is selected to
*                         be connected to IC1.
*                       - TIM1_ICSelection_TRGI: TIM1 Input 2 is selected to be
*                         connected to TRGI.
*                  - TIM1_ICFilter: Specifies the Input Capture Filter.
*                    This parameter must be a value between 0x00 and 0x0F.
* Output         : None
* Return         : None
*******************************************************************************/
static void TI2_Config(u16 TIM1_ICPolarity, u16 TIM1_ICSelection,
                       u8 TIM1_ICFilter)
{
  u32 tmpccmr1 = 0;

  tmpccmr1 = TIM1->CCMR1;

  /* Disable the Channel 2: Reset the CCE Bit */
  *(vu32 *) CCER_CC2E_BB = CCER_CCE_Reset;

  /* Select the Input and set the filter */
  tmpccmr1 &= CCMR_CC24S_Mask & CCMR_IC24F_Mask;
  tmpccmr1 |= (u16)((u16)TIM1_ICSelection << 8) | (u16)((u16)TIM1_ICFilter <<12);

  TIM1->CCMR1 = (u16)tmpccmr1;

  /* Select the Polarity */
  *(vu32 *) CCER_CC2P_BB = TIM1_ICPolarity;

  /* Set the CCE Bit */
  *(vu32 *) CCER_CC2E_BB = CCER_CCE_Set;

}

/*******************************************************************************
* Function Name  : TI3_Config
* Description    : Configure the TI3 as Input.
* Input          : - TIM1_ICPolarity : The Input Polarity.
*                    This parameter can be one of the following values:
*                       - TIM1_ICPolarity_Rising
*                       - TIM1_ICPolarity_Falling
*                  - TIM1_ICSelection: specifies the input to be used.
*                    This parameter can be one of the following values:
*                       - TIM1_ICSelection_DirectTI: TIM1 Input 3 is selected to
*                         be connected to IC3.
*                       - TIM1_ICSelection_IndirectTI: TIM1 Input 3 is selected to
*                         be connected to IC4.
*                       - TIM1_ICSelection_TRGI: TIM1 Input 3 is selected to be
*                         connected to TRGI.
*                  - TIM1_ICFilter: Specifies the Input Capture Filter.
*                    This parameter must be a value between 0x00 and 0x0F.
* Output         : None
* Return         : None
*******************************************************************************/
static void TI3_Config(u16 TIM1_ICPolarity, u16 TIM1_ICSelection,
                       u8 TIM1_ICFilter)
{
  u32 tmpccmr2 = 0;

  tmpccmr2 = TIM1->CCMR2;

  /* Disable the Channel 3: Reset the CCE Bit */
  *(vu32 *) CCER_CC3E_BB = CCER_CCE_Reset;

  /* Select the Input and set the filter */
  tmpccmr2 &= CCMR_CC13S_Mask & CCMR_IC13F_Mask;
  tmpccmr2 |= (u16)TIM1_ICSelection | (u16)((u16)TIM1_ICFilter << 4);

  TIM1->CCMR2 = (u16)tmpccmr2;

  /* Select the Polarity */
  *(vu32 *) CCER_CC3P_BB = TIM1_ICPolarity;

  /* Set the CCE Bit */
  *(vu32 *) CCER_CC3E_BB = CCER_CCE_Set;
}

/*******************************************************************************
* Function Name  : TI4_Config
* Description    : Configure the TI4 as Input.
* Input          : - TIM1_ICPolarity : The Input Polarity.
*                    This parameter can be one of the following values:
*                       - TIM1_ICPolarity_Rising
*                       - TIM1_ICPolarity_Falling
*                  - TIM1_ICSelection: specifies the input to be used.
*                    This parameter can be one of the following values:
*                       - TIM1_ICSelection_DirectTI: TIM1 Input 4 is selected to
*                         be connected to IC4.
*                       - TIM1_ICSelection_IndirectTI: TIM1 Input 4 is selected to
*                         be connected to IC3.
*                       - TIM1_ICSelection_TRGI: TIM1 Input 4 is selected to be
*                         connected to TRGI.
*                  - TIM1_ICFilter: Specifies the Input Capture Filter.
*                    This parameter must be a value between 0x00 and 0x0F.
* Output         : None
* Return         : None
*******************************************************************************/
static void TI4_Config(u16 TIM1_ICPolarity, u16 TIM1_ICSelection,
                       u8 TIM1_ICFilter)
{
  u32 tmpccmr2 = 0;

  tmpccmr2 = TIM1->CCMR2;
  
  /* Disable the Channel 4: Reset the CCE Bit */
  *(vu32 *) CCER_CC4E_BB = CCER_CCE_Reset;

  /* Select the Input and set the filter */
  tmpccmr2 &= CCMR_CC24S_Mask & CCMR_IC24F_Mask;
  tmpccmr2 |= (u16)((u16)TIM1_ICSelection << 8) | (u16)((u16)TIM1_ICFilter << 12);

  TIM1->CCMR2 = (u16)tmpccmr2;

  /* Select the Polarity */
  *(vu32 *) CCER_CC4P_BB = TIM1_ICPolarity;

  /* Set the CCE Bit */
  *(vu32 *) CCER_CC4E_BB = CCER_CCE_Set;
}

/*******************************************************************************
* Function Name  : ETR_Config
* Description    : Configure the External Trigger
* Input          : - TIM1_ExtTRGPrescaler: The external Trigger Prescaler.
*                    This parameter can be one of the following values:
*                       - TIM1_ExtTRGPSC_OFF
*                       - TIM1_ExtTRGPSC_DIV2
*                       - TIM1_ExtTRGPSC_DIV4
*                       - TIM1_ExtTRGPSC_DIV8
*                  - TIM1_ExtTRGPolarity: The external Trigger Polarity.
*                    This parameter can be one of the following values:
*                       - TIM1_ExtTRGPolarity_Inverted
*                       - TIM1_ExtTRGPolarity_NonInverted
*                  - ExtTRGFilter: External Trigger Filter.
*                    This parameter must be a value between 0x00 and 0x0F.
* Output         : None
* Return         : None
*******************************************************************************/
static void ETR_Config(u16 TIM1_ExtTRGPrescaler, u16 TIM1_ExtTRGPolarity,
                       u16 ExtTRGFilter)
{
  u32 tmpsmcr = 0;

  tmpsmcr = TIM1->SMCR;

  /* Set the Prescaler, the Filter value and the Polarity */
  tmpsmcr &= SMCR_ETR_Mask;
  tmpsmcr |= TIM1_ExtTRGPrescaler | TIM1_ExtTRGPolarity | (u16)((u16)ExtTRGFilter << 8);

  TIM1->SMCR = (u16)tmpsmcr;
}

/******************* (C) COPYRIGHT 2007 STMicroelectronics *****END OF FILE****/
