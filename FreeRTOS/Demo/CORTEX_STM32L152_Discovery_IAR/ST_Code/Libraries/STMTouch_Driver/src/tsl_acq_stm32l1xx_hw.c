/**
  ******************************************************************************
  * @file    tsl_acq_stm32l1xx_hw.c
  * @author  MCD Application Team
  * @version V1.3.2
  * @date    22-January-2013
  * @brief   This file contains all functions to manage the acquisition
  *          on STM32l1xx products using the Hardware mode (with Timers).
  ******************************************************************************
  * @attention
  *
  * <h2><center>&copy; COPYRIGHT 2013 STMicroelectronics</center></h2>
  *
  * Licensed under MCD-ST Liberty SW License Agreement V2, (the "License");
  * You may not use this file except in compliance with the License.
  * You may obtain a copy of the License at:
  *
  *        http://www.st.com/software_license_agreement_liberty_v2
  *
  * Unless required by applicable law or agreed to in writing, software
  * distributed under the License is distributed on an "AS IS" BASIS,
  * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  * See the License for the specific language governing permissions and
  * limitations under the License.
  *
  ******************************************************************************
  */

/* Includes ------------------------------------------------------------------*/
#include "tsl_acq_stm32l1xx_hw.h"
#include "tsl_globals.h"

/* Private typedefs ----------------------------------------------------------*/

// Register configuration
typedef struct
{
  unsigned int RI_ASCR     : 3;
  unsigned int RI_ASCR_bit : 5;
} TSL_RIConf_t;

/* Private defines -----------------------------------------------------------*/

/* Private macros ------------------------------------------------------------*/

#define IS_BANK_INDEX_OK(INDEX)   (((INDEX) == 0) || (((INDEX) > 0) && ((INDEX) < TSLPRM_TOTAL_BANKS)))

#define TSL_CHANNEL_PORT(channel)  (channel >> 4)
#define TSL_CHANNEL_IO(channel)    (channel & 0x0F)

#define TSL_GPIO_AFR(channel)        ((TSL_CHANNEL_IO(channel) < 8) ? 0 : 1)
#define TSL_GPIO_AFR_Shift(channel)  ((TSL_CHANNEL_IO(channel) < 8) ? (4 * TSL_CHANNEL_IO(channel)) : (4 * (TSL_CHANNEL_IO(channel) - 8)))

#define TSL_CPRI_HYSCR_MASK(channel) (1 << TSL_CHANNEL_IO(channel))
#define TSL_CPRI_ASMR_MASK(channel)  (1 << TSL_CHANNEL_IO(channel))
#define TSL_CPRI_CMR_MASK(channel)   (1 << TSL_CHANNEL_IO(channel))
#define TSL_CPRI_CICR_MASK(channel)  (1 << TSL_CHANNEL_IO(channel))

#define TSL_RCC_AHBENR_Config(channel) (RCC->AHBENR |= TSL_GPIO_Clock_LookUpTable[TSL_CHANNEL_PORT(channel)])

#define TSL_CPRI_ASCR_Config(channel)        (*TSL_CPRI_ASCR_LookUpTable[TSL_RI_Conf_LookUpTable[channel].RI_ASCR] |= (1 << (TSL_RI_Conf_LookUpTable[channel].RI_ASCR_bit)))
#define TSL_CPRI_HYSCR_Config(channel)       (*TSL_CPRI_HYSCR_LookUpTable[TSL_CHANNEL_PORT(channel)] |= TSL_CPRI_HYSCR_MASK(channel))
#define TSL_CPRI_ASMR_Config(channel)        (*TSL_CPRI_ASMR_LookUpTable[TSL_CHANNEL_PORT(channel)] |= TSL_CPRI_ASMR_MASK(channel))
#define TSL_CPRI_ASMR_Config_Clear(channel)  (*TSL_CPRI_ASMR_LookUpTable[TSL_CHANNEL_PORT(channel)] &= (uint32_t)(~TSL_CPRI_ASMR_MASK(channel)))
#define TSL_CPRI_CMR_Config(channel)         (*TSL_CPRI_CMR_LookUpTable[TSL_CHANNEL_PORT(channel)] |= TSL_CPRI_CMR_MASK(channel))
#define TSL_CPRI_CMR_Config_Clear(channel)   (*TSL_CPRI_CMR_LookUpTable[TSL_CHANNEL_PORT(channel)] &= (uint32_t)(~TSL_CPRI_CMR_MASK(channel)))
#define TSL_CPRI_CICR_Config(channel)        (*TSL_CPRI_CICR_LookUpTable[TSL_CHANNEL_PORT(channel)] |= TSL_CPRI_CICR_MASK(channel))
#define TSL_CPRI_CICR_Config_Clear(channel)  (*TSL_CPRI_CICR_LookUpTable[TSL_CHANNEL_PORT(channel)] &= (uint32_t)(~TSL_CPRI_CICR_MASK(channel)))

#define TSL_GPIO_MODER_IN_Config(channel)      (TSL_GPIO_LookUpTable[TSL_CHANNEL_PORT(channel)]->MODER &= (uint32_t)(~(3 << (2 * TSL_CHANNEL_IO(channel)))))
#define TSL_GPIO_MODER_AF_Config(channel)      (TSL_GPIO_LookUpTable[TSL_CHANNEL_PORT(channel)]->MODER = (TSL_GPIO_LookUpTable[TSL_CHANNEL_PORT(channel)]->MODER & (uint32_t)(~(3 << (2 * TSL_CHANNEL_IO(channel))))) | (2 << (2 * TSL_CHANNEL_IO(channel))))
#define TSL_GPIO_MODER_OUT_Config(channel)     (TSL_GPIO_LookUpTable[TSL_CHANNEL_PORT(channel)]->MODER = (TSL_GPIO_LookUpTable[TSL_CHANNEL_PORT(channel)]->MODER & (uint32_t)(~(3 << (2 * TSL_CHANNEL_IO(channel))))) | (1 << (2 * TSL_CHANNEL_IO(channel))))
#define TSL_GPIO_PUPDR_NO_PUPD_Config(channel) (TSL_GPIO_LookUpTable[TSL_CHANNEL_PORT(channel)]->PUPDR &= (uint32_t)(~(3 << (2 * TSL_CHANNEL_IO(channel)))))
#define TSL_GPIO_OTYPER_PP_Config(channel)     (TSL_GPIO_LookUpTable[TSL_CHANNEL_PORT(channel)]->OTYPER &= (uint32_t)(~(1 << TSL_CHANNEL_IO(channel))))
#define TSL_GPIO_OSPEEDR_VL_Config(channel)    (TSL_GPIO_LookUpTable[TSL_CHANNEL_PORT(channel)]->OSPEEDR &= (uint32_t)~(3 << (2 * TSL_CHANNEL_IO(channel))))
#define TSL_GPIO_AFR_Config(channel)           (TSL_GPIO_LookUpTable[TSL_CHANNEL_PORT(channel)]->AFR[TSL_GPIO_AFR(channel)] |= (0x0E << (TSL_GPIO_AFR_Shift(channel))))
#define TSL_GPIO_BS_Config(channel)            (TSL_GPIO_LookUpTable[TSL_CHANNEL_PORT(channel)]->BSRRL = (uint16_t)(1 << (TSL_CHANNEL_IO(channel))))
#define TSL_GPIO_BR_Config(channel)            (TSL_GPIO_LookUpTable[TSL_CHANNEL_PORT(channel)]->BSRRH = (uint16_t)(1 << (TSL_CHANNEL_IO(channel))))

#define TSL_GPIO_AFR_NOAF_Config(channel)      (TSL_GPIO_LookUpTable[TSL_CHANNEL_PORT(channel)]->AFR[TSL_GPIO_AFR(channel)] &= (uint32_t)(~(0x0F << (TSL_GPIO_AFR_Shift(channel)))))

#define TSL_GPIO_IDR_XOR_CPRI_CMR(channel)     ((TSL_GPIO_LookUpTable[TSL_CHANNEL_PORT(channel)]->IDR)^(*TSL_CPRI_CMR_LookUpTable[TSL_CHANNEL_PORT(channel)]))
#define TSL_GPIO_IDR_AND_CPRI_CMR(channel)     ((TSL_GPIO_LookUpTable[TSL_CHANNEL_PORT(channel)]->IDR)&(*TSL_CPRI_CMR_LookUpTable[TSL_CHANNEL_PORT(channel)]))

/* Private variables ---------------------------------------------------------*/
CONST TSL_Bank_T *bank;
TSL_tIndex_T NumberOfChannelOn = 0;
TSL_tNb_T NumberOfChannels = 0;
uint32_t tab_MeasurementCounter[11];
TSL_Status_enum_T TSL_Acq_Status = TSL_STATUS_BUSY;
static uint16_t GroupToCheck = 0;
static TSL_tIndex_T NumberOfChannelChecked = 0;

uint32_t TSL_GPIO_Clock_LookUpTable[] = {RCC_AHBPeriph_GPIOA, RCC_AHBPeriph_GPIOB, RCC_AHBPeriph_GPIOC, RCC_AHBPeriph_GPIOD, RCC_AHBPeriph_GPIOE, RCC_AHBPeriph_GPIOF, RCC_AHBPeriph_GPIOG, RCC_AHBPeriph_GPIOH};
GPIO_TypeDef *TSL_GPIO_LookUpTable[] = {GPIOA, GPIOB, GPIOC, GPIOD, GPIOE, GPIOF, GPIOG, GPIOH};

uint32_t *TSL_CPRI_ASCR_LookUpTable[] = {(uint32_t *)&CPRI->ASCR1, (uint32_t *)&CPRI->ASCR2};

uint16_t *TSL_CPRI_HYSCR_LookUpTable[] =
{
  (uint16_t *)&CPRI->HYSCR1, (uint16_t *)&CPRI->HYSCR1 + 1,
  (uint16_t *)&CPRI->HYSCR2, (uint16_t *)&CPRI->HYSCR2 + 1,
  (uint16_t *)&CPRI->HYSCR3, (uint16_t *)&CPRI->HYSCR3 + 1,
  (uint16_t *)&CPRI->HYSCR4, (uint16_t *)&CPRI->HYSCR4 + 1
};

uint32_t *TSL_CPRI_ASMR_LookUpTable[] = {(uint32_t *)&CPRI->ASMR1, (uint32_t *)&CPRI->ASMR2, (uint32_t *)&CPRI->ASMR3, 0, 0, (uint32_t *)&CPRI->ASMR4, (uint32_t *)&CPRI->ASMR5};
uint32_t *TSL_CPRI_CMR_LookUpTable[] = {(uint32_t *)&CPRI->CMR1, (uint32_t *)&CPRI->CMR2, (uint32_t *)&CPRI->CMR3, 0, 0, (uint32_t *)&CPRI->CMR4, (uint32_t *)&CPRI->CMR5};
uint32_t *TSL_CPRI_CICR_LookUpTable[] = {(uint32_t *)&CPRI->CICR1, (uint32_t *)&CPRI->CICR2, (uint32_t *)&CPRI->CICR3, 0, 0, (uint32_t *)&CPRI->CICR4, (uint32_t *)&CPRI->CICR5};

CONST TSL_RIConf_t TSL_RI_Conf_LookUpTable[101] =
{
    {0, 0},
    {0, 1},
    {0, 2},
    {0, 3},
    {0, 0},//padding
    {0, 0},//padding
    {0, 6},
    {0, 7},
    {1, 9},
    {1, 10},
    {1, 11},
    {1, 15},
    {0, 0},//padding
    {1, 6},
    {1, 7},
    {1, 8},

    {0, 8},
    {0, 9},
    {1, 16},
    {0, 0},//padding
    {1, 4},
    {1, 5},
    {1, 27},
    {1, 28},
    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding
    {0, 18},
    {0, 19},
    {0, 20},
    {0, 21},

    {0, 10},
    {0, 11},
    {0, 12},
    {0, 13},
    {0, 14},
    {0, 15},
    {1, 0},
    {1, 1},
    {1, 2},
    {1, 3},
    {1, 29},
    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding

    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding

    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding

    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding
    {0, 0},//padding
    {0, 27},
    {0, 28},
    {0, 29},
    {0, 30},
    {0, 16},
    {1, 17},
    {1, 18},
    {1, 19},
    {1, 20},
    {1, 21},

    {1, 22},
    {1, 23},
    {1, 24},
    {1, 25},
    {1, 26}
};

/* Private functions prototype -----------------------------------------------*/
void TSL_Init_GPIOs(void);
void TSL_Init_TIMs(void);
void TSL_Init_RI(void);
uint8_t TSL_Check_GPIO_IDR(uint8_t sample);
void SoftDelay(uint16_t val);


/**
  * @brief  Initializes the TouchSensing GPIOs.
  * @param  None
  * @retval None
  */
void TSL_Init_GPIOs(void)
{
  CONST TSL_Bank_T *LocalBank = &(TSL_Globals.Bank_Array[0]);
  TSL_tNb_T NumberOfBanks = TSLPRM_TOTAL_BANKS;
  TSL_tNb_T LocalNumberOfChannels = 0;
  TSL_tIndex_T idx_bk;
  TSL_tIndex_T idx_ch;
  CONST TSL_ChannelSrc_T *p_chSrc = LocalBank->p_chSrc; // Pointer to the current channel

  for (idx_bk = 0; idx_bk < NumberOfBanks; idx_bk++)
  {
    LocalBank = &(TSL_Globals.Bank_Array[idx_bk]);
    p_chSrc = LocalBank->p_chSrc;

#if (TSLPRM_USE_SHIELD > 0)
    // Enables GPIOs clock
    TSL_RCC_AHBENR_Config(LocalBank->shield_sample);

    // Bank shield configuration
    TSL_GPIO_OTYPER_PP_Config(LocalBank->shield_channel);
    TSL_GPIO_OSPEEDR_VL_Config(LocalBank->shield_channel);
    TSL_GPIO_PUPDR_NO_PUPD_Config(LocalBank->shield_channel);
    TSL_GPIO_AFR_Config(LocalBank->shield_channel);

    TSL_GPIO_OSPEEDR_VL_Config(LocalBank->shield_sample);
    TSL_GPIO_BR_Config(LocalBank->shield_sample);
    TSL_GPIO_OTYPER_PP_Config(LocalBank->shield_sample);
    TSL_GPIO_PUPDR_NO_PUPD_Config(LocalBank->shield_sample);

    TSL_GPIO_MODER_OUT_Config(LocalBank->shield_sample);
    TSL_GPIO_MODER_OUT_Config(LocalBank->shield_channel);
#endif

    LocalNumberOfChannels = LocalBank->NbChannels;

    for (idx_ch = 0;
         idx_ch < LocalNumberOfChannels;
         idx_ch++)
    {
      TSL_RCC_AHBENR_Config(p_chSrc->t_sample);
      TSL_RCC_AHBENR_Config(p_chSrc->t_channel);

      TSL_GPIO_OTYPER_PP_Config(p_chSrc->t_channel);
      TSL_GPIO_OSPEEDR_VL_Config(p_chSrc->t_channel);
      TSL_GPIO_PUPDR_NO_PUPD_Config(p_chSrc->t_channel);
      TSL_GPIO_AFR_Config(p_chSrc->t_channel);

      TSL_GPIO_OSPEEDR_VL_Config(p_chSrc->t_sample);
      TSL_GPIO_BR_Config(p_chSrc->t_sample);
      TSL_GPIO_OTYPER_PP_Config(p_chSrc->t_sample);
      TSL_GPIO_PUPDR_NO_PUPD_Config(p_chSrc->t_sample);

      TSL_GPIO_MODER_OUT_Config(p_chSrc->t_sample);
      TSL_GPIO_MODER_OUT_Config(p_chSrc->t_channel);

      p_chSrc++;
    }
  }
}

/**
  * @brief  Initializes the TouchSensing timers.
  * @param  None
  * @retval None
  */
void TSL_Init_TIMs(void)
{
  // Enable Timers clocks
  RCC->APB2ENR |= ((1 << 4) | (1 << 2)); // TIM11, TIM9

  //==============================
  // TIMER 9 configuration: Master
  //==============================
  // Set the option register to redirect cpri_tim9_itr_O to TIM9_itr
  TIM9->OR |= 4;
  // Set the Autoreload value (signal frequency)
  //TIM9->ARR = 64; // freq = (64*2)*31.25ns = 1us
  TIM9->ARR = TSLPRM_TIM_RELOAD; // freq = (64*2)*31.25ns = 1us
  // Set the Prescaler value
  //TIM9->PSC = 0; // fCK_CNT = 32MHz/(0+1) = 32MHz --> T=31.25ns
  TIM9->PSC = TSLPRM_TIM_PRESCALER; // fCK_CNT = 32MHz/(1+1) = 32MHz --> T=31.25ns
  // Set UP counter, Center-Aligned mode 1
  TIM9->CR1 = 0x20;
  // OC1REF used as TRGO
  TIM9->CR2 |= 0x40; // MMS=100
  // Select Master mode
  TIM9->SMCR = 0x95;
  // Set Update generation
  TIM9->EGR |= 0x01;

  // Channel 1 PWM configuration
  // Set the Output Compare Mode, PWM2
  TIM9->CCMR1 |= 0x0070;
  // Set the Pulse value
  //TIM9->CCR1 = 34; // duty cycle
  TIM9->CCR1 = (TSLPRM_TIM_RELOAD >> 1) + 1; // duty cycle
  // Compare output enable, active high
  TIM9->CCER |= 0x01;

  // Channel 2 PWM configuration
  // Set the Output Compare Mode, PWM2
  TIM9->CCMR1 |= 0x6000;
  // Set the Pulse value
  //TIM9->CCR2 = 30;
  TIM9->CCR2 = (TSLPRM_TIM_RELOAD >> 1) - 1;
  // Compare output enable, active high
  TIM9->CCER |= 0x10;

  //==============================
  // TIMER 11 configuration: slave
  //==============================
  // Set the option register to redirect TIM11_ic_o to TIM11_ti
  TIM11->OR |= 8;
  // Set the option register to redirect TIM9_tgo_cktim to TIM11_etri
  TIM11->OR |= 4;
  // Set the Prescaler value
  TIM11->PSC = 0;
  // Set UP counter, edge-aligned mode
  TIM11->CR1 = 0;
  // Select Slave mode, Internal Trigger 2 (ITR2 = TIM9), External clock mode 1
  TIM11->SMCR = 0x4000; // ECE bit
  // Channel 1 configured in Input capture mode
  TIM11->CCMR1 = 0x01; // No prescaler, no filter
  // Channel 1 capture enable (CCE1 = 1)
  TIM11->CCER = 0x01;
  // Interrupt Enable, active high
  TIM11->DIER |= 0x02;
  // Start slave timer
  TIM11->CR1 |= 0x01;
}


/**
  * @brief  Init TS routing interface.
  * @param  None
  * @retval None
  */
void TSL_Init_RI(void)
{
  CONST TSL_Bank_T *LocalBank;
  TSL_tNb_T NumberOfBanks = TSLPRM_TOTAL_BANKS;
  TSL_tNb_T LocalNumberOfChannels = 0;
  TSL_tIndex_T idx_bk;
  TSL_tIndex_T idx_ch;
  CONST TSL_ChannelSrc_T *p_chSrc; // Pointer to the current channel

  RCC->APB1ENR |= (uint32_t)((uint32_t)1 << 31); // COMP enable

  for (idx_bk = 0; idx_bk < NumberOfBanks; idx_bk++)
  {
    LocalBank = &(TSL_Globals.Bank_Array[idx_bk]);

#if (TSLPRM_USE_SHIELD > 0)
    TSL_CPRI_HYSCR_Config(LocalBank->shield_sample);
    TSL_CPRI_CICR_Config(LocalBank->shield_sample);
    TSL_CPRI_CICR_Config_Clear(LocalBank->shield_channel);

    TSL_CPRI_ASCR_Config(LocalBank->shield_sample);
#endif

    LocalNumberOfChannels = LocalBank->NbChannels;

    p_chSrc = LocalBank->p_chSrc;
    for (idx_ch = 0; idx_ch < LocalNumberOfChannels; idx_ch++)
    {
      TSL_CPRI_HYSCR_Config(p_chSrc->t_sample);
      TSL_CPRI_CICR_Config(p_chSrc->t_sample);
      TSL_CPRI_CICR_Config_Clear(p_chSrc->t_channel);
      TSL_CPRI_ASCR_Config(p_chSrc->t_sample);
      p_chSrc++;
    }
  }

  // Reset TSUSP bit, TIM9 ITR enabled to suspend OC TIM9 generation
  COMP->CSR &= (uint32_t)(~0x80000000);

}


/**
  * @brief  Initializes the acquisition module.
  * @param  None
  * @retval retval
  */
TSL_Status_enum_T TSL_acq_Init(void)
{
  NVIC_InitTypeDef  NVIC_InitStructure;

  NVIC_InitStructure.NVIC_IRQChannel = TIM11_IRQn;
  NVIC_InitStructure.NVIC_IRQChannelPreemptionPriority = 1;
  NVIC_InitStructure.NVIC_IRQChannelSubPriority = 1;
  NVIC_InitStructure.NVIC_IRQChannelCmd = ENABLE;
  NVIC_Init(&NVIC_InitStructure);

  TSL_Init_GPIOs();
  TSL_Init_TIMs();
  TSL_Init_RI();

  return TSL_STATUS_OK;
}


/**
  * @brief Configures a Bank.
  * @param[in] idx_bk  Index of the Bank to configure
  * @retval Status
  */
TSL_Status_enum_T TSL_acq_BankConfig(TSL_tIndex_T idx_bk)
{
  TSL_tIndex_T idx_dest;
  TSL_tIndex_T idx_ch;
  CONST TSL_ChannelDest_T *p_chDest; // Pointer to the current channel
  CONST TSL_ChannelSrc_T *p_chSrc; // Pointer to the current channel

  // Check parameters (if USE_FULL_ASSERT is defined)
  assert_param(IS_BANK_INDEX_OK(idx_bk));

  bank = &(TSL_Globals.Bank_Array[idx_bk]);

  NumberOfChannels = bank->NbChannels;

  GroupToCheck = 0;//init group to check
  NumberOfChannelOn = 0;//init number of channel on

  // init CPRI ASMR
  CPRI->ASMR1 = 0;
  CPRI->ASMR2 = 0;
  CPRI->ASMR3 = 0;
  CPRI->ASMR4 = 0;
  CPRI->ASMR5 = 0;

  p_chDest = bank->p_chDest;
  p_chSrc = bank->p_chSrc;
  for (idx_ch = 0; idx_ch < NumberOfChannels; idx_ch++)
  {
    // Get index in the result array associated to the current channel
    idx_dest = p_chDest->IdxDest;
    if (bank->p_chData[idx_dest].Flags.ObjStatus != TSL_OBJ_STATUS_OFF)
    {
      TSL_CPRI_CMR_Config(p_chSrc->t_sample);
      TSL_CPRI_ASMR_Config(p_chSrc->t_channel);
      GroupToCheck |= (1 << (p_chSrc->IdxSrc));
      NumberOfChannelOn++;
    }
    p_chDest++;
    p_chSrc++;
  }

  return TSL_STATUS_OK;

}


/**
  * @brief Start acquisition on a previously configured bank
  * @param None
  * @retval None
  */
void TSL_acq_BankStartAcq(void)
{
#if (TSLPRM_IODEF > 0)
  CONST TSL_Bank_T *LocalBank = &(TSL_Globals.Bank_Array[0]);
  TSL_tNb_T NumberOfBanks = TSLPRM_TOTAL_BANKS;
  TSL_tNb_T LocalNumberOfChannels = 0;
  TSL_tIndex_T BankIndex;
#endif
  CONST TSL_ChannelSrc_T *p_chSrc;
  CONST TSL_ChannelDest_T *p_chDest;
  TSL_tIndex_T idx_dest;
  TSL_tIndex_T idx_ch;

  if (NumberOfChannelOn)
  {
#if (TSLPRM_IODEF > 0)
    //============================
    // All GPIOs in Input floating
    //============================
    for (BankIndex = 0; BankIndex < NumberOfBanks; BankIndex++)
    {
      LocalBank = &(TSL_Globals.Bank_Array[BankIndex]);
      p_chSrc = LocalBank->p_chSrc;

#if (TSLPRM_USE_SHIELD > 0)
      TSL_GPIO_MODER_IN_Config(LocalBank->shield_sample);
      TSL_GPIO_MODER_IN_Config(LocalBank->shield_channel);
#endif

      LocalNumberOfChannels = LocalBank->NbChannels;

      for (idx_ch = 0;
           idx_ch < LocalNumberOfChannels;
           idx_ch++)
      {
        TSL_GPIO_MODER_IN_Config(p_chSrc->t_sample);
        TSL_GPIO_MODER_IN_Config(p_chSrc->t_channel);

        p_chSrc++;
      }
    }
#endif


    // Reset count
    TIM11->CNT = 0;

    // Discharge sample capacitors
    p_chDest = bank->p_chDest;
    p_chSrc = bank->p_chSrc;
    for (idx_ch = 0; idx_ch < NumberOfChannels; idx_ch++)
    {
      // Get index in the result array associated to the current channel
      idx_dest = p_chDest->IdxDest;
      if (bank->p_chData[idx_dest].Flags.ObjStatus != TSL_OBJ_STATUS_OFF)
      {
        TSL_GPIO_MODER_OUT_Config(p_chSrc->t_sample);
      }
      p_chDest++;
      p_chSrc++;
    }

#if (TSLPRM_USE_SHIELD > 0)
    // Discharge shield sample capacitor
    TSL_GPIO_MODER_OUT_Config(bank->shield_sample);
#endif

    // Wait for capa discharge
    SoftDelay(0x80);

#if (TSLPRM_USE_SHIELD > 0)
    // Init sample shield in floating input
    TSL_GPIO_MODER_IN_Config(bank->shield_sample);
    TSL_GPIO_MODER_AF_Config(bank->shield_channel);

    TSL_CPRI_ASMR_Config(bank->shield_channel);
#endif

    // Init samples in floating input and channels in alternate
    p_chDest = bank->p_chDest;
    p_chSrc = bank->p_chSrc;
    for (idx_ch = 0; idx_ch < NumberOfChannels; idx_ch++)
    {
      // Get index in the result array associated to the current channel
      idx_dest = p_chDest->IdxDest;

      if (bank->p_chData[idx_dest].Flags.ObjStatus != TSL_OBJ_STATUS_OFF)
      {
        TSL_GPIO_MODER_IN_Config(p_chSrc->t_sample);
        TSL_GPIO_MODER_AF_Config(p_chSrc->t_channel);
      }

      p_chDest++;
      p_chSrc++;
    }

    /* Start acquisition */
    TSL_Acq_Status = TSL_STATUS_BUSY;
    TIM9 ->CR1 |= 0x01; // Master
  }
  else
  {
    TSL_Acq_Status = TSL_STATUS_OK;
  }
}


/**
  * @brief Wait end of acquisition
  * @param None
  * @retval status
  */
TSL_Status_enum_T TSL_acq_BankWaitEOC(void)
{
  return TSL_Acq_Status;
}


/**
  * @brief Return the current measure
  * @param[in] index Index of the measure source
  * @retval Measure
  */
TSL_tMeas_T TSL_acq_GetMeas(TSL_tIndex_T index)
{
  return(tab_MeasurementCounter[index]);
}


/**
  * @brief  Check noise (not used)
  * @param  None
  * @retval Status
  */
TSL_AcqStatus_enum_T TSL_acq_CheckNoise(void)
{
  return TSL_ACQ_STATUS_OK;
}


/**
  * @brief Check GPIO IDR for the sample
  * @param[in] sample
  * @retval Status
  */
uint8_t TSL_Check_GPIO_IDR(uint8_t sample)
{
  GPIO_TypeDef *GPIO;
  uint32_t GPIO_IDR_Mask = 0;

  GPIO = TSL_GPIO_LookUpTable[TSL_CHANNEL_PORT(sample)];

  GPIO_IDR_Mask = (1 << (sample & 0x0F));

  if (((GPIO->IDR) & GPIO_IDR_Mask) == GPIO_IDR_Mask)
  {
    return 1;
  }
  else
  {
    return 0;
  }
}


/**
  * @brief  Process the TS Interrupt routine
  * @param  None
  * @retval None
  */
void TSL_acq_ProcessIT(void)
{
  CONST TSL_Bank_T *LocalBank = &(TSL_Globals.Bank_Array[0]);
  TSL_tNb_T NumberOfBanks = TSLPRM_TOTAL_BANKS;
  TSL_tNb_T LocalNumberOfChannels = 0;
  TSL_tIndex_T BankIndex;

  CONST TSL_ChannelSrc_T *p_chSrc;
  CONST TSL_ChannelDest_T *p_chDest;
  TSL_tIndex_T idx_dest;
  TSL_tIndex_T idx_ch;

  // Reset flags
  TIM11->SR = 0;
  idx_ch = 0;

  p_chDest = bank->p_chDest;
  p_chSrc = bank->p_chSrc;
  do
  {
    // Get index in the result array associated to the current channel
    idx_dest = p_chDest->IdxDest;

    if (bank->p_chData[idx_dest].Flags.ObjStatus != TSL_OBJ_STATUS_OFF)
    {
      if ((TSL_Check_GPIO_IDR(p_chSrc->t_sample)) &&
          ((GroupToCheck & (1 << (p_chSrc->IdxSrc))) == (1 << (p_chSrc->IdxSrc))))
      {
        tab_MeasurementCounter[p_chSrc->IdxSrc] = TIM11->CCR1;
        NumberOfChannelChecked++;
        GroupToCheck &= (uint32_t)(~(1 << (p_chSrc->IdxSrc)));

        // Reset CMR register to restart the timer
        TSL_CPRI_CMR_Config_Clear(p_chSrc->t_sample);
      }
    }
    p_chDest++;
    p_chSrc++;
    idx_ch++;
  }
  while (idx_ch < NumberOfChannels);

  if (NumberOfChannelChecked >= NumberOfChannelOn)
  {
    NumberOfChannelOn = 0;
    NumberOfChannelChecked = 0;

    // Disable master counter
    TIM9->CR1 &= (uint16_t)(~0x01);

    //====================
    // All GPIOs in PP Low
    //====================
    for (BankIndex = 0; BankIndex < NumberOfBanks; BankIndex++)
    {
      LocalBank = &(TSL_Globals.Bank_Array[BankIndex]);
      p_chSrc = LocalBank->p_chSrc;

#if (TSLPRM_USE_SHIELD > 0)
      TSL_GPIO_BR_Config(LocalBank->shield_sample);
      TSL_GPIO_BR_Config(LocalBank->shield_channel);
      TSL_GPIO_MODER_OUT_Config(LocalBank->shield_sample);
      TSL_GPIO_MODER_OUT_Config(LocalBank->shield_channel);
#endif

      LocalNumberOfChannels = LocalBank->NbChannels;

      for (idx_ch = 0;
           idx_ch < LocalNumberOfChannels;
           idx_ch++)
      {
        TSL_GPIO_BR_Config(p_chSrc->t_sample);
        TSL_GPIO_BR_Config(p_chSrc->t_channel);
        TSL_GPIO_MODER_OUT_Config(p_chSrc->t_sample);
        TSL_GPIO_MODER_OUT_Config(p_chSrc->t_channel);

        p_chSrc++;
      }
    }
    TSL_Acq_Status = TSL_STATUS_OK;
  }


}


/**
  * @brief Check if a filter must be used on the current channel (not used)
  * @param[in] pCh Pointer on the channel data information
  * @retval Result TRUE if a filter can be applied
  */
TSL_Bool_enum_T TSL_acq_UseFilter(TSL_ChannelData_T *pCh)
{
  return TSL_TRUE;
}


/**
  * @brief Compute the Delta value
  * @param[in] ref Reference value
  * @param[in] meas Last Measurement value
  * @retval Delta value
  */
TSL_tDelta_T TSL_acq_ComputeDelta(TSL_tRef_T ref, TSL_tMeas_T meas)
{
  return((TSL_tDelta_T)(ref - meas));
}


/**
  * @brief Compute the Measurement value
  * @param[in] ref Reference value
  * @param[in] delta Delta value
  * @retval Measurement value
  */
TSL_tMeas_T TSL_acq_ComputeMeas(TSL_tRef_T ref, TSL_tDelta_T delta)
{
  return((TSL_tMeas_T)(ref - delta));
}


/**
  * @brief Test if the Reference is incorrect (not used)
  * @param[in] pCh Pointer on the channel data information
  * @retval Result TRUE if the Reference is out of range
  */
TSL_Bool_enum_T TSL_acq_TestReferenceOutOfRange(TSL_ChannelData_T *pCh)
{
  return TSL_FALSE;
}


/**
  * @brief Test if the measure has crossed the reference target (not used)
  * @param[in] pCh Pointer on the channel data information
  * @param[in] new_meas Measure of the last acquisition on this channel
  * @retval Result TRUE if the Reference is valid
  */
TSL_Bool_enum_T TSL_acq_TestFirstReferenceIsValid(TSL_ChannelData_T *pCh, TSL_tMeas_T new_meas)
{
  return TSL_TRUE;
}


#if defined(__IAR_SYSTEMS_ICC__) // IAR/EWARM
#pragma optimize=medium
#elif defined(__CC_ARM) // Keil/MDK-ARM
#pragma O1
#pragma Ospace
#elif defined(__TASKING__) // Altium/Tasking
#pragma optimize O0
#elif defined(__GNUC__) // Atollic/True Studio + Raisonance/RKit
#pragma GCC push_options
#pragma GCC optimize ("O0")
#endif
/**
  * @brief  Software delay (private routine)
  * @param  val Wait delay
  * With fHCLK = 32MHz: 1 = ~1탎, 50 = ~14탎, 100 = ~25탎, 200 = ~50탎
  * @retval None
  */
void SoftDelay(uint16_t val)
{
  __IO uint16_t i;
  for (i = val; i > 0; i--)
  {}
}
#if defined(__TASKING__)
#pragma endoptimize
#endif

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
