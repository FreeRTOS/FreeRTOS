/**
  ******************************************************************************
  * @file    tsl_acq_stm32l1xx_sw.c
  * @author  MCD Application Team
  * @version V1.3.2
  * @date    22-January-2013
  * @brief   This file contains all functions to manage the acquisition
  *          on STM32l1xx products using the software mode.
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
#include "tsl_acq_stm32l1xx_sw.h"
#include "tsl_globals.h"

/* Private typedefs ----------------------------------------------------------*/

// Register configuration
typedef struct
{
  unsigned int RI_ASCR     : 3;
  unsigned int RI_ASCR_bit : 5;
} TSL_RIConf_t;

/* Private defines -----------------------------------------------------------*/
#define SIZEOFBANKCONF (17) //2 mask RIRs + 5 ports x 3 mask registers(MODER input, output, ODR) => 17 registers

/* Private macros ------------------------------------------------------------*/
#define IS_BANK_INDEX_OK(INDEX)   (((INDEX) == 0) || (((INDEX) > 0) && ((INDEX) < TSLPRM_TOTAL_BANKS)))

#define TSL_CHANNEL_PORT(channel)  (channel >> 4)
#define TSL_CHANNEL_IO(channel)    (channel & 0x0F)


#define TSL_RI_HYSCR_MASK(channel) (1 << TSL_CHANNEL_IO(channel))

#define TSL_RCC_AHBENR_Config(channel) (RCC->AHBENR |= TSL_GPIO_Clock_LookUpTable[TSL_CHANNEL_PORT(channel)])

#define TSL_RI_HYSCR_Config(channel)       (*TSL_RI_HYSCR_LookUpTable[TSL_CHANNEL_PORT(channel)] |= TSL_RI_HYSCR_MASK(channel))

#define TSL_GPIO_MODER_IN_Config(channel)      (TSL_GPIO_LookUpTable[TSL_CHANNEL_PORT(channel)]->MODER &= (uint32_t)(~(3 << (2 * TSL_CHANNEL_IO(channel)))))
#define TSL_GPIO_MODER_OUT_Config(channel)     (TSL_GPIO_LookUpTable[TSL_CHANNEL_PORT(channel)]->MODER = (TSL_GPIO_LookUpTable[TSL_CHANNEL_PORT(channel)]->MODER & (uint32_t)(~(3 << (2 * TSL_CHANNEL_IO(channel))))) | (1 << (2 * TSL_CHANNEL_IO(channel))))
#define TSL_GPIO_PUPDR_NO_PUPD_Config(channel) (TSL_GPIO_LookUpTable[TSL_CHANNEL_PORT(channel)]->PUPDR &= (uint32_t)(~(3 << (2 * TSL_CHANNEL_IO(channel)))))
#define TSL_GPIO_OTYPER_PP_Config(channel)     (TSL_GPIO_LookUpTable[TSL_CHANNEL_PORT(channel)]->OTYPER &= (uint32_t)(~(1 << TSL_CHANNEL_IO(channel))))
#define TSL_GPIO_OSPEEDR_VL_Config(channel)    (TSL_GPIO_LookUpTable[TSL_CHANNEL_PORT(channel)]->OSPEEDR &= (uint32_t)~(3 << (2 * TSL_CHANNEL_IO(channel))))
#define TSL_GPIO_BS_Config(channel)            (TSL_GPIO_LookUpTable[TSL_CHANNEL_PORT(channel)]->BSRRL = (uint16_t)(1 << (TSL_CHANNEL_IO(channel))))
#define TSL_GPIO_BR_Config(channel)            (TSL_GPIO_LookUpTable[TSL_CHANNEL_PORT(channel)]->BSRRH = (uint16_t)(1 << (TSL_CHANNEL_IO(channel))))


/* Private variables ---------------------------------------------------------*/
uint32_t TSL_BankSampleConf[SIZEOFBANKCONF];
uint32_t TSL_BankChannelConf[SIZEOFBANKCONF];
uint32_t tab_MeasurementCounter[11];
extern TSL_Params_T TSL_Params;

CONST TSL_Bank_T *bank;
TSL_tIndex_T NumberOfChannelOn = 0;
TSL_tNb_T NumberOfChannels = 0;
TSL_Status_enum_T TSL_Acq_Status = TSL_STATUS_BUSY;
uint16_t GroupToCheck = 0;

uint32_t TSL_GPIO_Clock_LookUpTable[] = {RCC_AHBPeriph_GPIOA, RCC_AHBPeriph_GPIOB, RCC_AHBPeriph_GPIOC, RCC_AHBPeriph_GPIOD, RCC_AHBPeriph_GPIOE, RCC_AHBPeriph_GPIOF, RCC_AHBPeriph_GPIOG, RCC_AHBPeriph_GPIOH};
GPIO_TypeDef *TSL_GPIO_LookUpTable[] = {GPIOA, GPIOB, GPIOC, GPIOD, GPIOE, GPIOF, GPIOG, GPIOH};

uint16_t *TSL_RI_HYSCR_LookUpTable[] =
{
    (uint16_t *)&RI->HYSCR1, (uint16_t *)&RI->HYSCR1 + 1,
    (uint16_t *)&RI->HYSCR2, (uint16_t *)&RI->HYSCR2 + 1,
    (uint16_t *)&RI->HYSCR3, (uint16_t *)&RI->HYSCR3 + 1,
    (uint16_t *)&RI->HYSCR4, (uint16_t *)&RI->HYSCR4 + 1
};

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

#if (TSLPRM_USE_GPIOA)
uint32_t GPIOA_IDR_Mask = 0;
#endif
#if (TSLPRM_USE_GPIOB)
uint32_t GPIOB_IDR_Mask = 0;
#endif
#if (TSLPRM_USE_GPIOC)
uint32_t GPIOC_IDR_Mask = 0;
#endif
#if (TSLPRM_USE_GPIOF)
uint32_t GPIOF_IDR_Mask = 0;
#endif
#if (TSLPRM_USE_GPIOG)
uint32_t GPIOG_IDR_Mask = 0;
#endif

/* Private functions prototype -----------------------------------------------*/
void SoftDelay(uint16_t val);
void TSL_BankConf(uint32_t * BankConf, TSL_Conf_t Conf);
void TSL_acq_GroupDone(uint16_t EndedGroup);

/**
  * @brief  Configures the acquisition module.
  * @param[in] BankConf Pointer to the bank to configure
  * @param[in] Conf Configuration
  * @retval None
  */
void TSL_BankConf(uint32_t *BankConf, TSL_Conf_t Conf)
{
  BankConf[TSL_RI_Conf_LookUpTable[Conf].RI_ASCR] |= (1 << (TSL_RI_Conf_LookUpTable[Conf].RI_ASCR_bit));

  switch (TSL_CHANNEL_PORT(Conf))
  {
    case TSL_BANK_GPIOA: BankConf[2] |= (3 << (2 * (TSL_CHANNEL_IO(Conf)))); //MODER input
      BankConf[3] |= (1 << (2 * (TSL_CHANNEL_IO(Conf)))); //MODER output
      BankConf[4] |= (1 << (TSL_CHANNEL_IO(Conf))); //ODR
      break;
    case TSL_BANK_GPIOB: BankConf[5] |= (3 << (2 * (TSL_CHANNEL_IO(Conf)))); //MODER input
      BankConf[6] |= (1 << (2 * (TSL_CHANNEL_IO(Conf)))); //MODER output
      BankConf[7] |= (1 << (TSL_CHANNEL_IO(Conf))); //ODR
      break;
    case TSL_BANK_GPIOC: BankConf[8] |= (3 << (2 * (TSL_CHANNEL_IO(Conf)))); //MODER input
      BankConf[9] |= (1 << (2 * (TSL_CHANNEL_IO(Conf)))); //MODER output
      BankConf[10] |= (1 << (TSL_CHANNEL_IO(Conf))); //ODR
      break;
    case TSL_BANK_GPIOF: BankConf[11] |= (3 << (2 * (TSL_CHANNEL_IO(Conf)))); //MODER input
      BankConf[12] |= (1 << (2 * (TSL_CHANNEL_IO(Conf)))); //MODER output
      BankConf[13] |= (1 << (TSL_CHANNEL_IO(Conf))); //ODR
      break;
    case TSL_BANK_GPIOG: BankConf[14] |= (3 << (2 * (TSL_CHANNEL_IO(Conf)))); //MODER input
      BankConf[15] |= (1 << (2 * (TSL_CHANNEL_IO(Conf)))); //MODER output
      BankConf[16] |= (1 << (TSL_CHANNEL_IO(Conf))); //ODR
      break;
    default: break;
  }
}


/**
  * @brief  Initializes the acquisition module.
  * @param  None
  * @retval None
  */
TSL_Status_enum_T TSL_acq_Init(void)
{
  CONST TSL_Bank_T *LocalBank = &(TSL_Globals.Bank_Array[0]);
  TSL_tNb_T NumberOfBanks = TSLPRM_TOTAL_BANKS;
  TSL_tNb_T LocalNumberOfChannels = 0;
  TSL_tIndex_T idx_bk;
  TSL_tIndex_T idx_ch;
  CONST TSL_ChannelSrc_T *p_chSrc = LocalBank->p_chSrc; // Pointer to the current channel

  /* Enables the comparator interface clock */
  RCC->APB1ENR |= RCC_APB1Periph_COMP;

  //====================
  // GPIOs configuration
  //====================
  for (idx_bk = 0; idx_bk < NumberOfBanks; idx_bk++)
  {
    LocalBank = &(TSL_Globals.Bank_Array[idx_bk]);
    p_chSrc = LocalBank->p_chSrc;

#if (TSLPRM_USE_SHIELD > 0)
    // Enables GPIOs clock
    TSL_RCC_AHBENR_Config(LocalBank->shield_sample);

    // Bank shield configuration
    /* Disables Hysteresis Register */
    TSL_RI_HYSCR_Config(LocalBank->shield_sample);

    /* Output PP config */
    TSL_GPIO_OTYPER_PP_Config(p_chSrc->t_sample);
    TSL_GPIO_OTYPER_PP_Config(p_chSrc->t_channel);
    /* 400kHz config */
    TSL_GPIO_OSPEEDR_VL_Config(p_chSrc->t_sample);
    TSL_GPIO_OSPEEDR_VL_Config(p_chSrc->t_channel);
    /* No pull up/pull down config */
    TSL_GPIO_PUPDR_NO_PUPD_Config(LocalBank->shield_sample);
    TSL_GPIO_PUPDR_NO_PUPD_Config(LocalBank->shield_channel);
    /* Set ODR */
    TSL_GPIO_BR_Config(LocalBank->shield_sample);
    TSL_GPIO_BR_Config(LocalBank->shield_channel);
    /* Output mode */
    TSL_GPIO_MODER_OUT_Config(LocalBank->shield_sample);
    TSL_GPIO_MODER_OUT_Config(LocalBank->shield_channel);
#endif

    LocalNumberOfChannels = LocalBank->NbChannels;

    for (idx_ch = 0;
         idx_ch < LocalNumberOfChannels;
         idx_ch++)
    {
      /* Enables GPIOs clock */
      TSL_RCC_AHBENR_Config(p_chSrc->t_sample);
      TSL_RCC_AHBENR_Config(p_chSrc->t_channel);

      // Bank/channel configuration
      /* Disables Hysteresis Register */
      TSL_RI_HYSCR_Config(p_chSrc->t_sample);
      /* Output PP config */
      TSL_GPIO_OTYPER_PP_Config(p_chSrc->t_sample);
      TSL_GPIO_OTYPER_PP_Config(p_chSrc->t_channel);
      /* 400kHz config */
      TSL_GPIO_OSPEEDR_VL_Config(p_chSrc->t_sample);
      TSL_GPIO_OSPEEDR_VL_Config(p_chSrc->t_channel);
      /* No pull up/pull down config */
      TSL_GPIO_PUPDR_NO_PUPD_Config(p_chSrc->t_sample);
      TSL_GPIO_PUPDR_NO_PUPD_Config(p_chSrc->t_channel);
      /* Set ODR */
      TSL_GPIO_BR_Config(p_chSrc->t_sample);
      TSL_GPIO_BR_Config(p_chSrc->t_channel);
      /* Output mode */
      TSL_GPIO_MODER_OUT_Config(p_chSrc->t_sample);
      TSL_GPIO_MODER_OUT_Config(p_chSrc->t_channel);

      p_chSrc++;
    }
  }

  /* Enable RI Switch */
  RI->ASCR1 &= (uint32_t)(~0x80000000); // ADC analog switches open !!!

  return  TSL_STATUS_OK;
}


/**
  * @brief Configures a Bank.
  * @param[in] idx_bk  Index of the Bank to configure
  * @retval Status
  */
TSL_Status_enum_T TSL_acq_BankConfig(TSL_tIndex_T idx_bk)
{
  TSL_tIndex_T index;
  TSL_tIndex_T idx_dest;
  TSL_tIndex_T idx_ch;
  CONST TSL_ChannelDest_T *p_chDest; // Pointer to the current channel
  CONST TSL_ChannelSrc_T *p_chSrc; // Pointer to the current channel

  // Check parameters (if USE_FULL_ASSERT is defined)
  assert_param(IS_BANK_INDEX_OK(idx_bk));

  bank = &(TSL_Globals.Bank_Array[idx_bk]);

  for (index = 0;index < SIZEOFBANKCONF;index++)
  {
    TSL_BankSampleConf[index] = 0x00000000;
    TSL_BankChannelConf[index] = 0x00000000;
  }

  NumberOfChannels = bank->NbChannels;
  NumberOfChannelOn = 0;
  GroupToCheck = 0;//init group to check

  p_chDest = bank->p_chDest;
  p_chSrc = bank->p_chSrc;
  for (idx_ch = 0; idx_ch < NumberOfChannels; idx_ch++)
  {
    // Get index in the result array associated to the current channel
    idx_dest = p_chDest->IdxDest;

    if (bank->p_chData[idx_dest].Flags.ObjStatus != TSL_OBJ_STATUS_OFF)
    {
      TSL_BankConf(TSL_BankSampleConf, p_chSrc->t_sample);
      TSL_BankConf(TSL_BankChannelConf, p_chSrc->t_channel);
      GroupToCheck |= (1 << (p_chSrc->IdxSrc));
      NumberOfChannelOn++;
    }

    p_chSrc++;
    p_chDest++;
  }

#if (TSLPRM_USE_GPIOA)
  GPIOA_IDR_Mask = TSL_BankSampleConf[4];
#endif

#if (TSLPRM_USE_GPIOB)
  GPIOB_IDR_Mask = TSL_BankSampleConf[7];
#endif

#if (TSLPRM_USE_GPIOC)
  GPIOC_IDR_Mask = TSL_BankSampleConf[10];
#endif

#if (TSLPRM_USE_GPIOF)
  GPIOF_IDR_Mask = TSL_BankSampleConf[13];
#endif

#if (TSLPRM_USE_GPIOG)
  GPIOG_IDR_Mask = TSL_BankSampleConf[16];
#endif


#if (TSLPRM_USE_SHIELD > 0)
  if (NumberOfChannelOn != 0)
  {
    TSL_BankConf(TSL_BankSampleConf, bank->shield_sample);
    TSL_BankConf(TSL_BankChannelConf, bank->shield_channel);
  }
#endif

  return TSL_STATUS_OK;

}


/**
  * @brief Check which group is not over
  * @param[in] EndedGroup
  * @retval None
  */
void TSL_acq_GroupDone(uint16_t EndedGroup)
{
  uint16_t i;

  for (i = 0;i < 11;i++)
  {
    if ((EndedGroup & (1 << i)) != (1 << i))
    {
      tab_MeasurementCounter[i] = TSL_Params.AcqMax + 1;
    }
  }

}


/**
  * @brief Start acquisition on a previously configured bank
  * @param None
  * @retval None
  */
void TSL_acq_BankStartAcq(void)
{
  CONST TSL_Bank_T *LocalBank = &(TSL_Globals.Bank_Array[0]);
  TSL_tNb_T NumberOfBanks = TSLPRM_TOTAL_BANKS;
  TSL_tNb_T LocalNumberOfChannels = 0;
  TSL_tIndex_T BankIndex;

  uint16_t MeasurementCounter = 0;
  CONST TSL_ChannelSrc_T *p_chSrc;
  TSL_tIndex_T idx_ch;
  uint16_t GroupToCheckMask = 0;
  uint32_t GPIO_IDR_Mask = 0;
  uint8_t Check_Input = 0;

#if (TSLPRM_USE_GPIOA)
  uint16_t TSL_GPIOA_IDR = 0;
#endif
#if (TSLPRM_USE_GPIOB)
  uint16_t TSL_GPIOB_IDR = 0;
#endif
#if (TSLPRM_USE_GPIOC)
  uint16_t TSL_GPIOC_IDR = 0;
#endif
#if (TSLPRM_USE_GPIOF)
  uint16_t TSL_GPIOF_IDR = 0;
#endif
#if (TSLPRM_USE_GPIOG)
  uint16_t TSL_GPIOG_IDR = 0;
#endif
  uint16_t GPIO_IDR = 0;

#if (TSLPRM_PROTECT_IO_ACCESS > 0)
  __disable_irq();
#endif
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
#if (TSLPRM_PROTECT_IO_ACCESS > 0)
  __enable_irq();
#endif

  /* Open the analog switches */
  RI->ASCR1 &= (uint32_t)(~(TSL_BankSampleConf[0] | TSL_BankChannelConf[0]));
  RI->ASCR2 &= (uint32_t)(~(TSL_BankSampleConf[1] | TSL_BankChannelConf[1]));

  /* All IO to pushpull LOW for discharging all capacitors (Ctouch and Csense) */
#if (TSLPRM_PROTECT_IO_ACCESS > 0)
  __disable_irq();
#endif
  /* Discharging sampling capacitor and CTouch */
#if (TSLPRM_USE_GPIOA)
  GPIOA->ODR &= (uint32_t)(~(TSL_BankSampleConf[4] | TSL_BankChannelConf[4]));
  GPIOA->MODER = (GPIOA->MODER & (uint32_t)(~(TSL_BankSampleConf[2] | TSL_BankChannelConf[2]))) | (TSL_BankSampleConf[3] | TSL_BankChannelConf[3]);
#endif
#if (TSLPRM_USE_GPIOB)
  GPIOB->ODR &= (uint32_t)(~(TSL_BankSampleConf[7] | TSL_BankChannelConf[7]));
  GPIOB->MODER = (GPIOB->MODER & (uint32_t)(~(TSL_BankSampleConf[5] | TSL_BankChannelConf[5]))) | (TSL_BankSampleConf[6] | TSL_BankChannelConf[6]);
#endif
#if (TSLPRM_USE_GPIOC)
  GPIOC->ODR &= (uint32_t)(~(TSL_BankSampleConf[10] | TSL_BankChannelConf[10]));
  GPIOC->MODER = (GPIOC->MODER & (uint32_t)(~(TSL_BankSampleConf[8] | TSL_BankChannelConf[8]))) | (TSL_BankSampleConf[9] | TSL_BankChannelConf[9]);
#endif
#if (TSLPRM_USE_GPIOF)
  GPIOF->ODR &= (uint32_t)(~(TSL_BankSampleConf[13] | TSL_BankChannelConf[13]));
  GPIOF->MODER = (GPIOF->MODER & (uint32_t)(~(TSL_BankSampleConf[11] | TSL_BankChannelConf[11]))) | (TSL_BankSampleConf[12] | TSL_BankChannelConf[12]);
#endif
#if (TSLPRM_USE_GPIOG)
  GPIOG->ODR &= (uint32_t)(~(TSL_BankSampleConf[16] | TSL_BankChannelConf[16]));
  GPIOG->MODER = (GPIOG->MODER & (uint32_t)(~(TSL_BankSampleConf[14] | TSL_BankChannelConf[14]))) | (TSL_BankSampleConf[15] | TSL_BankChannelConf[15]);
#endif



#if (TSLPRM_PROTECT_IO_ACCESS > 0)
  __enable_irq();
#endif

  /* Wait a while for a good discharging of all capacitors */
  SoftDelay(50); // ~14탎 with fHCLK = 32MHz
  //this time depends of the size of the sampling capacitor

#if (TSLPRM_PROTECT_IO_ACCESS > 0)
  __disable_irq();
#endif
  /* All IO in input floating */
#if (TSLPRM_USE_GPIOA)
  GPIOA->MODER &= (uint32_t)(~(TSL_BankSampleConf[2] | TSL_BankChannelConf[2]));
#endif
#if (TSLPRM_USE_GPIOB)
  GPIOB->MODER &= (uint32_t)(~(TSL_BankSampleConf[5] | TSL_BankChannelConf[5]));
#endif
#if (TSLPRM_USE_GPIOC)
  GPIOC->MODER &= (uint32_t)(~(TSL_BankSampleConf[8] | TSL_BankChannelConf[8]));
#endif
#if (TSLPRM_USE_GPIOF)
  GPIOF->MODER &= (uint32_t)(~(TSL_BankSampleConf[11] | TSL_BankChannelConf[11]));
#endif
#if (TSLPRM_USE_GPIOG)
  GPIOG->MODER &= (uint32_t)(~(TSL_BankSampleConf[14] | TSL_BankChannelConf[14]));
#endif

  /* set the IO to Vdd (io in push-pull HIGH when in output mode) */
#if (TSLPRM_USE_GPIOA)
  GPIOA->ODR |= (TSL_BankSampleConf[4] | TSL_BankChannelConf[4]); /* HIGH level */
#endif
#if (TSLPRM_USE_GPIOB)
  GPIOB->ODR |= (TSL_BankSampleConf[7] | TSL_BankChannelConf[7]); /* HIGH level */
#endif
#if (TSLPRM_USE_GPIOC)
  GPIOC->ODR |= (TSL_BankSampleConf[10] | TSL_BankChannelConf[10]); /* HIGH level */
#endif
#if (TSLPRM_USE_GPIOF)
  GPIOF->ODR |= (TSL_BankSampleConf[13] | TSL_BankChannelConf[13]); /* HIGH level */
#endif
#if (TSLPRM_USE_GPIOG)
  GPIOG->ODR |= (TSL_BankSampleConf[16] | TSL_BankChannelConf[16]); /* HIGH level */
#endif

#if (TSLPRM_PROTECT_IO_ACCESS > 0)
  __enable_irq();
#endif

  /* Close the sampling capacitor analog switch */
  RI->ASCR1 |= (TSL_BankSampleConf[0]);
  RI->ASCR2 |= (TSL_BankSampleConf[1]);


  /* Loop while all the 1st channel of each group have not reach the VIH level */
  do
  {

#if (TSLPRM_PROTECT_IO_ACCESS > 0)
    __disable_irq();
#endif
    /* Charging Ctouch by connecting the IO to Vdd (io in push-pull HIGH) */
#if (TSLPRM_USE_GPIOA)
    GPIOA->MODER |= (TSL_BankChannelConf[3]); /* Output push pull config */
#endif
#if (TSLPRM_USE_GPIOB)
    GPIOB->MODER |= (TSL_BankChannelConf[6]); /* Output push pull config */
#endif
#if (TSLPRM_USE_GPIOC)
    GPIOC->MODER |= (TSL_BankChannelConf[9]); /* Output push pull config */
#endif
#if (TSLPRM_USE_GPIOF)
    GPIOF->MODER |= (TSL_BankChannelConf[12]); /* Output push pull config */
#endif
#if (TSLPRM_USE_GPIOG)
    GPIOG->MODER |= (TSL_BankChannelConf[15]); /* Output push pull config */
#endif
#if (TSLPRM_PROTECT_IO_ACCESS > 0)
    __enable_irq();
#endif

    /* Wait a while for a good charging (programmable delay) */
    SoftDelay(1);

    /* test GPIOx->IDR bit + group configuration for each channel */

#if (TSLPRM_USE_GPIOA)
    TSL_GPIOA_IDR = GPIOA->IDR;
    if ((TSL_GPIOA_IDR & GPIOA_IDR_Mask) != 0)
    {
      Check_Input = 1;
      GPIOA_IDR_Mask &= (uint32_t)(~TSL_GPIOA_IDR);
    }
#endif

#if (TSLPRM_USE_GPIOB)
    TSL_GPIOB_IDR = GPIOB->IDR;
    if ((TSL_GPIOB_IDR & GPIOB_IDR_Mask) != 0)
    {
      Check_Input = (1 << 1);
      GPIOB_IDR_Mask &= (uint32_t)(~TSL_GPIOB_IDR);
    }
#endif

#if (TSLPRM_USE_GPIOC)
    TSL_GPIOC_IDR = GPIOC->IDR;
    if ((TSL_GPIOC_IDR & GPIOC_IDR_Mask) != 0)
    {
      Check_Input = (1 << 2);
      GPIOC_IDR_Mask &= (uint32_t)(~TSL_GPIOC_IDR);
    }
#endif

#if (TSLPRM_USE_GPIOF)
    TSL_GPIOF_IDR = GPIOF->IDR;
    if ((TSL_GPIOF_IDR & GPIOF_IDR_Mask) != 0)
    {
      Check_Input = (1 << 5);
      GPIOF_IDR_Mask &= (uint32_t)(~TSL_GPIOF_IDR);
    }
#endif

#if (TSLPRM_USE_GPIOG)
    TSL_GPIOG_IDR = GPIOG->IDR;
    if ((TSL_GPIOG_IDR & GPIOG_IDR_Mask) != 0)
    {
      Check_Input = (1 << 6);
      GPIOG_IDR_Mask &= (uint32_t)(~TSL_GPIOG_IDR);
    }
#endif


    if (Check_Input)
    {
      p_chSrc = bank->p_chSrc;
      for (idx_ch = 0; idx_ch < NumberOfChannels; idx_ch++)
      {
        GroupToCheckMask = (1 << (p_chSrc->IdxSrc));
        if ((GroupToCheck & GroupToCheckMask) == (GroupToCheckMask))
        {
          GPIO_IDR_Mask = (1 << TSL_CHANNEL_IO(p_chSrc->t_sample));

          switch (TSL_CHANNEL_PORT(p_chSrc->t_sample))
          {
#if (TSLPRM_USE_GPIOA)
            case 0: GPIO_IDR = TSL_GPIOA_IDR; break;
#endif
#if (TSLPRM_USE_GPIOB)
            case 1: GPIO_IDR = TSL_GPIOB_IDR; break;
#endif
#if (TSLPRM_USE_GPIOC)
            case 2: GPIO_IDR = TSL_GPIOC_IDR; break;
#endif
#if (TSLPRM_USE_GPIOF)
            case 5: GPIO_IDR = TSL_GPIOF_IDR; break;
#endif
#if (TSLPRM_USE_GPIOG)
            case 6: GPIO_IDR = TSL_GPIOG_IDR; break;
#endif
            default: break;
          }

          if ((GPIO_IDR & GPIO_IDR_Mask) == GPIO_IDR_Mask)
          {
            tab_MeasurementCounter[p_chSrc->IdxSrc] = MeasurementCounter;
            GroupToCheck &= (uint32_t)(~(1 << (p_chSrc->IdxSrc)));
            Check_Input &= (uint32_t)(~(1 << TSL_CHANNEL_PORT(p_chSrc->t_sample)));
          }
        }
        p_chSrc++;
      }
    }

    MeasurementCounter++;

#if (TSLPRM_PROTECT_IO_ACCESS > 0)
    __disable_irq();
#endif
    /* Configure All channels in input floating */
#if (TSLPRM_USE_GPIOA)
    GPIOA->MODER &= (uint32_t)(~(TSL_BankChannelConf[2]));
#endif
#if (TSLPRM_USE_GPIOB)
    GPIOB->MODER &= (uint32_t)(~(TSL_BankChannelConf[5]));
#endif
#if (TSLPRM_USE_GPIOC)
    GPIOC->MODER &= (uint32_t)(~(TSL_BankChannelConf[8]));
#endif
#if (TSLPRM_USE_GPIOF)
    GPIOF->MODER &= (uint32_t)(~(TSL_BankChannelConf[11]));
#endif
#if (TSLPRM_USE_GPIOG)
    GPIOG->MODER &= (uint32_t)(~(TSL_BankChannelConf[14]));
#endif

#if (TSLPRM_PROTECT_IO_ACCESS > 0)
    __enable_irq();
#endif

    /* Charging the Csense cap with connecting it to Ctouch by closing the analog switch */
    RI->ASCR1 |= (TSL_BankChannelConf[0]);
    RI->ASCR2 |= (TSL_BankChannelConf[1]);

    /* Wait a while for a good charge transfering (programmable delay) */
    SoftDelay(1);

    RI->ASCR1 &= (uint32_t)(~(TSL_BankChannelConf[0]));
    RI->ASCR2 &= (uint32_t)(~(TSL_BankChannelConf[1]));

    /*it's better to implement this like that because it's much more faster than to put this test in the "while test" below */
    if (MeasurementCounter > TSL_Params.AcqMax)
    {
      TSL_acq_GroupDone(GroupToCheck);
      __NOP();
      break;
    }

  }
  while (GroupToCheck != 0);


#if (TSLPRM_PROTECT_IO_ACCESS > 0)
  __disable_irq();
#endif
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
#if (TSLPRM_PROTECT_IO_ACCESS > 0)
  __enable_irq();
#endif


}


/**
  * @brief Wait end of acquisition
  * @param None
  * @retval status
  */
TSL_Status_enum_T TSL_acq_BankWaitEOC(void)
{
  TSL_Status_enum_T retval = TSL_STATUS_BUSY;
  retval = TSL_STATUS_OK;
  return retval;
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
  * @brief  Process the TS Interrupt routine
  * @param  None
  * @retval None
  */
void TSL_acq_ProcessIT(void)
{
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
