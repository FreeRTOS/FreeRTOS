/**
  ******************************************************************************
  * @file    system_stm32l1xx.c
  * @author  MCD Application Team
  * @version V1.0.0RC1
  * @date    07/02/2010
  * @brief   CMSIS Cortex-M3 Device Peripheral Access Layer System Source File.
  ******************************************************************************
  *
  * THE PRESENT FIRMWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
  * WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE
  * TIME. AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY
  * DIRECT, INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING
  * FROM THE CONTENT OF SUCH FIRMWARE AND/OR THE USE MADE BY CUSTOMERS OF THE
  * CODING INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
  *
  * <h2><center>&copy; COPYRIGHT 2010 STMicroelectronics</center></h2>
  ******************************************************************************
  */

/** @addtogroup CMSIS
  * @{
  */

/** @addtogroup stm32l1xx_system
  * @{
  */

/** @addtogroup STM32L1xx_System_Private_Includes
  * @{
  */

#include "stm32l1xx.h"

/**
  * @}
  */

/** @addtogroup STM32L1xx_System_Private_TypesDefinitions
  * @{
  */

/**
  * @}
  */

/** @addtogroup STM32L1xx_System_Private_Defines
  * @{
  */

/*!< Uncomment the line corresponding to the desired System clock (SYSCLK)
   frequency (after reset the MSI is used as SYSCLK source)

   IMPORTANT NOTE:
   ==============
   1. After each device reset the MSI is used as System clock source.

   2. Please make sure that the selected System clock doesn't exceed your device's
      maximum frequency.

   3. If none of the define below is enabled, the MSI (2MHz default) is used as
      System clock source.

   4. The System clock configuration functions provided within this file assume that:
        - For Ultra Low Power Medium Mensity devices an external 8MHz crystal is
          used to drive the System clock.
     If you are using different crystal you have to adapt those functions accordingly.
    */

/* #define SYSCLK_FREQ_MSI */

#ifndef SYSCLK_FREQ_MSI
/* #define SYSCLK_FREQ_HSI    HSI_VALUE */
/* #define SYSCLK_FREQ_HSE    HSE_VALUE */
/* #define SYSCLK_FREQ_4MHz   4000000 */
/* #define SYSCLK_FREQ_8MHz   8000000 */
/* #define SYSCLK_FREQ_16MHz  16000000 */
#define SYSCLK_FREQ_32MHz  32000000
#else
/* #define SYSCLK_FREQ_MSI_64KHz     64000 */
/* #define SYSCLK_FREQ_MSI_128KHz    128000 */
/* #define SYSCLK_FREQ_MSI_256KHz    256000 */
/* #define SYSCLK_FREQ_MSI_512KHz    512000 */
/* #define SYSCLK_FREQ_MSI_1MHz      1000000 */
/* #define SYSCLK_FREQ_MSI_2MHz      2000000 */
/* #define SYSCLK_FREQ_MSI_4MHz      4000000 */
#endif

/**
  * @}
  */

/** @addtogroup STM32L1xx_System_Private_Macros
  * @{
  */

/**
  * @}
  */

/** @addtogroup STM32L1xx_System_Private_Variables
  * @{
  */

/*******************************************************************************
*  Clock Definitions
*******************************************************************************/
#ifndef SYSCLK_FREQ_MSI
#ifdef SYSCLK_FREQ_HSI
  uint32_t SystemCoreClock         = SYSCLK_FREQ_HSI;        /*!< System Clock Frequency (Core Clock) */
#elif defined SYSCLK_FREQ_HSE
  uint32_t SystemCoreClock         = SYSCLK_FREQ_HSE;        /*!< System Clock Frequency (Core Clock) */
#elif defined SYSCLK_FREQ_4MHz
  uint32_t SystemCoreClock         = SYSCLK_FREQ_4MHz;       /*!< System Clock Frequency (Core Clock) */
#elif defined SYSCLK_FREQ_8MHz
  uint32_t SystemCoreClock         = SYSCLK_FREQ_8MHz;       /*!< System Clock Frequency (Core Clock) */
#elif defined SYSCLK_FREQ_16MHz
  uint32_t SystemCoreClock         = SYSCLK_FREQ_16MHz;      /*!< System Clock Frequency (Core Clock) */
#elif defined SYSCLK_FREQ_32MHz
  uint32_t SystemCoreClock         = SYSCLK_FREQ_32MHz;      /*!< System Clock Frequency (Core Clock) */
#else /*!< MSI Selected as System Clock source */
  uint32_t SystemCoreClock         = MSI_VALUE;              /*!< System Clock Frequency (Core Clock) */
#endif
#else
#ifdef SYSCLK_FREQ_MSI_64KHz
  uint32_t SystemCoreClock         = SYSCLK_FREQ_MSI_64KHz;  /*!< System Clock Frequency (Core Clock) */
#elif defined SYSCLK_FREQ_MSI_128KHz
  uint32_t SystemCoreClock         = SYSCLK_FREQ_MSI_128KHz; /*!< System Clock Frequency (Core Clock) */
#elif defined SYSCLK_FREQ_MSI_256KHz
  uint32_t SystemCoreClock         = SYSCLK_FREQ_MSI_256KHz; /*!< System Clock Frequency (Core Clock) */
#elif defined SYSCLK_FREQ_MSI_512KHz
  uint32_t SystemCoreClock         = SYSCLK_FREQ_MSI_512KHz; /*!< System Clock Frequency (Core Clock) */
#elif defined SYSCLK_FREQ_MSI_1MHz
  uint32_t SystemCoreClock         = SYSCLK_FREQ_MSI_1MHz;   /*!< System Clock Frequency (Core Clock) */
#elif defined SYSCLK_FREQ_MSI_2MHz
  uint32_t SystemCoreClock         = SYSCLK_FREQ_MSI_2MHz;   /*!< System Clock Frequency (Core Clock) */
#elif defined SYSCLK_FREQ_MSI_4MHz
  uint32_t SystemCoreClock         = SYSCLK_FREQ_MSI_4MHz;   /*!< System Clock Frequency (Core Clock) */
#else
  uint32_t SystemCoreClock         = MSI_VALUE;              /*!< System Clock Frequency (Core Clock) */
#endif
#endif

__I uint8_t PLLMulTable[9] = {3, 4, 6, 8, 12, 16, 24, 32, 48};
__I uint8_t MSITable[7] = {0, 0, 0, 0, 1, 2, 4};
__I uint8_t AHBPrescTable[16] = {0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 6, 7, 8, 9};

/**
  * @}
  */

/** @addtogroup STM32L1xx_System_Private_FunctionPrototypes
  * @{
  */

static void SetSysClock(void);

#ifdef SYSCLK_FREQ_HSI
  static void SetSysClockToHSI(void);
#elif defined SYSCLK_FREQ_HSE
  static void SetSysClockToHSE(void);
#elif defined SYSCLK_FREQ_4MHz
  static void SetSysClockTo4(void);
#elif defined SYSCLK_FREQ_8MHz
  static void SetSysClockTo8(void);
#elif defined SYSCLK_FREQ_16MHz
  static void SetSysClockTo16(void);
#elif defined SYSCLK_FREQ_32MHz
  static void SetSysClockTo32(void);
#else
  static void SetSysClockToMSI(void);
#endif

/**
  * @}
  */

/** @addtogroup STM32L1xx_System_Private_Functions
  * @{
  */

/**
  * @brief  Setup the microcontroller system
  *         Initialize the Embedded Flash Interface, the PLL and update the
  *         SystemCoreClock variable
  * @note   This function should be used only after reset.
  * @param  None
  * @retval None
  */
void SystemInit (void)
{
  /*!< Set MSION bit */
  RCC->CR |= (uint32_t)0x00000100;

  /*!< Reset SW[1:0], HPRE[3:0], PPRE1[2:0], PPRE2[2:0], MCOSEL[2:0] and MCOPRE[2:0] bits */
  RCC->CFGR &= (uint32_t)0x88FFC00C;

  /*!< Reset HSION, HSEON, CSSON and PLLON bits */
  RCC->CR &= (uint32_t)0xEEFEFFFE;

  /*!< Reset HSEBYP bit */
  RCC->CR &= (uint32_t)0xFFFBFFFF;

  /*!< Reset PLLSRC, PLLMUL[3:0] and PLLDIV[1:0] bits */
  RCC->CFGR &= (uint32_t)0xFF02FFFF;

  /*!< Disable all interrupts */
  RCC->CIR = 0x00000000;

  /*!< Configure the System clock frequency, HCLK, PCLK2 and PCLK1 prescalers */
  /*!< Configure the Flash Latency cycles and enable prefetch buffer */
  SetSysClock();

}

/**
  * @brief  Update SystemCoreClock according to Clock Register Values
  * @note   None
  * @param  None
  * @retval None
  */
void SystemCoreClockUpdate (void)
{
  uint32_t tmp = 0, pllmul = 0, plldiv = 0, pllsource = 0, msirange = 0;

  /* Get SYSCLK source -------------------------------------------------------*/
  tmp = RCC->CFGR & RCC_CFGR_SWS;

  switch (tmp)
  {
    case 0x00:  /* MSI used as system clock */
      msirange = (RCC->ICSCR & RCC_ICSCR_MSIRANGE) >> 13;
      SystemCoreClock = (((1 << msirange) * 64000) - (MSITable[msirange] * 24000));
      break;
    case 0x04:  /* HSI used as system clock */
      SystemCoreClock = HSI_VALUE;
      break;
    case 0x08:  /* HSE used as system clock */
      SystemCoreClock = HSE_VALUE;
      break;
    case 0x0C:  /* PLL used as system clock */
      /* Get PLL clock source and multiplication factor ----------------------*/
      pllmul = RCC->CFGR & RCC_CFGR_PLLMUL;
      plldiv = RCC->CFGR & RCC_CFGR_PLLDIV;
      pllmul = PLLMulTable[(pllmul >> 18)];
      plldiv = (plldiv >> 22) + 1;

      pllsource = RCC->CFGR & RCC_CFGR_PLLSRC;

      if (pllsource == 0x00)
      {
        /* HSI oscillator clock selected as PLL clock entry */
        SystemCoreClock = (((HSI_VALUE) * pllmul) / plldiv);
      }
      else
      {
        /* HSE selected as PLL clock entry */
        SystemCoreClock = (((HSE_VALUE) * pllmul) / plldiv);
      }
      break;
    default:
      SystemCoreClock = MSI_VALUE;
      break;
  }
  /* Compute HCLK clock frequency --------------------------------------------*/
  /* Get HCLK prescaler */
  tmp = AHBPrescTable[((RCC->CFGR & RCC_CFGR_HPRE) >> 4)];
  /* HCLK clock frequency */
  SystemCoreClock >>= tmp;
}

/**
  * @brief  Configures the System clock frequency, HCLK, PCLK2 and PCLK1 prescalers.
  * @param  None
  * @retval None
  */
static void SetSysClock(void)
{
#ifdef SYSCLK_FREQ_HSI
  SetSysClockToHSI();
#elif defined SYSCLK_FREQ_HSE
  SetSysClockToHSE();
#elif defined SYSCLK_FREQ_4MHz
  SetSysClockTo4();
#elif defined SYSCLK_FREQ_8MHz
  SetSysClockTo8();
#elif defined SYSCLK_FREQ_16MHz
  SetSysClockTo16();
#elif defined SYSCLK_FREQ_32MHz
  SetSysClockTo32();
#else
  SetSysClockToMSI();
#endif

 /* If none of the define above is enabled, the MSI (2MHz default) is used as
    System clock source (default after reset) */
}

#ifdef SYSCLK_FREQ_HSI
/**
  * @brief  Selects HSI as System clock source and configure HCLK, PCLK2
  *         and PCLK1 prescalers.
  * @note   This function should be used only after reset.
  * @param  None
  * @retval None
  */
static void SetSysClockToHSI(void)
{
  __IO uint32_t StartUpCounter = 0, HSIStatus = 0;

  /* SYSCLK, HCLK, PCLK2 and PCLK1 configuration ---------------------------*/
  /* Enable HSI */
  RCC->CR |= ((uint32_t)RCC_CR_HSION);

  /* Wait till HSI is ready and if Time out is reached exit */
  do
  {
    HSIStatus = RCC->CR & RCC_CR_HSIRDY;
    StartUpCounter++;
  } while((HSIStatus == 0) && (StartUpCounter != HSE_STARTUP_TIMEOUT));

  if ((RCC->CR & RCC_CR_HSIRDY) != RESET)
  {
    HSIStatus = (uint32_t)0x01;
  }
  else
  {
    HSIStatus = (uint32_t)0x00;
  }

  if (HSIStatus == (uint32_t)0x01)
  {
    /* Enable 64-bit access */
    FLASH->ACR |= FLASH_ACR_ACC64;

    /* Enable Prefetch Buffer */
    FLASH->ACR |= FLASH_ACR_PRFTEN;

    /* Flash 1 wait state */
    FLASH->ACR |= FLASH_ACR_LATENCY;

    /* Enable the PWR APB1 Clock */
    RCC->APB1ENR |= RCC_APB1ENR_PWREN;

    /* Select the Voltage Range 1 (1.8V) */
    PWR->CR = PWR_CR_VOS_0;

    /* Wait Until the Voltage Regulator is ready */
    while((PWR->CSR & PWR_CSR_VOSF) != RESET)
    {
    }

    /* HCLK = SYSCLK */
    RCC->CFGR |= (uint32_t)RCC_CFGR_HPRE_DIV1;

    /* PCLK2 = HCLK */
    RCC->CFGR |= (uint32_t)RCC_CFGR_PPRE2_DIV1;

    /* PCLK1 = HCLK */
    RCC->CFGR |= (uint32_t)RCC_CFGR_PPRE1_DIV1;

    /* Select HSI as system clock source */
    RCC->CFGR &= (uint32_t)((uint32_t)~(RCC_CFGR_SW));
    RCC->CFGR |= (uint32_t)RCC_CFGR_SW_HSI;

    /* Wait till HSI is used as system clock source */
    while ((RCC->CFGR & (uint32_t)RCC_CFGR_SWS) != (uint32_t)0x04)
    {
    }
  }
  else
  {
    /* If HSI fails to start-up, the application will have wrong clock
       configuration. User can add here some code to deal with this error */
  }
}

#elif defined SYSCLK_FREQ_HSE
/**
  * @brief  Selects HSE as System clock source and configure HCLK, PCLK2
  *         and PCLK1 prescalers.
  * @note   This function should be used only after reset.
  * @param  None
  * @retval None
  */
static void SetSysClockToHSE(void)
{
  __IO uint32_t StartUpCounter = 0, HSEStatus = 0;

  /* SYSCLK, HCLK, PCLK2 and PCLK1 configuration ---------------------------*/
  /* Enable HSE */
  RCC->CR |= ((uint32_t)RCC_CR_HSEON);

  /* Wait till HSE is ready and if Time out is reached exit */
  do
  {
    HSEStatus = RCC->CR & RCC_CR_HSERDY;
    StartUpCounter++;
  } while((HSEStatus == 0) && (StartUpCounter != HSE_STARTUP_TIMEOUT));

  if ((RCC->CR & RCC_CR_HSERDY) != RESET)
  {
    HSEStatus = (uint32_t)0x01;
  }
  else
  {
    HSEStatus = (uint32_t)0x00;
  }

  if (HSEStatus == (uint32_t)0x01)
  {
    /* Flash 0 wait state */
    FLASH->ACR &= ~FLASH_ACR_LATENCY;

    /* Disable Prefetch Buffer */
    FLASH->ACR &= ~FLASH_ACR_PRFTEN;

    /* Disable 64-bit access */
    FLASH->ACR &= ~FLASH_ACR_ACC64;

    /* Enable the PWR APB1 Clock */
    RCC->APB1ENR |= RCC_APB1ENR_PWREN;

    /* Select the Voltage Range 2 (1.5V) */
    PWR->CR = PWR_CR_VOS_1;

    /* Wait Until the Voltage Regulator is ready */
    while((PWR->CSR & PWR_CSR_VOSF) != RESET)
    {
    }

    /* HCLK = SYSCLK */
    RCC->CFGR |= (uint32_t)RCC_CFGR_HPRE_DIV1;

    /* PCLK2 = HCLK */
    RCC->CFGR |= (uint32_t)RCC_CFGR_PPRE2_DIV1;

    /* PCLK1 = HCLK */
    RCC->CFGR |= (uint32_t)RCC_CFGR_PPRE1_DIV1;

    /* Select HSE as system clock source */
    RCC->CFGR &= (uint32_t)((uint32_t)~(RCC_CFGR_SW));
    RCC->CFGR |= (uint32_t)RCC_CFGR_SW_HSE;

    /* Wait till HSE is used as system clock source */
    while ((RCC->CFGR & (uint32_t)RCC_CFGR_SWS) != (uint32_t)0x08)
    {
    }
  }
  else
  {
    /* If HSE fails to start-up, the application will have wrong clock
       configuration. User can add here some code to deal with this error */
  }
}
#elif defined SYSCLK_FREQ_4MHz
/**
  * @brief  Sets System clock frequency to 4MHz and configure HCLK, PCLK2
  *         and PCLK1 prescalers.
  * @note   This function should be used only after reset.
  * @param  None
  * @retval None
  */
static void SetSysClockTo4(void)
{
  __IO uint32_t StartUpCounter = 0, HSEStatus = 0;

  /* SYSCLK, HCLK, PCLK2 and PCLK1 configuration ---------------------------*/
  /* Enable HSE */
  RCC->CR |= ((uint32_t)RCC_CR_HSEON);

  /* Wait till HSE is ready and if Time out is reached exit */
  do
  {
    HSEStatus = RCC->CR & RCC_CR_HSERDY;
    StartUpCounter++;
  } while((HSEStatus == 0) && (StartUpCounter != HSE_STARTUP_TIMEOUT));

  if ((RCC->CR & RCC_CR_HSERDY) != RESET)
  {
    HSEStatus = (uint32_t)0x01;
  }
  else
  {
    HSEStatus = (uint32_t)0x00;
  }

  if (HSEStatus == (uint32_t)0x01)
  {
    /* Flash 0 wait state */
    FLASH->ACR &= ~FLASH_ACR_LATENCY;

    /* Disable Prefetch Buffer */
    FLASH->ACR &= ~FLASH_ACR_PRFTEN;

    /* Disable 64-bit access */
    FLASH->ACR &= ~FLASH_ACR_ACC64;

    /* Enable the PWR APB1 Clock */
    RCC->APB1ENR |= RCC_APB1ENR_PWREN;

    /* Select the Voltage Range 2 (1.5V) */
    PWR->CR = PWR_CR_VOS_1;

    /* Wait Until the Voltage Regulator is ready */
    while((PWR->CSR & PWR_CSR_VOSF) != RESET)
    {
    }

    /* HCLK = SYSCLK */
    RCC->CFGR |= (uint32_t)RCC_CFGR_HPRE_DIV2;

    /* PCLK2 = HCLK */
    RCC->CFGR |= (uint32_t)RCC_CFGR_PPRE2_DIV1;

    /* PCLK1 = HCLK */
    RCC->CFGR |= (uint32_t)RCC_CFGR_PPRE1_DIV1;

    /* Select HSE as system clock source */
    RCC->CFGR &= (uint32_t)((uint32_t)~(RCC_CFGR_SW));
    RCC->CFGR |= (uint32_t)RCC_CFGR_SW_HSE;

    /* Wait till HSE is used as system clock source */
    while ((RCC->CFGR & (uint32_t)RCC_CFGR_SWS) != (uint32_t)0x08)
    {
    }
  }
  else
  {
    /* If HSE fails to start-up, the application will have wrong clock
       configuration. User can add here some code to deal with this error */
  }
}

#elif defined SYSCLK_FREQ_8MHz
/**
  * @brief  Sets System clock frequency to 8MHz and configure HCLK, PCLK2
  *         and PCLK1 prescalers.
  * @note   This function should be used only after reset.
  * @param  None
  * @retval None
  */
static void SetSysClockTo8(void)
{
  __IO uint32_t StartUpCounter = 0, HSEStatus = 0;

  /* SYSCLK, HCLK, PCLK2 and PCLK1 configuration ---------------------------*/
  /* Enable HSE */
  RCC->CR |= ((uint32_t)RCC_CR_HSEON);

  /* Wait till HSE is ready and if Time out is reached exit */
  do
  {
    HSEStatus = RCC->CR & RCC_CR_HSERDY;
    StartUpCounter++;
  } while((HSEStatus == 0) && (StartUpCounter != HSE_STARTUP_TIMEOUT));

  if ((RCC->CR & RCC_CR_HSERDY) != RESET)
  {
    HSEStatus = (uint32_t)0x01;
  }
  else
  {
    HSEStatus = (uint32_t)0x00;
  }

  if (HSEStatus == (uint32_t)0x01)
  {
    /* Flash 0 wait state */
    FLASH->ACR &= ~FLASH_ACR_LATENCY;

    /* Disable Prefetch Buffer */
    FLASH->ACR &= ~FLASH_ACR_PRFTEN;

    /* Disable 64-bit access */
    FLASH->ACR &= ~FLASH_ACR_ACC64;

    /* Enable the PWR APB1 Clock */
    RCC->APB1ENR |= RCC_APB1ENR_PWREN;

    /* Select the Voltage Range 2 (1.5V) */
    PWR->CR = PWR_CR_VOS_1;

    /* Wait Until the Voltage Regulator is ready */
    while((PWR->CSR & PWR_CSR_VOSF) != RESET)
    {
    }

    /* HCLK = SYSCLK */
    RCC->CFGR |= (uint32_t)RCC_CFGR_HPRE_DIV1;

    /* PCLK2 = HCLK */
    RCC->CFGR |= (uint32_t)RCC_CFGR_PPRE2_DIV1;

    /* PCLK1 = HCLK */
    RCC->CFGR |= (uint32_t)RCC_CFGR_PPRE1_DIV1;

    /* Select HSE as system clock source */
    RCC->CFGR &= (uint32_t)((uint32_t)~(RCC_CFGR_SW));
    RCC->CFGR |= (uint32_t)RCC_CFGR_SW_HSE;

    /* Wait till HSE is used as system clock source */
    while ((RCC->CFGR & (uint32_t)RCC_CFGR_SWS) != (uint32_t)0x08)
    {
    }
  }
  else
  {
    /* If HSE fails to start-up, the application will have wrong clock
       configuration. User can add here some code to deal with this error */
  }
}

#elif defined SYSCLK_FREQ_16MHz
/**
  * @brief  Sets System clock frequency to 16MHz and configure HCLK, PCLK2
  *         and PCLK1 prescalers.
  * @note   This function should be used only after reset.
  * @param  None
  * @retval None
  */
static void SetSysClockTo16(void)
{
  __IO uint32_t StartUpCounter = 0, HSEStatus = 0;

  /* SYSCLK, HCLK, PCLK2 and PCLK1 configuration ---------------------------*/
  /* Enable HSE */
  RCC->CR |= ((uint32_t)RCC_CR_HSEON);

  /* Wait till HSE is ready and if Time out is reached exit */
  do
  {
    HSEStatus = RCC->CR & RCC_CR_HSERDY;
    StartUpCounter++;
  } while((HSEStatus == 0) && (StartUpCounter != HSE_STARTUP_TIMEOUT));

  if ((RCC->CR & RCC_CR_HSERDY) != RESET)
  {
    HSEStatus = (uint32_t)0x01;
  }
  else
  {
    HSEStatus = (uint32_t)0x00;
  }

  if (HSEStatus == (uint32_t)0x01)
  {
    /* Enable 64-bit access */
    FLASH->ACR |= FLASH_ACR_ACC64;

    /* Enable Prefetch Buffer */
    FLASH->ACR |= FLASH_ACR_PRFTEN;

    /* Flash 1 wait state */
    FLASH->ACR |= FLASH_ACR_LATENCY;

    /* Enable the PWR APB1 Clock */
    RCC->APB1ENR |= RCC_APB1ENR_PWREN;

    /* Select the Voltage Range 2 (1.5V) */
    PWR->CR = PWR_CR_VOS_1;

    /* Wait Until the Voltage Regulator is ready */
    while((PWR->CSR & PWR_CSR_VOSF) != RESET)
    {
    }

    /* HCLK = SYSCLK */
    RCC->CFGR |= (uint32_t)RCC_CFGR_HPRE_DIV2;

    /* PCLK2 = HCLK */
    RCC->CFGR |= (uint32_t)RCC_CFGR_PPRE2_DIV1;

    /* PCLK1 = HCLK */
    RCC->CFGR |= (uint32_t)RCC_CFGR_PPRE1_DIV1;

    /*  PLL configuration: PLLCLK = (HSE * 12) / 3 = 32MHz */
    RCC->CFGR &= (uint32_t)((uint32_t)~(RCC_CFGR_PLLSRC | RCC_CFGR_PLLMUL |
                                        RCC_CFGR_PLLDIV));
    RCC->CFGR |= (uint32_t)(RCC_CFGR_PLLSRC_HSE | RCC_CFGR_PLLMUL12 | RCC_CFGR_PLLDIV3);

    /* Enable PLL */
    RCC->CR |= RCC_CR_PLLON;

    /* Wait till PLL is ready */
    while((RCC->CR & RCC_CR_PLLRDY) == 0)
    {
    }

    /* Select PLL as system clock source */
    RCC->CFGR &= (uint32_t)((uint32_t)~(RCC_CFGR_SW));
    RCC->CFGR |= (uint32_t)RCC_CFGR_SW_PLL;

    /* Wait till PLL is used as system clock source */
    while ((RCC->CFGR & (uint32_t)RCC_CFGR_SWS) != (uint32_t)0x0C)
    {
    }
  }
  else
  {
    /* If HSE fails to start-up, the application will have wrong clock
       configuration. User can add here some code to deal with this error */
  }
}

#elif defined SYSCLK_FREQ_32MHz
/**
  * @brief  Sets System clock frequency to 32MHz and configure HCLK, PCLK2
  *         and PCLK1 prescalers.
  * @note   This function should be used only after reset.
  * @param  None
  * @retval None
  */
static void SetSysClockTo32(void)
{
  __IO uint32_t StartUpCounter = 0, HSEStatus = 0;

  /* SYSCLK, HCLK, PCLK2 and PCLK1 configuration ---------------------------*/
  /* Enable HSE */
  RCC->CR |= ((uint32_t)RCC_CR_HSEON);

  /* Wait till HSE is ready and if Time out is reached exit */
  do
  {
    HSEStatus = RCC->CR & RCC_CR_HSERDY;
    StartUpCounter++;
  } while((HSEStatus == 0) && (StartUpCounter != HSE_STARTUP_TIMEOUT));

  if ((RCC->CR & RCC_CR_HSERDY) != RESET)
  {
    HSEStatus = (uint32_t)0x01;
  }
  else
  {
    HSEStatus = (uint32_t)0x00;
  }

  if (HSEStatus == (uint32_t)0x01)
  {
    /* Enable 64-bit access */
    FLASH->ACR |= FLASH_ACR_ACC64;

    /* Enable Prefetch Buffer */
    FLASH->ACR |= FLASH_ACR_PRFTEN;

    /* Flash 1 wait state */
    FLASH->ACR |= FLASH_ACR_LATENCY;

    /* Enable the PWR APB1 Clock */
    RCC->APB1ENR |= RCC_APB1ENR_PWREN;

    /* Select the Voltage Range 1 (1.8V) */
    PWR->CR = PWR_CR_VOS_0;

    /* Wait Until the Voltage Regulator is ready */
    while((PWR->CSR & PWR_CSR_VOSF) != RESET)
    {
    }

    /* HCLK = SYSCLK */
    RCC->CFGR |= (uint32_t)RCC_CFGR_HPRE_DIV1;

    /* PCLK2 = HCLK */
    RCC->CFGR |= (uint32_t)RCC_CFGR_PPRE2_DIV1;

    /* PCLK1 = HCLK */
    RCC->CFGR |= (uint32_t)RCC_CFGR_PPRE1_DIV1;

    /*  PLL configuration: PLLCLK = (HSE * 12) / 3 = 32MHz */
    RCC->CFGR &= (uint32_t)((uint32_t)~(RCC_CFGR_PLLSRC | RCC_CFGR_PLLMUL |
                                        RCC_CFGR_PLLDIV));
    RCC->CFGR |= (uint32_t)(RCC_CFGR_PLLSRC_HSE | RCC_CFGR_PLLMUL12 | RCC_CFGR_PLLDIV3);

    /* Enable PLL */
    RCC->CR |= RCC_CR_PLLON;

    /* Wait till PLL is ready */
    while((RCC->CR & RCC_CR_PLLRDY) == 0)
    {
    }

    /* Select PLL as system clock source */
    RCC->CFGR &= (uint32_t)((uint32_t)~(RCC_CFGR_SW));
    RCC->CFGR |= (uint32_t)RCC_CFGR_SW_PLL;

    /* Wait till PLL is used as system clock source */
    while ((RCC->CFGR & (uint32_t)RCC_CFGR_SWS) != (uint32_t)0x0C)
    {
    }
  }
  else
  {
    /* If HSE fails to start-up, the application will have wrong clock
       configuration. User can add here some code to deal with this error */
  }
}

#else
/**
  * @brief  Selects MSI as System clock source and configure HCLK, PCLK2
  *         and PCLK1 prescalers.
  * @note   This function should be used only after reset.
  * @param  None
  * @retval None
  */
static void SetSysClockToMSI(void)
{
  __IO uint32_t StartUpCounter = 0, MSIStatus = 0;

  /* SYSCLK, HCLK, PCLK2 and PCLK1 configuration ---------------------------*/
  /* Enable MSI */
  RCC->CR |= ((uint32_t)RCC_CR_MSION);

  /* Wait till MSI is ready and if Time out is reached exit */
  do
  {
    MSIStatus = RCC->CR & RCC_CR_MSIRDY;
    StartUpCounter++;
  } while((MSIStatus == 0) && (StartUpCounter != HSE_STARTUP_TIMEOUT));

  if ((RCC->CR & RCC_CR_MSIRDY) != RESET)
  {
    MSIStatus = (uint32_t)0x01;
  }
  else
  {
    MSIStatus = (uint32_t)0x00;
  }

  if (MSIStatus == (uint32_t)0x01)
  {
#ifdef SYSCLK_FREQ_MSI
#ifdef SYSCLK_FREQ_MSI_4MHz
    /* Enable 64-bit access */
    FLASH->ACR |= FLASH_ACR_ACC64;

    /* Enable Prefetch Buffer */
    FLASH->ACR |= FLASH_ACR_PRFTEN;

    /* Flash 1 wait state */
    FLASH->ACR |= FLASH_ACR_LATENCY;
#else
    /* Flash 0 wait state */
    FLASH->ACR &= ~FLASH_ACR_LATENCY;

    /* Disable Prefetch Buffer */
    FLASH->ACR &= ~FLASH_ACR_PRFTEN;

    /* Disable 64-bit access */
    FLASH->ACR &= ~FLASH_ACR_ACC64;
#endif
#endif
    /* Enable the PWR APB1 Clock */
    RCC->APB1ENR |= RCC_APB1ENR_PWREN;

    /* Select the Voltage Range 3 (1.2V) */
    PWR->CR = PWR_CR_VOS;

    /* Wait Until the Voltage Regulator is ready */
    while((PWR->CSR & PWR_CSR_VOSF) != RESET)
    {
    }

    /* HCLK = SYSCLK */
    RCC->CFGR |= (uint32_t)RCC_CFGR_HPRE_DIV1;

    /* PCLK2 = HCLK */
    RCC->CFGR |= (uint32_t)RCC_CFGR_PPRE2_DIV1;

    /* PCLK1 = HCLK */
    RCC->CFGR |= (uint32_t)RCC_CFGR_PPRE1_DIV1;

#ifdef SYSCLK_FREQ_MSI
  #ifdef SYSCLK_FREQ_MSI_64KHz
    /* Set MSI clock range */
    RCC->ICSCR &= (uint32_t)((uint32_t)~(RCC_ICSCR_MSIRANGE));
    RCC->ICSCR |= (uint32_t)RCC_ICSCR_MSIRANGE_64KHz;
  #elif defined SYSCLK_FREQ_MSI_128KHz
    /* Set MSI clock range */
    RCC->ICSCR &= (uint32_t)((uint32_t)~(RCC_ICSCR_MSIRANGE));
    RCC->ICSCR |= (uint32_t)RCC_ICSCR_MSIRANGE_128KHz;
  #elif defined SYSCLK_FREQ_MSI_256KHz
    /* Set MSI clock range */
    RCC->ICSCR &= (uint32_t)((uint32_t)~(RCC_ICSCR_MSIRANGE));
    RCC->ICSCR |= (uint32_t)RCC_ICSCR_MSIRANGE_256KHz;
  #elif defined SYSCLK_FREQ_MSI_512KHz
    /* Set MSI clock range */
    RCC->ICSCR &= (uint32_t)((uint32_t)~(RCC_ICSCR_MSIRANGE));
    RCC->ICSCR |= (uint32_t)RCC_ICSCR_MSIRANGE_512KHz;
  #elif defined SYSCLK_FREQ_MSI_1MHz
    /* Set MSI clock range */
    RCC->ICSCR &= (uint32_t)((uint32_t)~(RCC_ICSCR_MSIRANGE));
    RCC->ICSCR |= (uint32_t)RCC_ICSCR_MSIRANGE_1MHz;
  #elif defined SYSCLK_FREQ_MSI_2MHz
    /* Set MSI clock range */
    RCC->ICSCR &= (uint32_t)((uint32_t)~(RCC_ICSCR_MSIRANGE));
    RCC->ICSCR |= (uint32_t)RCC_ICSCR_MSIRANGE_2MHz;
  #elif defined SYSCLK_FREQ_MSI_4MHz
    /* Set MSI clock range */
    RCC->ICSCR &= (uint32_t)((uint32_t)~(RCC_ICSCR_MSIRANGE));
    RCC->ICSCR |= (uint32_t)RCC_ICSCR_MSIRANGE_4MHz;
  #endif
#endif

    /* Select MSI as system clock source */
    RCC->CFGR &= (uint32_t)((uint32_t)~(RCC_CFGR_SW));
    RCC->CFGR |= (uint32_t)RCC_CFGR_SW_MSI;

    /* Wait till MSI is used as system clock source */
    while ((RCC->CFGR & (uint32_t)RCC_CFGR_SWS) != (uint32_t)0x00)
    {
    }
  }
  else
  {
    /* If MSI fails to start-up, the application will have wrong clock
       configuration. User can add here some code to deal with this error */
  }
}
#endif

/**
  * @}
  */

/**
  * @}
  */

/**
  * @}
  */

/******************* (C) COPYRIGHT 2010 STMicroelectronics *****END OF FILE****/
