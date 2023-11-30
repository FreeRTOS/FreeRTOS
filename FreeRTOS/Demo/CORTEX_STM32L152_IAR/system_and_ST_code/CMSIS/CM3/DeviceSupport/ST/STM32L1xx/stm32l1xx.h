/**
  ******************************************************************************
  * @file    stm32l1xx.h
  * @author  STMicroelectronics - MCD Application Team
  * @version V1.0.0RC1
  * @date    07/02/2010
  * @brief   CMSIS Cortex-M3 Device Peripheral Access Layer Header File. 
  *          This file contains all the peripheral register's definitions, bits 
  *          definitions and memory mapping for STM32L1xx devices.  
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

/** @addtogroup stm32l1xx
  * @{
  */
    
#ifndef __STM32L1XX_H
#define __STM32L1XX_H

#ifdef __cplusplus
 extern "C" {
#endif 
  
/** @addtogroup Library_configuration_section
  * @{
  */
  
/* Uncomment the line below according to the target STM32L device used in your 
   application 
  */

#if !defined (STM32L1XX_MD)
  #define STM32L1XX_MD    /*!< STM32L1XX_MD: STM32L Ultra Low Power Medium-density devices */
#endif
/*  Tip: To avoid modifying this file each time you need to switch between these
        devices, you can define the device in your toolchain compiler preprocessor.

 - Ultra Low Power Medium-density devices are STM32L151xx and STM32L152xx 
   microcontrollers where the Flash memory density ranges between 64 and 128 Kbytes.

  */

#if !defined  USE_STDPERIPH_DRIVER
/**
 * @brief Comment the line below if you will not use the peripherals drivers.
   In this case, these drivers will not be included and the application code will 
   be based on direct access to peripherals registers 
   */
  /*#define USE_STDPERIPH_DRIVER*/
#endif

/**
 * @brief In the following line adjust the value of External High Speed oscillator (HSE)
   used in your application 
   
   Tip: To avoid modifying this file each time you need to use different HSE, you
        can define the HSE value in your toolchain compiler preprocessor.
  */  
#define HSE_VALUE    ((uint32_t)8000000) /*!< Value of the External oscillator in Hz*/

/**
 * @brief In the following line adjust the External High Speed oscillator (HSE) Startup 
   Timeout value 
   */
#define HSE_STARTUP_TIMEOUT   ((uint16_t)0x0500) /*!< Time out for HSE start up */

#define MSI_VALUE  ((uint32_t)2000000)  /*!< Default value of the Internal Multi Speed oscillator in Hz */
#define HSI_VALUE  ((uint32_t)16000000) /*!< Value of the Internal High Speed oscillator in Hz */
#define LSI_VALUE  ((uint32_t)37000)    /*!< Value of the Internal Low Speed oscillator in Hz */
#define LSE_VALUE  ((uint32_t)32768)    /*!< Value of the External Low Speed oscillator in Hz */

/**
 * @brief STM32L1xx Standard Peripheral Library version number
   */
#define __STM32L1XX_STDPERIPH_VERSION_MAIN   (0x01) /*!< [31:16] STM32L1xx Standard Peripheral Library main version */                                  
#define __STM32L1XX_STDPERIPH_VERSION_SUB1   (0x00) /*!< [15:8]  STM32L1xx Standard Peripheral Library sub1 version */
#define __STM32L1XX_STDPERIPH_VERSION_SUB2   (0x00) /*!< [7:0]  STM32L1xx Standard Peripheral Library sub2 version */ 
#define __STM32L1XX_STDPERIPH_VERSION       ((__STM32L1XX_STDPERIPH_VERSION_MAIN << 16)\
                                             | (__STM32L1XX_STDPERIPH_VERSION_SUB1 << 8)\
                                             | __STM32L1XX_STDPERIPH_VERSION_SUB2)

/**
  * @}
  */

/** @addtogroup Configuration_section_for_CMSIS
  * @{
  */

/**
 * @brief STM32L1xx Interrupt Number Definition, according to the selected device 
 *        in @ref Library_configuration_section 
 */
#define __MPU_PRESENT             1 /*!< STM32L provide a MPU present */
#define __NVIC_PRIO_BITS          4 /*!< STM32 uses 4 Bits for the Priority Levels    */
#define __Vendor_SysTickConfig    0 /*!< Set to 1 if different SysTick Config is used */

/*!< Interrupt Number Definition */
typedef enum IRQn
{
/******  Cortex-M3 Processor Exceptions Numbers ***************************************************/
  NonMaskableInt_IRQn         = -14,    /*!< 2 Non Maskable Interrupt                             */
  MemoryManagement_IRQn       = -12,    /*!< 4 Cortex-M3 Memory Management Interrupt              */
  BusFault_IRQn               = -11,    /*!< 5 Cortex-M3 Bus Fault Interrupt                      */
  UsageFault_IRQn             = -10,    /*!< 6 Cortex-M3 Usage Fault Interrupt                    */
  SVCall_IRQn                 = -5,     /*!< 11 Cortex-M3 SV Call Interrupt                       */
  DebugMonitor_IRQn           = -4,     /*!< 12 Cortex-M3 Debug Monitor Interrupt                 */
  PendSV_IRQn                 = -2,     /*!< 14 Cortex-M3 Pend SV Interrupt                       */
  SysTick_IRQn                = -1,     /*!< 15 Cortex-M3 System Tick Interrupt                   */

/******  STM32L specific Interrupt Numbers ********************************************************/
  WWDG_IRQn                   = 0,      /*!< Window WatchDog Interrupt                            */
  PVD_IRQn                    = 1,      /*!< PVD through EXTI Line detection Interrupt            */
  TAMPER_STAMP_IRQn           = 2,      /*!< Tamper and Time Stamp through EXTI Line Interrupts   */
  RTC_WKUP_IRQn               = 3,      /*!< RTC Wakeup Timer through EXTI Line Interrupt         */
  FLASH_IRQn                  = 4,      /*!< FLASH global Interrupt                               */
  RCC_IRQn                    = 5,      /*!< RCC global Interrupt                                 */
  EXTI0_IRQn                  = 6,      /*!< EXTI Line0 Interrupt                                 */
  EXTI1_IRQn                  = 7,      /*!< EXTI Line1 Interrupt                                 */
  EXTI2_IRQn                  = 8,      /*!< EXTI Line2 Interrupt                                 */
  EXTI3_IRQn                  = 9,      /*!< EXTI Line3 Interrupt                                 */
  EXTI4_IRQn                  = 10,     /*!< EXTI Line4 Interrupt                                 */
  DMA1_Channel1_IRQn          = 11,     /*!< DMA1 Channel 1 global Interrupt                      */
  DMA1_Channel2_IRQn          = 12,     /*!< DMA1 Channel 2 global Interrupt                      */
  DMA1_Channel3_IRQn          = 13,     /*!< DMA1 Channel 3 global Interrupt                      */
  DMA1_Channel4_IRQn          = 14,     /*!< DMA1 Channel 4 global Interrupt                      */
  DMA1_Channel5_IRQn          = 15,     /*!< DMA1 Channel 5 global Interrupt                      */
  DMA1_Channel6_IRQn          = 16,     /*!< DMA1 Channel 6 global Interrupt                      */
  DMA1_Channel7_IRQn          = 17,     /*!< DMA1 Channel 7 global Interrupt                      */
  ADC1_IRQn                   = 18,     /*!< ADC1 global Interrupt                                */
  USB_HP_IRQn                 = 19,     /*!< USB High Priority Interrupt                          */
  USB_LP_IRQn                 = 20,     /*!< USB Low Priority Interrupt                           */
  DAC_IRQn                    = 21,     /*!< DAC Interrupt                                        */
  COMP_IRQn                   = 22,     /*!< Comparator through EXTI Line Interrupt               */
  EXTI9_5_IRQn                = 23,     /*!< External Line[9:5] Interrupts                        */
  LCD_IRQn                    = 24,     /*!< LCD Interrupt                                        */
  TIM9_IRQn                   = 25,     /*!< TIM9 global Interrupt                                */
  TIM10_IRQn                  = 26,     /*!< TIM10 global Interrupt                               */
  TIM11_IRQn                  = 27,     /*!< TIM11 global Interrupt                               */
  TIM2_IRQn                   = 28,     /*!< TIM2 global Interrupt                                */
  TIM3_IRQn                   = 29,     /*!< TIM3 global Interrupt                                */
  TIM4_IRQn                   = 30,     /*!< TIM4 global Interrupt                                */  
  I2C1_EV_IRQn                = 31,     /*!< I2C1 Event Interrupt                                 */
  I2C1_ER_IRQn                = 32,     /*!< I2C1 Error Interrupt                                 */
  I2C2_EV_IRQn                = 33,     /*!< I2C2 Event Interrupt                                 */
  I2C2_ER_IRQn                = 34,     /*!< I2C2 Error Interrupt                                 */  
  SPI1_IRQn                   = 35,     /*!< SPI1 global Interrupt                                */
  SPI2_IRQn                   = 36,     /*!< SPI2 global Interrupt                                */
  USART1_IRQn                 = 37,     /*!< USART1 global Interrupt                              */
  USART2_IRQn                 = 38,     /*!< USART2 global Interrupt                              */  
  USART3_IRQn                 = 39,     /*!< USART3 global Interrupt                              */  
  EXTI15_10_IRQn              = 40,     /*!< External Line[15:10] Interrupts                      */
  RTC_Alarm_IRQn              = 41,     /*!< RTC Alarm through EXTI Line Interrupt                */
  USB_FS_WKUP_IRQn            = 42,     /*!< USB FS WakeUp from suspend through EXTI Line Interrupt  */
  TIM6_IRQn                   = 43,     /*!< TIM6 global Interrupt                                */
  TIM7_IRQn                   = 44      /*!< TIM7 global Interrupt                                */
} IRQn_Type;

/**
  * @}
  */

#include "core_cm3.h"
#include "system_stm32l1xx.h"
#include <stdint.h>

/** @addtogroup Exported_types
  * @{
  */  

typedef enum {FALSE = 0, TRUE = !FALSE} bool;

typedef enum {RESET = 0, SET = !RESET} FlagStatus, ITStatus;

typedef enum {DISABLE = 0, ENABLE = !DISABLE} FunctionalState;
#define IS_FUNCTIONAL_STATE(STATE) (((STATE) == DISABLE) || ((STATE) == ENABLE))

typedef enum {ERROR = 0, SUCCESS = !ERROR} ErrorStatus;

/**
  * @}
  */

/** @addtogroup Peripheral_registers_structures
  * @{
  */   

/** 
  * @brief Analog to Digital Converter  
  */

typedef struct
{
  __IO uint32_t SR;
  __IO uint32_t CR1;
  __IO uint32_t CR2;
  __IO uint32_t SMPR1;
  __IO uint32_t SMPR2;
  __IO uint32_t SMPR3;
  __IO uint32_t JOFR1;
  __IO uint32_t JOFR2;
  __IO uint32_t JOFR3;
  __IO uint32_t JOFR4;
  __IO uint32_t HTR;
  __IO uint32_t LTR;
  __IO uint32_t SQR1;
  __IO uint32_t SQR2;
  __IO uint32_t SQR3;
  __IO uint32_t SQR4;
  __IO uint32_t SQR5;
  __IO uint32_t JSQR;
  __IO uint32_t JDR1;
  __IO uint32_t JDR2;
  __IO uint32_t JDR3;
  __IO uint32_t JDR4;
  __IO uint32_t DR;
} ADC_TypeDef;

typedef struct
{
  __IO uint32_t CSR;
  __IO uint32_t CCR;
} ADC_Common_TypeDef;


/** 
  * @brief Comparator 
  */

typedef struct
{
  __IO uint32_t CSR;
} COMP_TypeDef;

/** 
  * @brief CRC calculation unit 
  */

typedef struct
{
  __IO uint32_t DR;
  __IO uint8_t  IDR;
  uint8_t   RESERVED0;
  uint16_t  RESERVED1;
  __IO uint32_t CR;
} CRC_TypeDef;

/** 
  * @brief Digital to Analog Converter
  */

typedef struct
{
  __IO uint32_t CR;
  __IO uint32_t SWTRIGR;
  __IO uint32_t DHR12R1;
  __IO uint32_t DHR12L1;
  __IO uint32_t DHR8R1;
  __IO uint32_t DHR12R2;
  __IO uint32_t DHR12L2;
  __IO uint32_t DHR8R2;
  __IO uint32_t DHR12RD;
  __IO uint32_t DHR12LD;
  __IO uint32_t DHR8RD;
  __IO uint32_t DOR1;
  __IO uint32_t DOR2;
  __IO uint32_t SR;  
} DAC_TypeDef;

/** 
  * @brief Debug MCU
  */

typedef struct
{
  __IO uint32_t IDCODE;
  __IO uint32_t CR;
  __IO uint32_t APB1FZ;
  __IO uint32_t APB2FZ;	
}DBGMCU_TypeDef;

/** 
  * @brief DMA Controller
  */

typedef struct
{
  __IO uint32_t CCR;
  __IO uint32_t CNDTR;
  __IO uint32_t CPAR;
  __IO uint32_t CMAR;
} DMA_Channel_TypeDef;

typedef struct
{
  __IO uint32_t ISR;
  __IO uint32_t IFCR;
} DMA_TypeDef;

/** 
  * @brief External Interrupt/Event Controller
  */

typedef struct
{
  __IO uint32_t IMR;
  __IO uint32_t EMR;
  __IO uint32_t RTSR;
  __IO uint32_t FTSR;
  __IO uint32_t SWIER;
  __IO uint32_t PR;
} EXTI_TypeDef;

/** 
  * @brief FLASH Registers
  */

typedef struct
{
  __IO uint32_t ACR;
  __IO uint32_t PECR;
  __IO uint32_t PDKEYR;
  __IO uint32_t PEKEYR;
  __IO uint32_t PRGKEYR;
  __IO uint32_t OPTKEYR;
  __IO uint32_t SR;
  __IO uint32_t OBR;
  __IO uint32_t WRPR;       
} FLASH_TypeDef;

/** 
  * @brief Option Bytes Registers
  */
  
typedef struct
{
  __IO uint32_t RDP;
  __IO uint32_t USER;
  __IO uint32_t WRP01;
  __IO uint32_t WRP23;
} OB_TypeDef;

/** 
  * @brief General Purpose IO
  */

typedef struct
{
  __IO uint32_t MODER;
  __IO uint16_t OTYPER;
  uint16_t RESERVED0;
  __IO uint32_t OSPEEDR;
  __IO uint32_t PUPDR;
  __IO uint16_t IDR;
  uint16_t RESERVED1;
  __IO uint16_t ODR;
  uint16_t RESERVED2;
  __IO uint16_t BSRRL; /* BSRR register is split to 2 * 16-bit fields BSRRL */
  __IO uint16_t BSRRH; /* BSRR register is split to 2 * 16-bit fields BSRRH */
  __IO uint32_t LCKR;
  __IO uint32_t AFR[2];
} GPIO_TypeDef;

/** 
  * @brief SysTem Configuration
  */

typedef struct
{
  __IO uint32_t MEMRMP;
  __IO uint32_t PMC;
  __IO uint32_t EXTICR[4];
} SYSCFG_TypeDef;

/** 
  * @brief Inter-integrated Circuit Interface
  */

typedef struct
{
  __IO uint16_t CR1;
  uint16_t  RESERVED0;
  __IO uint16_t CR2;
  uint16_t  RESERVED1;
  __IO uint16_t OAR1;
  uint16_t  RESERVED2;
  __IO uint16_t OAR2;
  uint16_t  RESERVED3;
  __IO uint16_t DR;
  uint16_t  RESERVED4;
  __IO uint16_t SR1;
  uint16_t  RESERVED5;
  __IO uint16_t SR2;
  uint16_t  RESERVED6;
  __IO uint16_t CCR;
  uint16_t  RESERVED7;
  __IO uint16_t TRISE;
  uint16_t  RESERVED8;
} I2C_TypeDef;

/** 
  * @brief Independent WATCHDOG
  */

typedef struct
{
  __IO uint32_t KR;
  __IO uint32_t PR;
  __IO uint32_t RLR;
  __IO uint32_t SR;
} IWDG_TypeDef;


/** 
  * @brief LCD
  */

typedef struct
{
  __IO uint32_t CR;
  __IO uint32_t FCR;
  __IO uint32_t SR;
  __IO uint32_t CLR;
  uint32_t RESERVED;
  __IO uint32_t RAM[16];
} LCD_TypeDef;

/** 
  * @brief Power Control
  */

typedef struct
{
  __IO uint32_t CR;
  __IO uint32_t CSR;
} PWR_TypeDef;

/** 
  * @brief Reset and Clock Control
  */

typedef struct
{
  __IO uint32_t CR;
  __IO uint32_t ICSCR;
  __IO uint32_t CFGR;
  __IO uint32_t CIR;
  __IO uint32_t AHBRSTR;
  __IO uint32_t APB2RSTR;
  __IO uint32_t APB1RSTR;
  __IO uint32_t AHBENR;
  __IO uint32_t APB2ENR;
  __IO uint32_t APB1ENR;
  __IO uint32_t AHBLPENR;
  __IO uint32_t APB2LPENR;
  __IO uint32_t APB1LPENR;      
  __IO uint32_t CSR;    
} RCC_TypeDef;

/** 
  * @brief Routing Interface 
  */

typedef struct
{
  __IO uint32_t ICR;
  __IO uint32_t ASCR1;
  __IO uint32_t ASCR2;
  __IO uint32_t HYSCR1;
  __IO uint32_t HYSCR2;
  __IO uint32_t HYSCR3;
} RI_TypeDef;

/** 
  * @brief Real-Time Clock
  */

typedef struct
{
  __IO uint32_t TR;
  __IO uint32_t DR;
  __IO uint32_t CR;
  __IO uint32_t ISR;
  __IO uint32_t PRER;
  __IO uint32_t WUTR;
  __IO uint32_t CALIBR;
  __IO uint32_t ALRMAR;
  __IO uint32_t ALRMBR;
  __IO uint32_t WRP;
  uint32_t RESERVED1;
  uint32_t RESERVED2;
  __IO uint32_t TSTR;
  __IO uint32_t TSDR;
  uint32_t RESERVED3;
  uint32_t RESERVED4;
  __IO uint32_t TAFCR;
  uint32_t RESERVED5;
  uint32_t RESERVED6;
  uint32_t RESERVED7;
  __IO uint32_t BK0R;
  __IO uint32_t BK1R;
  __IO uint32_t BK2R;
  __IO uint32_t BK3R;
  __IO uint32_t BK4R;
  __IO uint32_t BK5R;
  __IO uint32_t BK6R;
  __IO uint32_t BK7R;
  __IO uint32_t BK8R;
  __IO uint32_t BK9R;
  __IO uint32_t BK10R;
  __IO uint32_t BK11R;
  __IO uint32_t BK12R;
  __IO uint32_t BK13R;
  __IO uint32_t BK14R;
  __IO uint32_t BK15R;
  __IO uint32_t BK16R;
  __IO uint32_t BK17R;
  __IO uint32_t BK18R;
  __IO uint32_t BK19R;
} RTC_TypeDef;

/** 
  * @brief Serial Peripheral Interface
  */

typedef struct
{
  __IO uint16_t CR1;
  uint16_t  RESERVED0;
  __IO uint16_t CR2;
  uint16_t  RESERVED1;
  __IO uint16_t SR;
  uint16_t  RESERVED2;
  __IO uint16_t DR;
  uint16_t  RESERVED3;
  __IO uint16_t CRCPR;
  uint16_t  RESERVED4;
  __IO uint16_t RXCRCR;
  uint16_t  RESERVED5;
  __IO uint16_t TXCRCR;
  uint16_t  RESERVED6;  
} SPI_TypeDef;

/** 
  * @brief TIM
  */

typedef struct
{
  __IO uint16_t CR1;
  uint16_t  RESERVED0;
  __IO uint16_t CR2;
  uint16_t  RESERVED1;
  __IO uint16_t SMCR;
  uint16_t  RESERVED2;
  __IO uint16_t DIER;
  uint16_t  RESERVED3;
  __IO uint16_t SR;
  uint16_t  RESERVED4;
  __IO uint16_t EGR;
  uint16_t  RESERVED5;
  __IO uint16_t CCMR1;
  uint16_t  RESERVED6;
  __IO uint16_t CCMR2;
  uint16_t  RESERVED7;
  __IO uint16_t CCER;
  uint16_t  RESERVED8;
  __IO uint16_t CNT;
  uint16_t  RESERVED9;
  __IO uint16_t PSC;
  uint16_t  RESERVED10;
  __IO uint16_t ARR;
  uint16_t  RESERVED11;
  uint32_t  RESERVED12;
  __IO uint16_t CCR1;
  uint16_t  RESERVED13;
  __IO uint16_t CCR2;
  uint16_t  RESERVED14;
  __IO uint16_t CCR3;
  uint16_t  RESERVED15;
  __IO uint16_t CCR4;
  uint16_t  RESERVED16;
  uint32_t  RESERVED17;
  __IO uint16_t DCR;
  uint16_t  RESERVED18;
  __IO uint16_t DMAR;
  uint16_t  RESERVED19;
  __IO uint16_t OR;
  uint16_t  RESERVED20;
} TIM_TypeDef;

/** 
  * @brief Universal Synchronous Asynchronous Receiver Transmitter
  */
 
typedef struct
{
  __IO uint16_t SR;
  uint16_t  RESERVED0;
  __IO uint16_t DR;
  uint16_t  RESERVED1;
  __IO uint16_t BRR;
  uint16_t  RESERVED2;
  __IO uint16_t CR1;
  uint16_t  RESERVED3;
  __IO uint16_t CR2;
  uint16_t  RESERVED4;
  __IO uint16_t CR3;
  uint16_t  RESERVED5;
  __IO uint16_t GTPR;
  uint16_t  RESERVED6;
} USART_TypeDef;

/** 
  * @brief Window WATCHDOG
  */

typedef struct
{
  __IO uint32_t CR;
  __IO uint32_t CFR;
  __IO uint32_t SR;
} WWDG_TypeDef;

/**
  * @}
  */
  
/** @addtogroup Peripheral_memory_map
  * @{
  */

#define PERIPH_BB_BASE        ((uint32_t)0x42000000) /*!< Peripheral base address in the alias region */
#define SRAM_BB_BASE          ((uint32_t)0x22000000) /*!< SRAM base address in the alias region */

#define SRAM_BASE             ((uint32_t)0x20000000) /*!< SRAM base address in the bit-band region */
#define PERIPH_BASE           ((uint32_t)0x40000000) /*!< Peripheral base address in the bit-band region */

/*!< Peripheral memory map */
#define APB1PERIPH_BASE       PERIPH_BASE
#define APB2PERIPH_BASE       (PERIPH_BASE + 0x10000)
#define AHBPERIPH_BASE        (PERIPH_BASE + 0x20000)

#define TIM2_BASE             (APB1PERIPH_BASE + 0x0000)
#define TIM3_BASE             (APB1PERIPH_BASE + 0x0400)
#define TIM4_BASE             (APB1PERIPH_BASE + 0x0800)
#define TIM6_BASE             (APB1PERIPH_BASE + 0x1000)
#define TIM7_BASE             (APB1PERIPH_BASE + 0x1400)
#define LCD_BASE              (APB1PERIPH_BASE + 0x2400)
#define RTC_BASE              (APB1PERIPH_BASE + 0x2800)
#define WWDG_BASE             (APB1PERIPH_BASE + 0x2C00)
#define IWDG_BASE             (APB1PERIPH_BASE + 0x3000)
#define SPI2_BASE             (APB1PERIPH_BASE + 0x3800)
#define USART2_BASE           (APB1PERIPH_BASE + 0x4400)
#define USART3_BASE           (APB1PERIPH_BASE + 0x4800)
#define I2C1_BASE             (APB1PERIPH_BASE + 0x5400)
#define I2C2_BASE             (APB1PERIPH_BASE + 0x5800)
#define PWR_BASE              (APB1PERIPH_BASE + 0x7000)
#define DAC_BASE              (APB1PERIPH_BASE + 0x7400)
#define COMP_BASE             (APB1PERIPH_BASE + 0x7C00)
#define RI_BASE               (APB1PERIPH_BASE + 0x7C04)

#define SYSCFG_BASE           (APB2PERIPH_BASE + 0x0000)
#define EXTI_BASE             (APB2PERIPH_BASE + 0x0400)
#define TIM9_BASE             (APB2PERIPH_BASE + 0x0800)
#define TIM10_BASE            (APB2PERIPH_BASE + 0x0C00)
#define TIM11_BASE            (APB2PERIPH_BASE + 0x1000)
#define ADC1_BASE             (APB2PERIPH_BASE + 0x2400)
#define ADC_BASE              (APB2PERIPH_BASE + 0x2700)
#define SPI1_BASE             (APB2PERIPH_BASE + 0x3000)
#define USART1_BASE           (APB2PERIPH_BASE + 0x3800)

#define GPIOA_BASE            (AHBPERIPH_BASE + 0x0000)
#define GPIOB_BASE            (AHBPERIPH_BASE + 0x0400)
#define GPIOC_BASE            (AHBPERIPH_BASE + 0x0800)
#define GPIOD_BASE            (AHBPERIPH_BASE + 0x0C00)
#define GPIOE_BASE            (AHBPERIPH_BASE + 0x1000)
#define GPIOH_BASE            (AHBPERIPH_BASE + 0x1400)
#define CRC_BASE              (AHBPERIPH_BASE + 0x3000)
#define RCC_BASE              (AHBPERIPH_BASE + 0x3800)


#define FLASH_R_BASE          (AHBPERIPH_BASE + 0x3C00) /*!< FLASH registers base address */
#define OB_BASE               ((uint32_t)0x1FF80000)    /*!< FLASH Option Bytes base address */

#define DMA1_BASE             (AHBPERIPH_BASE + 0x6000)
#define DMA1_Channel1_BASE    (DMA1_BASE + 0x0008)
#define DMA1_Channel2_BASE    (DMA1_BASE + 0x001C)
#define DMA1_Channel3_BASE    (DMA1_BASE + 0x0030)
#define DMA1_Channel4_BASE    (DMA1_BASE + 0x0044)
#define DMA1_Channel5_BASE    (DMA1_BASE + 0x0058)
#define DMA1_Channel6_BASE    (DMA1_BASE + 0x006C)
#define DMA1_Channel7_BASE    (DMA1_BASE + 0x0080)


#define DBGMCU_BASE           ((uint32_t)0xE0042000) /*!< Debug MCU registers base address */

/**
  * @}
  */
  
/** @addtogroup Peripheral_declaration
  * @{
  */  

#define TIM2                ((TIM_TypeDef *) TIM2_BASE)
#define TIM3                ((TIM_TypeDef *) TIM3_BASE)
#define TIM4                ((TIM_TypeDef *) TIM4_BASE)
#define TIM6                ((TIM_TypeDef *) TIM6_BASE)
#define TIM7                ((TIM_TypeDef *) TIM7_BASE)
#define LCD                 ((LCD_TypeDef *) LCD_BASE)
#define RTC                 ((RTC_TypeDef *) RTC_BASE)
#define WWDG                ((WWDG_TypeDef *) WWDG_BASE)
#define IWDG                ((IWDG_TypeDef *) IWDG_BASE)
#define SPI2                ((SPI_TypeDef *) SPI2_BASE)
#define USART2              ((USART_TypeDef *) USART2_BASE)
#define USART3              ((USART_TypeDef *) USART3_BASE)
#define I2C1                ((I2C_TypeDef *) I2C1_BASE)
#define I2C2                ((I2C_TypeDef *) I2C2_BASE)
#define PWR                 ((PWR_TypeDef *) PWR_BASE)
#define DAC                 ((DAC_TypeDef *) DAC_BASE)
#define COMP                ((COMP_TypeDef *) COMP_BASE)
#define RI                  ((RI_TypeDef *) RI_BASE)
#define SYSCFG              ((SYSCFG_TypeDef *) SYSCFG_BASE)
#define EXTI                ((EXTI_TypeDef *) EXTI_BASE)

#define ADC1                ((ADC_TypeDef *) ADC1_BASE)
#define ADC                 ((ADC_Common_TypeDef *) ADC_BASE)
#define TIM9                ((TIM_TypeDef *) TIM9_BASE)
#define TIM10               ((TIM_TypeDef *) TIM10_BASE)
#define TIM11               ((TIM_TypeDef *) TIM11_BASE)
#define SPI1                ((SPI_TypeDef *) SPI1_BASE)
#define USART1              ((USART_TypeDef *) USART1_BASE)
#define DMA1                ((DMA_TypeDef *) DMA1_BASE)
#define DMA1_Channel1       ((DMA_Channel_TypeDef *) DMA1_Channel1_BASE)
#define DMA1_Channel2       ((DMA_Channel_TypeDef *) DMA1_Channel2_BASE)
#define DMA1_Channel3       ((DMA_Channel_TypeDef *) DMA1_Channel3_BASE)
#define DMA1_Channel4       ((DMA_Channel_TypeDef *) DMA1_Channel4_BASE)
#define DMA1_Channel5       ((DMA_Channel_TypeDef *) DMA1_Channel5_BASE)
#define DMA1_Channel6       ((DMA_Channel_TypeDef *) DMA1_Channel6_BASE)
#define DMA1_Channel7       ((DMA_Channel_TypeDef *) DMA1_Channel7_BASE)
#define RCC                 ((RCC_TypeDef *) RCC_BASE)
#define CRC                 ((CRC_TypeDef *) CRC_BASE)

#define GPIOA               ((GPIO_TypeDef *) GPIOA_BASE)
#define GPIOB               ((GPIO_TypeDef *) GPIOB_BASE)
#define GPIOC               ((GPIO_TypeDef *) GPIOC_BASE)
#define GPIOD               ((GPIO_TypeDef *) GPIOD_BASE)
#define GPIOE               ((GPIO_TypeDef *) GPIOE_BASE)
#define GPIOH               ((GPIO_TypeDef *) GPIOH_BASE)

#define FLASH               ((FLASH_TypeDef *) FLASH_R_BASE)
#define OB                  ((OB_TypeDef *) OB_BASE) 

#define DBGMCU              ((DBGMCU_TypeDef *) DBGMCU_BASE)

/**
  * @}
  */

/** @addtogroup Exported_constants
  * @{
  */
  
  /** @addtogroup Peripheral_Registers_Bits_Definition
  * @{
  */
    
/******************************************************************************/
/*                         Peripheral Registers_Bits_Definition               */
/******************************************************************************/
/******************************************************************************/
/*                                                                            */
/*                        Analog to Digital Converter                         */
/*                                                                            */
/******************************************************************************/

/********************  Bit definition for ADC_SR register  ********************/
#define  ADC_SR_AWD                          ((uint32_t)0x00000001)        /*!< Analog watchdog flag */
#define  ADC_SR_EOC                          ((uint32_t)0x00000002)        /*!< End of conversion */
#define  ADC_SR_JEOC                         ((uint32_t)0x00000004)        /*!< Injected channel end of conversion */
#define  ADC_SR_JSTRT                        ((uint32_t)0x00000008)        /*!< Injected channel Start flag */
#define  ADC_SR_STRT                         ((uint32_t)0x00000010)        /*!< Regular channel Start flag */
#define  ADC_SR_OVR                          ((uint32_t)0x00000020)        /*!< Overrun flag */
#define  ADC_SR_ADONS                        ((uint32_t)0x00000040)        /*!< ADC ON status */
#define  ADC_SR_RCNR                         ((uint32_t)0x00000100)        /*!< Regular channel not ready flag */
#define  ADC_SR_JCNR                         ((uint32_t)0x00000200)        /*!< Injected channel not ready flag */

/*******************  Bit definition for ADC_CR1 register  ********************/
#define  ADC_CR1_AWDCH                       ((uint32_t)0x0000001F)        /*!< AWDCH[4:0] bits (Analog watchdog channel select bits) */
#define  ADC_CR1_AWDCH_0                     ((uint32_t)0x00000001)        /*!< Bit 0 */
#define  ADC_CR1_AWDCH_1                     ((uint32_t)0x00000002)        /*!< Bit 1 */
#define  ADC_CR1_AWDCH_2                     ((uint32_t)0x00000004)        /*!< Bit 2 */
#define  ADC_CR1_AWDCH_3                     ((uint32_t)0x00000008)        /*!< Bit 3 */
#define  ADC_CR1_AWDCH_4                     ((uint32_t)0x00000010)        /*!< Bit 4 */

#define  ADC_CR1_EOCIE                       ((uint32_t)0x00000020)        /*!< Interrupt enable for EOC */
#define  ADC_CR1_AWDIE                       ((uint32_t)0x00000040)        /*!< Analog Watchdog interrupt enable */
#define  ADC_CR1_JEOCIE                      ((uint32_t)0x00000080)        /*!< Interrupt enable for injected channels */
#define  ADC_CR1_SCAN                        ((uint32_t)0x00000100)        /*!< Scan mode */
#define  ADC_CR1_AWDSGL                      ((uint32_t)0x00000200)        /*!< Enable the watchdog on a single channel in scan mode */
#define  ADC_CR1_JAUTO                       ((uint32_t)0x00000400)        /*!< Automatic injected group conversion */
#define  ADC_CR1_DISCEN                      ((uint32_t)0x00000800)        /*!< Discontinuous mode on regular channels */
#define  ADC_CR1_JDISCEN                     ((uint32_t)0x00001000)        /*!< Discontinuous mode on injected channels */

#define  ADC_CR1_DISCNUM                     ((uint32_t)0x0000E000)        /*!< DISCNUM[2:0] bits (Discontinuous mode channel count) */
#define  ADC_CR1_DISCNUM_0                   ((uint32_t)0x00002000)        /*!< Bit 0 */
#define  ADC_CR1_DISCNUM_1                   ((uint32_t)0x00004000)        /*!< Bit 1 */
#define  ADC_CR1_DISCNUM_2                   ((uint32_t)0x00008000)        /*!< Bit 2 */

#define  ADC_CR1_PDD                         ((uint32_t)0x00010000)        /*!< Power Down during Delay phase */
#define  ADC_CR1_PDI                         ((uint32_t)0x00020000)        /*!< Power Down during Idle phase */

#define  ADC_CR1_JAWDEN                      ((uint32_t)0x00400000)        /*!< Analog watchdog enable on injected channels */
#define  ADC_CR1_AWDEN                       ((uint32_t)0x00800000)        /*!< Analog watchdog enable on regular channels */

#define  ADC_CR1_RES                         ((uint32_t)0x03000000)        /*!< RES[1:0] bits (Resolution) */
#define  ADC_CR1_RES_0                       ((uint32_t)0x01000000)        /*!< Bit 0 */
#define  ADC_CR1_RES_1                       ((uint32_t)0x02000000)        /*!< Bit 1 */

#define  ADC_CR1_OVRIE                       ((uint32_t)0x04000000)        /*!< Overrun interrupt enable */
  
/*******************  Bit definition for ADC_CR2 register  ********************/
#define  ADC_CR2_ADON                        ((uint32_t)0x00000001)        /*!< A/D Converter ON / OFF */
#define  ADC_CR2_CONT                        ((uint32_t)0x00000002)        /*!< Continuous Conversion */

#define  ADC_CR2_DELS                        ((uint32_t)0x00000070)        /*!< DELS[2:0] bits (Delay selection) */
#define  ADC_CR2_DELS_0                      ((uint32_t)0x00000010)        /*!< Bit 0 */
#define  ADC_CR2_DELS_1                      ((uint32_t)0x00000020)        /*!< Bit 1 */
#define  ADC_CR2_DELS_2                      ((uint32_t)0x00000040)        /*!< Bit 2 */

#define  ADC_CR2_DMA                         ((uint32_t)0x00000100)        /*!< Direct Memory access mode */
#define  ADC_CR2_DDS                         ((uint32_t)0x00000200)        /*!< DMA disable selection (Single ADC) */
#define  ADC_CR2_EOCS                        ((uint32_t)0x00000400)        /*!< End of conversion selection */
#define  ADC_CR2_ALIGN                       ((uint32_t)0x00000800)        /*!< Data Alignment */

#define  ADC_CR2_JEXTSEL                     ((uint32_t)0x000F0000)        /*!< JEXTSEL[3:0] bits (External event select for injected group) */
#define  ADC_CR2_JEXTSEL_0                   ((uint32_t)0x00010000)        /*!< Bit 0 */
#define  ADC_CR2_JEXTSEL_1                   ((uint32_t)0x00020000)        /*!< Bit 1 */
#define  ADC_CR2_JEXTSEL_2                   ((uint32_t)0x00040000)        /*!< Bit 2 */
#define  ADC_CR2_JEXTSEL_3                   ((uint32_t)0x00080000)        /*!< Bit 3 */

#define  ADC_CR2_JEXTEN                      ((uint32_t)0x00300000)        /*!< JEXTEN[1:0] bits (External Trigger Conversion mode for injected channels) */
#define  ADC_CR2_JEXTEN_0                    ((uint32_t)0x00100000)        /*!< Bit 0 */
#define  ADC_CR2_JEXTEN_1                    ((uint32_t)0x00200000)        /*!< Bit 1 */

#define  ADC_CR2_JSWSTART                    ((uint32_t)0x00400000)        /*!< Start Conversion of injected channels */

#define  ADC_CR2_EXTSEL                      ((uint32_t)0x0F000000)        /*!< EXTSEL[3:0] bits (External Event Select for regular group) */
#define  ADC_CR2_EXTSEL_0                    ((uint32_t)0x01000000)        /*!< Bit 0 */
#define  ADC_CR2_EXTSEL_1                    ((uint32_t)0x02000000)        /*!< Bit 1 */
#define  ADC_CR2_EXTSEL_2                    ((uint32_t)0x04000000)        /*!< Bit 2 */
#define  ADC_CR2_EXTSEL_3                    ((uint32_t)0x08000000)        /*!< Bit 3 */

#define  ADC_CR2_EXTEN                       ((uint32_t)0x30000000)        /*!< EXTEN[1:0] bits (External Trigger Conversion mode for regular channels) */
#define  ADC_CR2_EXTEN_0                     ((uint32_t)0x10000000)        /*!< Bit 0 */
#define  ADC_CR2_EXTEN_1                     ((uint32_t)0x20000000)        /*!< Bit 1 */

#define  ADC_CR2_SWSTART                     ((uint32_t)0x40000000)        /*!< Start Conversion of regular channels */

/******************  Bit definition for ADC_SMPR1 register  *******************/
#define  ADC_SMPR1_SMP20                     ((uint32_t)0x00000007)        /*!< SMP20[2:0] bits (Channel 20 Sample time selection) */
#define  ADC_SMPR1_SMP20_0                   ((uint32_t)0x00000001)        /*!< Bit 0 */
#define  ADC_SMPR1_SMP20_1                   ((uint32_t)0x00000002)        /*!< Bit 1 */
#define  ADC_SMPR1_SMP20_2                   ((uint32_t)0x00000004)        /*!< Bit 2 */

#define  ADC_SMPR1_SMP21                     ((uint32_t)0x00000038)        /*!< SMP21[2:0] bits (Channel 21 Sample time selection) */
#define  ADC_SMPR1_SMP21_0                   ((uint32_t)0x00000008)        /*!< Bit 0 */
#define  ADC_SMPR1_SMP21_1                   ((uint32_t)0x00000010)        /*!< Bit 1 */
#define  ADC_SMPR1_SMP21_2                   ((uint32_t)0x00000020)        /*!< Bit 2 */

#define  ADC_SMPR1_SMP22                     ((uint32_t)0x000001C0)        /*!< SMP22[2:0] bits (Channel 22 Sample time selection) */
#define  ADC_SMPR1_SMP22_0                   ((uint32_t)0x00000040)        /*!< Bit 0 */
#define  ADC_SMPR1_SMP22_1                   ((uint32_t)0x00000080)        /*!< Bit 1 */
#define  ADC_SMPR1_SMP22_2                   ((uint32_t)0x00000100)        /*!< Bit 2 */

#define  ADC_SMPR1_SMP23                     ((uint32_t)0x00000E00)        /*!< SMP23[2:0] bits (Channel 23 Sample time selection) */
#define  ADC_SMPR1_SMP23_0                   ((uint32_t)0x00000200)        /*!< Bit 0 */
#define  ADC_SMPR1_SMP23_1                   ((uint32_t)0x00000400)        /*!< Bit 1 */
#define  ADC_SMPR1_SMP23_2                   ((uint32_t)0x00000800)        /*!< Bit 2 */

#define  ADC_SMPR1_SMP24                     ((uint32_t)0x00007000)        /*!< SMP24[2:0] bits (Channel 24 Sample time selection) */
#define  ADC_SMPR1_SMP24_0                   ((uint32_t)0x00001000)        /*!< Bit 0 */
#define  ADC_SMPR1_SMP24_1                   ((uint32_t)0x00002000)        /*!< Bit 1 */
#define  ADC_SMPR1_SMP24_2                   ((uint32_t)0x00004000)        /*!< Bit 2 */

#define  ADC_SMPR1_SMP25                     ((uint32_t)0x00038000)        /*!< SMP25[2:0] bits (Channel 25 Sample time selection) */
#define  ADC_SMPR1_SMP25_0                   ((uint32_t)0x00008000)        /*!< Bit 0 */
#define  ADC_SMPR1_SMP25_1                   ((uint32_t)0x00010000)        /*!< Bit 1 */
#define  ADC_SMPR1_SMP25_2                   ((uint32_t)0x00020000)        /*!< Bit 2 */

/******************  Bit definition for ADC_SMPR2 register  *******************/
#define  ADC_SMPR2_SMP10                     ((uint32_t)0x00000007)        /*!< SMP10[2:0] bits (Channel 10 Sample time selection) */
#define  ADC_SMPR2_SMP10_0                   ((uint32_t)0x00000001)        /*!< Bit 0 */
#define  ADC_SMPR2_SMP10_1                   ((uint32_t)0x00000002)        /*!< Bit 1 */
#define  ADC_SMPR2_SMP10_2                   ((uint32_t)0x00000004)        /*!< Bit 2 */

#define  ADC_SMPR2_SMP11                     ((uint32_t)0x00000038)        /*!< SMP11[2:0] bits (Channel 11 Sample time selection) */
#define  ADC_SMPR2_SMP11_0                   ((uint32_t)0x00000008)        /*!< Bit 0 */
#define  ADC_SMPR2_SMP11_1                   ((uint32_t)0x00000010)        /*!< Bit 1 */
#define  ADC_SMPR2_SMP11_2                   ((uint32_t)0x00000020)        /*!< Bit 2 */

#define  ADC_SMPR2_SMP12                     ((uint32_t)0x000001C0)        /*!< SMP12[2:0] bits (Channel 12 Sample time selection) */
#define  ADC_SMPR2_SMP12_0                   ((uint32_t)0x00000040)        /*!< Bit 0 */
#define  ADC_SMPR2_SMP12_1                   ((uint32_t)0x00000080)        /*!< Bit 1 */
#define  ADC_SMPR2_SMP12_2                   ((uint32_t)0x00000100)        /*!< Bit 2 */

#define  ADC_SMPR2_SMP13                     ((uint32_t)0x00000E00)        /*!< SMP13[2:0] bits (Channel 13 Sample time selection) */
#define  ADC_SMPR2_SMP13_0                   ((uint32_t)0x00000200)        /*!< Bit 0 */
#define  ADC_SMPR2_SMP13_1                   ((uint32_t)0x00000400)        /*!< Bit 1 */
#define  ADC_SMPR2_SMP13_2                   ((uint32_t)0x00000800)        /*!< Bit 2 */

#define  ADC_SMPR2_SMP14                     ((uint32_t)0x00007000)        /*!< SMP14[2:0] bits (Channel 14 Sample time selection) */
#define  ADC_SMPR2_SMP14_0                   ((uint32_t)0x00001000)        /*!< Bit 0 */
#define  ADC_SMPR2_SMP14_1                   ((uint32_t)0x00002000)        /*!< Bit 1 */
#define  ADC_SMPR2_SMP14_2                   ((uint32_t)0x00004000)        /*!< Bit 2 */

#define  ADC_SMPR2_SMP15                     ((uint32_t)0x00038000)        /*!< SMP15[2:0] bits (Channel 5 Sample time selection) */
#define  ADC_SMPR2_SMP15_0                   ((uint32_t)0x00008000)        /*!< Bit 0 */
#define  ADC_SMPR2_SMP15_1                   ((uint32_t)0x00010000)        /*!< Bit 1 */
#define  ADC_SMPR2_SMP15_2                   ((uint32_t)0x00020000)        /*!< Bit 2 */

#define  ADC_SMPR2_SMP16                     ((uint32_t)0x001C0000)        /*!< SMP16[2:0] bits (Channel 16 Sample time selection) */
#define  ADC_SMPR2_SMP16_0                   ((uint32_t)0x00040000)        /*!< Bit 0 */
#define  ADC_SMPR2_SMP16_1                   ((uint32_t)0x00080000)        /*!< Bit 1 */
#define  ADC_SMPR2_SMP16_2                   ((uint32_t)0x00100000)        /*!< Bit 2 */

#define  ADC_SMPR2_SMP17                     ((uint32_t)0x00E00000)        /*!< SMP17[2:0] bits (Channel 17 Sample time selection) */
#define  ADC_SMPR2_SMP17_0                   ((uint32_t)0x00200000)        /*!< Bit 0 */
#define  ADC_SMPR2_SMP17_1                   ((uint32_t)0x00400000)        /*!< Bit 1 */
#define  ADC_SMPR2_SMP17_2                   ((uint32_t)0x00800000)        /*!< Bit 2 */

#define  ADC_SMPR2_SMP18                     ((uint32_t)0x07000000)        /*!< SMP18[2:0] bits (Channel 18 Sample time selection) */
#define  ADC_SMPR2_SMP18_0                   ((uint32_t)0x01000000)        /*!< Bit 0 */
#define  ADC_SMPR2_SMP18_1                   ((uint32_t)0x02000000)        /*!< Bit 1 */
#define  ADC_SMPR2_SMP18_2                   ((uint32_t)0x04000000)        /*!< Bit 2 */

#define  ADC_SMPR2_SMP19                     ((uint32_t)0x38000000)        /*!< SMP19[2:0] bits (Channel 19 Sample time selection) */
#define  ADC_SMPR2_SMP19_0                   ((uint32_t)0x08000000)        /*!< Bit 0 */
#define  ADC_SMPR2_SMP19_1                   ((uint32_t)0x10000000)        /*!< Bit 1 */
#define  ADC_SMPR2_SMP19_2                   ((uint32_t)0x20000000)        /*!< Bit 2 */

/******************  Bit definition for ADC_SMPR3 register  *******************/
#define  ADC_SMPR3_SMP0                      ((uint32_t)0x00000007)        /*!< SMP0[2:0] bits (Channel 0 Sample time selection) */
#define  ADC_SMPR3_SMP0_0                    ((uint32_t)0x00000001)        /*!< Bit 0 */
#define  ADC_SMPR3_SMP0_1                    ((uint32_t)0x00000002)        /*!< Bit 1 */
#define  ADC_SMPR3_SMP0_2                    ((uint32_t)0x00000004)        /*!< Bit 2 */
 
#define  ADC_SMPR3_SMP1                      ((uint32_t)0x00000038)        /*!< SMP1[2:0] bits (Channel 1 Sample time selection) */
#define  ADC_SMPR3_SMP1_0                    ((uint32_t)0x00000008)        /*!< Bit 0 */
#define  ADC_SMPR3_SMP1_1                    ((uint32_t)0x00000010)        /*!< Bit 1 */
#define  ADC_SMPR3_SMP1_2                    ((uint32_t)0x00000020)        /*!< Bit 2 */

#define  ADC_SMPR3_SMP2                      ((uint32_t)0x000001C0)        /*!< SMP2[2:0] bits (Channel 2 Sample time selection) */
#define  ADC_SMPR3_SMP2_0                    ((uint32_t)0x00000040)        /*!< Bit 0 */
#define  ADC_SMPR3_SMP2_1                    ((uint32_t)0x00000080)        /*!< Bit 1 */
#define  ADC_SMPR3_SMP2_2                    ((uint32_t)0x00000100)        /*!< Bit 2 */

#define  ADC_SMPR3_SMP3                      ((uint32_t)0x00000E00)        /*!< SMP3[2:0] bits (Channel 3 Sample time selection) */
#define  ADC_SMPR3_SMP3_0                    ((uint32_t)0x00000200)        /*!< Bit 0 */
#define  ADC_SMPR3_SMP3_1                    ((uint32_t)0x00000400)        /*!< Bit 1 */
#define  ADC_SMPR3_SMP3_2                    ((uint32_t)0x00000800)        /*!< Bit 2 */

#define  ADC_SMPR3_SMP4                      ((uint32_t)0x00007000)        /*!< SMP4[2:0] bits (Channel 4 Sample time selection) */
#define  ADC_SMPR3_SMP4_0                    ((uint32_t)0x00001000)        /*!< Bit 0 */
#define  ADC_SMPR3_SMP4_1                    ((uint32_t)0x00002000)        /*!< Bit 1 */
#define  ADC_SMPR3_SMP4_2                    ((uint32_t)0x00004000)        /*!< Bit 2 */

#define  ADC_SMPR3_SMP5                      ((uint32_t)0x00038000)        /*!< SMP5[2:0] bits (Channel 5 Sample time selection) */
#define  ADC_SMPR3_SMP5_0                    ((uint32_t)0x00008000)        /*!< Bit 0 */
#define  ADC_SMPR3_SMP5_1                    ((uint32_t)0x00010000)        /*!< Bit 1 */
#define  ADC_SMPR3_SMP5_2                    ((uint32_t)0x00020000)        /*!< Bit 2 */

#define  ADC_SMPR3_SMP6                      ((uint32_t)0x001C0000)        /*!< SMP6[2:0] bits (Channel 6 Sample time selection) */
#define  ADC_SMPR3_SMP6_0                    ((uint32_t)0x00040000)        /*!< Bit 0 */
#define  ADC_SMPR3_SMP6_1                    ((uint32_t)0x00080000)        /*!< Bit 1 */
#define  ADC_SMPR3_SMP6_2                    ((uint32_t)0x00100000)        /*!< Bit 2 */

#define  ADC_SMPR3_SMP7                      ((uint32_t)0x00E00000)        /*!< SMP7[2:0] bits (Channel 7 Sample time selection) */
#define  ADC_SMPR3_SMP7_0                    ((uint32_t)0x00200000)        /*!< Bit 0 */
#define  ADC_SMPR3_SMP7_1                    ((uint32_t)0x00400000)        /*!< Bit 1 */
#define  ADC_SMPR3_SMP7_2                    ((uint32_t)0x00800000)        /*!< Bit 2 */

#define  ADC_SMPR3_SMP8                      ((uint32_t)0x07000000)        /*!< SMP8[2:0] bits (Channel 8 Sample time selection) */
#define  ADC_SMPR3_SMP8_0                    ((uint32_t)0x01000000)        /*!< Bit 0 */
#define  ADC_SMPR3_SMP8_1                    ((uint32_t)0x02000000)        /*!< Bit 1 */
#define  ADC_SMPR3_SMP8_2                    ((uint32_t)0x04000000)        /*!< Bit 2 */

#define  ADC_SMPR3_SMP9                      ((uint32_t)0x38000000)        /*!< SMP9[2:0] bits (Channel 9 Sample time selection) */
#define  ADC_SMPR3_SMP9_0                    ((uint32_t)0x08000000)        /*!< Bit 0 */
#define  ADC_SMPR3_SMP9_1                    ((uint32_t)0x10000000)        /*!< Bit 1 */
#define  ADC_SMPR3_SMP9_2                    ((uint32_t)0x20000000)        /*!< Bit 2 */


/******************  Bit definition for ADC_JOFR1 register  *******************/
#define  ADC_JOFR1_JOFFSET1                  ((uint32_t)0x00000FFF)        /*!< Data offset for injected channel 1 */

/******************  Bit definition for ADC_JOFR2 register  *******************/
#define  ADC_JOFR2_JOFFSET2                  ((uint32_t)0x00000FFF)        /*!< Data offset for injected channel 2 */

/******************  Bit definition for ADC_JOFR3 register  *******************/
#define  ADC_JOFR3_JOFFSET3                  ((uint32_t)0x00000FFF)        /*!< Data offset for injected channel 3 */

/******************  Bit definition for ADC_JOFR4 register  *******************/
#define  ADC_JOFR4_JOFFSET4                  ((uint32_t)0x00000FFF)        /*!< Data offset for injected channel 4 */

/*******************  Bit definition for ADC_HTR register  ********************/
#define  ADC_HTR_HT                          ((uint32_t)0x00000FFF)        /*!< Analog watchdog high threshold */

/*******************  Bit definition for ADC_LTR register  ********************/
#define  ADC_LTR_LT                          ((uint32_t)0x00000FFF)         /*!< Analog watchdog low threshold */

/*******************  Bit definition for ADC_SQR1 register  *******************/
#define  ADC_SQR1_SQ25                       ((uint32_t)0x0000001F)        /*!< SQ25[4:0] bits (25th conversion in regular sequence) */
#define  ADC_SQR1_SQ25_0                     ((uint32_t)0x00000001)        /*!< Bit 0 */
#define  ADC_SQR1_SQ25_1                     ((uint32_t)0x00000002)        /*!< Bit 1 */
#define  ADC_SQR1_SQ25_2                     ((uint32_t)0x00000004)        /*!< Bit 2 */
#define  ADC_SQR1_SQ25_3                     ((uint32_t)0x00000008)        /*!< Bit 3 */
#define  ADC_SQR1_SQ25_4                     ((uint32_t)0x00000010)        /*!< Bit 4 */

#define  ADC_SQR1_SQ26                       ((uint32_t)0x000003E0)        /*!< SQ26[4:0] bits (26th conversion in regular sequence) */
#define  ADC_SQR1_SQ26_0                     ((uint32_t)0x00000020)        /*!< Bit 0 */
#define  ADC_SQR1_SQ26_1                     ((uint32_t)0x00000040)        /*!< Bit 1 */
#define  ADC_SQR1_SQ26_2                     ((uint32_t)0x00000080)        /*!< Bit 2 */
#define  ADC_SQR1_SQ26_3                     ((uint32_t)0x00000100)        /*!< Bit 3 */
#define  ADC_SQR1_SQ26_4                     ((uint32_t)0x00000200)        /*!< Bit 4 */

#define  ADC_SQR1_SQ27                       ((uint32_t)0x00007C00)        /*!< SQ27[4:0] bits (27th conversion in regular sequence) */
#define  ADC_SQR1_SQ27_0                     ((uint32_t)0x00000400)        /*!< Bit 0 */
#define  ADC_SQR1_SQ27_1                     ((uint32_t)0x00000800)        /*!< Bit 1 */
#define  ADC_SQR1_SQ27_2                     ((uint32_t)0x00001000)        /*!< Bit 2 */
#define  ADC_SQR1_SQ27_3                     ((uint32_t)0x00002000)        /*!< Bit 3 */
#define  ADC_SQR1_SQ27_4                     ((uint32_t)0x00004000)        /*!< Bit 4 */

#define  ADC_SQR1_L                          ((uint32_t)0x00F00000)        /*!< L[3:0] bits (Regular channel sequence length) */
#define  ADC_SQR1_L_0                        ((uint32_t)0x00100000)        /*!< Bit 0 */
#define  ADC_SQR1_L_1                        ((uint32_t)0x00200000)        /*!< Bit 1 */
#define  ADC_SQR1_L_2                        ((uint32_t)0x00400000)        /*!< Bit 2 */
#define  ADC_SQR1_L_3                        ((uint32_t)0x00800000)        /*!< Bit 3 */

/*******************  Bit definition for ADC_SQR2 register  *******************/
#define  ADC_SQR2_SQ19                       ((uint32_t)0x0000001F)        /*!< SQ19[4:0] bits (19th conversion in regular sequence) */
#define  ADC_SQR2_SQ19_0                     ((uint32_t)0x00000001)        /*!< Bit 0 */
#define  ADC_SQR2_SQ19_1                     ((uint32_t)0x00000002)        /*!< Bit 1 */
#define  ADC_SQR2_SQ19_2                     ((uint32_t)0x00000004)        /*!< Bit 2 */
#define  ADC_SQR2_SQ19_3                     ((uint32_t)0x00000008)        /*!< Bit 3 */
#define  ADC_SQR2_SQ19_4                     ((uint32_t)0x00000010)        /*!< Bit 4 */

#define  ADC_SQR2_SQ20                       ((uint32_t)0x000003E0)        /*!< SQ20[4:0] bits (20th conversion in regular sequence) */
#define  ADC_SQR2_SQ20_0                     ((uint32_t)0x00000020)        /*!< Bit 0 */
#define  ADC_SQR2_SQ20_1                     ((uint32_t)0x00000040)        /*!< Bit 1 */
#define  ADC_SQR2_SQ20_2                     ((uint32_t)0x00000080)        /*!< Bit 2 */
#define  ADC_SQR2_SQ20_3                     ((uint32_t)0x00000100)        /*!< Bit 3 */
#define  ADC_SQR2_SQ20_4                     ((uint32_t)0x00000200)        /*!< Bit 4 */

#define  ADC_SQR2_SQ21                       ((uint32_t)0x00007C00)        /*!< SQ21[4:0] bits (21th conversion in regular sequence) */
#define  ADC_SQR2_SQ21_0                     ((uint32_t)0x00000400)        /*!< Bit 0 */
#define  ADC_SQR2_SQ21_1                     ((uint32_t)0x00000800)        /*!< Bit 1 */
#define  ADC_SQR2_SQ21_2                     ((uint32_t)0x00001000)        /*!< Bit 2 */
#define  ADC_SQR2_SQ21_3                     ((uint32_t)0x00002000)        /*!< Bit 3 */
#define  ADC_SQR2_SQ21_4                     ((uint32_t)0x00004000)        /*!< Bit 4 */

#define  ADC_SQR2_SQ22                       ((uint32_t)0x000F8000)        /*!< SQ22[4:0] bits (22th conversion in regular sequence) */
#define  ADC_SQR2_SQ22_0                     ((uint32_t)0x00008000)        /*!< Bit 0 */
#define  ADC_SQR2_SQ22_1                     ((uint32_t)0x00010000)        /*!< Bit 1 */
#define  ADC_SQR2_SQ22_2                     ((uint32_t)0x00020000)        /*!< Bit 2 */
#define  ADC_SQR2_SQ22_3                     ((uint32_t)0x00040000)        /*!< Bit 3 */
#define  ADC_SQR2_SQ22_4                     ((uint32_t)0x00080000)        /*!< Bit 4 */

#define  ADC_SQR2_SQ23                       ((uint32_t)0x01F00000)        /*!< SQ23[4:0] bits (23th conversion in regular sequence) */
#define  ADC_SQR2_SQ23_0                     ((uint32_t)0x00100000)        /*!< Bit 0 */
#define  ADC_SQR2_SQ23_1                     ((uint32_t)0x00200000)        /*!< Bit 1 */
#define  ADC_SQR2_SQ23_2                     ((uint32_t)0x00400000)        /*!< Bit 2 */
#define  ADC_SQR2_SQ23_3                     ((uint32_t)0x00800000)        /*!< Bit 3 */
#define  ADC_SQR2_SQ23_4                     ((uint32_t)0x01000000)        /*!< Bit 4 */

#define  ADC_SQR2_SQ24                       ((uint32_t)0x3E000000)        /*!< SQ24[4:0] bits (24th conversion in regular sequence) */
#define  ADC_SQR2_SQ24_0                     ((uint32_t)0x02000000)        /*!< Bit 0 */
#define  ADC_SQR2_SQ24_1                     ((uint32_t)0x04000000)        /*!< Bit 1 */
#define  ADC_SQR2_SQ24_2                     ((uint32_t)0x08000000)        /*!< Bit 2 */
#define  ADC_SQR2_SQ24_3                     ((uint32_t)0x10000000)        /*!< Bit 3 */
#define  ADC_SQR2_SQ24_4                     ((uint32_t)0x20000000)        /*!< Bit 4 */

/*******************  Bit definition for ADC_SQR3 register  *******************/
#define  ADC_SQR3_SQ13                       ((uint32_t)0x0000001F)        /*!< SQ13[4:0] bits (13th conversion in regular sequence) */
#define  ADC_SQR3_SQ13_0                     ((uint32_t)0x00000001)        /*!< Bit 0 */
#define  ADC_SQR3_SQ13_1                     ((uint32_t)0x00000002)        /*!< Bit 1 */
#define  ADC_SQR3_SQ13_2                     ((uint32_t)0x00000004)        /*!< Bit 2 */
#define  ADC_SQR3_SQ13_3                     ((uint32_t)0x00000008)        /*!< Bit 3 */
#define  ADC_SQR3_SQ13_4                     ((uint32_t)0x00000010)        /*!< Bit 4 */

#define  ADC_SQR3_SQ14                       ((uint32_t)0x000003E0)        /*!< SQ14[4:0] bits (14th conversion in regular sequence) */
#define  ADC_SQR3_SQ14_0                     ((uint32_t)0x00000020)        /*!< Bit 0 */
#define  ADC_SQR3_SQ14_1                     ((uint32_t)0x00000040)        /*!< Bit 1 */
#define  ADC_SQR3_SQ14_2                     ((uint32_t)0x00000080)        /*!< Bit 2 */
#define  ADC_SQR3_SQ14_3                     ((uint32_t)0x00000100)        /*!< Bit 3 */
#define  ADC_SQR3_SQ14_4                     ((uint32_t)0x00000200)        /*!< Bit 4 */

#define  ADC_SQR3_SQ15                       ((uint32_t)0x00007C00)        /*!< SQ15[4:0] bits (15th conversion in regular sequence) */
#define  ADC_SQR3_SQ15_0                     ((uint32_t)0x00000400)        /*!< Bit 0 */
#define  ADC_SQR3_SQ15_1                     ((uint32_t)0x00000800)        /*!< Bit 1 */
#define  ADC_SQR3_SQ15_2                     ((uint32_t)0x00001000)        /*!< Bit 2 */
#define  ADC_SQR3_SQ15_3                     ((uint32_t)0x00002000)        /*!< Bit 3 */
#define  ADC_SQR3_SQ15_4                     ((uint32_t)0x00004000)        /*!< Bit 4 */

#define  ADC_SQR3_SQ16                       ((uint32_t)0x000F8000)        /*!< SQ16[4:0] bits (16th conversion in regular sequence) */
#define  ADC_SQR3_SQ16_0                     ((uint32_t)0x00008000)        /*!< Bit 0 */
#define  ADC_SQR3_SQ16_1                     ((uint32_t)0x00010000)        /*!< Bit 1 */
#define  ADC_SQR3_SQ16_2                     ((uint32_t)0x00020000)        /*!< Bit 2 */
#define  ADC_SQR3_SQ16_3                     ((uint32_t)0x00040000)        /*!< Bit 3 */
#define  ADC_SQR3_SQ16_4                     ((uint32_t)0x00080000)        /*!< Bit 4 */

#define  ADC_SQR3_SQ17                       ((uint32_t)0x01F00000)        /*!< SQ17[4:0] bits (17th conversion in regular sequence) */
#define  ADC_SQR3_SQ17_0                     ((uint32_t)0x00100000)        /*!< Bit 0 */
#define  ADC_SQR3_SQ17_1                     ((uint32_t)0x00200000)        /*!< Bit 1 */
#define  ADC_SQR3_SQ17_2                     ((uint32_t)0x00400000)        /*!< Bit 2 */
#define  ADC_SQR3_SQ17_3                     ((uint32_t)0x00800000)        /*!< Bit 3 */
#define  ADC_SQR3_SQ17_4                     ((uint32_t)0x01000000)        /*!< Bit 4 */

#define  ADC_SQR3_SQ18                       ((uint32_t)0x3E000000)        /*!< SQ18[4:0] bits (18th conversion in regular sequence) */
#define  ADC_SQR3_SQ18_0                     ((uint32_t)0x02000000)        /*!< Bit 0 */
#define  ADC_SQR3_SQ18_1                     ((uint32_t)0x04000000)        /*!< Bit 1 */
#define  ADC_SQR3_SQ18_2                     ((uint32_t)0x08000000)        /*!< Bit 2 */
#define  ADC_SQR3_SQ18_3                     ((uint32_t)0x10000000)        /*!< Bit 3 */
#define  ADC_SQR3_SQ18_4                     ((uint32_t)0x20000000)        /*!< Bit 4 */

/*******************  Bit definition for ADC_SQR4 register  *******************/
#define  ADC_SQR4_SQ7                        ((uint32_t)0x0000001F)        /*!< SQ7[4:0] bits (7th conversion in regular sequence) */
#define  ADC_SQR4_SQ7_0                      ((uint32_t)0x00000001)        /*!< Bit 0 */
#define  ADC_SQR4_SQ7_1                      ((uint32_t)0x00000002)        /*!< Bit 1 */
#define  ADC_SQR4_SQ7_2                      ((uint32_t)0x00000004)        /*!< Bit 2 */
#define  ADC_SQR4_SQ7_3                      ((uint32_t)0x00000008)        /*!< Bit 3 */
#define  ADC_SQR4_SQ7_4                      ((uint32_t)0x00000010)        /*!< Bit 4 */

#define  ADC_SQR4_SQ8                        ((uint32_t)0x000003E0)        /*!< SQ8[4:0] bits (8th conversion in regular sequence) */
#define  ADC_SQR4_SQ8_0                      ((uint32_t)0x00000020)        /*!< Bit 0 */
#define  ADC_SQR4_SQ8_1                      ((uint32_t)0x00000040)        /*!< Bit 1 */
#define  ADC_SQR4_SQ8_2                      ((uint32_t)0x00000080)        /*!< Bit 2 */
#define  ADC_SQR4_SQ8_3                      ((uint32_t)0x00000100)        /*!< Bit 3 */
#define  ADC_SQR4_SQ8_4                      ((uint32_t)0x00000200)        /*!< Bit 4 */

#define  ADC_SQR4_SQ9                        ((uint32_t)0x00007C00)        /*!< SQ9[4:0] bits (9th conversion in regular sequence) */
#define  ADC_SQR4_SQ9_0                      ((uint32_t)0x00000400)        /*!< Bit 0 */
#define  ADC_SQR4_SQ9_1                      ((uint32_t)0x00000800)        /*!< Bit 1 */
#define  ADC_SQR4_SQ9_2                      ((uint32_t)0x00001000)        /*!< Bit 2 */
#define  ADC_SQR4_SQ9_3                      ((uint32_t)0x00002000)        /*!< Bit 3 */
#define  ADC_SQR4_SQ9_4                      ((uint32_t)0x00004000)        /*!< Bit 4 */

#define  ADC_SQR4_SQ10                        ((uint32_t)0x000F8000)        /*!< SQ10[4:0] bits (10th conversion in regular sequence) */
#define  ADC_SQR4_SQ10_0                      ((uint32_t)0x00008000)        /*!< Bit 0 */
#define  ADC_SQR4_SQ10_1                      ((uint32_t)0x00010000)        /*!< Bit 1 */
#define  ADC_SQR4_SQ10_2                      ((uint32_t)0x00020000)        /*!< Bit 2 */
#define  ADC_SQR4_SQ10_3                      ((uint32_t)0x00040000)        /*!< Bit 3 */
#define  ADC_SQR4_SQ10_4                      ((uint32_t)0x00080000)        /*!< Bit 4 */

#define  ADC_SQR4_SQ11                        ((uint32_t)0x01F00000)        /*!< SQ11[4:0] bits (11th conversion in regular sequence) */
#define  ADC_SQR4_SQ11_0                      ((uint32_t)0x00100000)        /*!< Bit 0 */
#define  ADC_SQR4_SQ11_1                      ((uint32_t)0x00200000)        /*!< Bit 1 */
#define  ADC_SQR4_SQ11_2                      ((uint32_t)0x00400000)        /*!< Bit 2 */
#define  ADC_SQR4_SQ11_3                      ((uint32_t)0x00800000)        /*!< Bit 3 */
#define  ADC_SQR4_SQ11_4                      ((uint32_t)0x01000000)        /*!< Bit 4 */

#define  ADC_SQR4_SQ12                        ((uint32_t)0x3E000000)        /*!< SQ12[4:0] bits (12th conversion in regular sequence) */
#define  ADC_SQR4_SQ12_0                      ((uint32_t)0x02000000)        /*!< Bit 0 */
#define  ADC_SQR4_SQ12_1                      ((uint32_t)0x04000000)        /*!< Bit 1 */
#define  ADC_SQR4_SQ12_2                      ((uint32_t)0x08000000)        /*!< Bit 2 */
#define  ADC_SQR4_SQ12_3                      ((uint32_t)0x10000000)        /*!< Bit 3 */
#define  ADC_SQR4_SQ12_4                      ((uint32_t)0x20000000)        /*!< Bit 4 */

/*******************  Bit definition for ADC_SQR5 register  *******************/
#define  ADC_SQR5_SQ1                        ((uint32_t)0x0000001F)        /*!< SQ1[4:0] bits (1st conversion in regular sequence) */
#define  ADC_SQR5_SQ1_0                      ((uint32_t)0x00000001)        /*!< Bit 0 */
#define  ADC_SQR5_SQ1_1                      ((uint32_t)0x00000002)        /*!< Bit 1 */
#define  ADC_SQR5_SQ1_2                      ((uint32_t)0x00000004)        /*!< Bit 2 */
#define  ADC_SQR5_SQ1_3                      ((uint32_t)0x00000008)        /*!< Bit 3 */
#define  ADC_SQR5_SQ1_4                      ((uint32_t)0x00000010)        /*!< Bit 4 */

#define  ADC_SQR5_SQ2                        ((uint32_t)0x000003E0)        /*!< SQ2[4:0] bits (2nd conversion in regular sequence) */
#define  ADC_SQR5_SQ2_0                      ((uint32_t)0x00000020)        /*!< Bit 0 */
#define  ADC_SQR5_SQ2_1                      ((uint32_t)0x00000040)        /*!< Bit 1 */
#define  ADC_SQR5_SQ2_2                      ((uint32_t)0x00000080)        /*!< Bit 2 */
#define  ADC_SQR5_SQ2_3                      ((uint32_t)0x00000100)        /*!< Bit 3 */
#define  ADC_SQR5_SQ2_4                      ((uint32_t)0x00000200)        /*!< Bit 4 */

#define  ADC_SQR5_SQ3                        ((uint32_t)0x00007C00)        /*!< SQ3[4:0] bits (3rd conversion in regular sequence) */
#define  ADC_SQR5_SQ3_0                      ((uint32_t)0x00000400)        /*!< Bit 0 */
#define  ADC_SQR5_SQ3_1                      ((uint32_t)0x00000800)        /*!< Bit 1 */
#define  ADC_SQR5_SQ3_2                      ((uint32_t)0x00001000)        /*!< Bit 2 */
#define  ADC_SQR5_SQ3_3                      ((uint32_t)0x00002000)        /*!< Bit 3 */
#define  ADC_SQR5_SQ3_4                      ((uint32_t)0x00004000)        /*!< Bit 4 */

#define  ADC_SQR5_SQ4                        ((uint32_t)0x000F8000)        /*!< SQ4[4:0] bits (4th conversion in regular sequence) */
#define  ADC_SQR5_SQ4_0                      ((uint32_t)0x00008000)        /*!< Bit 0 */
#define  ADC_SQR5_SQ4_1                      ((uint32_t)0x00010000)        /*!< Bit 1 */
#define  ADC_SQR5_SQ4_2                      ((uint32_t)0x00020000)        /*!< Bit 2 */
#define  ADC_SQR5_SQ4_3                      ((uint32_t)0x00040000)        /*!< Bit 3 */
#define  ADC_SQR5_SQ4_4                      ((uint32_t)0x00080000)        /*!< Bit 4 */

#define  ADC_SQR5_SQ5                        ((uint32_t)0x01F00000)        /*!< SQ5[4:0] bits (5th conversion in regular sequence) */
#define  ADC_SQR5_SQ5_0                      ((uint32_t)0x00100000)        /*!< Bit 0 */
#define  ADC_SQR5_SQ5_1                      ((uint32_t)0x00200000)        /*!< Bit 1 */
#define  ADC_SQR5_SQ5_2                      ((uint32_t)0x00400000)        /*!< Bit 2 */
#define  ADC_SQR5_SQ5_3                      ((uint32_t)0x00800000)        /*!< Bit 3 */
#define  ADC_SQR5_SQ5_4                      ((uint32_t)0x01000000)        /*!< Bit 4 */

#define  ADC_SQR5_SQ6                        ((uint32_t)0x3E000000)        /*!< SQ6[4:0] bits (6th conversion in regular sequence) */
#define  ADC_SQR5_SQ6_0                      ((uint32_t)0x02000000)        /*!< Bit 0 */
#define  ADC_SQR5_SQ6_1                      ((uint32_t)0x04000000)        /*!< Bit 1 */
#define  ADC_SQR5_SQ6_2                      ((uint32_t)0x08000000)        /*!< Bit 2 */
#define  ADC_SQR5_SQ6_3                      ((uint32_t)0x10000000)        /*!< Bit 3 */
#define  ADC_SQR5_SQ6_4                      ((uint32_t)0x20000000)        /*!< Bit 4 */


/*******************  Bit definition for ADC_JSQR register  *******************/
#define  ADC_JSQR_JSQ1                       ((uint32_t)0x0000001F)        /*!< JSQ1[4:0] bits (1st conversion in injected sequence) */  
#define  ADC_JSQR_JSQ1_0                     ((uint32_t)0x00000001)        /*!< Bit 0 */
#define  ADC_JSQR_JSQ1_1                     ((uint32_t)0x00000002)        /*!< Bit 1 */
#define  ADC_JSQR_JSQ1_2                     ((uint32_t)0x00000004)        /*!< Bit 2 */
#define  ADC_JSQR_JSQ1_3                     ((uint32_t)0x00000008)        /*!< Bit 3 */
#define  ADC_JSQR_JSQ1_4                     ((uint32_t)0x00000010)        /*!< Bit 4 */

#define  ADC_JSQR_JSQ2                       ((uint32_t)0x000003E0)        /*!< JSQ2[4:0] bits (2nd conversion in injected sequence) */
#define  ADC_JSQR_JSQ2_0                     ((uint32_t)0x00000020)        /*!< Bit 0 */
#define  ADC_JSQR_JSQ2_1                     ((uint32_t)0x00000040)        /*!< Bit 1 */
#define  ADC_JSQR_JSQ2_2                     ((uint32_t)0x00000080)        /*!< Bit 2 */
#define  ADC_JSQR_JSQ2_3                     ((uint32_t)0x00000100)        /*!< Bit 3 */
#define  ADC_JSQR_JSQ2_4                     ((uint32_t)0x00000200)        /*!< Bit 4 */

#define  ADC_JSQR_JSQ3                       ((uint32_t)0x00007C00)        /*!< JSQ3[4:0] bits (3rd conversion in injected sequence) */
#define  ADC_JSQR_JSQ3_0                     ((uint32_t)0x00000400)        /*!< Bit 0 */
#define  ADC_JSQR_JSQ3_1                     ((uint32_t)0x00000800)        /*!< Bit 1 */
#define  ADC_JSQR_JSQ3_2                     ((uint32_t)0x00001000)        /*!< Bit 2 */
#define  ADC_JSQR_JSQ3_3                     ((uint32_t)0x00002000)        /*!< Bit 3 */
#define  ADC_JSQR_JSQ3_4                     ((uint32_t)0x00004000)        /*!< Bit 4 */

#define  ADC_JSQR_JSQ4                       ((uint32_t)0x000F8000)        /*!< JSQ4[4:0] bits (4th conversion in injected sequence) */
#define  ADC_JSQR_JSQ4_0                     ((uint32_t)0x00008000)        /*!< Bit 0 */
#define  ADC_JSQR_JSQ4_1                     ((uint32_t)0x00010000)        /*!< Bit 1 */
#define  ADC_JSQR_JSQ4_2                     ((uint32_t)0x00020000)        /*!< Bit 2 */
#define  ADC_JSQR_JSQ4_3                     ((uint32_t)0x00040000)        /*!< Bit 3 */
#define  ADC_JSQR_JSQ4_4                     ((uint32_t)0x00080000)        /*!< Bit 4 */

#define  ADC_JSQR_JL                         ((uint32_t)0x00300000)        /*!< JL[1:0] bits (Injected Sequence length) */
#define  ADC_JSQR_JL_0                       ((uint32_t)0x00100000)        /*!< Bit 0 */
#define  ADC_JSQR_JL_1                       ((uint32_t)0x00200000)        /*!< Bit 1 */

/*******************  Bit definition for ADC_JDR1 register  *******************/
#define  ADC_JDR1_JDATA                      ((uint32_t)0x0000FFFF)        /*!< Injected data */

/*******************  Bit definition for ADC_JDR2 register  *******************/
#define  ADC_JDR2_JDATA                      ((uint32_t)0x0000FFFF)        /*!< Injected data */

/*******************  Bit definition for ADC_JDR3 register  *******************/
#define  ADC_JDR3_JDATA                      ((uint32_t)0x0000FFFF)        /*!< Injected data */

/*******************  Bit definition for ADC_JDR4 register  *******************/
#define  ADC_JDR4_JDATA                      ((uint32_t)0x0000FFFF)        /*!< Injected data */

/********************  Bit definition for ADC_DR register  ********************/
#define  ADC_DR_DATA                         ((uint32_t)0x0000FFFF)        /*!< Regular data */


/*******************  Bit definition for ADC_CSR register  ********************/
#define  ADC_CSR_AWD1                        ((uint32_t)0x00000001)        /*!< ADC1 Analog watchdog flag */
#define  ADC_CSR_EOC1                        ((uint32_t)0x00000002)        /*!< ADC1 End of conversion */
#define  ADC_CSR_JEOC1                       ((uint32_t)0x00000004)        /*!< ADC1 Injected channel end of conversion */
#define  ADC_CSR_JSTRT1                      ((uint32_t)0x00000008)        /*!< ADC1 Injected channel Start flag */
#define  ADC_CSR_STRT1                       ((uint32_t)0x00000010)        /*!< ADC1 Regular channel Start flag */
#define  ADC_CSR_OVR1                        ((uint32_t)0x00000020)        /*!< ADC1 overrun  flag */
#define  ADC_CSR_ADONS1                      ((uint32_t)0x00000040)        /*!< ADON status of ADC1 */

/*******************  Bit definition for ADC_CCR register  ********************/
#define  ADC_CCR_ADCPRE                      ((uint32_t)0x00030000)        /*!< ADC prescaler*/
#define  ADC_CCR_ADCPRE_0                    ((uint32_t)0x00010000)        /*!< Bit 0 */
#define  ADC_CCR_ADCPRE_1                    ((uint32_t)0x00020000)        /*!< Bit 1 */ 
#define  ADC_CCR_TSVREFE                     ((uint32_t)0x00800000)        /*!< Temperature Sensor and VREFINT Enable */

/******************************************************************************/
/*                                                                            */
/*                        Comparator                                          */
/*                                                                            */
/******************************************************************************/

/******************  Bit definition for COMP_CSR register  ********************/
#define  COMP_CSR_10KPU                      ((uint32_t)0x00000001)        /*!< 10K pull-up resistor */
#define  COMP_CSR_400KPU                     ((uint32_t)0x00000002)        /*!< 400K pull-up resistor */
#define  COMP_CSR_10KPD                      ((uint32_t)0x00000004)        /*!< 10K pull-down resistor */
#define  COMP_CSR_400KPD                     ((uint32_t)0x00000008)        /*!< 400K pull-down resistor */

#define  COMP_CSR_CMP1EN                     ((uint32_t)0x00000010)        /*!< Comparator 1 enable */
#define  COMP_CSR_CMP1OUT                    ((uint32_t)0x00000080)        /*!< Comparator 1 output */

#define  COMP_CSR_SPEED                      ((uint32_t)0x00001000)        /*!< Comparator 2 speed */
#define  COMP_CSR_CMP2OUT                    ((uint32_t)0x00002000)        /*!< Comparator 2 ouput */

#define  COMP_CSR_VREFOUTEN                  ((uint32_t)0x00010000)        /*!< Comparator Vref Enable */
#define  COMP_CSR_WNDWE                      ((uint32_t)0x00020000)        /*!< Window mode enable */

#define  COMP_CSR_INSEL                      ((uint32_t)0x001C0000)        /*!< INSEL[2:0] Inversion input Selection */
#define  COMP_CSR_INSEL_0                    ((uint32_t)0x00040000)        /*!< Bit 0 */
#define  COMP_CSR_INSEL_1                    ((uint32_t)0x00080000)        /*!< Bit 1 */
#define  COMP_CSR_INSEL_2                    ((uint32_t)0x00100000)        /*!< Bit 2 */

#define  COMP_CSR_OUTSEL                     ((uint32_t)0x00E00000)        /*!< OUTSEL[2:0] comparator 2 output redirection */
#define  COMP_CSR_OUTSEL_0                   ((uint32_t)0x00200000)        /*!< Bit 0 */
#define  COMP_CSR_OUTSEL_1                   ((uint32_t)0x00400000)        /*!< Bit 1 */
#define  COMP_CSR_OUTSEL_2                   ((uint32_t)0x00800000)        /*!< Bit 2 */

/******************************************************************************/
/*                                                                            */
/*                          CRC calculation unit                              */
/*                                                                            */
/******************************************************************************/

/*******************  Bit definition for CRC_DR register  *********************/
#define  CRC_DR_DR                           ((uint32_t)0xFFFFFFFF) /*!< Data register bits */

/*******************  Bit definition for CRC_IDR register  ********************/
#define  CRC_IDR_IDR                         ((uint8_t)0xFF)        /*!< General-purpose 8-bit data register bits */

/********************  Bit definition for CRC_CR register  ********************/
#define  CRC_CR_RESET                        ((uint32_t)0x00000001) /*!< RESET bit */

/******************************************************************************/
/*                                                                            */
/*                      Digital to Analog Converter                           */
/*                                                                            */
/******************************************************************************/

/********************  Bit definition for DAC_CR register  ********************/
#define  DAC_CR_EN1                          ((uint32_t)0x00000001)        /*!<DAC channel1 enable */
#define  DAC_CR_BOFF1                        ((uint32_t)0x00000002)        /*!<DAC channel1 output buffer disable */
#define  DAC_CR_TEN1                         ((uint32_t)0x00000004)        /*!<DAC channel1 Trigger enable */

#define  DAC_CR_TSEL1                        ((uint32_t)0x00000038)        /*!<TSEL1[2:0] (DAC channel1 Trigger selection) */
#define  DAC_CR_TSEL1_0                      ((uint32_t)0x00000008)        /*!<Bit 0 */
#define  DAC_CR_TSEL1_1                      ((uint32_t)0x00000010)        /*!<Bit 1 */
#define  DAC_CR_TSEL1_2                      ((uint32_t)0x00000020)        /*!<Bit 2 */

#define  DAC_CR_WAVE1                        ((uint32_t)0x000000C0)        /*!<WAVE1[1:0] (DAC channel1 noise/triangle wave generation enable) */
#define  DAC_CR_WAVE1_0                      ((uint32_t)0x00000040)        /*!<Bit 0 */
#define  DAC_CR_WAVE1_1                      ((uint32_t)0x00000080)        /*!<Bit 1 */

#define  DAC_CR_MAMP1                        ((uint32_t)0x00000F00)        /*!<MAMP1[3:0] (DAC channel1 Mask/Amplitude selector) */
#define  DAC_CR_MAMP1_0                      ((uint32_t)0x00000100)        /*!<Bit 0 */
#define  DAC_CR_MAMP1_1                      ((uint32_t)0x00000200)        /*!<Bit 1 */
#define  DAC_CR_MAMP1_2                      ((uint32_t)0x00000400)        /*!<Bit 2 */
#define  DAC_CR_MAMP1_3                      ((uint32_t)0x00000800)        /*!<Bit 3 */

#define  DAC_CR_DMAEN1                       ((uint32_t)0x00001000)        /*!<DAC channel1 DMA enable */
#define  DAC_CR_EN2                          ((uint32_t)0x00010000)        /*!<DAC channel2 enable */
#define  DAC_CR_BOFF2                        ((uint32_t)0x00020000)        /*!<DAC channel2 output buffer disable */
#define  DAC_CR_TEN2                         ((uint32_t)0x00040000)        /*!<DAC channel2 Trigger enable */

#define  DAC_CR_TSEL2                        ((uint32_t)0x00380000)        /*!<TSEL2[2:0] (DAC channel2 Trigger selection) */
#define  DAC_CR_TSEL2_0                      ((uint32_t)0x00080000)        /*!<Bit 0 */
#define  DAC_CR_TSEL2_1                      ((uint32_t)0x00100000)        /*!<Bit 1 */
#define  DAC_CR_TSEL2_2                      ((uint32_t)0x00200000)        /*!<Bit 2 */

#define  DAC_CR_WAVE2                        ((uint32_t)0x00C00000)        /*!<WAVE2[1:0] (DAC channel2 noise/triangle wave generation enable) */
#define  DAC_CR_WAVE2_0                      ((uint32_t)0x00400000)        /*!<Bit 0 */
#define  DAC_CR_WAVE2_1                      ((uint32_t)0x00800000)        /*!<Bit 1 */

#define  DAC_CR_MAMP2                        ((uint32_t)0x0F000000)        /*!<MAMP2[3:0] (DAC channel2 Mask/Amplitude selector) */
#define  DAC_CR_MAMP2_0                      ((uint32_t)0x01000000)        /*!<Bit 0 */
#define  DAC_CR_MAMP2_1                      ((uint32_t)0x02000000)        /*!<Bit 1 */
#define  DAC_CR_MAMP2_2                      ((uint32_t)0x04000000)        /*!<Bit 2 */
#define  DAC_CR_MAMP2_3                      ((uint32_t)0x08000000)        /*!<Bit 3 */

#define  DAC_CR_DMAEN2                       ((uint32_t)0x10000000)        /*!<DAC channel2 DMA enabled */

/*****************  Bit definition for DAC_SWTRIGR register  ******************/
#define  DAC_SWTRIGR_SWTRIG1                 ((uint8_t)0x01)               /*!<DAC channel1 software trigger */
#define  DAC_SWTRIGR_SWTRIG2                 ((uint8_t)0x02)               /*!<DAC channel2 software trigger */

/*****************  Bit definition for DAC_DHR12R1 register  ******************/
#define  DAC_DHR12R1_DACC1DHR                ((uint16_t)0x0FFF)            /*!<DAC channel1 12-bit Right aligned data */

/*****************  Bit definition for DAC_DHR12L1 register  ******************/
#define  DAC_DHR12L1_DACC1DHR                ((uint16_t)0xFFF0)            /*!<DAC channel1 12-bit Left aligned data */

/******************  Bit definition for DAC_DHR8R1 register  ******************/
#define  DAC_DHR8R1_DACC1DHR                 ((uint8_t)0xFF)               /*!<DAC channel1 8-bit Right aligned data */

/*****************  Bit definition for DAC_DHR12R2 register  ******************/
#define  DAC_DHR12R2_DACC2DHR                ((uint16_t)0x0FFF)            /*!<DAC channel2 12-bit Right aligned data */

/*****************  Bit definition for DAC_DHR12L2 register  ******************/
#define  DAC_DHR12L2_DACC2DHR                ((uint16_t)0xFFF0)            /*!<DAC channel2 12-bit Left aligned data */

/******************  Bit definition for DAC_DHR8R2 register  ******************/
#define  DAC_DHR8R2_DACC2DHR                 ((uint8_t)0xFF)               /*!<DAC channel2 8-bit Right aligned data */

/*****************  Bit definition for DAC_DHR12RD register  ******************/
#define  DAC_DHR12RD_DACC1DHR                ((uint32_t)0x00000FFF)        /*!<DAC channel1 12-bit Right aligned data */
#define  DAC_DHR12RD_DACC2DHR                ((uint32_t)0x0FFF0000)        /*!<DAC channel2 12-bit Right aligned data */

/*****************  Bit definition for DAC_DHR12LD register  ******************/
#define  DAC_DHR12LD_DACC1DHR                ((uint32_t)0x0000FFF0)        /*!<DAC channel1 12-bit Left aligned data */
#define  DAC_DHR12LD_DACC2DHR                ((uint32_t)0xFFF00000)        /*!<DAC channel2 12-bit Left aligned data */

/******************  Bit definition for DAC_DHR8RD register  ******************/
#define  DAC_DHR8RD_DACC1DHR                 ((uint16_t)0x00FF)            /*!<DAC channel1 8-bit Right aligned data */
#define  DAC_DHR8RD_DACC2DHR                 ((uint16_t)0xFF00)            /*!<DAC channel2 8-bit Right aligned data */

/*******************  Bit definition for DAC_DOR1 register  *******************/
#define  DAC_DOR1_DACC1DOR                   ((uint16_t)0x0FFF)            /*!<DAC channel1 data output */

/*******************  Bit definition for DAC_DOR2 register  *******************/
#define  DAC_DOR2_DACC2DOR                   ((uint16_t)0x0FFF)            /*!<DAC channel2 data output */

/********************  Bit definition for DAC_SR register  ********************/
#define  DAC_SR_DMAUDR1                      ((uint32_t)0x00002000)        /*!<DAC channel1 DMA underrun flag */
#define  DAC_SR_DMAUDR2                      ((uint32_t)0x20000000)        /*!<DAC channel2 DMA underrun flag */

/******************************************************************************/
/*                                                                            */
/*                                 Debug MCU                                  */
/*                                                                            */
/******************************************************************************/

/****************  Bit definition for DBGMCU_IDCODE register  *****************/
#define  DBGMCU_IDCODE_DEV_ID                ((uint32_t)0x00000FFF)        /*!< Device Identifier */

#define  DBGMCU_IDCODE_REV_ID                ((uint32_t)0xFFFF0000)        /*!< REV_ID[15:0] bits (Revision Identifier) */
#define  DBGMCU_IDCODE_REV_ID_0              ((uint32_t)0x00010000)        /*!< Bit 0 */
#define  DBGMCU_IDCODE_REV_ID_1              ((uint32_t)0x00020000)        /*!< Bit 1 */
#define  DBGMCU_IDCODE_REV_ID_2              ((uint32_t)0x00040000)        /*!< Bit 2 */
#define  DBGMCU_IDCODE_REV_ID_3              ((uint32_t)0x00080000)        /*!< Bit 3 */
#define  DBGMCU_IDCODE_REV_ID_4              ((uint32_t)0x00100000)        /*!< Bit 4 */
#define  DBGMCU_IDCODE_REV_ID_5              ((uint32_t)0x00200000)        /*!< Bit 5 */
#define  DBGMCU_IDCODE_REV_ID_6              ((uint32_t)0x00400000)        /*!< Bit 6 */
#define  DBGMCU_IDCODE_REV_ID_7              ((uint32_t)0x00800000)        /*!< Bit 7 */
#define  DBGMCU_IDCODE_REV_ID_8              ((uint32_t)0x01000000)        /*!< Bit 8 */
#define  DBGMCU_IDCODE_REV_ID_9              ((uint32_t)0x02000000)        /*!< Bit 9 */
#define  DBGMCU_IDCODE_REV_ID_10             ((uint32_t)0x04000000)        /*!< Bit 10 */
#define  DBGMCU_IDCODE_REV_ID_11             ((uint32_t)0x08000000)        /*!< Bit 11 */
#define  DBGMCU_IDCODE_REV_ID_12             ((uint32_t)0x10000000)        /*!< Bit 12 */
#define  DBGMCU_IDCODE_REV_ID_13             ((uint32_t)0x20000000)        /*!< Bit 13 */
#define  DBGMCU_IDCODE_REV_ID_14             ((uint32_t)0x40000000)        /*!< Bit 14 */
#define  DBGMCU_IDCODE_REV_ID_15             ((uint32_t)0x80000000)        /*!< Bit 15 */

/******************  Bit definition for DBGMCU_CR register  *******************/
#define  DBGMCU_CR_DBG_SLEEP                 ((uint32_t)0x00000001)        /*!< Debug Sleep Mode */
#define  DBGMCU_CR_DBG_STOP                  ((uint32_t)0x00000002)        /*!< Debug Stop Mode */
#define  DBGMCU_CR_DBG_STANDBY               ((uint32_t)0x00000004)        /*!< Debug Standby mode */
#define  DBGMCU_CR_TRACE_IOEN                ((uint32_t)0x00000020)        /*!< Trace Pin Assignment Control */

#define  DBGMCU_CR_TRACE_MODE                ((uint32_t)0x000000C0)        /*!< TRACE_MODE[1:0] bits (Trace Pin Assignment Control) */
#define  DBGMCU_CR_TRACE_MODE_0              ((uint32_t)0x00000040)        /*!< Bit 0 */
#define  DBGMCU_CR_TRACE_MODE_1              ((uint32_t)0x00000080)        /*!< Bit 1 */

/******************  Bit definition for DBGMCU_APB1_FZ register  **************/

#define  DBGMCU_APB1_FZ_DBG_TIM2_STOP             ((uint32_t)0x00000001)        /*!< TIM2 counter stopped when core is halted */
#define  DBGMCU_APB1_FZ_DBG_TIM3_STOP             ((uint32_t)0x00000002)        /*!< TIM3 counter stopped when core is halted */
#define  DBGMCU_APB1_FZ_DBG_TIM4_STOP             ((uint32_t)0x00000004)        /*!< TIM4 counter stopped when core is halted */
#define  DBGMCU_APB1_FZ_DBG_TIM6_STOP             ((uint32_t)0x00000010)        /*!< TIM6 counter stopped when core is halted */
#define  DBGMCU_APB1_FZ_DBG_TIM7_STOP             ((uint32_t)0x00000020)        /*!< TIM7 counter stopped when core is halted */
#define  DBGMCU_APB1_FZ_DBG_WWDG_STOP             ((uint32_t)0x00000800)        /*!< Debug Window Watchdog stopped when Core is halted */
#define  DBGMCU_APB1_FZ_DBG_IWDG_STOP             ((uint32_t)0x00001000)        /*!< Debug Independent Watchdog stopped when Core is halted */
#define  DBGMCU_APB1_FZ_DBG_I2C1_SMBUS_TIMEOUT    ((uint32_t)0x00200000)        /*!< SMBUS timeout mode stopped when Core is halted */
#define  DBGMCU_APB1_FZ_DBG_I2C2_SMBUS_TIMEOUT    ((uint32_t)0x00400000)        /*!< SMBUS timeout mode stopped when Core is halted */

/******************  Bit definition for DBGMCU_APB2_FZ register  **************/

#define  DBGMCU_APB2_FZ_DBG_TIM9_STOP             ((uint32_t)0x00000004)        /*!< TIM9 counter stopped when core is halted */
#define  DBGMCU_APB2_FZ_DBG_TIM10_STOP            ((uint32_t)0x00000008)        /*!< TIM10 counter stopped when core is halted */
#define  DBGMCU_APB2_FZ_DBG_TIM11_STOP            ((uint32_t)0x00000010)        /*!< TIM11 counter stopped when core is halted */

/******************************************************************************/
/*                                                                            */
/*                             DMA Controller                                 */
/*                                                                            */
/******************************************************************************/

/*******************  Bit definition for DMA_ISR register  ********************/
#define  DMA_ISR_GIF1                        ((uint32_t)0x00000001)        /*!< Channel 1 Global interrupt flag */
#define  DMA_ISR_TCIF1                       ((uint32_t)0x00000002)        /*!< Channel 1 Transfer Complete flag */
#define  DMA_ISR_HTIF1                       ((uint32_t)0x00000004)        /*!< Channel 1 Half Transfer flag */
#define  DMA_ISR_TEIF1                       ((uint32_t)0x00000008)        /*!< Channel 1 Transfer Error flag */
#define  DMA_ISR_GIF2                        ((uint32_t)0x00000010)        /*!< Channel 2 Global interrupt flag */
#define  DMA_ISR_TCIF2                       ((uint32_t)0x00000020)        /*!< Channel 2 Transfer Complete flag */
#define  DMA_ISR_HTIF2                       ((uint32_t)0x00000040)        /*!< Channel 2 Half Transfer flag */
#define  DMA_ISR_TEIF2                       ((uint32_t)0x00000080)        /*!< Channel 2 Transfer Error flag */
#define  DMA_ISR_GIF3                        ((uint32_t)0x00000100)        /*!< Channel 3 Global interrupt flag */
#define  DMA_ISR_TCIF3                       ((uint32_t)0x00000200)        /*!< Channel 3 Transfer Complete flag */
#define  DMA_ISR_HTIF3                       ((uint32_t)0x00000400)        /*!< Channel 3 Half Transfer flag */
#define  DMA_ISR_TEIF3                       ((uint32_t)0x00000800)        /*!< Channel 3 Transfer Error flag */
#define  DMA_ISR_GIF4                        ((uint32_t)0x00001000)        /*!< Channel 4 Global interrupt flag */
#define  DMA_ISR_TCIF4                       ((uint32_t)0x00002000)        /*!< Channel 4 Transfer Complete flag */
#define  DMA_ISR_HTIF4                       ((uint32_t)0x00004000)        /*!< Channel 4 Half Transfer flag */
#define  DMA_ISR_TEIF4                       ((uint32_t)0x00008000)        /*!< Channel 4 Transfer Error flag */
#define  DMA_ISR_GIF5                        ((uint32_t)0x00010000)        /*!< Channel 5 Global interrupt flag */
#define  DMA_ISR_TCIF5                       ((uint32_t)0x00020000)        /*!< Channel 5 Transfer Complete flag */
#define  DMA_ISR_HTIF5                       ((uint32_t)0x00040000)        /*!< Channel 5 Half Transfer flag */
#define  DMA_ISR_TEIF5                       ((uint32_t)0x00080000)        /*!< Channel 5 Transfer Error flag */
#define  DMA_ISR_GIF6                        ((uint32_t)0x00100000)        /*!< Channel 6 Global interrupt flag */
#define  DMA_ISR_TCIF6                       ((uint32_t)0x00200000)        /*!< Channel 6 Transfer Complete flag */
#define  DMA_ISR_HTIF6                       ((uint32_t)0x00400000)        /*!< Channel 6 Half Transfer flag */
#define  DMA_ISR_TEIF6                       ((uint32_t)0x00800000)        /*!< Channel 6 Transfer Error flag */
#define  DMA_ISR_GIF7                        ((uint32_t)0x01000000)        /*!< Channel 7 Global interrupt flag */
#define  DMA_ISR_TCIF7                       ((uint32_t)0x02000000)        /*!< Channel 7 Transfer Complete flag */
#define  DMA_ISR_HTIF7                       ((uint32_t)0x04000000)        /*!< Channel 7 Half Transfer flag */
#define  DMA_ISR_TEIF7                       ((uint32_t)0x08000000)        /*!< Channel 7 Transfer Error flag */

/*******************  Bit definition for DMA_IFCR register  *******************/
#define  DMA_IFCR_CGIF1                      ((uint32_t)0x00000001)        /*!< Channel 1 Global interrupt clearr */
#define  DMA_IFCR_CTCIF1                     ((uint32_t)0x00000002)        /*!< Channel 1 Transfer Complete clear */
#define  DMA_IFCR_CHTIF1                     ((uint32_t)0x00000004)        /*!< Channel 1 Half Transfer clear */
#define  DMA_IFCR_CTEIF1                     ((uint32_t)0x00000008)        /*!< Channel 1 Transfer Error clear */
#define  DMA_IFCR_CGIF2                      ((uint32_t)0x00000010)        /*!< Channel 2 Global interrupt clear */
#define  DMA_IFCR_CTCIF2                     ((uint32_t)0x00000020)        /*!< Channel 2 Transfer Complete clear */
#define  DMA_IFCR_CHTIF2                     ((uint32_t)0x00000040)        /*!< Channel 2 Half Transfer clear */
#define  DMA_IFCR_CTEIF2                     ((uint32_t)0x00000080)        /*!< Channel 2 Transfer Error clear */
#define  DMA_IFCR_CGIF3                      ((uint32_t)0x00000100)        /*!< Channel 3 Global interrupt clear */
#define  DMA_IFCR_CTCIF3                     ((uint32_t)0x00000200)        /*!< Channel 3 Transfer Complete clear */
#define  DMA_IFCR_CHTIF3                     ((uint32_t)0x00000400)        /*!< Channel 3 Half Transfer clear */
#define  DMA_IFCR_CTEIF3                     ((uint32_t)0x00000800)        /*!< Channel 3 Transfer Error clear */
#define  DMA_IFCR_CGIF4                      ((uint32_t)0x00001000)        /*!< Channel 4 Global interrupt clear */
#define  DMA_IFCR_CTCIF4                     ((uint32_t)0x00002000)        /*!< Channel 4 Transfer Complete clear */
#define  DMA_IFCR_CHTIF4                     ((uint32_t)0x00004000)        /*!< Channel 4 Half Transfer clear */
#define  DMA_IFCR_CTEIF4                     ((uint32_t)0x00008000)        /*!< Channel 4 Transfer Error clear */
#define  DMA_IFCR_CGIF5                      ((uint32_t)0x00010000)        /*!< Channel 5 Global interrupt clear */
#define  DMA_IFCR_CTCIF5                     ((uint32_t)0x00020000)        /*!< Channel 5 Transfer Complete clear */
#define  DMA_IFCR_CHTIF5                     ((uint32_t)0x00040000)        /*!< Channel 5 Half Transfer clear */
#define  DMA_IFCR_CTEIF5                     ((uint32_t)0x00080000)        /*!< Channel 5 Transfer Error clear */
#define  DMA_IFCR_CGIF6                      ((uint32_t)0x00100000)        /*!< Channel 6 Global interrupt clear */
#define  DMA_IFCR_CTCIF6                     ((uint32_t)0x00200000)        /*!< Channel 6 Transfer Complete clear */
#define  DMA_IFCR_CHTIF6                     ((uint32_t)0x00400000)        /*!< Channel 6 Half Transfer clear */
#define  DMA_IFCR_CTEIF6                     ((uint32_t)0x00800000)        /*!< Channel 6 Transfer Error clear */
#define  DMA_IFCR_CGIF7                      ((uint32_t)0x01000000)        /*!< Channel 7 Global interrupt clear */
#define  DMA_IFCR_CTCIF7                     ((uint32_t)0x02000000)        /*!< Channel 7 Transfer Complete clear */
#define  DMA_IFCR_CHTIF7                     ((uint32_t)0x04000000)        /*!< Channel 7 Half Transfer clear */
#define  DMA_IFCR_CTEIF7                     ((uint32_t)0x08000000)        /*!< Channel 7 Transfer Error clear */

/*******************  Bit definition for DMA_CCR1 register  *******************/
#define  DMA_CCR1_EN                         ((uint16_t)0x0001)            /*!< Channel enable*/
#define  DMA_CCR1_TCIE                       ((uint16_t)0x0002)            /*!< Transfer complete interrupt enable */
#define  DMA_CCR1_HTIE                       ((uint16_t)0x0004)            /*!< Half Transfer interrupt enable */
#define  DMA_CCR1_TEIE                       ((uint16_t)0x0008)            /*!< Transfer error interrupt enable */
#define  DMA_CCR1_DIR                        ((uint16_t)0x0010)            /*!< Data transfer direction */
#define  DMA_CCR1_CIRC                       ((uint16_t)0x0020)            /*!< Circular mode */
#define  DMA_CCR1_PINC                       ((uint16_t)0x0040)            /*!< Peripheral increment mode */
#define  DMA_CCR1_MINC                       ((uint16_t)0x0080)            /*!< Memory increment mode */

#define  DMA_CCR1_PSIZE                      ((uint16_t)0x0300)            /*!< PSIZE[1:0] bits (Peripheral size) */
#define  DMA_CCR1_PSIZE_0                    ((uint16_t)0x0100)            /*!< Bit 0 */
#define  DMA_CCR1_PSIZE_1                    ((uint16_t)0x0200)            /*!< Bit 1 */

#define  DMA_CCR1_MSIZE                      ((uint16_t)0x0C00)            /*!< MSIZE[1:0] bits (Memory size) */
#define  DMA_CCR1_MSIZE_0                    ((uint16_t)0x0400)            /*!< Bit 0 */
#define  DMA_CCR1_MSIZE_1                    ((uint16_t)0x0800)            /*!< Bit 1 */

#define  DMA_CCR1_PL                         ((uint16_t)0x3000)            /*!< PL[1:0] bits(Channel Priority level) */
#define  DMA_CCR1_PL_0                       ((uint16_t)0x1000)            /*!< Bit 0 */
#define  DMA_CCR1_PL_1                       ((uint16_t)0x2000)            /*!< Bit 1 */

#define  DMA_CCR1_MEM2MEM                    ((uint16_t)0x4000)            /*!< Memory to memory mode */

/*******************  Bit definition for DMA_CCR2 register  *******************/
#define  DMA_CCR2_EN                         ((uint16_t)0x0001)            /*!< Channel enable */
#define  DMA_CCR2_TCIE                       ((uint16_t)0x0002)            /*!< ransfer complete interrupt enable */
#define  DMA_CCR2_HTIE                       ((uint16_t)0x0004)            /*!< Half Transfer interrupt enable */
#define  DMA_CCR2_TEIE                       ((uint16_t)0x0008)            /*!< Transfer error interrupt enable */
#define  DMA_CCR2_DIR                        ((uint16_t)0x0010)            /*!< Data transfer direction */
#define  DMA_CCR2_CIRC                       ((uint16_t)0x0020)            /*!< Circular mode */
#define  DMA_CCR2_PINC                       ((uint16_t)0x0040)            /*!< Peripheral increment mode */
#define  DMA_CCR2_MINC                       ((uint16_t)0x0080)            /*!< Memory increment mode */

#define  DMA_CCR2_PSIZE                      ((uint16_t)0x0300)            /*!< PSIZE[1:0] bits (Peripheral size) */
#define  DMA_CCR2_PSIZE_0                    ((uint16_t)0x0100)            /*!< Bit 0 */
#define  DMA_CCR2_PSIZE_1                    ((uint16_t)0x0200)            /*!< Bit 1 */

#define  DMA_CCR2_MSIZE                      ((uint16_t)0x0C00)            /*!< MSIZE[1:0] bits (Memory size) */
#define  DMA_CCR2_MSIZE_0                    ((uint16_t)0x0400)            /*!< Bit 0 */
#define  DMA_CCR2_MSIZE_1                    ((uint16_t)0x0800)            /*!< Bit 1 */

#define  DMA_CCR2_PL                         ((uint16_t)0x3000)            /*!< PL[1:0] bits (Channel Priority level) */
#define  DMA_CCR2_PL_0                       ((uint16_t)0x1000)            /*!< Bit 0 */
#define  DMA_CCR2_PL_1                       ((uint16_t)0x2000)            /*!< Bit 1 */

#define  DMA_CCR2_MEM2MEM                    ((uint16_t)0x4000)            /*!< Memory to memory mode */

/*******************  Bit definition for DMA_CCR3 register  *******************/
#define  DMA_CCR3_EN                         ((uint16_t)0x0001)            /*!< Channel enable */
#define  DMA_CCR3_TCIE                       ((uint16_t)0x0002)            /*!< Transfer complete interrupt enable */
#define  DMA_CCR3_HTIE                       ((uint16_t)0x0004)            /*!< Half Transfer interrupt enable */
#define  DMA_CCR3_TEIE                       ((uint16_t)0x0008)            /*!< Transfer error interrupt enable */
#define  DMA_CCR3_DIR                        ((uint16_t)0x0010)            /*!< Data transfer direction */
#define  DMA_CCR3_CIRC                       ((uint16_t)0x0020)            /*!< Circular mode */
#define  DMA_CCR3_PINC                       ((uint16_t)0x0040)            /*!< Peripheral increment mode */
#define  DMA_CCR3_MINC                       ((uint16_t)0x0080)            /*!< Memory increment mode */

#define  DMA_CCR3_PSIZE                      ((uint16_t)0x0300)            /*!< PSIZE[1:0] bits (Peripheral size) */
#define  DMA_CCR3_PSIZE_0                    ((uint16_t)0x0100)            /*!< Bit 0 */
#define  DMA_CCR3_PSIZE_1                    ((uint16_t)0x0200)            /*!< Bit 1 */

#define  DMA_CCR3_MSIZE                      ((uint16_t)0x0C00)            /*!< MSIZE[1:0] bits (Memory size) */
#define  DMA_CCR3_MSIZE_0                    ((uint16_t)0x0400)            /*!< Bit 0 */
#define  DMA_CCR3_MSIZE_1                    ((uint16_t)0x0800)            /*!< Bit 1 */

#define  DMA_CCR3_PL                         ((uint16_t)0x3000)            /*!< PL[1:0] bits (Channel Priority level) */
#define  DMA_CCR3_PL_0                       ((uint16_t)0x1000)            /*!< Bit 0 */
#define  DMA_CCR3_PL_1                       ((uint16_t)0x2000)            /*!< Bit 1 */

#define  DMA_CCR3_MEM2MEM                    ((uint16_t)0x4000)            /*!< Memory to memory mode */

/*!<******************  Bit definition for DMA_CCR4 register  *******************/
#define  DMA_CCR4_EN                         ((uint16_t)0x0001)            /*!< Channel enable */
#define  DMA_CCR4_TCIE                       ((uint16_t)0x0002)            /*!< Transfer complete interrupt enable */
#define  DMA_CCR4_HTIE                       ((uint16_t)0x0004)            /*!< Half Transfer interrupt enable */
#define  DMA_CCR4_TEIE                       ((uint16_t)0x0008)            /*!< Transfer error interrupt enable */
#define  DMA_CCR4_DIR                        ((uint16_t)0x0010)            /*!< Data transfer direction */
#define  DMA_CCR4_CIRC                       ((uint16_t)0x0020)            /*!< Circular mode */
#define  DMA_CCR4_PINC                       ((uint16_t)0x0040)            /*!< Peripheral increment mode */
#define  DMA_CCR4_MINC                       ((uint16_t)0x0080)            /*!< Memory increment mode */

#define  DMA_CCR4_PSIZE                      ((uint16_t)0x0300)            /*!< PSIZE[1:0] bits (Peripheral size) */
#define  DMA_CCR4_PSIZE_0                    ((uint16_t)0x0100)            /*!< Bit 0 */
#define  DMA_CCR4_PSIZE_1                    ((uint16_t)0x0200)            /*!< Bit 1 */

#define  DMA_CCR4_MSIZE                      ((uint16_t)0x0C00)            /*!< MSIZE[1:0] bits (Memory size) */
#define  DMA_CCR4_MSIZE_0                    ((uint16_t)0x0400)            /*!< Bit 0 */
#define  DMA_CCR4_MSIZE_1                    ((uint16_t)0x0800)            /*!< Bit 1 */

#define  DMA_CCR4_PL                         ((uint16_t)0x3000)            /*!< PL[1:0] bits (Channel Priority level) */
#define  DMA_CCR4_PL_0                       ((uint16_t)0x1000)            /*!< Bit 0 */
#define  DMA_CCR4_PL_1                       ((uint16_t)0x2000)            /*!< Bit 1 */

#define  DMA_CCR4_MEM2MEM                    ((uint16_t)0x4000)            /*!< Memory to memory mode */

/******************  Bit definition for DMA_CCR5 register  *******************/
#define  DMA_CCR5_EN                         ((uint16_t)0x0001)            /*!< Channel enable */
#define  DMA_CCR5_TCIE                       ((uint16_t)0x0002)            /*!< Transfer complete interrupt enable */
#define  DMA_CCR5_HTIE                       ((uint16_t)0x0004)            /*!< Half Transfer interrupt enable */
#define  DMA_CCR5_TEIE                       ((uint16_t)0x0008)            /*!< Transfer error interrupt enable */
#define  DMA_CCR5_DIR                        ((uint16_t)0x0010)            /*!< Data transfer direction */
#define  DMA_CCR5_CIRC                       ((uint16_t)0x0020)            /*!< Circular mode */
#define  DMA_CCR5_PINC                       ((uint16_t)0x0040)            /*!< Peripheral increment mode */
#define  DMA_CCR5_MINC                       ((uint16_t)0x0080)            /*!< Memory increment mode */

#define  DMA_CCR5_PSIZE                      ((uint16_t)0x0300)            /*!< PSIZE[1:0] bits (Peripheral size) */
#define  DMA_CCR5_PSIZE_0                    ((uint16_t)0x0100)            /*!< Bit 0 */
#define  DMA_CCR5_PSIZE_1                    ((uint16_t)0x0200)            /*!< Bit 1 */

#define  DMA_CCR5_MSIZE                      ((uint16_t)0x0C00)            /*!< MSIZE[1:0] bits (Memory size) */
#define  DMA_CCR5_MSIZE_0                    ((uint16_t)0x0400)            /*!< Bit 0 */
#define  DMA_CCR5_MSIZE_1                    ((uint16_t)0x0800)            /*!< Bit 1 */

#define  DMA_CCR5_PL                         ((uint16_t)0x3000)            /*!< PL[1:0] bits (Channel Priority level) */
#define  DMA_CCR5_PL_0                       ((uint16_t)0x1000)            /*!< Bit 0 */
#define  DMA_CCR5_PL_1                       ((uint16_t)0x2000)            /*!< Bit 1 */

#define  DMA_CCR5_MEM2MEM                    ((uint16_t)0x4000)            /*!< Memory to memory mode enable */

/*******************  Bit definition for DMA_CCR6 register  *******************/
#define  DMA_CCR6_EN                         ((uint16_t)0x0001)            /*!< Channel enable */
#define  DMA_CCR6_TCIE                       ((uint16_t)0x0002)            /*!< Transfer complete interrupt enable */
#define  DMA_CCR6_HTIE                       ((uint16_t)0x0004)            /*!< Half Transfer interrupt enable */
#define  DMA_CCR6_TEIE                       ((uint16_t)0x0008)            /*!< Transfer error interrupt enable */
#define  DMA_CCR6_DIR                        ((uint16_t)0x0010)            /*!< Data transfer direction */
#define  DMA_CCR6_CIRC                       ((uint16_t)0x0020)            /*!< Circular mode */
#define  DMA_CCR6_PINC                       ((uint16_t)0x0040)            /*!< Peripheral increment mode */
#define  DMA_CCR6_MINC                       ((uint16_t)0x0080)            /*!< Memory increment mode */

#define  DMA_CCR6_PSIZE                      ((uint16_t)0x0300)            /*!< PSIZE[1:0] bits (Peripheral size) */
#define  DMA_CCR6_PSIZE_0                    ((uint16_t)0x0100)            /*!< Bit 0 */
#define  DMA_CCR6_PSIZE_1                    ((uint16_t)0x0200)            /*!< Bit 1 */

#define  DMA_CCR6_MSIZE                      ((uint16_t)0x0C00)            /*!< MSIZE[1:0] bits (Memory size) */
#define  DMA_CCR6_MSIZE_0                    ((uint16_t)0x0400)            /*!< Bit 0 */
#define  DMA_CCR6_MSIZE_1                    ((uint16_t)0x0800)            /*!< Bit 1 */

#define  DMA_CCR6_PL                         ((uint16_t)0x3000)            /*!< PL[1:0] bits (Channel Priority level) */
#define  DMA_CCR6_PL_0                       ((uint16_t)0x1000)            /*!< Bit 0 */
#define  DMA_CCR6_PL_1                       ((uint16_t)0x2000)            /*!< Bit 1 */

#define  DMA_CCR6_MEM2MEM                    ((uint16_t)0x4000)            /*!< Memory to memory mode */

/*******************  Bit definition for DMA_CCR7 register  *******************/
#define  DMA_CCR7_EN                         ((uint16_t)0x0001)            /*!< Channel enable */
#define  DMA_CCR7_TCIE                       ((uint16_t)0x0002)            /*!< Transfer complete interrupt enable */
#define  DMA_CCR7_HTIE                       ((uint16_t)0x0004)            /*!< Half Transfer interrupt enable */
#define  DMA_CCR7_TEIE                       ((uint16_t)0x0008)            /*!< Transfer error interrupt enable */
#define  DMA_CCR7_DIR                        ((uint16_t)0x0010)            /*!< Data transfer direction */
#define  DMA_CCR7_CIRC                       ((uint16_t)0x0020)            /*!< Circular mode */
#define  DMA_CCR7_PINC                       ((uint16_t)0x0040)            /*!< Peripheral increment mode */
#define  DMA_CCR7_MINC                       ((uint16_t)0x0080)            /*!< Memory increment mode */

#define  DMA_CCR7_PSIZE            ,         ((uint16_t)0x0300)            /*!< PSIZE[1:0] bits (Peripheral size) */
#define  DMA_CCR7_PSIZE_0                    ((uint16_t)0x0100)            /*!< Bit 0 */
#define  DMA_CCR7_PSIZE_1                    ((uint16_t)0x0200)            /*!< Bit 1 */

#define  DMA_CCR7_MSIZE                      ((uint16_t)0x0C00)            /*!< MSIZE[1:0] bits (Memory size) */
#define  DMA_CCR7_MSIZE_0                    ((uint16_t)0x0400)            /*!< Bit 0 */
#define  DMA_CCR7_MSIZE_1                    ((uint16_t)0x0800)            /*!< Bit 1 */

#define  DMA_CCR7_PL                         ((uint16_t)0x3000)            /*!< PL[1:0] bits (Channel Priority level) */
#define  DMA_CCR7_PL_0                       ((uint16_t)0x1000)            /*!< Bit 0 */
#define  DMA_CCR7_PL_1                       ((uint16_t)0x2000)            /*!< Bit 1 */

#define  DMA_CCR7_MEM2MEM                    ((uint16_t)0x4000)            /*!< Memory to memory mode enable */

/******************  Bit definition for DMA_CNDTR1 register  ******************/
#define  DMA_CNDTR1_NDT                      ((uint16_t)0xFFFF)            /*!< Number of data to Transfer */

/******************  Bit definition for DMA_CNDTR2 register  ******************/
#define  DMA_CNDTR2_NDT                      ((uint16_t)0xFFFF)            /*!< Number of data to Transfer */

/******************  Bit definition for DMA_CNDTR3 register  ******************/
#define  DMA_CNDTR3_NDT                      ((uint16_t)0xFFFF)            /*!< Number of data to Transfer */

/******************  Bit definition for DMA_CNDTR4 register  ******************/
#define  DMA_CNDTR4_NDT                      ((uint16_t)0xFFFF)            /*!< Number of data to Transfer */

/******************  Bit definition for DMA_CNDTR5 register  ******************/
#define  DMA_CNDTR5_NDT                      ((uint16_t)0xFFFF)            /*!< Number of data to Transfer */

/******************  Bit definition for DMA_CNDTR6 register  ******************/
#define  DMA_CNDTR6_NDT                      ((uint16_t)0xFFFF)            /*!< Number of data to Transfer */

/******************  Bit definition for DMA_CNDTR7 register  ******************/
#define  DMA_CNDTR7_NDT                      ((uint16_t)0xFFFF)            /*!< Number of data to Transfer */

/******************  Bit definition for DMA_CPAR1 register  *******************/
#define  DMA_CPAR1_PA                        ((uint32_t)0xFFFFFFFF)        /*!< Peripheral Address */

/******************  Bit definition for DMA_CPAR2 register  *******************/
#define  DMA_CPAR2_PA                        ((uint32_t)0xFFFFFFFF)        /*!< Peripheral Address */

/******************  Bit definition for DMA_CPAR3 register  *******************/
#define  DMA_CPAR3_PA                        ((uint32_t)0xFFFFFFFF)        /*!< Peripheral Address */


/******************  Bit definition for DMA_CPAR4 register  *******************/
#define  DMA_CPAR4_PA                        ((uint32_t)0xFFFFFFFF)        /*!< Peripheral Address */

/******************  Bit definition for DMA_CPAR5 register  *******************/
#define  DMA_CPAR5_PA                        ((uint32_t)0xFFFFFFFF)        /*!< Peripheral Address */

/******************  Bit definition for DMA_CPAR6 register  *******************/
#define  DMA_CPAR6_PA                        ((uint32_t)0xFFFFFFFF)        /*!< Peripheral Address */


/******************  Bit definition for DMA_CPAR7 register  *******************/
#define  DMA_CPAR7_PA                        ((uint32_t)0xFFFFFFFF)        /*!< Peripheral Address */

/******************  Bit definition for DMA_CMAR1 register  *******************/
#define  DMA_CMAR1_MA                        ((uint32_t)0xFFFFFFFF)        /*!< Memory Address */

/******************  Bit definition for DMA_CMAR2 register  *******************/
#define  DMA_CMAR2_MA                        ((uint32_t)0xFFFFFFFF)        /*!< Memory Address */

/******************  Bit definition for DMA_CMAR3 register  *******************/
#define  DMA_CMAR3_MA                        ((uint32_t)0xFFFFFFFF)        /*!< Memory Address */


/******************  Bit definition for DMA_CMAR4 register  *******************/
#define  DMA_CMAR4_MA                        ((uint32_t)0xFFFFFFFF)        /*!< Memory Address */

/******************  Bit definition for DMA_CMAR5 register  *******************/
#define  DMA_CMAR5_MA                        ((uint32_t)0xFFFFFFFF)        /*!< Memory Address */

/******************  Bit definition for DMA_CMAR6 register  *******************/
#define  DMA_CMAR6_MA                        ((uint32_t)0xFFFFFFFF)        /*!< Memory Address */

/******************  Bit definition for DMA_CMAR7 register  *******************/
#define  DMA_CMAR7_MA                        ((uint32_t)0xFFFFFFFF)        /*!< Memory Address */

/******************************************************************************/
/*                                                                            */
/*                    External Interrupt/Event Controller                     */
/*                                                                            */
/******************************************************************************/

/*******************  Bit definition for EXTI_IMR register  *******************/
#define  EXTI_IMR_MR0                        ((uint32_t)0x00000001)        /*!< Interrupt Mask on line 0 */
#define  EXTI_IMR_MR1                        ((uint32_t)0x00000002)        /*!< Interrupt Mask on line 1 */
#define  EXTI_IMR_MR2                        ((uint32_t)0x00000004)        /*!< Interrupt Mask on line 2 */
#define  EXTI_IMR_MR3                        ((uint32_t)0x00000008)        /*!< Interrupt Mask on line 3 */
#define  EXTI_IMR_MR4                        ((uint32_t)0x00000010)        /*!< Interrupt Mask on line 4 */
#define  EXTI_IMR_MR5                        ((uint32_t)0x00000020)        /*!< Interrupt Mask on line 5 */
#define  EXTI_IMR_MR6                        ((uint32_t)0x00000040)        /*!< Interrupt Mask on line 6 */
#define  EXTI_IMR_MR7                        ((uint32_t)0x00000080)        /*!< Interrupt Mask on line 7 */
#define  EXTI_IMR_MR8                        ((uint32_t)0x00000100)        /*!< Interrupt Mask on line 8 */
#define  EXTI_IMR_MR9                        ((uint32_t)0x00000200)        /*!< Interrupt Mask on line 9 */
#define  EXTI_IMR_MR10                       ((uint32_t)0x00000400)        /*!< Interrupt Mask on line 10 */
#define  EXTI_IMR_MR11                       ((uint32_t)0x00000800)        /*!< Interrupt Mask on line 11 */
#define  EXTI_IMR_MR12                       ((uint32_t)0x00001000)        /*!< Interrupt Mask on line 12 */
#define  EXTI_IMR_MR13                       ((uint32_t)0x00002000)        /*!< Interrupt Mask on line 13 */
#define  EXTI_IMR_MR14                       ((uint32_t)0x00004000)        /*!< Interrupt Mask on line 14 */
#define  EXTI_IMR_MR15                       ((uint32_t)0x00008000)        /*!< Interrupt Mask on line 15 */
#define  EXTI_IMR_MR16                       ((uint32_t)0x00010000)        /*!< Interrupt Mask on line 16 */
#define  EXTI_IMR_MR17                       ((uint32_t)0x00020000)        /*!< Interrupt Mask on line 17 */
#define  EXTI_IMR_MR18                       ((uint32_t)0x00040000)        /*!< Interrupt Mask on line 18 */
#define  EXTI_IMR_MR19                       ((uint32_t)0x00080000)        /*!< Interrupt Mask on line 19 */
#define  EXTI_IMR_MR20                       ((uint32_t)0x00100000)        /*!< Interrupt Mask on line 20 */
#define  EXTI_IMR_MR21                       ((uint32_t)0x00200000)        /*!< Interrupt Mask on line 21 */
#define  EXTI_IMR_MR22                       ((uint32_t)0x00400000)        /*!< Interrupt Mask on line 22 */

/*******************  Bit definition for EXTI_EMR register  *******************/
#define  EXTI_EMR_MR0                        ((uint32_t)0x00000001)        /*!< Event Mask on line 0 */
#define  EXTI_EMR_MR1                        ((uint32_t)0x00000002)        /*!< Event Mask on line 1 */
#define  EXTI_EMR_MR2                        ((uint32_t)0x00000004)        /*!< Event Mask on line 2 */
#define  EXTI_EMR_MR3                        ((uint32_t)0x00000008)        /*!< Event Mask on line 3 */
#define  EXTI_EMR_MR4                        ((uint32_t)0x00000010)        /*!< Event Mask on line 4 */
#define  EXTI_EMR_MR5                        ((uint32_t)0x00000020)        /*!< Event Mask on line 5 */
#define  EXTI_EMR_MR6                        ((uint32_t)0x00000040)        /*!< Event Mask on line 6 */
#define  EXTI_EMR_MR7                        ((uint32_t)0x00000080)        /*!< Event Mask on line 7 */
#define  EXTI_EMR_MR8                        ((uint32_t)0x00000100)        /*!< Event Mask on line 8 */
#define  EXTI_EMR_MR9                        ((uint32_t)0x00000200)        /*!< Event Mask on line 9 */
#define  EXTI_EMR_MR10                       ((uint32_t)0x00000400)        /*!< Event Mask on line 10 */
#define  EXTI_EMR_MR11                       ((uint32_t)0x00000800)        /*!< Event Mask on line 11 */
#define  EXTI_EMR_MR12                       ((uint32_t)0x00001000)        /*!< Event Mask on line 12 */
#define  EXTI_EMR_MR13                       ((uint32_t)0x00002000)        /*!< Event Mask on line 13 */
#define  EXTI_EMR_MR14                       ((uint32_t)0x00004000)        /*!< Event Mask on line 14 */
#define  EXTI_EMR_MR15                       ((uint32_t)0x00008000)        /*!< Event Mask on line 15 */
#define  EXTI_EMR_MR16                       ((uint32_t)0x00010000)        /*!< Event Mask on line 16 */
#define  EXTI_EMR_MR17                       ((uint32_t)0x00020000)        /*!< Event Mask on line 17 */
#define  EXTI_EMR_MR18                       ((uint32_t)0x00040000)        /*!< Event Mask on line 18 */
#define  EXTI_EMR_MR19                       ((uint32_t)0x00080000)        /*!< Event Mask on line 19 */
#define  EXTI_EMR_MR20                       ((uint32_t)0x00100000)        /*!< Event Mask on line 20 */
#define  EXTI_EMR_MR21                       ((uint32_t)0x00200000)        /*!< Event Mask on line 21 */
#define  EXTI_EMR_MR22                       ((uint32_t)0x00400000)        /*!< Event Mask on line 22 */

/******************  Bit definition for EXTI_RTSR register  *******************/
#define  EXTI_RTSR_TR0                       ((uint32_t)0x00000001)        /*!< Rising trigger event configuration bit of line 0 */
#define  EXTI_RTSR_TR1                       ((uint32_t)0x00000002)        /*!< Rising trigger event configuration bit of line 1 */
#define  EXTI_RTSR_TR2                       ((uint32_t)0x00000004)        /*!< Rising trigger event configuration bit of line 2 */
#define  EXTI_RTSR_TR3                       ((uint32_t)0x00000008)        /*!< Rising trigger event configuration bit of line 3 */
#define  EXTI_RTSR_TR4                       ((uint32_t)0x00000010)        /*!< Rising trigger event configuration bit of line 4 */
#define  EXTI_RTSR_TR5                       ((uint32_t)0x00000020)        /*!< Rising trigger event configuration bit of line 5 */
#define  EXTI_RTSR_TR6                       ((uint32_t)0x00000040)        /*!< Rising trigger event configuration bit of line 6 */
#define  EXTI_RTSR_TR7                       ((uint32_t)0x00000080)        /*!< Rising trigger event configuration bit of line 7 */
#define  EXTI_RTSR_TR8                       ((uint32_t)0x00000100)        /*!< Rising trigger event configuration bit of line 8 */
#define  EXTI_RTSR_TR9                       ((uint32_t)0x00000200)        /*!< Rising trigger event configuration bit of line 9 */
#define  EXTI_RTSR_TR10                      ((uint32_t)0x00000400)        /*!< Rising trigger event configuration bit of line 10 */
#define  EXTI_RTSR_TR11                      ((uint32_t)0x00000800)        /*!< Rising trigger event configuration bit of line 11 */
#define  EXTI_RTSR_TR12                      ((uint32_t)0x00001000)        /*!< Rising trigger event configuration bit of line 12 */
#define  EXTI_RTSR_TR13                      ((uint32_t)0x00002000)        /*!< Rising trigger event configuration bit of line 13 */
#define  EXTI_RTSR_TR14                      ((uint32_t)0x00004000)        /*!< Rising trigger event configuration bit of line 14 */
#define  EXTI_RTSR_TR15                      ((uint32_t)0x00008000)        /*!< Rising trigger event configuration bit of line 15 */
#define  EXTI_RTSR_TR16                      ((uint32_t)0x00010000)        /*!< Rising trigger event configuration bit of line 16 */
#define  EXTI_RTSR_TR17                      ((uint32_t)0x00020000)        /*!< Rising trigger event configuration bit of line 17 */
#define  EXTI_RTSR_TR18                      ((uint32_t)0x00040000)        /*!< Rising trigger event configuration bit of line 18 */
#define  EXTI_RTSR_TR19                      ((uint32_t)0x00080000)        /*!< Rising trigger event configuration bit of line 19 */
#define  EXTI_RTSR_TR20                      ((uint32_t)0x00100000)        /*!< Rising trigger event configuration bit of line 20 */
#define  EXTI_RTSR_TR21                      ((uint32_t)0x00200000)        /*!< Rising trigger event configuration bit of line 21 */
#define  EXTI_RTSR_TR22                      ((uint32_t)0x00400000)        /*!< Rising trigger event configuration bit of line 22 */

/******************  Bit definition for EXTI_FTSR register  *******************/
#define  EXTI_FTSR_TR0                       ((uint32_t)0x00000001)        /*!< Falling trigger event configuration bit of line 0 */
#define  EXTI_FTSR_TR1                       ((uint32_t)0x00000002)        /*!< Falling trigger event configuration bit of line 1 */
#define  EXTI_FTSR_TR2                       ((uint32_t)0x00000004)        /*!< Falling trigger event configuration bit of line 2 */
#define  EXTI_FTSR_TR3                       ((uint32_t)0x00000008)        /*!< Falling trigger event configuration bit of line 3 */
#define  EXTI_FTSR_TR4                       ((uint32_t)0x00000010)        /*!< Falling trigger event configuration bit of line 4 */
#define  EXTI_FTSR_TR5                       ((uint32_t)0x00000020)        /*!< Falling trigger event configuration bit of line 5 */
#define  EXTI_FTSR_TR6                       ((uint32_t)0x00000040)        /*!< Falling trigger event configuration bit of line 6 */
#define  EXTI_FTSR_TR7                       ((uint32_t)0x00000080)        /*!< Falling trigger event configuration bit of line 7 */
#define  EXTI_FTSR_TR8                       ((uint32_t)0x00000100)        /*!< Falling trigger event configuration bit of line 8 */
#define  EXTI_FTSR_TR9                       ((uint32_t)0x00000200)        /*!< Falling trigger event configuration bit of line 9 */
#define  EXTI_FTSR_TR10                      ((uint32_t)0x00000400)        /*!< Falling trigger event configuration bit of line 10 */
#define  EXTI_FTSR_TR11                      ((uint32_t)0x00000800)        /*!< Falling trigger event configuration bit of line 11 */
#define  EXTI_FTSR_TR12                      ((uint32_t)0x00001000)        /*!< Falling trigger event configuration bit of line 12 */
#define  EXTI_FTSR_TR13                      ((uint32_t)0x00002000)        /*!< Falling trigger event configuration bit of line 13 */
#define  EXTI_FTSR_TR14                      ((uint32_t)0x00004000)        /*!< Falling trigger event configuration bit of line 14 */
#define  EXTI_FTSR_TR15                      ((uint32_t)0x00008000)        /*!< Falling trigger event configuration bit of line 15 */
#define  EXTI_FTSR_TR16                      ((uint32_t)0x00010000)        /*!< Falling trigger event configuration bit of line 16 */
#define  EXTI_FTSR_TR17                      ((uint32_t)0x00020000)        /*!< Falling trigger event configuration bit of line 17 */
#define  EXTI_FTSR_TR18                      ((uint32_t)0x00040000)        /*!< Falling trigger event configuration bit of line 18 */
#define  EXTI_FTSR_TR19                      ((uint32_t)0x00080000)        /*!< Falling trigger event configuration bit of line 19 */
#define  EXTI_FTSR_TR20                      ((uint32_t)0x00100000)        /*!< Falling trigger event configuration bit of line 20 */
#define  EXTI_FTSR_TR21                      ((uint32_t)0x00200000)        /*!< Falling trigger event configuration bit of line 21 */
#define  EXTI_FTSR_TR22                      ((uint32_t)0x00400000)        /*!< Falling trigger event configuration bit of line 22 */

/******************  Bit definition for EXTI_SWIER register  ******************/
#define  EXTI_SWIER_SWIER0                   ((uint32_t)0x00000001)        /*!< Software Interrupt on line 0 */
#define  EXTI_SWIER_SWIER1                   ((uint32_t)0x00000002)        /*!< Software Interrupt on line 1 */
#define  EXTI_SWIER_SWIER2                   ((uint32_t)0x00000004)        /*!< Software Interrupt on line 2 */
#define  EXTI_SWIER_SWIER3                   ((uint32_t)0x00000008)        /*!< Software Interrupt on line 3 */
#define  EXTI_SWIER_SWIER4                   ((uint32_t)0x00000010)        /*!< Software Interrupt on line 4 */
#define  EXTI_SWIER_SWIER5                   ((uint32_t)0x00000020)        /*!< Software Interrupt on line 5 */
#define  EXTI_SWIER_SWIER6                   ((uint32_t)0x00000040)        /*!< Software Interrupt on line 6 */
#define  EXTI_SWIER_SWIER7                   ((uint32_t)0x00000080)        /*!< Software Interrupt on line 7 */
#define  EXTI_SWIER_SWIER8                   ((uint32_t)0x00000100)        /*!< Software Interrupt on line 8 */
#define  EXTI_SWIER_SWIER9                   ((uint32_t)0x00000200)        /*!< Software Interrupt on line 9 */
#define  EXTI_SWIER_SWIER10                  ((uint32_t)0x00000400)        /*!< Software Interrupt on line 10 */
#define  EXTI_SWIER_SWIER11                  ((uint32_t)0x00000800)        /*!< Software Interrupt on line 11 */
#define  EXTI_SWIER_SWIER12                  ((uint32_t)0x00001000)        /*!< Software Interrupt on line 12 */
#define  EXTI_SWIER_SWIER13                  ((uint32_t)0x00002000)        /*!< Software Interrupt on line 13 */
#define  EXTI_SWIER_SWIER14                  ((uint32_t)0x00004000)        /*!< Software Interrupt on line 14 */
#define  EXTI_SWIER_SWIER15                  ((uint32_t)0x00008000)        /*!< Software Interrupt on line 15 */
#define  EXTI_SWIER_SWIER16                  ((uint32_t)0x00010000)        /*!< Software Interrupt on line 16 */
#define  EXTI_SWIER_SWIER17                  ((uint32_t)0x00020000)        /*!< Software Interrupt on line 17 */
#define  EXTI_SWIER_SWIER18                  ((uint32_t)0x00040000)        /*!< Software Interrupt on line 18 */
#define  EXTI_SWIER_SWIER19                  ((uint32_t)0x00080000)        /*!< Software Interrupt on line 19 */
#define  EXTI_SWIER_SWIER20                  ((uint32_t)0x00100000)        /*!< Software Interrupt on line 20 */
#define  EXTI_SWIER_SWIER21                  ((uint32_t)0x00200000)        /*!< Software Interrupt on line 21 */
#define  EXTI_SWIER_SWIER22                  ((uint32_t)0x00400000)        /*!< Software Interrupt on line 22 */

/*******************  Bit definition for EXTI_PR register  ********************/
#define  EXTI_PR_PR0                         ((uint32_t)0x00000001)        /*!< Pending bit 0 */
#define  EXTI_PR_PR1                         ((uint32_t)0x00000002)        /*!< Pending bit 1 */
#define  EXTI_PR_PR2                         ((uint32_t)0x00000004)        /*!< Pending bit 2 */
#define  EXTI_PR_PR3                         ((uint32_t)0x00000008)        /*!< Pending bit 3 */
#define  EXTI_PR_PR4                         ((uint32_t)0x00000010)        /*!< Pending bit 4 */
#define  EXTI_PR_PR5                         ((uint32_t)0x00000020)        /*!< Pending bit 5 */
#define  EXTI_PR_PR6                         ((uint32_t)0x00000040)        /*!< Pending bit 6 */
#define  EXTI_PR_PR7                         ((uint32_t)0x00000080)        /*!< Pending bit 7 */
#define  EXTI_PR_PR8                         ((uint32_t)0x00000100)        /*!< Pending bit 8 */
#define  EXTI_PR_PR9                         ((uint32_t)0x00000200)        /*!< Pending bit 9 */
#define  EXTI_PR_PR10                        ((uint32_t)0x00000400)        /*!< Pending bit 10 */
#define  EXTI_PR_PR11                        ((uint32_t)0x00000800)        /*!< Pending bit 11 */
#define  EXTI_PR_PR12                        ((uint32_t)0x00001000)        /*!< Pending bit 12 */
#define  EXTI_PR_PR13                        ((uint32_t)0x00002000)        /*!< Pending bit 13 */
#define  EXTI_PR_PR14                        ((uint32_t)0x00004000)        /*!< Pending bit 14 */
#define  EXTI_PR_PR15                        ((uint32_t)0x00008000)        /*!< Pending bit 15 */
#define  EXTI_PR_PR16                        ((uint32_t)0x00010000)        /*!< Pending bit 16 */
#define  EXTI_PR_PR17                        ((uint32_t)0x00020000)        /*!< Pending bit 17 */
#define  EXTI_PR_PR18                        ((uint32_t)0x00040000)        /*!< Pending bit 18 */
#define  EXTI_PR_PR19                        ((uint32_t)0x00080000)        /*!< Pending bit 19 */
#define  EXTI_PR_PR20                        ((uint32_t)0x00100000)        /*!< Pending bit 20 */
#define  EXTI_PR_PR21                        ((uint32_t)0x00200000)        /*!< Pending bit 21 */
#define  EXTI_PR_PR22                        ((uint32_t)0x00400000)        /*!< Pending bit 22 */

/******************************************************************************/
/*                                                                            */
/*                      FLASH and Option Bytes Registers                      */
/*                                                                            */
/******************************************************************************/

/*******************  Bit definition for FLASH_ACR register  ******************/
#define  FLASH_ACR_LATENCY                   ((uint32_t)0x00000001)        /*!< Latency */
#define  FLASH_ACR_PRFTEN                    ((uint32_t)0x00000002)        /*!< Prefetch Buffer Enable */
#define  FLASH_ACR_ACC64                     ((uint32_t)0x00000004)        /*!< Access 64 bits */
#define  FLASH_ACR_SLEEP_PD                  ((uint32_t)0x00000008)        /*!< Flash mode during sleep mode */
#define  FLASH_ACR_RUN_PD                    ((uint32_t)0x00000010)        /*!< Flash mode during RUN mode */

/*******************  Bit definition for FLASH_PECR register  ******************/
#define FLASH_PECR_PELOCK                    ((uint32_t)0x00000001)        /*!< FLASH_PECR and Flash data Lock */
#define FLASH_PECR_PRGLOCK                   ((uint32_t)0x00000002)        /*!< Program matrix Lock */
#define FLASH_PECR_OPTLOCK                   ((uint32_t)0x00000004)        /*!< Option byte matrix Lock */
#define FLASH_PECR_PROG                      ((uint32_t)0x00000008)        /*!< Program matrix selection */
#define FLASH_PECR_DATA                      ((uint32_t)0x00000010)        /*!< Data matrix selection */
#define FLASH_PECR_FTDW                      ((uint32_t)0x00000100)        /*!< Fixed Time Data write for Word/Half Word/Byte programming */
#define FLASH_PECR_ERASE                     ((uint32_t)0x00000200)        /*!< Page erasing mode */
#define FLASH_PECR_FPRG                      ((uint32_t)0x00000400)        /*!< Fast Page/Half Page programming mode */
#define FLASH_PECR_EOPIE                     ((uint32_t)0x00010000)        /*!< End of programming interrupt */ 
#define FLASH_PECR_ERRIE                     ((uint32_t)0x00020000)        /*!< Error interrupt */ 
#define FLASH_PECR_OBL_LAUNCH                ((uint32_t)0x00040000)        /*!< Launch the option byte loading */ 

/******************  Bit definition for FLASH_PDKEYR register  ******************/
#define  FLASH_PDKEYR_PDKEYR                 ((uint32_t)0xFFFFFFFF)       /*!< FLASH_PEC and data matrix Key */

/******************  Bit definition for FLASH_PEKEYR register  ******************/
#define  FLASH_PEKEYR_PEKEYR                 ((uint32_t)0xFFFFFFFF)       /*!< FLASH_PEC and data matrix Key */

/******************  Bit definition for FLASH_PRGKEYR register  ******************/
#define  FLASH_PRGKEYR_PRGKEYR               ((uint32_t)0xFFFFFFFF)        /*!< Program matrix Key */

/******************  Bit definition for FLASH_OPTKEYR register  ******************/
#define  FLASH_OPTKEYR_OPTKEYR               ((uint32_t)0xFFFFFFFF)        /*!< Option bytes matrix Key */

/******************  Bit definition for FLASH_SR register  *******************/
#define  FLASH_SR_BSY                        ((uint32_t)0x00000001)        /*!< Busy */
#define  FLASH_SR_EOP                        ((uint32_t)0x00000002)        /*!< End Of Programming*/
#define  FLASH_SR_ENHV                       ((uint32_t)0x00000004)        /*!< End of high voltage */
#define  FLASH_SR_READY                      ((uint32_t)0x00000008)        /*!< Flash ready after low power mode */

#define  FLASH_SR_WRPERR                     ((uint32_t)0x00000100)        /*!< Write protected error */
#define  FLASH_SR_PGAERR                     ((uint32_t)0x00000200)        /*!< Programming Alignment Error */
#define  FLASH_SR_SIZERR                     ((uint32_t)0x00000400)        /*!< Size error */
#define  FLASH_SR_OPTVERR                    ((uint32_t)0x00000800)        /*!< Option validity error */

/******************  Bit definition for FLASH_OBR register  *******************/
#define  FLASH_OBR_RDPRT                     ((uint16_t)0x000000AA)        /*!< Read Protection */
#define  FLASH_OBR_BOR_LEV                   ((uint16_t)0x000F0000)        /*!< BOR_LEV[3:0] Brown Out Reset Threshold Level*/
#define  FLASH_OBR_USER                      ((uint32_t)0x00700000)        /*!< User Option Bytes */
#define  FLASH_OBR_IWDG_SW                   ((uint32_t)0x00100000)        /*!< IWDG_SW */
#define  FLASH_OBR_nRST_STOP                 ((uint32_t)0x00200000)        /*!< nRST_STOP */
#define  FLASH_OBR_nRST_STDBY                ((uint32_t)0x00400000)        /*!< nRST_STDBY */

/******************  Bit definition for FLASH_WRPR register  ******************/
#define  FLASH_WRPR_WRP                      ((uint32_t)0xFFFFFFFF)        /*!< Write Protect */

/******************************************************************************/
/*                                                                            */
/*                        General Purpose IOs                                 */
/*                                                                            */
/******************************************************************************/
/*******************  Bit definition for GPIO_MODER register  *****************/  
#define GPIO_MODER_MODER0          ((uint32_t)0x00000003)
#define GPIO_MODER_MODER0_0        ((uint32_t)0x00000001)
#define GPIO_MODER_MODER0_1        ((uint32_t)0x00000002)
#define GPIO_MODER_MODER1          ((uint32_t)0x0000000C)
#define GPIO_MODER_MODER1_0        ((uint32_t)0x00000004)
#define GPIO_MODER_MODER1_1        ((uint32_t)0x00000008)
#define GPIO_MODER_MODER2          ((uint32_t)0x00000030)
#define GPIO_MODER_MODER2_0        ((uint32_t)0x00000010)
#define GPIO_MODER_MODER2_1        ((uint32_t)0x00000020)
#define GPIO_MODER_MODER3          ((uint32_t)0x000000C0)
#define GPIO_MODER_MODER3_0        ((uint32_t)0x00000040)
#define GPIO_MODER_MODER3_1        ((uint32_t)0x00000080)
#define GPIO_MODER_MODER4          ((uint32_t)0x00000300)
#define GPIO_MODER_MODER4_0        ((uint32_t)0x00000100)
#define GPIO_MODER_MODER4_1        ((uint32_t)0x00000200)
#define GPIO_MODER_MODER5          ((uint32_t)0x00000C00)
#define GPIO_MODER_MODER5_0        ((uint32_t)0x00000400)
#define GPIO_MODER_MODER5_1        ((uint32_t)0x00000800)
#define GPIO_MODER_MODER6          ((uint32_t)0x00003000)
#define GPIO_MODER_MODER6_0        ((uint32_t)0x00001000)
#define GPIO_MODER_MODER6_1        ((uint32_t)0x00002000)
#define GPIO_MODER_MODER7          ((uint32_t)0x0000C000)
#define GPIO_MODER_MODER7_0        ((uint32_t)0x00004000)
#define GPIO_MODER_MODER7_1        ((uint32_t)0x00008000)
#define GPIO_MODER_MODER8          ((uint32_t)0x00030000)
#define GPIO_MODER_MODER8_0        ((uint32_t)0x00010000)
#define GPIO_MODER_MODER8_1        ((uint32_t)0x00020000)
#define GPIO_MODER_MODER9          ((uint32_t)0x000C0000)
#define GPIO_MODER_MODER9_0        ((uint32_t)0x00040000)
#define GPIO_MODER_MODER9_1        ((uint32_t)0x00080000)
#define GPIO_MODER_MODER10         ((uint32_t)0x00300000)
#define GPIO_MODER_MODER10_0       ((uint32_t)0x00100000)
#define GPIO_MODER_MODER10_1       ((uint32_t)0x00200000)
#define GPIO_MODER_MODER11         ((uint32_t)0x00C00000)
#define GPIO_MODER_MODER11_0       ((uint32_t)0x00400000)
#define GPIO_MODER_MODER11_1       ((uint32_t)0x00800000)
#define GPIO_MODER_MODER12         ((uint32_t)0x03000000)
#define GPIO_MODER_MODER12_0       ((uint32_t)0x01000000)
#define GPIO_MODER_MODER12_1       ((uint32_t)0x02000000)
#define GPIO_MODER_MODER13         ((uint32_t)0x0C000000)
#define GPIO_MODER_MODER13_0       ((uint32_t)0x04000000)
#define GPIO_MODER_MODER13_1       ((uint32_t)0x08000000)
#define GPIO_MODER_MODER14         ((uint32_t)0x30000000)
#define GPIO_MODER_MODER14_0       ((uint32_t)0x10000000)
#define GPIO_MODER_MODER14_1       ((uint32_t)0x20000000)
#define GPIO_MODER_MODER15         ((uint32_t)0xC0000000)
#define GPIO_MODER_MODER15_0       ((uint32_t)0x40000000)
#define GPIO_MODER_MODER15_1       ((uint32_t)0x80000000)

/*******************  Bit definition for GPIO_OTYPER register  ****************/   
#define GPIO_OTYPER_OT_0           ((uint32_t)0x00000001)
#define GPIO_OTYPER_OT_1           ((uint32_t)0x00000002)
#define GPIO_OTYPER_OT_2           ((uint32_t)0x00000004)
#define GPIO_OTYPER_OT_3           ((uint32_t)0x00000008)
#define GPIO_OTYPER_OT_4           ((uint32_t)0x00000010)
#define GPIO_OTYPER_OT_5           ((uint32_t)0x00000020)
#define GPIO_OTYPER_OT_6           ((uint32_t)0x00000040)
#define GPIO_OTYPER_OT_7           ((uint32_t)0x00000080)
#define GPIO_OTYPER_OT_8           ((uint32_t)0x00000100)
#define GPIO_OTYPER_OT_9           ((uint32_t)0x00000200)
#define GPIO_OTYPER_OT_10          ((uint32_t)0x00000400)
#define GPIO_OTYPER_OT_11          ((uint32_t)0x00000800)
#define GPIO_OTYPER_OT_12          ((uint32_t)0x00001000)
#define GPIO_OTYPER_OT_13          ((uint32_t)0x00002000)
#define GPIO_OTYPER_OT_14          ((uint32_t)0x00004000)
#define GPIO_OTYPER_OT_15          ((uint32_t)0x00008000)

/*******************  Bit definition for GPIO_OSPEEDR register  ***************/  
#define GPIO_OSPEEDER_OSPEEDR0     ((uint32_t)0x00000003)
#define GPIO_OSPEEDER_OSPEEDR0_0   ((uint32_t)0x00000001)
#define GPIO_OSPEEDER_OSPEEDR0_1   ((uint32_t)0x00000002)
#define GPIO_OSPEEDER_OSPEEDR1     ((uint32_t)0x0000000C)
#define GPIO_OSPEEDER_OSPEEDR1_0   ((uint32_t)0x00000004)
#define GPIO_OSPEEDER_OSPEEDR1_1   ((uint32_t)0x00000008)
#define GPIO_OSPEEDER_OSPEEDR2     ((uint32_t)0x00000030)
#define GPIO_OSPEEDER_OSPEEDR2_0   ((uint32_t)0x00000010)
#define GPIO_OSPEEDER_OSPEEDR2_1   ((uint32_t)0x00000020)
#define GPIO_OSPEEDER_OSPEEDR3     ((uint32_t)0x000000C0)
#define GPIO_OSPEEDER_OSPEEDR3_0   ((uint32_t)0x00000040)
#define GPIO_OSPEEDER_OSPEEDR3_1   ((uint32_t)0x00000080)
#define GPIO_OSPEEDER_OSPEEDR4     ((uint32_t)0x00000300)
#define GPIO_OSPEEDER_OSPEEDR4_0   ((uint32_t)0x00000100)
#define GPIO_OSPEEDER_OSPEEDR4_1   ((uint32_t)0x00000200)
#define GPIO_OSPEEDER_OSPEEDR5     ((uint32_t)0x00000C00)
#define GPIO_OSPEEDER_OSPEEDR5_0   ((uint32_t)0x00000400)
#define GPIO_OSPEEDER_OSPEEDR5_1   ((uint32_t)0x00000800)
#define GPIO_OSPEEDER_OSPEEDR6     ((uint32_t)0x00003000)
#define GPIO_OSPEEDER_OSPEEDR6_0   ((uint32_t)0x00001000)
#define GPIO_OSPEEDER_OSPEEDR6_1   ((uint32_t)0x00002000)
#define GPIO_OSPEEDER_OSPEEDR7     ((uint32_t)0x0000C000)
#define GPIO_OSPEEDER_OSPEEDR7_0   ((uint32_t)0x00004000)
#define GPIO_OSPEEDER_OSPEEDR7_1   ((uint32_t)0x00008000)
#define GPIO_OSPEEDER_OSPEEDR8     ((uint32_t)0x00030000)
#define GPIO_OSPEEDER_OSPEEDR8_0   ((uint32_t)0x00010000)
#define GPIO_OSPEEDER_OSPEEDR8_1   ((uint32_t)0x00020000)
#define GPIO_OSPEEDER_OSPEEDR9     ((uint32_t)0x000C0000)
#define GPIO_OSPEEDER_OSPEEDR9_0   ((uint32_t)0x00040000)
#define GPIO_OSPEEDER_OSPEEDR9_1   ((uint32_t)0x00080000)
#define GPIO_OSPEEDER_OSPEEDR10    ((uint32_t)0x00300000)
#define GPIO_OSPEEDER_OSPEEDR10_0  ((uint32_t)0x00100000)
#define GPIO_OSPEEDER_OSPEEDR10_1  ((uint32_t)0x00200000)
#define GPIO_OSPEEDER_OSPEEDR11    ((uint32_t)0x00C00000)
#define GPIO_OSPEEDER_OSPEEDR11_0  ((uint32_t)0x00400000)
#define GPIO_OSPEEDER_OSPEEDR11_1  ((uint32_t)0x00800000)
#define GPIO_OSPEEDER_OSPEEDR12    ((uint32_t)0x03000000)
#define GPIO_OSPEEDER_OSPEEDR12_0  ((uint32_t)0x01000000)
#define GPIO_OSPEEDER_OSPEEDR12_1  ((uint32_t)0x02000000)
#define GPIO_OSPEEDER_OSPEEDR13    ((uint32_t)0x0C000000)
#define GPIO_OSPEEDER_OSPEEDR13_0  ((uint32_t)0x04000000)
#define GPIO_OSPEEDER_OSPEEDR13_1  ((uint32_t)0x08000000)
#define GPIO_OSPEEDER_OSPEEDR14    ((uint32_t)0x30000000)
#define GPIO_OSPEEDER_OSPEEDR14_0  ((uint32_t)0x10000000)
#define GPIO_OSPEEDER_OSPEEDR14_1  ((uint32_t)0x20000000)
#define GPIO_OSPEEDER_OSPEEDR15    ((uint32_t)0xC0000000)
#define GPIO_OSPEEDER_OSPEEDR15_0  ((uint32_t)0x40000000)
#define GPIO_OSPEEDER_OSPEEDR15_1  ((uint32_t)0x80000000)

/*******************  Bit definition for GPIO_PUPDR register  *****************/  
#define GPIO_PUPDR_PUPDR0          ((uint32_t)0x00000003)
#define GPIO_PUPDR_PUPDR0_0        ((uint32_t)0x00000001)
#define GPIO_PUPDR_PUPDR0_1        ((uint32_t)0x00000002)
#define GPIO_PUPDR_PUPDR1          ((uint32_t)0x0000000C)
#define GPIO_PUPDR_PUPDR1_0        ((uint32_t)0x00000004)
#define GPIO_PUPDR_PUPDR1_1        ((uint32_t)0x00000008)
#define GPIO_PUPDR_PUPDR2          ((uint32_t)0x00000030)
#define GPIO_PUPDR_PUPDR2_0        ((uint32_t)0x00000010)
#define GPIO_PUPDR_PUPDR2_1        ((uint32_t)0x00000020)
#define GPIO_PUPDR_PUPDR3          ((uint32_t)0x000000C0)
#define GPIO_PUPDR_PUPDR3_0        ((uint32_t)0x00000040)
#define GPIO_PUPDR_PUPDR3_1        ((uint32_t)0x00000080)
#define GPIO_PUPDR_PUPDR4          ((uint32_t)0x00000300)
#define GPIO_PUPDR_PUPDR4_0        ((uint32_t)0x00000100)
#define GPIO_PUPDR_PUPDR4_1        ((uint32_t)0x00000200)
#define GPIO_PUPDR_PUPDR5          ((uint32_t)0x00000C00)
#define GPIO_PUPDR_PUPDR5_0        ((uint32_t)0x00000400)
#define GPIO_PUPDR_PUPDR5_1        ((uint32_t)0x00000800)
#define GPIO_PUPDR_PUPDR6          ((uint32_t)0x00003000)
#define GPIO_PUPDR_PUPDR6_0        ((uint32_t)0x00001000)
#define GPIO_PUPDR_PUPDR6_1        ((uint32_t)0x00002000)
#define GPIO_PUPDR_PUPDR7          ((uint32_t)0x0000C000)
#define GPIO_PUPDR_PUPDR7_0        ((uint32_t)0x00004000)
#define GPIO_PUPDR_PUPDR7_1        ((uint32_t)0x00008000)
#define GPIO_PUPDR_PUPDR8          ((uint32_t)0x00030000)
#define GPIO_PUPDR_PUPDR8_0        ((uint32_t)0x00010000)
#define GPIO_PUPDR_PUPDR8_1        ((uint32_t)0x00020000)
#define GPIO_PUPDR_PUPDR9          ((uint32_t)0x000C0000)
#define GPIO_PUPDR_PUPDR9_0        ((uint32_t)0x00040000)
#define GPIO_PUPDR_PUPDR9_1        ((uint32_t)0x00080000)
#define GPIO_PUPDR_PUPDR10         ((uint32_t)0x00300000)
#define GPIO_PUPDR_PUPDR10_0       ((uint32_t)0x00100000)
#define GPIO_PUPDR_PUPDR10_1       ((uint32_t)0x00200000)
#define GPIO_PUPDR_PUPDR11         ((uint32_t)0x00C00000)
#define GPIO_PUPDR_PUPDR11_0       ((uint32_t)0x00400000)
#define GPIO_PUPDR_PUPDR11_1       ((uint32_t)0x00800000)
#define GPIO_PUPDR_PUPDR12         ((uint32_t)0x03000000)
#define GPIO_PUPDR_PUPDR12_0       ((uint32_t)0x01000000)
#define GPIO_PUPDR_PUPDR12_1       ((uint32_t)0x02000000)
#define GPIO_PUPDR_PUPDR13         ((uint32_t)0x0C000000)
#define GPIO_PUPDR_PUPDR13_0       ((uint32_t)0x04000000)
#define GPIO_PUPDR_PUPDR13_1       ((uint32_t)0x08000000)
#define GPIO_PUPDR_PUPDR14         ((uint32_t)0x30000000)
#define GPIO_PUPDR_PUPDR14_0       ((uint32_t)0x10000000)
#define GPIO_PUPDR_PUPDR14_1       ((uint32_t)0x20000000)
#define GPIO_PUPDR_PUPDR15         ((uint32_t)0xC0000000)
#define GPIO_PUPDR_PUPDR15_0       ((uint32_t)0x40000000)
#define GPIO_PUPDR_PUPDR15_1       ((uint32_t)0x80000000)

/*******************  Bit definition for GPIO_IDR register  *******************/  
#define GPIO_OTYPER_IDR_0          ((uint32_t)0x00000001)
#define GPIO_OTYPER_IDR_1          ((uint32_t)0x00000002)
#define GPIO_OTYPER_IDR_2          ((uint32_t)0x00000004)
#define GPIO_OTYPER_IDR_3          ((uint32_t)0x00000008)
#define GPIO_OTYPER_IDR_4          ((uint32_t)0x00000010)
#define GPIO_OTYPER_IDR_5          ((uint32_t)0x00000020)
#define GPIO_OTYPER_IDR_6          ((uint32_t)0x00000040)
#define GPIO_OTYPER_IDR_7          ((uint32_t)0x00000080)
#define GPIO_OTYPER_IDR_8          ((uint32_t)0x00000100)
#define GPIO_OTYPER_IDR_9          ((uint32_t)0x00000200)
#define GPIO_OTYPER_IDR_10         ((uint32_t)0x00000400)
#define GPIO_OTYPER_IDR_11         ((uint32_t)0x00000800)
#define GPIO_OTYPER_IDR_12         ((uint32_t)0x00001000)
#define GPIO_OTYPER_IDR_13         ((uint32_t)0x00002000)
#define GPIO_OTYPER_IDR_14         ((uint32_t)0x00004000)
#define GPIO_OTYPER_IDR_15         ((uint32_t)0x00008000)

/*******************  Bit definition for GPIO_ODR register  *******************/   
#define GPIO_OTYPER_ODR_0          ((uint32_t)0x00000001)
#define GPIO_OTYPER_ODR_1          ((uint32_t)0x00000002)
#define GPIO_OTYPER_ODR_2          ((uint32_t)0x00000004)
#define GPIO_OTYPER_ODR_3          ((uint32_t)0x00000008)
#define GPIO_OTYPER_ODR_4          ((uint32_t)0x00000010)
#define GPIO_OTYPER_ODR_5          ((uint32_t)0x00000020)
#define GPIO_OTYPER_ODR_6          ((uint32_t)0x00000040)
#define GPIO_OTYPER_ODR_7          ((uint32_t)0x00000080)
#define GPIO_OTYPER_ODR_8          ((uint32_t)0x00000100)
#define GPIO_OTYPER_ODR_9          ((uint32_t)0x00000200)
#define GPIO_OTYPER_ODR_10         ((uint32_t)0x00000400)
#define GPIO_OTYPER_ODR_11         ((uint32_t)0x00000800)
#define GPIO_OTYPER_ODR_12         ((uint32_t)0x00001000)
#define GPIO_OTYPER_ODR_13         ((uint32_t)0x00002000)
#define GPIO_OTYPER_ODR_14         ((uint32_t)0x00004000)
#define GPIO_OTYPER_ODR_15         ((uint32_t)0x00008000)

/*******************  Bit definition for GPIO_BSRR register  ******************/  
#define GPIO_BSRR_BS_0             ((uint32_t)0x00000001)
#define GPIO_BSRR_BS_1             ((uint32_t)0x00000002)
#define GPIO_BSRR_BS_2             ((uint32_t)0x00000004)
#define GPIO_BSRR_BS_3             ((uint32_t)0x00000008)
#define GPIO_BSRR_BS_4             ((uint32_t)0x00000010)
#define GPIO_BSRR_BS_5             ((uint32_t)0x00000020)
#define GPIO_BSRR_BS_6             ((uint32_t)0x00000040)
#define GPIO_BSRR_BS_7             ((uint32_t)0x00000080)
#define GPIO_BSRR_BS_8             ((uint32_t)0x00000100)
#define GPIO_BSRR_BS_9             ((uint32_t)0x00000200)
#define GPIO_BSRR_BS_10            ((uint32_t)0x00000400)
#define GPIO_BSRR_BS_11            ((uint32_t)0x00000800)
#define GPIO_BSRR_BS_12            ((uint32_t)0x00001000)
#define GPIO_BSRR_BS_13            ((uint32_t)0x00002000)
#define GPIO_BSRR_BS_14            ((uint32_t)0x00004000)
#define GPIO_BSRR_BS_15            ((uint32_t)0x00008000)
#define GPIO_BSRR_BR_0             ((uint32_t)0x00010000)
#define GPIO_BSRR_BR_1             ((uint32_t)0x00020000)
#define GPIO_BSRR_BR_2             ((uint32_t)0x00040000)
#define GPIO_BSRR_BR_3             ((uint32_t)0x00080000)
#define GPIO_BSRR_BR_4             ((uint32_t)0x00100000)
#define GPIO_BSRR_BR_5             ((uint32_t)0x00200000)
#define GPIO_BSRR_BR_6             ((uint32_t)0x00400000)
#define GPIO_BSRR_BR_7             ((uint32_t)0x00800000)
#define GPIO_BSRR_BR_8             ((uint32_t)0x01000000)
#define GPIO_BSRR_BR_9             ((uint32_t)0x02000000)
#define GPIO_BSRR_BR_10            ((uint32_t)0x04000000)
#define GPIO_BSRR_BR_11            ((uint32_t)0x08000000)
#define GPIO_BSRR_BR_12            ((uint32_t)0x10000000)
#define GPIO_BSRR_BR_13            ((uint32_t)0x20000000)
#define GPIO_BSRR_BR_14            ((uint32_t)0x40000000)
#define GPIO_BSRR_BR_15            ((uint32_t)0x80000000)

/******************************************************************************/
/*                                                                            */
/*                      Inter-integrated Circuit Interface                    */
/*                                                                            */
/******************************************************************************/

/*******************  Bit definition for I2C_CR1 register  ********************/
#define  I2C_CR1_PE                          ((uint16_t)0x0001)            /*!< Peripheral Enable */
#define  I2C_CR1_SMBUS                       ((uint16_t)0x0002)            /*!< SMBus Mode */
#define  I2C_CR1_SMBTYPE                     ((uint16_t)0x0008)            /*!< SMBus Type */
#define  I2C_CR1_ENARP                       ((uint16_t)0x0010)            /*!< ARP Enable */
#define  I2C_CR1_ENPEC                       ((uint16_t)0x0020)            /*!< PEC Enable */
#define  I2C_CR1_ENGC                        ((uint16_t)0x0040)            /*!< General Call Enable */
#define  I2C_CR1_NOSTRETCH                   ((uint16_t)0x0080)            /*!< Clock Stretching Disable (Slave mode) */
#define  I2C_CR1_START                       ((uint16_t)0x0100)            /*!< Start Generation */
#define  I2C_CR1_STOP                        ((uint16_t)0x0200)            /*!< Stop Generation */
#define  I2C_CR1_ACK                         ((uint16_t)0x0400)            /*!< Acknowledge Enable */
#define  I2C_CR1_POS                         ((uint16_t)0x0800)            /*!< Acknowledge/PEC Position (for data reception) */
#define  I2C_CR1_PEC                         ((uint16_t)0x1000)            /*!< Packet Error Checking */
#define  I2C_CR1_ALERT                       ((uint16_t)0x2000)            /*!< SMBus Alert */
#define  I2C_CR1_SWRST                       ((uint16_t)0x8000)            /*!< Software Reset */

/*******************  Bit definition for I2C_CR2 register  ********************/
#define  I2C_CR2_FREQ                        ((uint16_t)0x003F)            /*!< FREQ[5:0] bits (Peripheral Clock Frequency) */
#define  I2C_CR2_FREQ_0                      ((uint16_t)0x0001)            /*!< Bit 0 */
#define  I2C_CR2_FREQ_1                      ((uint16_t)0x0002)            /*!< Bit 1 */
#define  I2C_CR2_FREQ_2                      ((uint16_t)0x0004)            /*!< Bit 2 */
#define  I2C_CR2_FREQ_3                      ((uint16_t)0x0008)            /*!< Bit 3 */
#define  I2C_CR2_FREQ_4                      ((uint16_t)0x0010)            /*!< Bit 4 */
#define  I2C_CR2_FREQ_5                      ((uint16_t)0x0020)            /*!< Bit 5 */

#define  I2C_CR2_ITERREN                     ((uint16_t)0x0100)            /*!< Error Interrupt Enable */
#define  I2C_CR2_ITEVTEN                     ((uint16_t)0x0200)            /*!< Event Interrupt Enable */
#define  I2C_CR2_ITBUFEN                     ((uint16_t)0x0400)            /*!< Buffer Interrupt Enable */
#define  I2C_CR2_DMAEN                       ((uint16_t)0x0800)            /*!< DMA Requests Enable */
#define  I2C_CR2_LAST                        ((uint16_t)0x1000)            /*!< DMA Last Transfer */

/*******************  Bit definition for I2C_OAR1 register  *******************/
#define  I2C_OAR1_ADD1_7                     ((uint16_t)0x00FE)            /*!< Interface Address */
#define  I2C_OAR1_ADD8_9                     ((uint16_t)0x0300)            /*!< Interface Address */

#define  I2C_OAR1_ADD0                       ((uint16_t)0x0001)            /*!< Bit 0 */
#define  I2C_OAR1_ADD1                       ((uint16_t)0x0002)            /*!< Bit 1 */
#define  I2C_OAR1_ADD2                       ((uint16_t)0x0004)            /*!< Bit 2 */
#define  I2C_OAR1_ADD3                       ((uint16_t)0x0008)            /*!< Bit 3 */
#define  I2C_OAR1_ADD4                       ((uint16_t)0x0010)            /*!< Bit 4 */
#define  I2C_OAR1_ADD5                       ((uint16_t)0x0020)            /*!< Bit 5 */
#define  I2C_OAR1_ADD6                       ((uint16_t)0x0040)            /*!< Bit 6 */
#define  I2C_OAR1_ADD7                       ((uint16_t)0x0080)            /*!< Bit 7 */
#define  I2C_OAR1_ADD8                       ((uint16_t)0x0100)            /*!< Bit 8 */
#define  I2C_OAR1_ADD9                       ((uint16_t)0x0200)            /*!< Bit 9 */

#define  I2C_OAR1_ADDMODE                    ((uint16_t)0x8000)            /*!< Addressing Mode (Slave mode) */

/*******************  Bit definition for I2C_OAR2 register  *******************/
#define  I2C_OAR2_ENDUAL                     ((uint8_t)0x01)               /*!< Dual addressing mode enable */
#define  I2C_OAR2_ADD2                       ((uint8_t)0xFE)               /*!< Interface address */

/********************  Bit definition for I2C_DR register  ********************/
#define  I2C_DR_DR                           ((uint8_t)0xFF)               /*!< 8-bit Data Register */

/*******************  Bit definition for I2C_SR1 register  ********************/
#define  I2C_SR1_SB                          ((uint16_t)0x0001)            /*!< Start Bit (Master mode) */
#define  I2C_SR1_ADDR                        ((uint16_t)0x0002)            /*!< Address sent (master mode)/matched (slave mode) */
#define  I2C_SR1_BTF                         ((uint16_t)0x0004)            /*!< Byte Transfer Finished */
#define  I2C_SR1_ADD10                       ((uint16_t)0x0008)            /*!< 10-bit header sent (Master mode) */
#define  I2C_SR1_STOPF                       ((uint16_t)0x0010)            /*!< Stop detection (Slave mode) */
#define  I2C_SR1_RXNE                        ((uint16_t)0x0040)            /*!< Data Register not Empty (receivers) */
#define  I2C_SR1_TXE                         ((uint16_t)0x0080)            /*!< Data Register Empty (transmitters) */
#define  I2C_SR1_BERR                        ((uint16_t)0x0100)            /*!< Bus Error */
#define  I2C_SR1_ARLO                        ((uint16_t)0x0200)            /*!< Arbitration Lost (master mode) */
#define  I2C_SR1_AF                          ((uint16_t)0x0400)            /*!< Acknowledge Failure */
#define  I2C_SR1_OVR                         ((uint16_t)0x0800)            /*!< Overrun/Underrun */
#define  I2C_SR1_PECERR                      ((uint16_t)0x1000)            /*!< PEC Error in reception */
#define  I2C_SR1_TIMEOUT                     ((uint16_t)0x4000)            /*!< Timeout or Tlow Error */
#define  I2C_SR1_SMBALERT                    ((uint16_t)0x8000)            /*!< SMBus Alert */

/*******************  Bit definition for I2C_SR2 register  ********************/
#define  I2C_SR2_MSL                         ((uint16_t)0x0001)            /*!< Master/Slave */
#define  I2C_SR2_BUSY                        ((uint16_t)0x0002)            /*!< Bus Busy */
#define  I2C_SR2_TRA                         ((uint16_t)0x0004)            /*!< Transmitter/Receiver */
#define  I2C_SR2_GENCALL                     ((uint16_t)0x0010)            /*!< General Call Address (Slave mode) */
#define  I2C_SR2_SMBDEFAULT                  ((uint16_t)0x0020)            /*!< SMBus Device Default Address (Slave mode) */
#define  I2C_SR2_SMBHOST                     ((uint16_t)0x0040)            /*!< SMBus Host Header (Slave mode) */
#define  I2C_SR2_DUALF                       ((uint16_t)0x0080)            /*!< Dual Flag (Slave mode) */
#define  I2C_SR2_PEC                         ((uint16_t)0xFF00)            /*!< Packet Error Checking Register */

/*******************  Bit definition for I2C_CCR register  ********************/
#define  I2C_CCR_CCR                         ((uint16_t)0x0FFF)            /*!< Clock Control Register in Fast/Standard mode (Master mode) */
#define  I2C_CCR_DUTY                        ((uint16_t)0x4000)            /*!< Fast Mode Duty Cycle */
#define  I2C_CCR_FS                          ((uint16_t)0x8000)            /*!< I2C Master Mode Selection */

/******************  Bit definition for I2C_TRISE register  *******************/
#define  I2C_TRISE_TRISE                     ((uint8_t)0x3F)               /*!< Maximum Rise Time in Fast/Standard mode (Master mode) */

/******************************************************************************/
/*                                                                            */
/*                           Independent WATCHDOG                             */
/*                                                                            */
/******************************************************************************/

/*******************  Bit definition for IWDG_KR register  ********************/
#define  IWDG_KR_KEY                         ((uint16_t)0xFFFF)            /*!< Key value (write only, read 0000h) */

/*******************  Bit definition for IWDG_PR register  ********************/
#define  IWDG_PR_PR                          ((uint8_t)0x07)               /*!< PR[2:0] (Prescaler divider) */
#define  IWDG_PR_PR_0                        ((uint8_t)0x01)               /*!< Bit 0 */
#define  IWDG_PR_PR_1                        ((uint8_t)0x02)               /*!< Bit 1 */
#define  IWDG_PR_PR_2                        ((uint8_t)0x04)               /*!< Bit 2 */

/*******************  Bit definition for IWDG_RLR register  *******************/
#define  IWDG_RLR_RL                         ((uint16_t)0x0FFF)            /*!< Watchdog counter reload value */

/*******************  Bit definition for IWDG_SR register  ********************/
#define  IWDG_SR_PVU                         ((uint8_t)0x01)               /*!< Watchdog prescaler value update */
#define  IWDG_SR_RVU                         ((uint8_t)0x02)               /*!< Watchdog counter reload value update */

/******************************************************************************/
/*                                                                            */
/*                                    LCD                                     */
/*                                                                            */
/******************************************************************************/

/*******************  Bit definition for LCD_CR register  *********************/
#define LCD_CR_LCDEN               ((uint32_t)0x00000001)     /*!< LCD Enable Bit */
#define LCD_CR_VSEL                ((uint32_t)0x00000002)     /*!< Voltage source selector Bit */

#define LCD_CR_DUTY                ((uint32_t)0x0000001C)     /*!< DUTY[2:0] bits (Duty selector) */
#define LCD_CR_DUTY_0              ((uint32_t)0x00000004)     /*!< Duty selector Bit 0 */
#define LCD_CR_DUTY_1              ((uint32_t)0x00000008)     /*!< Duty selector Bit 1 */
#define LCD_CR_DUTY_2              ((uint32_t)0x00000010)     /*!< Duty selector Bit 2 */

#define LCD_CR_BIAS                ((uint32_t)0x00000060)     /*!< BIAS[1:0] bits (Bias selector) */
#define LCD_CR_BIAS_0              ((uint32_t)0x00000020)     /*!< Bias selector Bit 0 */
#define LCD_CR_BIAS_1              ((uint32_t)0x00000040)     /*!< Bias selector Bit 1 */

#define LCD_CR_MUX_SEG             ((uint32_t)0x00000080)     /*!< Mux Segment Enable Bit */

/*******************  Bit definition for LCD_FCR register  ********************/
#define LCD_FCR_HD                 ((uint32_t)0x00000001)     /*!< High Drive Enable Bit */
#define LCD_FCR_SOFIE              ((uint32_t)0x00000002)     /*!< Start of Frame Interrupt Enable Bit */
#define LCD_FCR_UDDIE              ((uint32_t)0x00000008)     /*!< Update Display Done Interrupt Enable Bit */

#define LCD_FCR_PON                ((uint32_t)0x00000070)     /*!< PON[2:0] bits (Puls ON Duration) */
#define LCD_FCR_PON_0              ((uint32_t)0x00000010)     /*!< Bit 0 */
#define LCD_FCR_PON_1              ((uint32_t)0x00000020)     /*!< Bit 1 */
#define LCD_FCR_PON_2              ((uint32_t)0x00000040)     /*!< Bit 2 */

#define LCD_FCR_DEAD               ((uint32_t)0x00000380)     /*!< DEAD[2:0] bits (DEAD Time) */
#define LCD_FCR_DEAD_0             ((uint32_t)0x00000080)     /*!< Bit 0 */
#define LCD_FCR_DEAD_1             ((uint32_t)0x00000100)     /*!< Bit 1 */
#define LCD_FCR_DEAD_2             ((uint32_t)0x00000200)     /*!< Bit 2 */

#define LCD_FCR_CC                 ((uint32_t)0x00001C00)     /*!< CC[2:0] bits (Contrast Control) */
#define LCD_FCR_CC_0               ((uint32_t)0x00000400)     /*!< Bit 0 */
#define LCD_FCR_CC_1               ((uint32_t)0x00000800)     /*!< Bit 1 */
#define LCD_FCR_CC_2               ((uint32_t)0x00001000)     /*!< Bit 2 */

#define LCD_FCR_BLINKF             ((uint32_t)0x0000E000)     /*!< BLINKF[2:0] bits (Blink Frequency) */
#define LCD_FCR_BLINKF_0           ((uint32_t)0x00002000)     /*!< Bit 0 */
#define LCD_FCR_BLINKF_1           ((uint32_t)0x00004000)     /*!< Bit 1 */
#define LCD_FCR_BLINKF_2           ((uint32_t)0x00008000)     /*!< Bit 2 */

#define LCD_FCR_BLINK              ((uint32_t)0x00030000)     /*!< BLINK[1:0] bits (Blink Enable) */
#define LCD_FCR_BLINK_0            ((uint32_t)0x00010000)     /*!< Bit 0 */
#define LCD_FCR_BLINK_1            ((uint32_t)0x00020000)     /*!< Bit 1 */

#define LCD_FCR_DIV                ((uint32_t)0x003C0000)     /*!< DIV[3:0] bits (Divider) */
#define LCD_FCR_PS                 ((uint32_t)0x03C00000)     /*!< PS[3:0] bits (Prescaler) */

/*******************  Bit definition for LCD_SR register  *********************/
#define LCD_SR_ENS                 ((uint32_t)0x00000001)     /*!< LCD Enabled Bit */
#define LCD_SR_SOF                 ((uint32_t)0x00000002)     /*!< Start Of Frame Flag Bit */
#define LCD_SR_UDR                 ((uint32_t)0x00000004)     /*!< Update Display Request Bit */
#define LCD_SR_UDD                 ((uint32_t)0x00000008)     /*!< Update Display Done Flag Bit */
#define LCD_SR_RDY                 ((uint32_t)0x00000010)     /*!< Ready Flag Bit */
#define LCD_SR_FCRSR               ((uint32_t)0x00000020)     /*!< LCD FCR Register Synchronization Flag Bit */

/*******************  Bit definition for LCD_CLR register  ********************/
#define LCD_CLR_SOFC               ((uint32_t)0x00000002)     /*!< Start Of Frame Flag Clear Bit */
#define LCD_CLR_UDDC               ((uint32_t)0x00000008)     /*!< Update Display Done Flag Clear Bit */

/*******************  Bit definition for LCD_RAM register  ********************/
#define LCD_RAM_SEGMENT_DATA       ((uint32_t)0xFFFFFFFF)     /*!< Segment Data Bits */

/******************************************************************************/
/*                                                                            */
/*                             Power Control                                  */
/*                                                                            */
/******************************************************************************/

/********************  Bit definition for PWR_CR register  ********************/
#define  PWR_CR_LPSDSR                       ((uint16_t)0x0001)     /*!< Low-power deepsleep/sleep/low power run */
#define  PWR_CR_PDDS                         ((uint16_t)0x0002)     /*!< Power Down Deepsleep */
#define  PWR_CR_CWUF                         ((uint16_t)0x0004)     /*!< Clear Wakeup Flag */
#define  PWR_CR_CSBF                         ((uint16_t)0x0008)     /*!< Clear Standby Flag */
#define  PWR_CR_PVDE                         ((uint16_t)0x0010)     /*!< Power Voltage Detector Enable */

#define  PWR_CR_PLS                          ((uint16_t)0x00E0)     /*!< PLS[2:0] bits (PVD Level Selection) */
#define  PWR_CR_PLS_0                        ((uint16_t)0x0020)     /*!< Bit 0 */
#define  PWR_CR_PLS_1                        ((uint16_t)0x0040)     /*!< Bit 1 */
#define  PWR_CR_PLS_2                        ((uint16_t)0x0080)     /*!< Bit 2 */

/*!< PVD level configuration */
#define  PWR_CR_PLS_LEV0                     ((uint16_t)0x0000)     /*!< PVD level 0 */
#define  PWR_CR_PLS_LEV1                     ((uint16_t)0x0020)     /*!< PVD level 1 */
#define  PWR_CR_PLS_LEV2                     ((uint16_t)0x0040)     /*!< PVD level 2 */
#define  PWR_CR_PLS_LEV3                     ((uint16_t)0x0060)     /*!< PVD level 3 */
#define  PWR_CR_PLS_LEV4                     ((uint16_t)0x0080)     /*!< PVD level 4 */
#define  PWR_CR_PLS_LEV5                     ((uint16_t)0x00A0)     /*!< PVD level 5 */
#define  PWR_CR_PLS_LEV6                     ((uint16_t)0x00C0)     /*!< PVD level 6 */
#define  PWR_CR_PLS_LEV7                     ((uint16_t)0x00E0)     /*!< PVD level 7 */

#define  PWR_CR_DBP                          ((uint16_t)0x0100)     /*!< Disable Backup Domain write protection */
#define  PWR_CR_ULP                          ((uint16_t)0x0200)     /*!< Ultra Low Power mode */
#define  PWR_CR_FWU                          ((uint16_t)0x0400)     /*!< Fast wakeup */

#define  PWR_CR_VOS                          ((uint16_t)0x1800)     /*!< VOS[1:0] bits (Voltage scaling range selection) */
#define  PWR_CR_VOS_0                        ((uint16_t)0x0800)     /*!< Bit 0 */
#define  PWR_CR_VOS_1                        ((uint16_t)0x1000)     /*!< Bit 1 */
#define  PWR_CR_LPRUN                        ((uint16_t)0x4000)     /*!< Low power run mode */

/*******************  Bit definition for PWR_CSR register  ********************/
#define  PWR_CSR_WUF                         ((uint16_t)0x0001)     /*!< Wakeup Flag */
#define  PWR_CSR_SBF                         ((uint16_t)0x0002)     /*!< Standby Flag */
#define  PWR_CSR_PVDO                        ((uint16_t)0x0004)     /*!< PVD Output */
#define  PWR_CSR_VREFINTRDYF                 ((uint16_t)0x0008)     /*!< Internal voltage reference (VREFINT) ready flag */
#define  PWR_CSR_VOSF                        ((uint16_t)0x0010)     /*!< Voltage Scaling select flag */
#define  PWR_CSR_REGLPF                      ((uint16_t)0x0020)     /*!< Regulator LP flag */

#define  PWR_CSR_EWUP1                       ((uint16_t)0x0100)     /*!< Enable WKUP pin 1 */
#define  PWR_CSR_EWUP2                       ((uint16_t)0x0200)     /*!< Enable WKUP pin 2 */
#define  PWR_CSR_EWUP3                       ((uint16_t)0x0400)     /*!< Enable WKUP pin 3 */

/******************************************************************************/
/*                                                                            */
/*                         Reset and Clock Control                            */
/*                                                                            */
/******************************************************************************/
/********************  Bit definition for RCC_CR register  ********************/
#define  RCC_CR_HSION                        ((uint32_t)0x00000001)        /*!< Internal High Speed clock enable */
#define  RCC_CR_HSIRDY                       ((uint32_t)0x00000002)        /*!< Internal High Speed clock ready flag */

#define  RCC_CR_MSION                        ((uint32_t)0x00000100)        /*!< Internal Multi Speed clock enable */
#define  RCC_CR_MSIRDY                       ((uint32_t)0x00000200)        /*!< Internal Multi Speed clock ready flag */

#define  RCC_CR_HSEON                        ((uint32_t)0x00010000)        /*!< External High Speed clock enable */
#define  RCC_CR_HSERDY                       ((uint32_t)0x00020000)        /*!< External High Speed clock ready flag */
#define  RCC_CR_HSEBYP                       ((uint32_t)0x00040000)        /*!< External High Speed clock Bypass */

#define  RCC_CR_PLLON                        ((uint32_t)0x01000000)        /*!< PLL enable */
#define  RCC_CR_PLLRDY                       ((uint32_t)0x02000000)        /*!< PLL clock ready flag */
#define  RCC_CR_CSSON                        ((uint32_t)0x10000000)        /*!< Clock Security System enable */

#define  RCC_CR_RTCPRE                       ((uint32_t)0x60000000)        /*!< RTC/LCD Prescaler */
#define  RCC_CR_RTCPRE_0                     ((uint32_t)0x20000000)        /*!< Bit0 */
#define  RCC_CR_RTCPRE_1                     ((uint32_t)0x40000000)        /*!< Bit1 */

/********************  Bit definition for RCC_ICSCR register  *****************/
#define  RCC_ICSCR_HSICAL                    ((uint32_t)0x000000FF)        /*!< Internal High Speed clock Calibration */
#define  RCC_ICSCR_HSITRIM                   ((uint32_t)0x00001F00)        /*!< Internal High Speed clock trimming */

#define  RCC_ICSCR_MSIRANGE                  ((uint32_t)0x0000E000)        /*!< Internal Multi Speed clock Range */
#define  RCC_ICSCR_MSIRANGE_64KHz            ((uint32_t)0x00000000)        /*!< Internal Multi Speed clock Range 64KHz */
#define  RCC_ICSCR_MSIRANGE_128KHz           ((uint32_t)0x00002000)        /*!< Internal Multi Speed clock Range 128KHz */
#define  RCC_ICSCR_MSIRANGE_256KHz           ((uint32_t)0x00004000)        /*!< Internal Multi Speed clock Range 256KHz */
#define  RCC_ICSCR_MSIRANGE_512KHz           ((uint32_t)0x00006000)        /*!< Internal Multi Speed clock Range 512KHz */
#define  RCC_ICSCR_MSIRANGE_1MHz             ((uint32_t)0x00008000)        /*!< Internal Multi Speed clock Range 1MHz */
#define  RCC_ICSCR_MSIRANGE_2MHz             ((uint32_t)0x0000A000)        /*!< Internal Multi Speed clock Range 2MHz */
#define  RCC_ICSCR_MSIRANGE_4MHz             ((uint32_t)0x0000C000)        /*!< Internal Multi Speed clock Range 4MHz */
#define  RCC_ICSCR_MSICAL                    ((uint32_t)0x00FF0000)        /*!< Internal Multi Speed clock Calibration */
#define  RCC_ICSCR_MSITRIM                   ((uint32_t)0xFF000000)        /*!< Internal Multi Speed clock trimming */

/********************  Bit definition for RCC_CFGR register  ******************/
#define  RCC_CFGR_SW                         ((uint32_t)0x00000003)        /*!< SW[1:0] bits (System clock Switch) */
#define  RCC_CFGR_SW_0                       ((uint32_t)0x00000001)        /*!< Bit 0 */
#define  RCC_CFGR_SW_1                       ((uint32_t)0x00000002)        /*!< Bit 1 */

/*!< SW configuration */
#define  RCC_CFGR_SW_MSI                     ((uint32_t)0x00000000)        /*!< MSI selected as system clock */
#define  RCC_CFGR_SW_HSI                     ((uint32_t)0x00000001)        /*!< HSI selected as system clock */
#define  RCC_CFGR_SW_HSE                     ((uint32_t)0x00000002)        /*!< HSE selected as system clock */
#define  RCC_CFGR_SW_PLL                     ((uint32_t)0x00000003)        /*!< PLL selected as system clock */

#define  RCC_CFGR_SWS                        ((uint32_t)0x0000000C)        /*!< SWS[1:0] bits (System Clock Switch Status) */
#define  RCC_CFGR_SWS_0                      ((uint32_t)0x00000004)        /*!< Bit 0 */
#define  RCC_CFGR_SWS_1                      ((uint32_t)0x00000008)        /*!< Bit 1 */

/*!< SWS configuration */
#define  RCC_CFGR_SWS_MSI                    ((uint32_t)0x00000000)        /*!< MSI oscillator used as system clock */
#define  RCC_CFGR_SWS_HSI                    ((uint32_t)0x00000004)        /*!< HSI oscillator used as system clock */
#define  RCC_CFGR_SWS_HSE                    ((uint32_t)0x00000008)        /*!< HSE oscillator used as system clock */
#define  RCC_CFGR_SWS_PLL                    ((uint32_t)0x0000000C)        /*!< PLL used as system clock */

#define  RCC_CFGR_HPRE                       ((uint32_t)0x000000F0)        /*!< HPRE[3:0] bits (AHB prescaler) */
#define  RCC_CFGR_HPRE_0                     ((uint32_t)0x00000010)        /*!< Bit 0 */
#define  RCC_CFGR_HPRE_1                     ((uint32_t)0x00000020)        /*!< Bit 1 */
#define  RCC_CFGR_HPRE_2                     ((uint32_t)0x00000040)        /*!< Bit 2 */
#define  RCC_CFGR_HPRE_3                     ((uint32_t)0x00000080)        /*!< Bit 3 */

/*!< HPRE configuration */
#define  RCC_CFGR_HPRE_DIV1                  ((uint32_t)0x00000000)        /*!< SYSCLK not divided */
#define  RCC_CFGR_HPRE_DIV2                  ((uint32_t)0x00000080)        /*!< SYSCLK divided by 2 */
#define  RCC_CFGR_HPRE_DIV4                  ((uint32_t)0x00000090)        /*!< SYSCLK divided by 4 */
#define  RCC_CFGR_HPRE_DIV8                  ((uint32_t)0x000000A0)        /*!< SYSCLK divided by 8 */
#define  RCC_CFGR_HPRE_DIV16                 ((uint32_t)0x000000B0)        /*!< SYSCLK divided by 16 */
#define  RCC_CFGR_HPRE_DIV64                 ((uint32_t)0x000000C0)        /*!< SYSCLK divided by 64 */
#define  RCC_CFGR_HPRE_DIV128                ((uint32_t)0x000000D0)        /*!< SYSCLK divided by 128 */
#define  RCC_CFGR_HPRE_DIV256                ((uint32_t)0x000000E0)        /*!< SYSCLK divided by 256 */
#define  RCC_CFGR_HPRE_DIV512                ((uint32_t)0x000000F0)        /*!< SYSCLK divided by 512 */

#define  RCC_CFGR_PPRE1                      ((uint32_t)0x00000700)        /*!< PRE1[2:0] bits (APB1 prescaler) */
#define  RCC_CFGR_PPRE1_0                    ((uint32_t)0x00000100)        /*!< Bit 0 */
#define  RCC_CFGR_PPRE1_1                    ((uint32_t)0x00000200)        /*!< Bit 1 */
#define  RCC_CFGR_PPRE1_2                    ((uint32_t)0x00000400)        /*!< Bit 2 */

/*!< PPRE1 configuration */
#define  RCC_CFGR_PPRE1_DIV1                 ((uint32_t)0x00000000)        /*!< HCLK not divided */
#define  RCC_CFGR_PPRE1_DIV2                 ((uint32_t)0x00000400)        /*!< HCLK divided by 2 */
#define  RCC_CFGR_PPRE1_DIV4                 ((uint32_t)0x00000500)        /*!< HCLK divided by 4 */
#define  RCC_CFGR_PPRE1_DIV8                 ((uint32_t)0x00000600)        /*!< HCLK divided by 8 */
#define  RCC_CFGR_PPRE1_DIV16                ((uint32_t)0x00000700)        /*!< HCLK divided by 16 */

#define  RCC_CFGR_PPRE2                      ((uint32_t)0x00003800)        /*!< PRE2[2:0] bits (APB2 prescaler) */
#define  RCC_CFGR_PPRE2_0                    ((uint32_t)0x00000800)        /*!< Bit 0 */
#define  RCC_CFGR_PPRE2_1                    ((uint32_t)0x00001000)        /*!< Bit 1 */
#define  RCC_CFGR_PPRE2_2                    ((uint32_t)0x00002000)        /*!< Bit 2 */

/*!< PPRE2 configuration */
#define  RCC_CFGR_PPRE2_DIV1                 ((uint32_t)0x00000000)        /*!< HCLK not divided */
#define  RCC_CFGR_PPRE2_DIV2                 ((uint32_t)0x00002000)        /*!< HCLK divided by 2 */
#define  RCC_CFGR_PPRE2_DIV4                 ((uint32_t)0x00002800)        /*!< HCLK divided by 4 */
#define  RCC_CFGR_PPRE2_DIV8                 ((uint32_t)0x00003000)        /*!< HCLK divided by 8 */
#define  RCC_CFGR_PPRE2_DIV16                ((uint32_t)0x00003800)        /*!< HCLK divided by 16 */

/*!< PLL entry clock source*/
#define  RCC_CFGR_PLLSRC                     ((uint32_t)0x00010000)        /*!< PLL entry clock source */

#define  RCC_CFGR_PLLSRC_HSI                 ((uint32_t)0x00000000)        /*!< HSI as PLL entry clock source */
#define  RCC_CFGR_PLLSRC_HSE                 ((uint32_t)0x00010000)        /*!< HSE as PLL entry clock source */


#define  RCC_CFGR_PLLMUL                     ((uint32_t)0x003C0000)        /*!< PLLMUL[3:0] bits (PLL multiplication factor) */
#define  RCC_CFGR_PLLMUL_0                   ((uint32_t)0x00040000)        /*!< Bit 0 */
#define  RCC_CFGR_PLLMUL_1                   ((uint32_t)0x00080000)        /*!< Bit 1 */
#define  RCC_CFGR_PLLMUL_2                   ((uint32_t)0x00100000)        /*!< Bit 2 */
#define  RCC_CFGR_PLLMUL_3                   ((uint32_t)0x00200000)        /*!< Bit 3 */

/*!< PLLMUL configuration */
#define  RCC_CFGR_PLLMUL3                    ((uint32_t)0x00000000)        /*!< PLL input clock * 3 */
#define  RCC_CFGR_PLLMUL4                    ((uint32_t)0x00040000)        /*!< PLL input clock * 4 */
#define  RCC_CFGR_PLLMUL6                    ((uint32_t)0x00080000)        /*!< PLL input clock * 6 */
#define  RCC_CFGR_PLLMUL8                    ((uint32_t)0x000C0000)        /*!< PLL input clock * 8 */
#define  RCC_CFGR_PLLMUL12                   ((uint32_t)0x00100000)        /*!< PLL input clock * 12 */
#define  RCC_CFGR_PLLMUL16                   ((uint32_t)0x00140000)        /*!< PLL input clock * 16 */
#define  RCC_CFGR_PLLMUL24                   ((uint32_t)0x00180000)        /*!< PLL input clock * 24 */
#define  RCC_CFGR_PLLMUL32                   ((uint32_t)0x001C0000)        /*!< PLL input clock * 32 */
#define  RCC_CFGR_PLLMUL48                   ((uint32_t)0x00200000)        /*!< PLL input clock * 48 */

/*!< PLLDIV configuration */
#define  RCC_CFGR_PLLDIV                     ((uint32_t)0x00C00000)        /*!< PLLDIV[1:0] bits (PLL Output Division) */
#define  RCC_CFGR_PLLDIV_0                   ((uint32_t)0x00400000)        /*!< Bit0 */
#define  RCC_CFGR_PLLDIV_1                   ((uint32_t)0x00800000)        /*!< Bit1 */


/*!< PLLDIV configuration */
#define  RCC_CFGR_PLLDIV1                    ((uint32_t)0x00000000)        /*!< PLL clock output = CKVCO / 1 */
#define  RCC_CFGR_PLLDIV2                    ((uint32_t)0x00400000)        /*!< PLL clock output = CKVCO / 2 */
#define  RCC_CFGR_PLLDIV3                    ((uint32_t)0x00800000)        /*!< PLL clock output = CKVCO / 3 */
#define  RCC_CFGR_PLLDIV4                    ((uint32_t)0x00C00000)        /*!< PLL clock output = CKVCO / 4 */


#define  RCC_CFGR_MCOSEL                     ((uint32_t)0x07000000)        /*!< MCO[2:0] bits (Microcontroller Clock Output) */
#define  RCC_CFGR_MCOSEL_0                   ((uint32_t)0x01000000)        /*!< Bit 0 */
#define  RCC_CFGR_MCOSEL_1                   ((uint32_t)0x02000000)        /*!< Bit 1 */
#define  RCC_CFGR_MCOSEL_2                   ((uint32_t)0x04000000)        /*!< Bit 2 */

/*!< MCO configuration */
#define  RCC_CFGR_MCO_NOCLOCK                ((uint32_t)0x00000000)        /*!< No clock */
#define  RCC_CFGR_MCO_SYSCLK                 ((uint32_t)0x01000000)        /*!< System clock selected */
#define  RCC_CFGR_MCO_HSI                    ((uint32_t)0x02000000)        /*!< Internal 16 MHz RC oscillator clock selected */
#define  RCC_CFGR_MCO_MSI                    ((uint32_t)0x03000000)        /*!< Internal Medium Speed RC oscillator clock selected */
#define  RCC_CFGR_MCO_HSE                    ((uint32_t)0x04000000)        /*!< External 1-25 MHz oscillator clock selected */
#define  RCC_CFGR_MCO_PLL                    ((uint32_t)0x05000000)        /*!< PLL clock divided */
#define  RCC_CFGR_MCO_LSI                    ((uint32_t)0x06000000)        /*!< LSI selected */
#define  RCC_CFGR_MCO_LSE                    ((uint32_t)0x07000000)        /*!< LSE selected */

#define  RCC_CFGR_MCOPRE                     ((uint32_t)0x70000000)        /*!< MCOPRE[2:0] bits (Microcontroller Clock Output Prescaler) */
#define  RCC_CFGR_MCOPRE_0                   ((uint32_t)0x10000000)        /*!< Bit 0 */
#define  RCC_CFGR_MCOPRE_1                   ((uint32_t)0x20000000)        /*!< Bit 1 */
#define  RCC_CFGR_MCOPRE_2                   ((uint32_t)0x40000000)        /*!< Bit 2 */

/*!< MCO Prescaler configuration */
#define  RCC_CFGR_MCO_DIV1                   ((uint32_t)0x00000000)        /*!< MCO Clock divided by 1 */
#define  RCC_CFGR_MCO_DIV2                   ((uint32_t)0x10000000)        /*!< MCO Clock divided by 2 */
#define  RCC_CFGR_MCO_DIV4                   ((uint32_t)0x20000000)        /*!< MCO Clock divided by 4 */
#define  RCC_CFGR_MCO_DIV8                   ((uint32_t)0x30000000)        /*!< MCO Clock divided by 8 */
#define  RCC_CFGR_MCO_DIV16                  ((uint32_t)0x40000000)        /*!< MCO Clock divided by 16 */

/*!<******************  Bit definition for RCC_CIR register  ********************/
#define  RCC_CIR_LSIRDYF                     ((uint32_t)0x00000001)        /*!< LSI Ready Interrupt flag */
#define  RCC_CIR_LSERDYF                     ((uint32_t)0x00000002)        /*!< LSE Ready Interrupt flag */
#define  RCC_CIR_HSIRDYF                     ((uint32_t)0x00000004)        /*!< HSI Ready Interrupt flag */
#define  RCC_CIR_HSERDYF                     ((uint32_t)0x00000008)        /*!< HSE Ready Interrupt flag */
#define  RCC_CIR_PLLRDYF                     ((uint32_t)0x00000010)        /*!< PLL Ready Interrupt flag */
#define  RCC_CIR_MSIRDYF                     ((uint32_t)0x00000020)        /*!< MSI Ready Interrupt flag */
#define  RCC_CIR_CSSF                        ((uint32_t)0x00000080)        /*!< Clock Security System Interrupt flag */

#define  RCC_CIR_LSIRDYIE                    ((uint32_t)0x00000100)        /*!< LSI Ready Interrupt Enable */
#define  RCC_CIR_LSERDYIE                    ((uint32_t)0x00000200)        /*!< LSE Ready Interrupt Enable */
#define  RCC_CIR_HSIRDYIE                    ((uint32_t)0x00000400)        /*!< HSI Ready Interrupt Enable */
#define  RCC_CIR_HSERDYIE                    ((uint32_t)0x00000800)        /*!< HSE Ready Interrupt Enable */
#define  RCC_CIR_PLLRDYIE                    ((uint32_t)0x00001000)        /*!< PLL Ready Interrupt Enable */
#define  RCC_CIR_MSIRDYIE                    ((uint32_t)0x00002000)        /*!< MSI Ready Interrupt Enable */

#define  RCC_CIR_LSIRDYC                     ((uint32_t)0x00010000)        /*!< LSI Ready Interrupt Clear */
#define  RCC_CIR_LSERDYC                     ((uint32_t)0x00020000)        /*!< LSE Ready Interrupt Clear */
#define  RCC_CIR_HSIRDYC                     ((uint32_t)0x00040000)        /*!< HSI Ready Interrupt Clear */
#define  RCC_CIR_HSERDYC                     ((uint32_t)0x00080000)        /*!< HSE Ready Interrupt Clear */
#define  RCC_CIR_PLLRDYC                     ((uint32_t)0x00100000)        /*!< PLL Ready Interrupt Clear */
#define  RCC_CIR_MSIRDYC                     ((uint32_t)0x00200000)        /*!< MSI Ready Interrupt Clear */
#define  RCC_CIR_CSSC                        ((uint32_t)0x00800000)        /*!< Clock Security System Interrupt Clear */


/*****************  Bit definition for RCC_AHBRSTR register  ******************/
#define  RCC_AHBRSTR_GPIOARST                ((uint32_t)0x00000001)        /*!< GPIO port A reset */
#define  RCC_AHBRSTR_GPIOBRST                ((uint32_t)0x00000002)        /*!< GPIO port B reset */
#define  RCC_AHBRSTR_GPIOCRST                ((uint32_t)0x00000004)        /*!< GPIO port C reset */
#define  RCC_AHBRSTR_GPIODRST                ((uint32_t)0x00000008)        /*!< GPIO port D reset */
#define  RCC_AHBRSTR_GPIOERST                ((uint32_t)0x00000010)        /*!< GPIO port E reset */
#define  RCC_AHBRSTR_GPIOHRST                ((uint32_t)0x00000020)        /*!< GPIO port H reset */
#define  RCC_AHBRSTR_CRCRST                  ((uint32_t)0x00001000)        /*!< CRC reset */
#define  RCC_AHBRSTR_FLITFRST                ((uint32_t)0x00008000)        /*!< FLITF reset */
#define  RCC_AHBRSTR_DMA1RST                 ((uint32_t)0x01000000)        /*!< DMA1 reset */
 
/*****************  Bit definition for RCC_APB2RSTR register  *****************/
#define  RCC_APB2RSTR_SYSCFGRST              ((uint32_t)0x00000001)        /*!< System Configuration SYSCFG reset */
#define  RCC_APB2RSTR_TIM9RST                ((uint32_t)0x00000004)        /*!< TIM9 reset */
#define  RCC_APB2RSTR_TIM10RST               ((uint32_t)0x00000008)        /*!< TIM10 reset */
#define  RCC_APB2RSTR_TIM11RST               ((uint32_t)0x00000010)        /*!< TIM11 reset */
#define  RCC_APB2RSTR_ADC1RST                ((uint32_t)0x00000200)        /*!< ADC1 reset */
#define  RCC_APB2RSTR_SPI1RST                ((uint32_t)0x00001000)        /*!< SPI1 reset */
#define  RCC_APB2RSTR_USART1RST              ((uint32_t)0x00004000)        /*!< USART1 reset */

/*****************  Bit definition for RCC_APB1RSTR register  *****************/
#define  RCC_APB1RSTR_TIM2RST                ((uint32_t)0x00000001)        /*!< Timer 2 reset */
#define  RCC_APB1RSTR_TIM3RST                ((uint32_t)0x00000002)        /*!< Timer 3 reset */
#define  RCC_APB1RSTR_TIM4RST                ((uint32_t)0x00000004)        /*!< Timer 4 reset */
#define  RCC_APB1RSTR_TIM6RST                ((uint32_t)0x00000010)        /*!< Timer 6 reset */
#define  RCC_APB1RSTR_TIM7RST                ((uint32_t)0x00000020)        /*!< Timer 7 reset */
#define  RCC_APB1RSTR_LCDRST                 ((uint32_t)0x00000200)        /*!< LCD reset */
#define  RCC_APB1RSTR_WWDGRST                ((uint32_t)0x00000800)        /*!< Window Watchdog reset */
#define  RCC_APB1RSTR_SPI2RST                ((uint32_t)0x00004000)        /*!< SPI 2 reset */
#define  RCC_APB1RSTR_USART2RST              ((uint32_t)0x00020000)        /*!< USART 2 reset */
#define  RCC_APB1RSTR_USART3RST              ((uint32_t)0x00040000)        /*!< RUSART 3 reset */
#define  RCC_APB1RSTR_I2C1RST                ((uint32_t)0x00200000)        /*!< I2C 1 reset */
#define  RCC_APB1RSTR_I2C2RST                ((uint32_t)0x00400000)        /*!< I2C 2 reset */
#define  RCC_APB1RSTR_USBRST                 ((uint32_t)0x00800000)        /*!< USB reset */
#define  RCC_APB1RSTR_PWRRST                 ((uint32_t)0x10000000)        /*!< Power interface reset */
#define  RCC_APB1RSTR_DACRST                 ((uint32_t)0x20000000)        /*!< DAC interface reset */
#define  RCC_APB1RSTR_COMPRST                ((uint32_t)0x80000000)        /*!< Comparator interface reset */

/******************  Bit definition for RCC_AHBENR register  ******************/
#define  RCC_AHBENR_GPIOAEN                  ((uint32_t)0x00000001)        /*!< GPIO port A clock enable */
#define  RCC_AHBENR_GPIOBEN                  ((uint32_t)0x00000002)        /*!< GPIO port B clock enable */
#define  RCC_AHBENR_GPIOCEN                  ((uint32_t)0x00000004)        /*!< GPIO port C clock enable */
#define  RCC_AHBENR_GPIODEN                  ((uint32_t)0x00000008)        /*!< GPIO port D clock enable */
#define  RCC_AHBENR_GPIOEEN                  ((uint32_t)0x00000010)        /*!< GPIO port E clock enable */
#define  RCC_AHBENR_GPIOHEN                  ((uint32_t)0x00000020)        /*!< GPIO port H clock enable */
#define  RCC_AHBENR_CRCEN                    ((uint32_t)0x00001000)        /*!< CRC clock enable */
#define  RCC_AHBENR_FLITFEN                  ((uint32_t)0x00008000)        /*!< FLITF clock enable (has effect only when
                                                                                the Flash memory is in power down mode) */
#define  RCC_AHBENR_DMA1EN                   ((uint32_t)0x01000000)        /*!< DMA1 clock enable */


/******************  Bit definition for RCC_APB2ENR register  *****************/
#define  RCC_APB2ENR_SYSCFGEN                ((uint32_t)0x00000001)         /*!< System Configuration SYSCFG clock enable */
#define  RCC_APB2ENR_TIM9EN                  ((uint32_t)0x00000004)         /*!< TIM9 interface clock enable */
#define  RCC_APB2ENR_TIM10EN                 ((uint32_t)0x00000008)         /*!< TIM10 interface clock enable */
#define  RCC_APB2ENR_TIM11EN                 ((uint32_t)0x00000010)         /*!< TIM11 Timer clock enable */
#define  RCC_APB2ENR_ADC1EN                  ((uint32_t)0x00000200)         /*!< ADC1 clock enable */
#define  RCC_APB2ENR_SPI1EN                  ((uint32_t)0x00001000)         /*!< SPI1 clock enable */
#define  RCC_APB2ENR_USART1EN                ((uint32_t)0x00004000)         /*!< USART1 clock enable */


/*****************  Bit definition for RCC_APB1ENR register  ******************/
#define  RCC_APB1ENR_TIM2EN                  ((uint32_t)0x00000001)        /*!< Timer 2 clock enabled*/
#define  RCC_APB1ENR_TIM3EN                  ((uint32_t)0x00000002)        /*!< Timer 3 clock enable */
#define  RCC_APB1ENR_TIM4EN                  ((uint32_t)0x00000004)        /*!< Timer 4 clock enable */
#define  RCC_APB1ENR_TIM6EN                  ((uint32_t)0x00000010)        /*!< Timer 6 clock enable */
#define  RCC_APB1ENR_TIM7EN                  ((uint32_t)0x00000020)        /*!< Timer 7 clock enable */
#define  RCC_APB1ENR_LCDEN                   ((uint32_t)0x00000200)        /*!< LCD clock enable */
#define  RCC_APB1ENR_WWDGEN                  ((uint32_t)0x00000800)        /*!< Window Watchdog clock enable */
#define  RCC_APB1ENR_SPI2EN                  ((uint32_t)0x00004000)        /*!< SPI 2 clock enable */
#define  RCC_APB1ENR_USART2EN                ((uint32_t)0x00020000)        /*!< USART 2 clock enable */
#define  RCC_APB1ENR_USART3EN                ((uint32_t)0x00040000)        /*!< USART 3 clock enable */
#define  RCC_APB1ENR_I2C1EN                  ((uint32_t)0x00200000)        /*!< I2C 1 clock enable */
#define  RCC_APB1ENR_I2C2EN                  ((uint32_t)0x00400000)        /*!< I2C 2 clock enable */
#define  RCC_APB1ENR_USBEN                   ((uint32_t)0x00800000)        /*!< USB clock enable */
#define  RCC_APB1ENR_PWREN                   ((uint32_t)0x10000000)        /*!< Power interface clock enable */
#define  RCC_APB1ENR_DACEN                   ((uint32_t)0x20000000)        /*!< DAC interface clock enable */
#define  RCC_APB1ENR_COMPEN                  ((uint32_t)0x80000000)        /*!< Comparator interface clock enable */

/******************  Bit definition for RCC_AHBLPENR register  ****************/
#define  RCC_AHBLPENR_GPIOALPEN              ((uint32_t)0x00000001)        /*!< GPIO port A clock enabled in sleep mode */
#define  RCC_AHBLPENR_GPIOBLPEN              ((uint32_t)0x00000002)        /*!< GPIO port B clock enabled in sleep mode */
#define  RCC_AHBLPENR_GPIOCLPEN              ((uint32_t)0x00000004)        /*!< GPIO port C clock enabled in sleep mode */
#define  RCC_AHBLPENR_GPIODLPEN              ((uint32_t)0x00000008)        /*!< GPIO port D clock enabled in sleep mode */
#define  RCC_AHBLPENR_GPIOELPEN              ((uint32_t)0x00000010)        /*!< GPIO port E clock enabled in sleep mode */
#define  RCC_AHBLPENR_GPIOHLPEN              ((uint32_t)0x00000020)        /*!< GPIO port H clock enabled in sleep mode */
#define  RCC_AHBLPENR_CRCLPEN                ((uint32_t)0x00001000)        /*!< CRC clock enabled in sleep mode */
#define  RCC_AHBLPENR_FLITFLPEN              ((uint32_t)0x00008000)        /*!< Flash Interface clock enabled in sleep mode
                                                                                (has effect only when the Flash memory is
                                                                                 in power down mode) */
#define  RCC_AHBLPENR_SRAMLPEN               ((uint32_t)0x00010000)        /*!< SRAM clock enabled in sleep mode */
#define  RCC_AHBLPENR_DMA1LPEN               ((uint32_t)0x01000000)        /*!< DMA1 clock enabled in sleep mode */

/******************  Bit definition for RCC_APB2LPENR register  ***************/
#define  RCC_APB2LPENR_SYSCFGLPEN            ((uint32_t)0x00000001)         /*!< System Configuration SYSCFG clock enabled in sleep mode */
#define  RCC_APB2LPENR_TIM9LPEN              ((uint32_t)0x00000004)         /*!< TIM9 interface clock enabled in sleep mode */
#define  RCC_APB2LPENR_TIM10LPEN             ((uint32_t)0x00000008)         /*!< TIM10 interface clock enabled in sleep mode */
#define  RCC_APB2LPENR_TIM11LPEN             ((uint32_t)0x00000010)         /*!< TIM11 Timer clock enabled in sleep mode */
#define  RCC_APB2LPENR_ADC1LPEN              ((uint32_t)0x00000200)         /*!< ADC1 clock enabled in sleep mode */
#define  RCC_APB2LPENR_SPI1LPEN              ((uint32_t)0x00001000)         /*!< SPI1 clock enabled in sleep mode */
#define  RCC_APB2LPENR_USART1LPEN            ((uint32_t)0x00004000)         /*!< USART1 clock enabled in sleep mode */

/*****************  Bit definition for RCC_APB1LPENR register  ****************/
#define  RCC_APB1LPENR_TIM2LPEN              ((uint32_t)0x00000001)        /*!< Timer 2 clock enabled in sleep mode */
#define  RCC_APB1LPENR_TIM3LPEN              ((uint32_t)0x00000002)        /*!< Timer 3 clock enabled in sleep mode */
#define  RCC_APB1LPENR_TIM4LPEN              ((uint32_t)0x00000004)        /*!< Timer 4 clock enabled in sleep mode */
#define  RCC_APB1LPENR_TIM6LPEN              ((uint32_t)0x00000010)        /*!< Timer 6 clock enabled in sleep mode */
#define  RCC_APB1LPENR_TIM7LPEN              ((uint32_t)0x00000020)        /*!< Timer 7 clock enabled in sleep mode */
#define  RCC_APB1LPENR_LCDLPEN               ((uint32_t)0x00000200)        /*!< LCD clock enabled in sleep mode */
#define  RCC_APB1LPENR_WWDGLPEN              ((uint32_t)0x00000800)        /*!< Window Watchdog clock enabled in sleep mode */
#define  RCC_APB1LPENR_SPI2LPEN              ((uint32_t)0x00004000)        /*!< SPI 2 clock enabled in sleep mode */
#define  RCC_APB1LPENR_USART2LPEN            ((uint32_t)0x00020000)        /*!< USART 2 clock enabled in sleep mode */
#define  RCC_APB1LPENR_USART3LPEN            ((uint32_t)0x00040000)        /*!< USART 3 clock enabled in sleep mode */
#define  RCC_APB1LPENR_I2C1LPEN              ((uint32_t)0x00200000)        /*!< I2C 1 clock enabled in sleep mode */
#define  RCC_APB1LPENR_I2C2LPEN              ((uint32_t)0x00400000)        /*!< I2C 2 clock enabled in sleep mode */
#define  RCC_APB1LPENR_USBLPEN               ((uint32_t)0x00800000)        /*!< USB clock enabled in sleep mode */
#define  RCC_APB1LPENR_PWRLPEN               ((uint32_t)0x10000000)        /*!< Power interface clock enabled in sleep mode */
#define  RCC_APB1LPENR_DACLPEN               ((uint32_t)0x20000000)        /*!< DAC interface clock enabled in sleep mode */
#define  RCC_APB1LPENR_COMPLPEN              ((uint32_t)0x80000000)        /*!< Comparator interface clock enabled in sleep mode*/

/*******************  Bit definition for RCC_CSR register  ********************/
#define  RCC_CSR_LSION                      ((uint32_t)0x00000001)        /*!< Internal Low Speed oscillator enable */
#define  RCC_CSR_LSIRDY                     ((uint32_t)0x00000002)        /*!< Internal Low Speed oscillator Ready */

#define  RCC_CSR_LSEON                      ((uint32_t)0x00000100)        /*!< External Low Speed oscillator enable */
#define  RCC_CSR_LSERDY                     ((uint32_t)0x00000200)        /*!< External Low Speed oscillator Ready */
#define  RCC_CSR_LSEBYP                     ((uint32_t)0x00000400)        /*!< External Low Speed oscillator Bypass */

#define  RCC_CSR_RTCSEL                     ((uint32_t)0x00030000)        /*!< RTCSEL[1:0] bits (RTC clock source selection) */
#define  RCC_CSR_RTCSEL_0                   ((uint32_t)0x00010000)        /*!< Bit 0 */
#define  RCC_CSR_RTCSEL_1                   ((uint32_t)0x00020000)        /*!< Bit 1 */

/*!< RTC congiguration */
#define  RCC_CSR_RTCSEL_NOCLOCK             ((uint32_t)0x00000000)        /*!< No clock */
#define  RCC_CSR_RTCSEL_LSE                 ((uint32_t)0x00010000)        /*!< LSE oscillator clock used as RTC clock */
#define  RCC_CSR_RTCSEL_LSI                 ((uint32_t)0x00020000)        /*!< LSI oscillator clock used as RTC clock */
#define  RCC_CSR_RTCSEL_HSE                 ((uint32_t)0x00030000)        /*!< HSE oscillator clock divided by 2, 4, 8 or 16 by RTCPRE used as RTC clock */

#define  RCC_CSR_RTCEN                      ((uint32_t)0x00400000)        /*!< RTC clock enable */
#define  RCC_CSR_RTCRST                     ((uint32_t)0x00800000)        /*!< RTC reset  */
 
#define  RCC_CSR_RMVF                       ((uint32_t)0x01000000)        /*!< Remove reset flag */
#define  RCC_CSR_OBLRSTF                    ((uint32_t)0x02000000)        /*!< Option Bytes Loader reset flag */
#define  RCC_CSR_PINRSTF                    ((uint32_t)0x04000000)        /*!< PIN reset flag */
#define  RCC_CSR_PORRSTF                    ((uint32_t)0x08000000)        /*!< POR/PDR reset flag */
#define  RCC_CSR_SFTRSTF                    ((uint32_t)0x10000000)        /*!< Software Reset flag */
#define  RCC_CSR_IWDGRSTF                   ((uint32_t)0x20000000)        /*!< Independent Watchdog reset flag */
#define  RCC_CSR_WWDGRSTF                   ((uint32_t)0x40000000)        /*!< Window watchdog reset flag */
#define  RCC_CSR_LPWRRSTF                   ((uint32_t)0x80000000)        /*!< Low-Power reset flag */


/******************************************************************************/
/*                                                                            */
/*                             Real-Time Clock                                */
/*                                                                            */
/******************************************************************************/
/********************  Bits definition for RTC_TR register  *******************/
#define RTC_TR_PM                            ((uint32_t)0x00400000)
#define RTC_TR_HT                            ((uint32_t)0x00300000)
#define RTC_TR_HT_0                          ((uint32_t)0x00100000)
#define RTC_TR_HT_1                          ((uint32_t)0x00200000)
#define RTC_TR_HU                            ((uint32_t)0x000F0000)
#define RTC_TR_HU_0                          ((uint32_t)0x00010000)
#define RTC_TR_HU_1                          ((uint32_t)0x00020000)
#define RTC_TR_HU_2                          ((uint32_t)0x00040000)
#define RTC_TR_HU_3                          ((uint32_t)0x00080000)
#define RTC_TR_MNT                           ((uint32_t)0x00007000)
#define RTC_TR_MNT_0                         ((uint32_t)0x00001000)
#define RTC_TR_MNT_1                         ((uint32_t)0x00002000)
#define RTC_TR_MNT_2                         ((uint32_t)0x00004000)
#define RTC_TR_MNU                           ((uint32_t)0x00000F00)
#define RTC_TR_MNU_0                         ((uint32_t)0x00000100)
#define RTC_TR_MNU_1                         ((uint32_t)0x00000200)
#define RTC_TR_MNU_2                         ((uint32_t)0x00000400)
#define RTC_TR_MNU_3                         ((uint32_t)0x00000800)
#define RTC_TR_ST                            ((uint32_t)0x00000070)
#define RTC_TR_ST_0                          ((uint32_t)0x00000010)
#define RTC_TR_ST_1                          ((uint32_t)0x00000020)
#define RTC_TR_ST_2                          ((uint32_t)0x00000040)
#define RTC_TR_SU                            ((uint32_t)0x0000000F)
#define RTC_TR_SU_0                          ((uint32_t)0x00000001)
#define RTC_TR_SU_1                          ((uint32_t)0x00000002)
#define RTC_TR_SU_2                          ((uint32_t)0x00000004)
#define RTC_TR_SU_3                          ((uint32_t)0x00000008)

/********************  Bits definition for RTC_DR register  *******************/
#define RTC_DR_YT                            ((uint32_t)0x00F00000)
#define RTC_DR_YT_0                          ((uint32_t)0x00100000)
#define RTC_DR_YT_1                          ((uint32_t)0x00200000)
#define RTC_DR_YT_2                          ((uint32_t)0x00400000)
#define RTC_DR_YT_3                          ((uint32_t)0x00800000)
#define RTC_DR_YU                            ((uint32_t)0x000F0000)
#define RTC_DR_YU_0                          ((uint32_t)0x00010000)
#define RTC_DR_YU_1                          ((uint32_t)0x00020000)
#define RTC_DR_YU_2                          ((uint32_t)0x00040000)
#define RTC_DR_YU_3                          ((uint32_t)0x00080000)
#define RTC_DR_WDU                           ((uint32_t)0x0000E000)
#define RTC_DR_WDU_0                         ((uint32_t)0x00002000)
#define RTC_DR_WDU_1                         ((uint32_t)0x00004000)
#define RTC_DR_WDU_2                         ((uint32_t)0x00008000)
#define RTC_DR_MT                            ((uint32_t)0x00001000)
#define RTC_DR_MU                            ((uint32_t)0x00000F00)
#define RTC_DR_MU_0                          ((uint32_t)0x00000100)
#define RTC_DR_MU_1                          ((uint32_t)0x00000200)
#define RTC_DR_MU_2                          ((uint32_t)0x00000400)
#define RTC_DR_MU_3                          ((uint32_t)0x00000800)
#define RTC_DR_DT                            ((uint32_t)0x00000030)
#define RTC_DR_DT_0                          ((uint32_t)0x00000010)
#define RTC_DR_DT_1                          ((uint32_t)0x00000020)
#define RTC_DR_DU                            ((uint32_t)0x0000000F)
#define RTC_DR_DU_0                          ((uint32_t)0x00000001)
#define RTC_DR_DU_1                          ((uint32_t)0x00000002)
#define RTC_DR_DU_2                          ((uint32_t)0x00000004)
#define RTC_DR_DU_3                          ((uint32_t)0x00000008)

/********************  Bits definition for RTC_CR register  *******************/
#define RTC_CR_COE                           ((uint32_t)0x00800000)
#define RTC_CR_OSEL                          ((uint32_t)0x00600000)
#define RTC_CR_OSEL_0                        ((uint32_t)0x00200000)
#define RTC_CR_OSEL_1                        ((uint32_t)0x00400000)
#define RTC_CR_POL                           ((uint32_t)0x00100000)
#define RTC_CR_BCK                           ((uint32_t)0x00040000)
#define RTC_CR_SUB1H                         ((uint32_t)0x00020000)
#define RTC_CR_ADD1H                         ((uint32_t)0x00010000)
#define RTC_CR_TSIE                          ((uint32_t)0x00008000)
#define RTC_CR_WUTIE                         ((uint32_t)0x00004000)
#define RTC_CR_ALRBIE                        ((uint32_t)0x00002000)
#define RTC_CR_ALRAIE                        ((uint32_t)0x00001000)
#define RTC_CR_TSE                           ((uint32_t)0x00000800)
#define RTC_CR_WUTE                          ((uint32_t)0x00000400)
#define RTC_CR_ALRBE                         ((uint32_t)0x00000200)
#define RTC_CR_ALRAE                         ((uint32_t)0x00000100)
#define RTC_CR_DCE                           ((uint32_t)0x00000080)
#define RTC_CR_FMT                           ((uint32_t)0x00000040)
#define RTC_CR_REFCKON                       ((uint32_t)0x00000010)
#define RTC_CR_TSEDGE                        ((uint32_t)0x00000008)
#define RTC_CR_WUCKSEL                       ((uint32_t)0x00000007)
#define RTC_CR_WUCKSEL_0                     ((uint32_t)0x00000001)
#define RTC_CR_WUCKSEL_1                     ((uint32_t)0x00000002)
#define RTC_CR_WUCKSEL_2                     ((uint32_t)0x00000004)

/********************  Bits definition for RTC_ISR register  ******************/
#define RTC_ISR_TAMPF                        ((uint32_t)0x00002000)
#define RTC_ISR_TSOVF                        ((uint32_t)0x00001000)
#define RTC_ISR_TSF                          ((uint32_t)0x00000800)
#define RTC_ISR_WUTF                         ((uint32_t)0x00000400)
#define RTC_ISR_ALRBF                        ((uint32_t)0x00000200)
#define RTC_ISR_ALRAF                        ((uint32_t)0x00000100)
#define RTC_ISR_INIT                         ((uint32_t)0x00000080)
#define RTC_ISR_INITF                        ((uint32_t)0x00000040)
#define RTC_ISR_RSF                          ((uint32_t)0x00000020)
#define RTC_ISR_INITS                        ((uint32_t)0x00000010)
#define RTC_ISR_WUTWF                        ((uint32_t)0x00000004)
#define RTC_ISR_ALRBWF                       ((uint32_t)0x00000002)
#define RTC_ISR_ALRAWF                       ((uint32_t)0x00000001)

/********************  Bits definition for RTC_PRER register  *****************/
#define RTC_PRER_PREDIV_A                    ((uint32_t)0x007F0000)
#define RTC_PRER_PREDIV_S                    ((uint32_t)0x00001FFF)

/********************  Bits definition for RTC_WUTR register  *****************/
#define RTC_WUTR_WUT                         ((uint32_t)0x0000FFFF)

/********************  Bits definition for RTC_CALIBR register  ***************/
#define RTC_CALIBR_DCS                       ((uint32_t)0x00000080)
#define RTC_CALIBR_DC                        ((uint32_t)0x0000001F)

/********************  Bits definition for RTC_ALRMAR register  ***************/
#define RTC_ALRMAR_MSK3                      ((uint32_t)0x80000000)
#define RTC_ALRMAR_WDSEL                     ((uint32_t)0x40000000)
#define RTC_ALRMAR_DT                        ((uint32_t)0x30000000)
#define RTC_ALRMAR_DT_0                      ((uint32_t)0x10000000)
#define RTC_ALRMAR_DT_1                      ((uint32_t)0x20000000)
#define RTC_ALRMAR_DU                        ((uint32_t)0x0F000000)
#define RTC_ALRMAR_DU_0                      ((uint32_t)0x01000000)
#define RTC_ALRMAR_DU_1                      ((uint32_t)0x02000000)
#define RTC_ALRMAR_DU_2                      ((uint32_t)0x04000000)
#define RTC_ALRMAR_DU_3                      ((uint32_t)0x08000000)
#define RTC_ALRMAR_MSK2                      ((uint32_t)0x00800000)
#define RTC_ALRMAR_PM                        ((uint32_t)0x00400000)
#define RTC_ALRMAR_HT                        ((uint32_t)0x00300000)
#define RTC_ALRMAR_HT_0                      ((uint32_t)0x00100000)
#define RTC_ALRMAR_HT_1                      ((uint32_t)0x00200000)
#define RTC_ALRMAR_HU                        ((uint32_t)0x000F0000)
#define RTC_ALRMAR_HU_0                      ((uint32_t)0x00010000)
#define RTC_ALRMAR_HU_1                      ((uint32_t)0x00020000)
#define RTC_ALRMAR_HU_2                      ((uint32_t)0x00040000)
#define RTC_ALRMAR_HU_3                      ((uint32_t)0x00080000)
#define RTC_ALRMAR_MSK1                      ((uint32_t)0x00008000)
#define RTC_ALRMAR_MNT                       ((uint32_t)0x00007000)
#define RTC_ALRMAR_MNT_0                     ((uint32_t)0x00001000)
#define RTC_ALRMAR_MNT_1                     ((uint32_t)0x00002000)
#define RTC_ALRMAR_MNT_2                     ((uint32_t)0x00004000)
#define RTC_ALRMAR_MNU                       ((uint32_t)0x00000F00)
#define RTC_ALRMAR_MNU_0                     ((uint32_t)0x00000100)
#define RTC_ALRMAR_MNU_1                     ((uint32_t)0x00000200)
#define RTC_ALRMAR_MNU_2                     ((uint32_t)0x00000400)
#define RTC_ALRMAR_MNU_3                     ((uint32_t)0x00000800)
#define RTC_ALRMAR_MSK0                      ((uint32_t)0x00000080)
#define RTC_ALRMAR_ST                        ((uint32_t)0x00000070)
#define RTC_ALRMAR_ST_0                      ((uint32_t)0x00000010)
#define RTC_ALRMAR_ST_1                      ((uint32_t)0x00000020)
#define RTC_ALRMAR_ST_2                      ((uint32_t)0x00000040)
#define RTC_ALRMAR_SU                        ((uint32_t)0x0000000F)
#define RTC_ALRMAR_SU_0                      ((uint32_t)0x00000001)
#define RTC_ALRMAR_SU_1                      ((uint32_t)0x00000002)
#define RTC_ALRMAR_SU_2                      ((uint32_t)0x00000004)
#define RTC_ALRMAR_SU_3                      ((uint32_t)0x00000008)

/********************  Bits definition for RTC_ALRMBR register  ***************/
#define RTC_ALRMBR_MSK3                      ((uint32_t)0x80000000)
#define RTC_ALRMBR_WDSEL                     ((uint32_t)0x40000000)
#define RTC_ALRMBR_DT                        ((uint32_t)0x30000000)
#define RTC_ALRMBR_DT_0                      ((uint32_t)0x10000000)
#define RTC_ALRMBR_DT_1                      ((uint32_t)0x20000000)
#define RTC_ALRMBR_DU                        ((uint32_t)0x0F000000)
#define RTC_ALRMBR_DU_0                      ((uint32_t)0x01000000)
#define RTC_ALRMBR_DU_1                      ((uint32_t)0x02000000)
#define RTC_ALRMBR_DU_2                      ((uint32_t)0x04000000)
#define RTC_ALRMBR_DU_3                      ((uint32_t)0x08000000)
#define RTC_ALRMBR_MSK2                      ((uint32_t)0x00800000)
#define RTC_ALRMBR_PM                        ((uint32_t)0x00400000)
#define RTC_ALRMBR_HT                        ((uint32_t)0x00300000)
#define RTC_ALRMBR_HT_0                      ((uint32_t)0x00100000)
#define RTC_ALRMBR_HT_1                      ((uint32_t)0x00200000)
#define RTC_ALRMBR_HU                        ((uint32_t)0x000F0000)
#define RTC_ALRMBR_HU_0                      ((uint32_t)0x00010000)
#define RTC_ALRMBR_HU_1                      ((uint32_t)0x00020000)
#define RTC_ALRMBR_HU_2                      ((uint32_t)0x00040000)
#define RTC_ALRMBR_HU_3                      ((uint32_t)0x00080000)
#define RTC_ALRMBR_MSK1                      ((uint32_t)0x00008000)
#define RTC_ALRMBR_MNT                       ((uint32_t)0x00007000)
#define RTC_ALRMBR_MNT_0                     ((uint32_t)0x00001000)
#define RTC_ALRMBR_MNT_1                     ((uint32_t)0x00002000)
#define RTC_ALRMBR_MNT_2                     ((uint32_t)0x00004000)
#define RTC_ALRMBR_MNU                       ((uint32_t)0x00000F00)
#define RTC_ALRMBR_MNU_0                     ((uint32_t)0x00000100)
#define RTC_ALRMBR_MNU_1                     ((uint32_t)0x00000200)
#define RTC_ALRMBR_MNU_2                     ((uint32_t)0x00000400)
#define RTC_ALRMBR_MNU_3                     ((uint32_t)0x00000800)
#define RTC_ALRMBR_MSK0                      ((uint32_t)0x00000080)
#define RTC_ALRMBR_ST                        ((uint32_t)0x00000070)
#define RTC_ALRMBR_ST_0                      ((uint32_t)0x00000010)
#define RTC_ALRMBR_ST_1                      ((uint32_t)0x00000020)
#define RTC_ALRMBR_ST_2                      ((uint32_t)0x00000040)
#define RTC_ALRMBR_SU                        ((uint32_t)0x0000000F)
#define RTC_ALRMBR_SU_0                      ((uint32_t)0x00000001)
#define RTC_ALRMBR_SU_1                      ((uint32_t)0x00000002)
#define RTC_ALRMBR_SU_2                      ((uint32_t)0x00000004)
#define RTC_ALRMBR_SU_3                      ((uint32_t)0x00000008)

/********************  Bits definition for RTC_WRP register  ******************/
#define RTC_WRP_KEY                          ((uint32_t)0x000000FF)

/********************  Bits definition for RTC_TSTR register  *****************/
#define RTC_TSTR_PM                          ((uint32_t)0x00400000)
#define RTC_TSTR_HT                          ((uint32_t)0x00300000)
#define RTC_TSTR_HT_0                        ((uint32_t)0x00100000)
#define RTC_TSTR_HT_1                        ((uint32_t)0x00200000)
#define RTC_TSTR_HU                          ((uint32_t)0x000F0000)
#define RTC_TSTR_HU_0                        ((uint32_t)0x00010000)
#define RTC_TSTR_HU_1                        ((uint32_t)0x00020000)
#define RTC_TSTR_HU_2                        ((uint32_t)0x00040000)
#define RTC_TSTR_HU_3                        ((uint32_t)0x00080000)
#define RTC_TSTR_MNT                         ((uint32_t)0x00007000)
#define RTC_TSTR_MNT_0                       ((uint32_t)0x00001000)
#define RTC_TSTR_MNT_1                       ((uint32_t)0x00002000)
#define RTC_TSTR_MNT_2                       ((uint32_t)0x00004000)
#define RTC_TSTR_MNU                         ((uint32_t)0x00000F00)
#define RTC_TSTR_MNU_0                       ((uint32_t)0x00000100)
#define RTC_TSTR_MNU_1                       ((uint32_t)0x00000200)
#define RTC_TSTR_MNU_2                       ((uint32_t)0x00000400)
#define RTC_TSTR_MNU_3                       ((uint32_t)0x00000800)
#define RTC_TSTR_ST                          ((uint32_t)0x00000070)
#define RTC_TSTR_ST_0                        ((uint32_t)0x00000010)
#define RTC_TSTR_ST_1                        ((uint32_t)0x00000020)
#define RTC_TSTR_ST_2                        ((uint32_t)0x00000040)
#define RTC_TSTR_SU                          ((uint32_t)0x0000000F)
#define RTC_TSTR_SU_0                        ((uint32_t)0x00000001)
#define RTC_TSTR_SU_1                        ((uint32_t)0x00000002)
#define RTC_TSTR_SU_2                        ((uint32_t)0x00000004)
#define RTC_TSTR_SU_3                        ((uint32_t)0x00000008)

/********************  Bits definition for RTC_TSDR register  *****************/
#define RTC_TSDR_WDU                         ((uint32_t)0x0000E000)
#define RTC_TSDR_WDU_0                       ((uint32_t)0x00002000)
#define RTC_TSDR_WDU_1                       ((uint32_t)0x00004000)
#define RTC_TSDR_WDU_2                       ((uint32_t)0x00008000)
#define RTC_TSDR_MT                          ((uint32_t)0x00001000)
#define RTC_TSDR_MU                          ((uint32_t)0x00000F00)
#define RTC_TSDR_MU_0                        ((uint32_t)0x00000100)
#define RTC_TSDR_MU_1                        ((uint32_t)0x00000200)
#define RTC_TSDR_MU_2                        ((uint32_t)0x00000400)
#define RTC_TSDR_MU_3                        ((uint32_t)0x00000800)
#define RTC_TSDR_DT                          ((uint32_t)0x00000030)
#define RTC_TSDR_DT_0                        ((uint32_t)0x00000010)
#define RTC_TSDR_DT_1                        ((uint32_t)0x00000020)
#define RTC_TSDR_DU                          ((uint32_t)0x0000000F)
#define RTC_TSDR_DU_0                        ((uint32_t)0x00000001)
#define RTC_TSDR_DU_1                        ((uint32_t)0x00000002)
#define RTC_TSDR_DU_2                        ((uint32_t)0x00000004)
#define RTC_TSDR_DU_3                        ((uint32_t)0x00000008)

/********************  Bits definition for RTC_TAFCR register  ****************/
#define RTC_TAFCR_ALARMOUTTYPE               ((uint32_t)0x00040000)
#define RTC_TAFCR_TAMPIE                     ((uint32_t)0x00000004)
#define RTC_TAFCR_TAMPEDGE                   ((uint32_t)0x00000002)
#define RTC_TAFCR_TAMPE                      ((uint32_t)0x00000001)

/********************  Bits definition for RTC_BK0R register  *****************/
#define RTC_BK0R_BCK                         ((uint32_t)0xFFFFFFFF)

/********************  Bits definition for RTC_BK1R register  *****************/
#define RTC_BK1R_BCK                         ((uint32_t)0xFFFFFFFF)

/********************  Bits definition for RTC_BK2R register  *****************/
#define RTC_BK2R_BCK                         ((uint32_t)0xFFFFFFFF)

/********************  Bits definition for RTC_BK3R register  *****************/
#define RTC_BK3R_BCK                         ((uint32_t)0xFFFFFFFF)

/********************  Bits definition for RTC_BK4R register  *****************/
#define RTC_BK4R_BCK                         ((uint32_t)0xFFFFFFFF)

/********************  Bits definition for RTC_BK5R register  *****************/
#define RTC_BK5R_BCK                         ((uint32_t)0xFFFFFFFF)

/********************  Bits definition for RTC_BK6R register  *****************/
#define RTC_BK6R_BCK                         ((uint32_t)0xFFFFFFFF)

/********************  Bits definition for RTC_BK7R register  *****************/
#define RTC_BK7R_BCK                         ((uint32_t)0xFFFFFFFF)

/********************  Bits definition for RTC_BK8R register  *****************/
#define RTC_BK8R_BCK                         ((uint32_t)0xFFFFFFFF)

/********************  Bits definition for RTC_BK9R register  *****************/
#define RTC_BK9R_BCK                         ((uint32_t)0xFFFFFFFF)

/********************  Bits definition for RTC_BK10R register  ****************/
#define RTC_BK10R_BCK                        ((uint32_t)0xFFFFFFFF)

/********************  Bits definition for RTC_BK11R register  ****************/
#define RTC_BK11R_BCK                        ((uint32_t)0xFFFFFFFF)

/********************  Bits definition for RTC_BK12R register  ****************/
#define RTC_BK12R_BCK                        ((uint32_t)0xFFFFFFFF)

/********************  Bits definition for RTC_BK13R register  ****************/
#define RTC_BK13R_BCK                        ((uint32_t)0xFFFFFFFF)

/********************  Bits definition for RTC_BK14R register  ****************/
#define RTC_BK14R_BCK                        ((uint32_t)0xFFFFFFFF)

/********************  Bits definition for RTC_BK15R register  ****************/
#define RTC_BK15R_BCK                        ((uint32_t)0xFFFFFFFF)

/********************  Bits definition for RTC_BK16R register  ****************/
#define RTC_BK16R_BCK                        ((uint32_t)0xFFFFFFFF)

/********************  Bits definition for RTC_BK17R register  ****************/
#define RTC_BK17R_BCK                        ((uint32_t)0xFFFFFFFF)

/********************  Bits definition for RTC_BK18R register  ****************/
#define RTC_BK18R_BCK                        ((uint32_t)0xFFFFFFFF)

/********************  Bits definition for RTC_BK19R register  ****************/
#define RTC_BK19R_BCK                        ((uint32_t)0xFFFFFFFF)

/******************************************************************************/
/*                                                                            */
/*                        Serial Peripheral Interface                         */
/*                                                                            */
/******************************************************************************/

/*******************  Bit definition for SPI_CR1 register  ********************/
#define  SPI_CR1_CPHA                        ((uint16_t)0x0001)            /*!< Clock Phase */
#define  SPI_CR1_CPOL                        ((uint16_t)0x0002)            /*!< Clock Polarity */
#define  SPI_CR1_MSTR                        ((uint16_t)0x0004)            /*!< Master Selection */

#define  SPI_CR1_BR                          ((uint16_t)0x0038)            /*!< BR[2:0] bits (Baud Rate Control) */
#define  SPI_CR1_BR_0                        ((uint16_t)0x0008)            /*!< Bit 0 */
#define  SPI_CR1_BR_1                        ((uint16_t)0x0010)            /*!< Bit 1 */
#define  SPI_CR1_BR_2                        ((uint16_t)0x0020)            /*!< Bit 2 */

#define  SPI_CR1_SPE                         ((uint16_t)0x0040)            /*!< SPI Enable */
#define  SPI_CR1_LSBFIRST                    ((uint16_t)0x0080)            /*!< Frame Format */
#define  SPI_CR1_SSI                         ((uint16_t)0x0100)            /*!< Internal slave select */
#define  SPI_CR1_SSM                         ((uint16_t)0x0200)            /*!< Software slave management */
#define  SPI_CR1_RXONLY                      ((uint16_t)0x0400)            /*!< Receive only */
#define  SPI_CR1_DFF                         ((uint16_t)0x0800)            /*!< Data Frame Format */
#define  SPI_CR1_CRCNEXT                     ((uint16_t)0x1000)            /*!< Transmit CRC next */
#define  SPI_CR1_CRCEN                       ((uint16_t)0x2000)            /*!< Hardware CRC calculation enable */
#define  SPI_CR1_BIDIOE                      ((uint16_t)0x4000)            /*!< Output enable in bidirectional mode */
#define  SPI_CR1_BIDIMODE                    ((uint16_t)0x8000)            /*!< Bidirectional data mode enable */

/*******************  Bit definition for SPI_CR2 register  ********************/
#define  SPI_CR2_RXDMAEN                     ((uint8_t)0x01)               /*!< Rx Buffer DMA Enable */
#define  SPI_CR2_TXDMAEN                     ((uint8_t)0x02)               /*!< Tx Buffer DMA Enable */
#define  SPI_CR2_SSOE                        ((uint8_t)0x04)               /*!< SS Output Enable */
#define  SPI_CR2_ERRIE                       ((uint8_t)0x20)               /*!< Error Interrupt Enable */
#define  SPI_CR2_RXNEIE                      ((uint8_t)0x40)               /*!< RX buffer Not Empty Interrupt Enable */
#define  SPI_CR2_TXEIE                       ((uint8_t)0x80)               /*!< Tx buffer Empty Interrupt Enable */

/********************  Bit definition for SPI_SR register  ********************/
#define  SPI_SR_RXNE                         ((uint8_t)0x01)               /*!< Receive buffer Not Empty */
#define  SPI_SR_TXE                          ((uint8_t)0x02)               /*!< Transmit buffer Empty */
#define  SPI_SR_CRCERR                       ((uint8_t)0x10)               /*!< CRC Error flag */
#define  SPI_SR_MODF                         ((uint8_t)0x20)               /*!< Mode fault */
#define  SPI_SR_OVR                          ((uint8_t)0x40)               /*!< Overrun flag */
#define  SPI_SR_BSY                          ((uint8_t)0x80)               /*!< Busy flag */

/********************  Bit definition for SPI_DR register  ********************/
#define  SPI_DR_DR                           ((uint16_t)0xFFFF)            /*!< Data Register */

/*******************  Bit definition for SPI_CRCPR register  ******************/
#define  SPI_CRCPR_CRCPOLY                   ((uint16_t)0xFFFF)            /*!< CRC polynomial register */

/******************  Bit definition for SPI_RXCRCR register  ******************/
#define  SPI_RXCRCR_RXCRC                    ((uint16_t)0xFFFF)            /*!< Rx CRC Register */

/******************  Bit definition for SPI_TXCRCR register  ******************/
#define  SPI_TXCRCR_TXCRC                    ((uint16_t)0xFFFF)            /*!< Tx CRC Register */

/******************************************************************************/
/*                                                                            */
/*                       System Configuration (SYSCFG)                        */
/*                                                                            */
/******************************************************************************/
/*****************  Bit definition for SYSCFG_MEMRMP register  ****************/
#define SYSCFG_MEMRMP_MEM_MODE          ((uint32_t)0x00000003) /*!< SYSCFG_Memory Remap Config */
#define SYSCFG_MEMRMP_MEM_MODE_0        ((uint32_t)0x00000001) /*!< Bit 0 */
#define SYSCFG_MEMRMP_MEM_MODE_1        ((uint32_t)0x00000002) /*!< Bit 1 */

/*****************  Bit definition for SYSCFG_PMC register  *******************/
#define SYSCFG_PMC_USB_PU               ((uint32_t)0x00000001) /*!< SYSCFG PMC */

/*****************  Bit definition for SYSCFG_EXTICR1 register  ***************/
#define SYSCFG_EXTICR1_EXTI0            ((uint16_t)0x000F) /*!< EXTI 0 configuration */
#define SYSCFG_EXTICR1_EXTI1            ((uint16_t)0x00F0) /*!< EXTI 1 configuration */
#define SYSCFG_EXTICR1_EXTI2            ((uint16_t)0x0F00) /*!< EXTI 2 configuration */
#define SYSCFG_EXTICR1_EXTI3            ((uint16_t)0xF000) /*!< EXTI 3 configuration */

/** 
  * @brief  EXTI0 configuration  
  */ 
#define SYSCFG_EXTICR1_EXTI0_PA         ((uint16_t)0x0000) /*!< PA[0] pin */
#define SYSCFG_EXTICR1_EXTI0_PB         ((uint16_t)0x0001) /*!< PB[0] pin */
#define SYSCFG_EXTICR1_EXTI0_PC         ((uint16_t)0x0002) /*!< PC[0] pin */
#define SYSCFG_EXTICR1_EXTI0_PD         ((uint16_t)0x0003) /*!< PD[0] pin */
#define SYSCFG_EXTICR1_EXTI0_PE         ((uint16_t)0x0004) /*!< PE[0] pin */
#define SYSCFG_EXTICR1_EXTI0_PH         ((uint16_t)0x0005) /*!< PH[0] pin */

/** 
  * @brief  EXTI1 configuration  
  */ 
#define SYSCFG_EXTICR1_EXTI1_PA         ((uint16_t)0x0000) /*!< PA[1] pin */
#define SYSCFG_EXTICR1_EXTI1_PB         ((uint16_t)0x0010) /*!< PB[1] pin */
#define SYSCFG_EXTICR1_EXTI1_PC         ((uint16_t)0x0020) /*!< PC[1] pin */
#define SYSCFG_EXTICR1_EXTI1_PD         ((uint16_t)0x0030) /*!< PD[1] pin */
#define SYSCFG_EXTICR1_EXTI1_PE         ((uint16_t)0x0040) /*!< PE[1] pin */
#define SYSCFG_EXTICR1_EXTI1_PH         ((uint16_t)0x0050) /*!< PH[1] pin */

/** 
  * @brief  EXTI2 configuration  
  */ 
#define SYSCFG_EXTICR1_EXTI2_PA         ((uint16_t)0x0000) /*!< PA[2] pin */
#define SYSCFG_EXTICR1_EXTI2_PB         ((uint16_t)0x0100) /*!< PB[2] pin */
#define SYSCFG_EXTICR1_EXTI2_PC         ((uint16_t)0x0200) /*!< PC[2] pin */
#define SYSCFG_EXTICR1_EXTI2_PD         ((uint16_t)0x0300) /*!< PD[2] pin */
#define SYSCFG_EXTICR1_EXTI2_PE         ((uint16_t)0x0400) /*!< PE[2] pin */
#define SYSCFG_EXTICR1_EXTI2_PH         ((uint16_t)0x0500) /*!< PH[2] pin */

/** 
  * @brief  EXTI3 configuration  
  */ 
#define SYSCFG_EXTICR1_EXTI3_PA         ((uint16_t)0x0000) /*!< PA[3] pin */
#define SYSCFG_EXTICR1_EXTI3_PB         ((uint16_t)0x1000) /*!< PB[3] pin */
#define SYSCFG_EXTICR1_EXTI3_PC         ((uint16_t)0x2000) /*!< PC[3] pin */
#define SYSCFG_EXTICR1_EXTI3_PD         ((uint16_t)0x3000) /*!< PD[3] pin */
#define SYSCFG_EXTICR1_EXTI3_PE         ((uint16_t)0x4000) /*!< PE[3] pin */

/*****************  Bit definition for SYSCFG_EXTICR2 register  *****************/
#define SYSCFG_EXTICR2_EXTI4            ((uint16_t)0x000F) /*!< EXTI 4 configuration */
#define SYSCFG_EXTICR2_EXTI5            ((uint16_t)0x00F0) /*!< EXTI 5 configuration */
#define SYSCFG_EXTICR2_EXTI6            ((uint16_t)0x0F00) /*!< EXTI 6 configuration */
#define SYSCFG_EXTICR2_EXTI7            ((uint16_t)0xF000) /*!< EXTI 7 configuration */

/** 
  * @brief  EXTI4 configuration  
  */ 
#define SYSCFG_EXTICR2_EXTI4_PA         ((uint16_t)0x0000) /*!< PA[4] pin */
#define SYSCFG_EXTICR2_EXTI4_PB         ((uint16_t)0x0001) /*!< PB[4] pin */
#define SYSCFG_EXTICR2_EXTI4_PC         ((uint16_t)0x0002) /*!< PC[4] pin */
#define SYSCFG_EXTICR2_EXTI4_PD         ((uint16_t)0x0003) /*!< PD[4] pin */
#define SYSCFG_EXTICR2_EXTI4_PE         ((uint16_t)0x0004) /*!< PE[4] pin */

/** 
  * @brief  EXTI5 configuration  
  */ 
#define SYSCFG_EXTICR2_EXTI5_PA         ((uint16_t)0x0000) /*!< PA[5] pin */
#define SYSCFG_EXTICR2_EXTI5_PB         ((uint16_t)0x0010) /*!< PB[5] pin */
#define SYSCFG_EXTICR2_EXTI5_PC         ((uint16_t)0x0020) /*!< PC[5] pin */
#define SYSCFG_EXTICR2_EXTI5_PD         ((uint16_t)0x0030) /*!< PD[5] pin */
#define SYSCFG_EXTICR2_EXTI5_PE         ((uint16_t)0x0040) /*!< PE[5] pin */

/** 
  * @brief  EXTI6 configuration  
  */ 
#define SYSCFG_EXTICR2_EXTI6_PA         ((uint16_t)0x0000) /*!< PA[6] pin */
#define SYSCFG_EXTICR2_EXTI6_PB         ((uint16_t)0x0100) /*!< PB[6] pin */
#define SYSCFG_EXTICR2_EXTI6_PC         ((uint16_t)0x0200) /*!< PC[6] pin */
#define SYSCFG_EXTICR2_EXTI6_PD         ((uint16_t)0x0300) /*!< PD[6] pin */
#define SYSCFG_EXTICR2_EXTI6_PE         ((uint16_t)0x0400) /*!< PE[6] pin */

/** 
  * @brief  EXTI7 configuration  
  */ 
#define SYSCFG_EXTICR2_EXTI7_PA         ((uint16_t)0x0000) /*!< PA[7] pin */
#define SYSCFG_EXTICR2_EXTI7_PB         ((uint16_t)0x1000) /*!< PB[7] pin */
#define SYSCFG_EXTICR2_EXTI7_PC         ((uint16_t)0x2000) /*!< PC[7] pin */
#define SYSCFG_EXTICR2_EXTI7_PD         ((uint16_t)0x3000) /*!< PD[7] pin */
#define SYSCFG_EXTICR2_EXTI7_PE         ((uint16_t)0x4000) /*!< PE[7] pin */

/*****************  Bit definition for SYSCFG_EXTICR3 register  *****************/
#define SYSCFG_EXTICR3_EXTI8            ((uint16_t)0x000F) /*!< EXTI 8 configuration */
#define SYSCFG_EXTICR3_EXTI9            ((uint16_t)0x00F0) /*!< EXTI 9 configuration */
#define SYSCFG_EXTICR3_EXTI10           ((uint16_t)0x0F00) /*!< EXTI 10 configuration */
#define SYSCFG_EXTICR3_EXTI11           ((uint16_t)0xF000) /*!< EXTI 11 configuration */
									  
/** 
  * @brief  EXTI8 configuration  
  */ 
#define SYSCFG_EXTICR3_EXTI8_PA         ((uint16_t)0x0000) /*!< PA[8] pin */
#define SYSCFG_EXTICR3_EXTI8_PB         ((uint16_t)0x0001) /*!< PB[8] pin */
#define SYSCFG_EXTICR3_EXTI8_PC         ((uint16_t)0x0002) /*!< PC[8] pin */
#define SYSCFG_EXTICR3_EXTI8_PD         ((uint16_t)0x0003) /*!< PD[8] pin */
#define SYSCFG_EXTICR3_EXTI8_PE         ((uint16_t)0x0004) /*!< PE[8] pin */

/** 
  * @brief  EXTI9 configuration  
  */ 
#define SYSCFG_EXTICR3_EXTI9_PA         ((uint16_t)0x0000) /*!< PA[9] pin */
#define SYSCFG_EXTICR3_EXTI9_PB         ((uint16_t)0x0010) /*!< PB[9] pin */
#define SYSCFG_EXTICR3_EXTI9_PC         ((uint16_t)0x0020) /*!< PC[9] pin */
#define SYSCFG_EXTICR3_EXTI9_PD         ((uint16_t)0x0030) /*!< PD[9] pin */
#define SYSCFG_EXTICR3_EXTI9_PE         ((uint16_t)0x0040) /*!< PE[9] pin */

/** 
  * @brief  EXTI10 configuration  
  */ 
#define SYSCFG_EXTICR3_EXTI10_PA        ((uint16_t)0x0000) /*!< PA[10] pin */
#define SYSCFG_EXTICR3_EXTI10_PB        ((uint16_t)0x0100) /*!< PB[10] pin */
#define SYSCFG_EXTICR3_EXTI10_PC        ((uint16_t)0x0200) /*!< PC[10] pin */
#define SYSCFG_EXTICR3_EXTI10_PD        ((uint16_t)0x0300) /*!< PD[10] pin */
#define SYSCFG_EXTICR3_EXTI10_PE        ((uint16_t)0x0400) /*!< PE[10] pin */

/** 
  * @brief  EXTI11 configuration  
  */ 
#define SYSCFG_EXTICR3_EXTI11_PA        ((uint16_t)0x0000) /*!< PA[11] pin */
#define SYSCFG_EXTICR3_EXTI11_PB        ((uint16_t)0x1000) /*!< PB[11] pin */
#define SYSCFG_EXTICR3_EXTI11_PC        ((uint16_t)0x2000) /*!< PC[11] pin */
#define SYSCFG_EXTICR3_EXTI11_PD        ((uint16_t)0x3000) /*!< PD[11] pin */
#define SYSCFG_EXTICR3_EXTI11_PE        ((uint16_t)0x4000) /*!< PE[11] pin */

/*****************  Bit definition for SYSCFG_EXTICR4 register  *****************/
#define SYSCFG_EXTICR4_EXTI12           ((uint16_t)0x000F) /*!< EXTI 12 configuration */
#define SYSCFG_EXTICR4_EXTI13           ((uint16_t)0x00F0) /*!< EXTI 13 configuration */
#define SYSCFG_EXTICR4_EXTI14           ((uint16_t)0x0F00) /*!< EXTI 14 configuration */
#define SYSCFG_EXTICR4_EXTI15           ((uint16_t)0xF000) /*!< EXTI 15 configuration */

/** 
  * @brief  EXTI12 configuration  
  */ 
#define SYSCFG_EXTICR4_EXTI12_PA        ((uint16_t)0x0000) /*!< PA[12] pin */
#define SYSCFG_EXTICR4_EXTI12_PB        ((uint16_t)0x0001) /*!< PB[12] pin */
#define SYSCFG_EXTICR4_EXTI12_PC        ((uint16_t)0x0002) /*!< PC[12] pin */
#define SYSCFG_EXTICR4_EXTI12_PD        ((uint16_t)0x0003) /*!< PD[12] pin */
#define SYSCFG_EXTICR4_EXTI12_PE        ((uint16_t)0x0004) /*!< PE[12] pin */

/** 
  * @brief  EXTI13 configuration  
  */ 
#define SYSCFG_EXTICR4_EXTI13_PA        ((uint16_t)0x0000) /*!< PA[13] pin */
#define SYSCFG_EXTICR4_EXTI13_PB        ((uint16_t)0x0010) /*!< PB[13] pin */
#define SYSCFG_EXTICR4_EXTI13_PC        ((uint16_t)0x0020) /*!< PC[13] pin */
#define SYSCFG_EXTICR4_EXTI13_PD        ((uint16_t)0x0030) /*!< PD[13] pin */
#define SYSCFG_EXTICR4_EXTI13_PE        ((uint16_t)0x0040) /*!< PE[13] pin */

/** 
  * @brief  EXTI14 configuration  
  */ 
#define SYSCFG_EXTICR4_EXTI14_PA        ((uint16_t)0x0000) /*!< PA[14] pin */
#define SYSCFG_EXTICR4_EXTI14_PB        ((uint16_t)0x0100) /*!< PB[14] pin */
#define SYSCFG_EXTICR4_EXTI14_PC        ((uint16_t)0x0200) /*!< PC[14] pin */
#define SYSCFG_EXTICR4_EXTI14_PD        ((uint16_t)0x0300) /*!< PD[14] pin */
#define SYSCFG_EXTICR4_EXTI14_PE        ((uint16_t)0x0400) /*!< PE[14] pin */

/** 
  * @brief  EXTI15 configuration  
  */ 
#define SYSCFG_EXTICR4_EXTI15_PA        ((uint16_t)0x0000) /*!< PA[15] pin */
#define SYSCFG_EXTICR4_EXTI15_PB        ((uint16_t)0x1000) /*!< PB[15] pin */
#define SYSCFG_EXTICR4_EXTI15_PC        ((uint16_t)0x2000) /*!< PC[15] pin */
#define SYSCFG_EXTICR4_EXTI15_PD        ((uint16_t)0x3000) /*!< PD[15] pin */
#define SYSCFG_EXTICR4_EXTI15_PE        ((uint16_t)0x4000) /*!< PE[15] pin */
 
/******************************************************************************/
/*                                                                            */
/*                       Routing Interface (RI)                               */
/*                                                                            */
/******************************************************************************/

/********************  Bit definition for RI_ICR register  ********************/
#define  RI_ICR_IC1Z                    ((uint32_t)0x0000000F) /*!< IC1Z[3:0] bits (Input Capture 1 select bits) */
#define  RI_ICR_IC1Z_0                  ((uint32_t)0x00000001) /*!< Bit 0 */
#define  RI_ICR_IC1Z_1                  ((uint32_t)0x00000002) /*!< Bit 1 */
#define  RI_ICR_IC1Z_2                  ((uint32_t)0x00000004) /*!< Bit 2 */
#define  RI_ICR_IC1Z_3                  ((uint32_t)0x00000008) /*!< Bit 3 */

#define  RI_ICR_IC2Z                    ((uint32_t)0x000000F0) /*!< IC2Z[3:0] bits (Input Capture 2 select bits) */
#define  RI_ICR_IC2Z_0                  ((uint32_t)0x00000010) /*!< Bit 0 */
#define  RI_ICR_IC2Z_1                  ((uint32_t)0x00000020) /*!< Bit 1 */
#define  RI_ICR_IC2Z_2                  ((uint32_t)0x00000040) /*!< Bit 2 */
#define  RI_ICR_IC2Z_3                  ((uint32_t)0x00000080) /*!< Bit 3 */

#define  RI_ICR_IC3Z                    ((uint32_t)0x00000F00) /*!< IC3Z[3:0] bits (Input Capture 3 select bits) */
#define  RI_ICR_IC3Z_0                  ((uint32_t)0x00000100) /*!< Bit 0 */
#define  RI_ICR_IC3Z_1                  ((uint32_t)0x00000200) /*!< Bit 1 */
#define  RI_ICR_IC3Z_2                  ((uint32_t)0x00000400) /*!< Bit 2 */
#define  RI_ICR_IC3Z_3                  ((uint32_t)0x00000800) /*!< Bit 3 */

#define  RI_ICR_IC4Z                    ((uint32_t)0x0000F000) /*!< IC2Z[3:0] bits (Input Capture 2 select bits) */
#define  RI_ICR_IC4Z_0                  ((uint32_t)0x00001000) /*!< Bit 0 */
#define  RI_ICR_IC4Z_1                  ((uint32_t)0x00002000) /*!< Bit 1 */
#define  RI_ICR_IC4Z_2                  ((uint32_t)0x00004000) /*!< Bit 2 */
#define  RI_ICR_IC4Z_3                  ((uint32_t)0x00008000) /*!< Bit 3 */

#define  RI_ICR_TIM                     ((uint32_t)0x00030000) /*!< TIM[3:0] bits (Timers select bits) */
#define  RI_ICR_TIM_0                   ((uint32_t)0x00010000) /*!< Bit 0 */
#define  RI_ICR_TIM_1                   ((uint32_t)0x00020000) /*!< Bit 1 */

#define  RI_ICR_IC1                     ((uint32_t)0x00040000) /*!< Input capture 1 */
#define  RI_ICR_IC2                     ((uint32_t)0x00080000) /*!< Input capture 2 */
#define  RI_ICR_IC3                     ((uint32_t)0x00100000) /*!< Input capture 3 */
#define  RI_ICR_IC4                     ((uint32_t)0x00200000) /*!< Input capture 4 */

/********************  Bit definition for RI_ASCR1 register  ********************/
#define  RI_ASCR1_CH                    ((uint32_t)0x03FCFFFF) /*!< AS_CH[25:18] & AS_CH[15:0] bits ( Analog switches selection bits) */
#define  RI_ASCR1_CH_0                  ((uint32_t)0x00000001) /*!< Bit 0 */
#define  RI_ASCR1_CH_1                  ((uint32_t)0x00000002) /*!< Bit 1 */
#define  RI_ASCR1_CH_2                  ((uint32_t)0x00000004) /*!< Bit 2 */
#define  RI_ASCR1_CH_3                  ((uint32_t)0x00000008) /*!< Bit 3 */
#define  RI_ASCR1_CH_4                  ((uint32_t)0x00000010) /*!< Bit 4 */
#define  RI_ASCR1_CH_5                  ((uint32_t)0x00000020) /*!< Bit 5 */
#define  RI_ASCR1_CH_6                  ((uint32_t)0x00000040) /*!< Bit 6 */
#define  RI_ASCR1_CH_7                  ((uint32_t)0x00000080) /*!< Bit 7 */
#define  RI_ASCR1_CH_8                  ((uint32_t)0x00000100) /*!< Bit 8 */
#define  RI_ASCR1_CH_9                  ((uint32_t)0x00000200) /*!< Bit 9 */
#define  RI_ASCR1_CH_10                 ((uint32_t)0x00000400) /*!< Bit 10 */
#define  RI_ASCR1_CH_11                 ((uint32_t)0x00000800) /*!< Bit 11 */
#define  RI_ASCR1_CH_12                 ((uint32_t)0x00001000) /*!< Bit 12 */
#define  RI_ASCR1_CH_13                 ((uint32_t)0x00002000) /*!< Bit 13 */
#define  RI_ASCR1_CH_14                 ((uint32_t)0x00004000) /*!< Bit 14 */
#define  RI_ASCR1_CH_15                 ((uint32_t)0x00008000) /*!< Bit 15 */
#define  RI_ASCR1_CH_18                 ((uint32_t)0x00040000) /*!< Bit 18 */
#define  RI_ASCR1_CH_19                 ((uint32_t)0x00080000) /*!< Bit 19 */
#define  RI_ASCR1_CH_20                 ((uint32_t)0x00100000) /*!< Bit 20 */
#define  RI_ASCR1_CH_21                 ((uint32_t)0x00200000) /*!< Bit 21 */
#define  RI_ASCR1_CH_22                 ((uint32_t)0x00400000) /*!< Bit 22 */
#define  RI_ASCR1_CH_23                 ((uint32_t)0x00800000) /*!< Bit 23 */
#define  RI_ASCR1_CH_24                 ((uint32_t)0x01000000) /*!< Bit 24 */
#define  RI_ASCR1_CH_25                 ((uint32_t)0x02000000) /*!< Bit 25 */

#define  RI_ASCR1_VCOMP                 ((uint32_t)0x04000000) /*!< ADC analog switch selection for internal node to COMP1 */
#define  RI_ASCR1_SCM                   ((uint32_t)0x80000000) /*!< I/O Switch control mode */

/********************  Bit definition for RI_ASCR2 register  ********************/
#define  RI_ASCR2_GR10_1                ((uint32_t)0x00000001) /*!< GR10-1 selection bit */
#define  RI_ASCR2_GR10_2                ((uint32_t)0x00000002) /*!< GR10-2 selection bit */
#define  RI_ASCR2_GR10_3                ((uint32_t)0x00000004) /*!< GR10-3 selection bit */
#define  RI_ASCR2_GR10_4                ((uint32_t)0x00000008) /*!< GR10-4 selection bit */
#define  RI_ASCR2_GR6_1                 ((uint32_t)0x00000010) /*!< GR6-1 selection bit */
#define  RI_ASCR2_GR6_2                 ((uint32_t)0x00000020) /*!< GR6-2 selection bit */
#define  RI_ASCR2_GR5_1                 ((uint32_t)0x00000040) /*!< GR5-1 selection bit */
#define  RI_ASCR2_GR5_2                 ((uint32_t)0x00000080) /*!< GR5-2 selection bit */
#define  RI_ASCR2_GR5_3                 ((uint32_t)0x00000100) /*!< GR5-3 selection bit */
#define  RI_ASCR2_GR4_1                 ((uint32_t)0x00000200) /*!< GR4-1 selection bit */
#define  RI_ASCR2_GR4_2                 ((uint32_t)0x00000400) /*!< GR4-2 selection bit */
#define  RI_ASCR2_GR4_3                 ((uint32_t)0x00000800) /*!< GR4-3 selection bit */


/********************  Bit definition for RI_HYSCR1 register  ********************/
#define  RI_HYSCR1_PA                   ((uint32_t)0x0000FFFF) /*!< PA[15:0] Port A Hysteresis selection */
#define  RI_HYSCR1_PA_0                 ((uint32_t)0x00000001) /*!< Bit 0 */
#define  RI_HYSCR1_PA_1                 ((uint32_t)0x00000002) /*!< Bit 1 */
#define  RI_HYSCR1_PA_2                 ((uint32_t)0x00000004) /*!< Bit 2 */
#define  RI_HYSCR1_PA_3                 ((uint32_t)0x00000008) /*!< Bit 3 */
#define  RI_HYSCR1_PA_4                 ((uint32_t)0x00000010) /*!< Bit 4 */
#define  RI_HYSCR1_PA_5                 ((uint32_t)0x00000020) /*!< Bit 5 */
#define  RI_HYSCR1_PA_6                 ((uint32_t)0x00000040) /*!< Bit 6 */
#define  RI_HYSCR1_PA_7                 ((uint32_t)0x00000080) /*!< Bit 7 */
#define  RI_HYSCR1_PA_8                 ((uint32_t)0x00000100) /*!< Bit 8 */
#define  RI_HYSCR1_PA_9                 ((uint32_t)0x00000200) /*!< Bit 9 */
#define  RI_HYSCR1_PA_10                ((uint32_t)0x00000400) /*!< Bit 10 */
#define  RI_HYSCR1_PA_11                ((uint32_t)0x00000800) /*!< Bit 11 */
#define  RI_HYSCR1_PA_12                ((uint32_t)0x00001000) /*!< Bit 12 */
#define  RI_HYSCR1_PA_13                ((uint32_t)0x00002000) /*!< Bit 13 */
#define  RI_HYSCR1_PA_14                ((uint32_t)0x00004000) /*!< Bit 14 */
#define  RI_HYSCR1_PA_15                ((uint32_t)0x00008000) /*!< Bit 15 */

#define  RI_HYSCR1_PB                   ((uint32_t)0xFFFF0000) /*!< PB[15:0] Port B Hysteresis selection */
#define  RI_HYSCR1_PB_0                 ((uint32_t)0x00010000) /*!< Bit 0 */
#define  RI_HYSCR1_PB_1                 ((uint32_t)0x00020000) /*!< Bit 1 */
#define  RI_HYSCR1_PB_2                 ((uint32_t)0x00040000) /*!< Bit 2 */
#define  RI_HYSCR1_PB_3                 ((uint32_t)0x00080000) /*!< Bit 3 */
#define  RI_HYSCR1_PB_4                 ((uint32_t)0x00100000) /*!< Bit 4 */
#define  RI_HYSCR1_PB_5                 ((uint32_t)0x00200000) /*!< Bit 5 */
#define  RI_HYSCR1_PB_6                 ((uint32_t)0x00400000) /*!< Bit 6 */
#define  RI_HYSCR1_PB_7                 ((uint32_t)0x00800000) /*!< Bit 7 */
#define  RI_HYSCR1_PB_8                 ((uint32_t)0x01000000) /*!< Bit 8 */
#define  RI_HYSCR1_PB_9                 ((uint32_t)0x02000000) /*!< Bit 9 */
#define  RI_HYSCR1_PB_10                ((uint32_t)0x04000000) /*!< Bit 10 */
#define  RI_HYSCR1_PB_11                ((uint32_t)0x08000000) /*!< Bit 11 */
#define  RI_HYSCR1_PB_12                ((uint32_t)0x10000000) /*!< Bit 12 */
#define  RI_HYSCR1_PB_13                ((uint32_t)0x20000000) /*!< Bit 13 */
#define  RI_HYSCR1_PB_14                ((uint32_t)0x40000000) /*!< Bit 14 */
#define  RI_HYSCR1_PB_15                ((uint32_t)0x80000000) /*!< Bit 15 */

/********************  Bit definition for RI_HYSCR2 register  ********************/
#define  RI_HYSCR2_PC                   ((uint32_t)0x0000FFFF) /*!< PC[15:0] Port C Hysteresis selection */
#define  RI_HYSCR2_PC_0                 ((uint32_t)0x00000001) /*!< Bit 0 */
#define  RI_HYSCR2_PC_1                 ((uint32_t)0x00000002) /*!< Bit 1 */
#define  RI_HYSCR2_PC_2                 ((uint32_t)0x00000004) /*!< Bit 2 */
#define  RI_HYSCR2_PC_3                 ((uint32_t)0x00000008) /*!< Bit 3 */
#define  RI_HYSCR2_PC_4                 ((uint32_t)0x00000010) /*!< Bit 4 */
#define  RI_HYSCR2_PC_5                 ((uint32_t)0x00000020) /*!< Bit 5 */
#define  RI_HYSCR2_PC_6                 ((uint32_t)0x00000040) /*!< Bit 6 */
#define  RI_HYSCR2_PC_7                 ((uint32_t)0x00000080) /*!< Bit 7 */
#define  RI_HYSCR2_PC_8                 ((uint32_t)0x00000100) /*!< Bit 8 */
#define  RI_HYSCR2_PC_9                 ((uint32_t)0x00000200) /*!< Bit 9 */
#define  RI_HYSCR2_PC_10                ((uint32_t)0x00000400) /*!< Bit 10 */
#define  RI_HYSCR2_PC_11                ((uint32_t)0x00000800) /*!< Bit 11 */
#define  RI_HYSCR2_PC_12                ((uint32_t)0x00001000) /*!< Bit 12 */
#define  RI_HYSCR2_PC_13                ((uint32_t)0x00002000) /*!< Bit 13 */
#define  RI_HYSCR2_PC_14                ((uint32_t)0x00004000) /*!< Bit 14 */
#define  RI_HYSCR2_PC_15                ((uint32_t)0x00008000) /*!< Bit 15 */

#define  RI_HYSCR2_PD                   ((uint32_t)0xFFFF0000) /*!< PD[15:0] Port D Hysteresis selection */
#define  RI_HYSCR2_PD_0                 ((uint32_t)0x00010000) /*!< Bit 0 */
#define  RI_HYSCR2_PD_1                 ((uint32_t)0x00020000) /*!< Bit 1 */
#define  RI_HYSCR2_PD_2                 ((uint32_t)0x00040000) /*!< Bit 2 */
#define  RI_HYSCR2_PD_3                 ((uint32_t)0x00080000) /*!< Bit 3 */
#define  RI_HYSCR2_PD_4                 ((uint32_t)0x00100000) /*!< Bit 4 */
#define  RI_HYSCR2_PD_5                 ((uint32_t)0x00200000) /*!< Bit 5 */
#define  RI_HYSCR2_PD_6                 ((uint32_t)0x00400000) /*!< Bit 6 */
#define  RI_HYSCR2_PD_7                 ((uint32_t)0x00800000) /*!< Bit 7 */
#define  RI_HYSCR2_PD_8                 ((uint32_t)0x01000000) /*!< Bit 8 */
#define  RI_HYSCR2_PD_9                 ((uint32_t)0x02000000) /*!< Bit 9 */
#define  RI_HYSCR2_PD_10                ((uint32_t)0x04000000) /*!< Bit 10 */
#define  RI_HYSCR2_PD_11                ((uint32_t)0x08000000) /*!< Bit 11 */
#define  RI_HYSCR2_PD_12                ((uint32_t)0x10000000) /*!< Bit 12 */
#define  RI_HYSCR2_PD_13                ((uint32_t)0x20000000) /*!< Bit 13 */
#define  RI_HYSCR2_PD_14                ((uint32_t)0x40000000) /*!< Bit 14 */
#define  RI_HYSCR2_PD_15                ((uint32_t)0x80000000) /*!< Bit 15 */

/********************  Bit definition for RI_HYSCR3 register  ********************/
#define  RI_HYSCR2_PE                   ((uint32_t)0x0000FFFF) /*!< PE[15:0] Port E Hysteresis selection */
#define  RI_HYSCR2_PE_0                 ((uint32_t)0x00000001) /*!< Bit 0 */
#define  RI_HYSCR2_PE_1                 ((uint32_t)0x00000002) /*!< Bit 1 */
#define  RI_HYSCR2_PE_2                 ((uint32_t)0x00000004) /*!< Bit 2 */
#define  RI_HYSCR2_PE_3                 ((uint32_t)0x00000008) /*!< Bit 3 */
#define  RI_HYSCR2_PE_4                 ((uint32_t)0x00000010) /*!< Bit 4 */
#define  RI_HYSCR2_PE_5                 ((uint32_t)0x00000020) /*!< Bit 5 */
#define  RI_HYSCR2_PE_6                 ((uint32_t)0x00000040) /*!< Bit 6 */
#define  RI_HYSCR2_PE_7                 ((uint32_t)0x00000080) /*!< Bit 7 */
#define  RI_HYSCR2_PE_8                 ((uint32_t)0x00000100) /*!< Bit 8 */
#define  RI_HYSCR2_PE_9                 ((uint32_t)0x00000200) /*!< Bit 9 */
#define  RI_HYSCR2_PE_10                ((uint32_t)0x00000400) /*!< Bit 10 */
#define  RI_HYSCR2_PE_11                ((uint32_t)0x00000800) /*!< Bit 11 */
#define  RI_HYSCR2_PE_12                ((uint32_t)0x00001000) /*!< Bit 12 */
#define  RI_HYSCR2_PE_13                ((uint32_t)0x00002000) /*!< Bit 13 */
#define  RI_HYSCR2_PE_14                ((uint32_t)0x00004000) /*!< Bit 14 */
#define  RI_HYSCR2_PE_15                ((uint32_t)0x00008000) /*!< Bit 15 */

/******************************************************************************/
/*                                                                            */
/*                                    TIM                                     */
/*                                                                            */
/******************************************************************************/

/*******************  Bit definition for TIM_CR1 register  ********************/
#define  TIM_CR1_CEN                         ((uint16_t)0x0001)            /*!<Counter enable */
#define  TIM_CR1_UDIS                        ((uint16_t)0x0002)            /*!<Update disable */
#define  TIM_CR1_URS                         ((uint16_t)0x0004)            /*!<Update request source */
#define  TIM_CR1_OPM                         ((uint16_t)0x0008)            /*!<One pulse mode */
#define  TIM_CR1_DIR                         ((uint16_t)0x0010)            /*!<Direction */

#define  TIM_CR1_CMS                         ((uint16_t)0x0060)            /*!<CMS[1:0] bits (Center-aligned mode selection) */
#define  TIM_CR1_CMS_0                       ((uint16_t)0x0020)            /*!<Bit 0 */
#define  TIM_CR1_CMS_1                       ((uint16_t)0x0040)            /*!<Bit 1 */

#define  TIM_CR1_ARPE                        ((uint16_t)0x0080)            /*!<Auto-reload preload enable */

#define  TIM_CR1_CKD                         ((uint16_t)0x0300)            /*!<CKD[1:0] bits (clock division) */
#define  TIM_CR1_CKD_0                       ((uint16_t)0x0100)            /*!<Bit 0 */
#define  TIM_CR1_CKD_1                       ((uint16_t)0x0200)            /*!<Bit 1 */

/*******************  Bit definition for TIM_CR2 register  ********************/
#define  TIM_CR2_CCPC                        ((uint16_t)0x0001)            /*!<Capture/Compare Preloaded Control */
#define  TIM_CR2_CCUS                        ((uint16_t)0x0004)            /*!<Capture/Compare Control Update Selection */
#define  TIM_CR2_CCDS                        ((uint16_t)0x0008)            /*!<Capture/Compare DMA Selection */

#define  TIM_CR2_MMS                         ((uint16_t)0x0070)            /*!<MMS[2:0] bits (Master Mode Selection) */
#define  TIM_CR2_MMS_0                       ((uint16_t)0x0010)            /*!<Bit 0 */
#define  TIM_CR2_MMS_1                       ((uint16_t)0x0020)            /*!<Bit 1 */
#define  TIM_CR2_MMS_2                       ((uint16_t)0x0040)            /*!<Bit 2 */

#define  TIM_CR2_TI1S                        ((uint16_t)0x0080)            /*!<TI1 Selection */
#define  TIM_CR2_OIS1                        ((uint16_t)0x0100)            /*!<Output Idle state 1 (OC1 output) */
#define  TIM_CR2_OIS1N                       ((uint16_t)0x0200)            /*!<Output Idle state 1 (OC1N output) */
#define  TIM_CR2_OIS2                        ((uint16_t)0x0400)            /*!<Output Idle state 2 (OC2 output) */
#define  TIM_CR2_OIS2N                       ((uint16_t)0x0800)            /*!<Output Idle state 2 (OC2N output) */
#define  TIM_CR2_OIS3                        ((uint16_t)0x1000)            /*!<Output Idle state 3 (OC3 output) */
#define  TIM_CR2_OIS3N                       ((uint16_t)0x2000)            /*!<Output Idle state 3 (OC3N output) */
#define  TIM_CR2_OIS4                        ((uint16_t)0x4000)            /*!<Output Idle state 4 (OC4 output) */

/*******************  Bit definition for TIM_SMCR register  *******************/
#define  TIM_SMCR_SMS                        ((uint16_t)0x0007)            /*!<SMS[2:0] bits (Slave mode selection) */
#define  TIM_SMCR_SMS_0                      ((uint16_t)0x0001)            /*!<Bit 0 */
#define  TIM_SMCR_SMS_1                      ((uint16_t)0x0002)            /*!<Bit 1 */
#define  TIM_SMCR_SMS_2                      ((uint16_t)0x0004)            /*!<Bit 2 */

#define  TIM_SMCR_OCCS                       ((uint16_t)0x0008)            /*!<OCCS bits (OCref Clear Selection) */

#define  TIM_SMCR_TS                         ((uint16_t)0x0070)            /*!<TS[2:0] bits (Trigger selection) */
#define  TIM_SMCR_TS_0                       ((uint16_t)0x0010)            /*!<Bit 0 */
#define  TIM_SMCR_TS_1                       ((uint16_t)0x0020)            /*!<Bit 1 */
#define  TIM_SMCR_TS_2                       ((uint16_t)0x0040)            /*!<Bit 2 */

#define  TIM_SMCR_MSM                        ((uint16_t)0x0080)            /*!<Master/slave mode */

#define  TIM_SMCR_ETF                        ((uint16_t)0x0F00)            /*!<ETF[3:0] bits (External trigger filter) */
#define  TIM_SMCR_ETF_0                      ((uint16_t)0x0100)            /*!<Bit 0 */
#define  TIM_SMCR_ETF_1                      ((uint16_t)0x0200)            /*!<Bit 1 */
#define  TIM_SMCR_ETF_2                      ((uint16_t)0x0400)            /*!<Bit 2 */
#define  TIM_SMCR_ETF_3                      ((uint16_t)0x0800)            /*!<Bit 3 */

#define  TIM_SMCR_ETPS                       ((uint16_t)0x3000)            /*!<ETPS[1:0] bits (External trigger prescaler) */
#define  TIM_SMCR_ETPS_0                     ((uint16_t)0x1000)            /*!<Bit 0 */
#define  TIM_SMCR_ETPS_1                     ((uint16_t)0x2000)            /*!<Bit 1 */

#define  TIM_SMCR_ECE                        ((uint16_t)0x4000)            /*!<External clock enable */
#define  TIM_SMCR_ETP                        ((uint16_t)0x8000)            /*!<External trigger polarity */

/*******************  Bit definition for TIM_DIER register  *******************/
#define  TIM_DIER_UIE                        ((uint16_t)0x0001)            /*!<Update interrupt enable */
#define  TIM_DIER_CC1IE                      ((uint16_t)0x0002)            /*!<Capture/Compare 1 interrupt enable */
#define  TIM_DIER_CC2IE                      ((uint16_t)0x0004)            /*!<Capture/Compare 2 interrupt enable */
#define  TIM_DIER_CC3IE                      ((uint16_t)0x0008)            /*!<Capture/Compare 3 interrupt enable */
#define  TIM_DIER_CC4IE                      ((uint16_t)0x0010)            /*!<Capture/Compare 4 interrupt enable */
#define  TIM_DIER_COMIE                      ((uint16_t)0x0020)            /*!<COM interrupt enable */
#define  TIM_DIER_TIE                        ((uint16_t)0x0040)            /*!<Trigger interrupt enable */
#define  TIM_DIER_BIE                        ((uint16_t)0x0080)            /*!<Break interrupt enable */
#define  TIM_DIER_UDE                        ((uint16_t)0x0100)            /*!<Update DMA request enable */
#define  TIM_DIER_CC1DE                      ((uint16_t)0x0200)            /*!<Capture/Compare 1 DMA request enable */
#define  TIM_DIER_CC2DE                      ((uint16_t)0x0400)            /*!<Capture/Compare 2 DMA request enable */
#define  TIM_DIER_CC3DE                      ((uint16_t)0x0800)            /*!<Capture/Compare 3 DMA request enable */
#define  TIM_DIER_CC4DE                      ((uint16_t)0x1000)            /*!<Capture/Compare 4 DMA request enable */
#define  TIM_DIER_COMDE                      ((uint16_t)0x2000)            /*!<COM DMA request enable */
#define  TIM_DIER_TDE                        ((uint16_t)0x4000)            /*!<Trigger DMA request enable */

/********************  Bit definition for TIM_SR register  ********************/
#define  TIM_SR_UIF                          ((uint16_t)0x0001)            /*!<Update interrupt Flag */
#define  TIM_SR_CC1IF                        ((uint16_t)0x0002)            /*!<Capture/Compare 1 interrupt Flag */
#define  TIM_SR_CC2IF                        ((uint16_t)0x0004)            /*!<Capture/Compare 2 interrupt Flag */
#define  TIM_SR_CC3IF                        ((uint16_t)0x0008)            /*!<Capture/Compare 3 interrupt Flag */
#define  TIM_SR_CC4IF                        ((uint16_t)0x0010)            /*!<Capture/Compare 4 interrupt Flag */
#define  TIM_SR_COMIF                        ((uint16_t)0x0020)            /*!<COM interrupt Flag */
#define  TIM_SR_TIF                          ((uint16_t)0x0040)            /*!<Trigger interrupt Flag */
#define  TIM_SR_BIF                          ((uint16_t)0x0080)            /*!<Break interrupt Flag */
#define  TIM_SR_CC1OF                        ((uint16_t)0x0200)            /*!<Capture/Compare 1 Overcapture Flag */
#define  TIM_SR_CC2OF                        ((uint16_t)0x0400)            /*!<Capture/Compare 2 Overcapture Flag */
#define  TIM_SR_CC3OF                        ((uint16_t)0x0800)            /*!<Capture/Compare 3 Overcapture Flag */
#define  TIM_SR_CC4OF                        ((uint16_t)0x1000)            /*!<Capture/Compare 4 Overcapture Flag */

/*******************  Bit definition for TIM_EGR register  ********************/
#define  TIM_EGR_UG                          ((uint8_t)0x01)               /*!<Update Generation */
#define  TIM_EGR_CC1G                        ((uint8_t)0x02)               /*!<Capture/Compare 1 Generation */
#define  TIM_EGR_CC2G                        ((uint8_t)0x04)               /*!<Capture/Compare 2 Generation */
#define  TIM_EGR_CC3G                        ((uint8_t)0x08)               /*!<Capture/Compare 3 Generation */
#define  TIM_EGR_CC4G                        ((uint8_t)0x10)               /*!<Capture/Compare 4 Generation */
#define  TIM_EGR_COMG                        ((uint8_t)0x20)               /*!<Capture/Compare Control Update Generation */
#define  TIM_EGR_TG                          ((uint8_t)0x40)               /*!<Trigger Generation */
#define  TIM_EGR_BG                          ((uint8_t)0x80)               /*!<Break Generation */

/******************  Bit definition for TIM_CCMR1 register  *******************/
#define  TIM_CCMR1_CC1S                      ((uint16_t)0x0003)            /*!<CC1S[1:0] bits (Capture/Compare 1 Selection) */
#define  TIM_CCMR1_CC1S_0                    ((uint16_t)0x0001)            /*!<Bit 0 */
#define  TIM_CCMR1_CC1S_1                    ((uint16_t)0x0002)            /*!<Bit 1 */

#define  TIM_CCMR1_OC1FE                     ((uint16_t)0x0004)            /*!<Output Compare 1 Fast enable */
#define  TIM_CCMR1_OC1PE                     ((uint16_t)0x0008)            /*!<Output Compare 1 Preload enable */

#define  TIM_CCMR1_OC1M                      ((uint16_t)0x0070)            /*!<OC1M[2:0] bits (Output Compare 1 Mode) */
#define  TIM_CCMR1_OC1M_0                    ((uint16_t)0x0010)            /*!<Bit 0 */
#define  TIM_CCMR1_OC1M_1                    ((uint16_t)0x0020)            /*!<Bit 1 */
#define  TIM_CCMR1_OC1M_2                    ((uint16_t)0x0040)            /*!<Bit 2 */

#define  TIM_CCMR1_OC1CE                     ((uint16_t)0x0080)            /*!<Output Compare 1Clear Enable */

#define  TIM_CCMR1_CC2S                      ((uint16_t)0x0300)            /*!<CC2S[1:0] bits (Capture/Compare 2 Selection) */
#define  TIM_CCMR1_CC2S_0                    ((uint16_t)0x0100)            /*!<Bit 0 */
#define  TIM_CCMR1_CC2S_1                    ((uint16_t)0x0200)            /*!<Bit 1 */

#define  TIM_CCMR1_OC2FE                     ((uint16_t)0x0400)            /*!<Output Compare 2 Fast enable */
#define  TIM_CCMR1_OC2PE                     ((uint16_t)0x0800)            /*!<Output Compare 2 Preload enable */

#define  TIM_CCMR1_OC2M                      ((uint16_t)0x7000)            /*!<OC2M[2:0] bits (Output Compare 2 Mode) */
#define  TIM_CCMR1_OC2M_0                    ((uint16_t)0x1000)            /*!<Bit 0 */
#define  TIM_CCMR1_OC2M_1                    ((uint16_t)0x2000)            /*!<Bit 1 */
#define  TIM_CCMR1_OC2M_2                    ((uint16_t)0x4000)            /*!<Bit 2 */

#define  TIM_CCMR1_OC2CE                     ((uint16_t)0x8000)            /*!<Output Compare 2 Clear Enable */

/*----------------------------------------------------------------------------*/

#define  TIM_CCMR1_IC1PSC                    ((uint16_t)0x000C)            /*!<IC1PSC[1:0] bits (Input Capture 1 Prescaler) */
#define  TIM_CCMR1_IC1PSC_0                  ((uint16_t)0x0004)            /*!<Bit 0 */
#define  TIM_CCMR1_IC1PSC_1                  ((uint16_t)0x0008)            /*!<Bit 1 */

#define  TIM_CCMR1_IC1F                      ((uint16_t)0x00F0)            /*!<IC1F[3:0] bits (Input Capture 1 Filter) */
#define  TIM_CCMR1_IC1F_0                    ((uint16_t)0x0010)            /*!<Bit 0 */
#define  TIM_CCMR1_IC1F_1                    ((uint16_t)0x0020)            /*!<Bit 1 */
#define  TIM_CCMR1_IC1F_2                    ((uint16_t)0x0040)            /*!<Bit 2 */
#define  TIM_CCMR1_IC1F_3                    ((uint16_t)0x0080)            /*!<Bit 3 */

#define  TIM_CCMR1_IC2PSC                    ((uint16_t)0x0C00)            /*!<IC2PSC[1:0] bits (Input Capture 2 Prescaler) */
#define  TIM_CCMR1_IC2PSC_0                  ((uint16_t)0x0400)            /*!<Bit 0 */
#define  TIM_CCMR1_IC2PSC_1                  ((uint16_t)0x0800)            /*!<Bit 1 */

#define  TIM_CCMR1_IC2F                      ((uint16_t)0xF000)            /*!<IC2F[3:0] bits (Input Capture 2 Filter) */
#define  TIM_CCMR1_IC2F_0                    ((uint16_t)0x1000)            /*!<Bit 0 */
#define  TIM_CCMR1_IC2F_1                    ((uint16_t)0x2000)            /*!<Bit 1 */
#define  TIM_CCMR1_IC2F_2                    ((uint16_t)0x4000)            /*!<Bit 2 */
#define  TIM_CCMR1_IC2F_3                    ((uint16_t)0x8000)            /*!<Bit 3 */

/******************  Bit definition for TIM_CCMR2 register  *******************/
#define  TIM_CCMR2_CC3S                      ((uint16_t)0x0003)            /*!<CC3S[1:0] bits (Capture/Compare 3 Selection) */
#define  TIM_CCMR2_CC3S_0                    ((uint16_t)0x0001)            /*!<Bit 0 */
#define  TIM_CCMR2_CC3S_1                    ((uint16_t)0x0002)            /*!<Bit 1 */

#define  TIM_CCMR2_OC3FE                     ((uint16_t)0x0004)            /*!<Output Compare 3 Fast enable */
#define  TIM_CCMR2_OC3PE                     ((uint16_t)0x0008)            /*!<Output Compare 3 Preload enable */

#define  TIM_CCMR2_OC3M                      ((uint16_t)0x0070)            /*!<OC3M[2:0] bits (Output Compare 3 Mode) */
#define  TIM_CCMR2_OC3M_0                    ((uint16_t)0x0010)            /*!<Bit 0 */
#define  TIM_CCMR2_OC3M_1                    ((uint16_t)0x0020)            /*!<Bit 1 */
#define  TIM_CCMR2_OC3M_2                    ((uint16_t)0x0040)            /*!<Bit 2 */

#define  TIM_CCMR2_OC3CE                     ((uint16_t)0x0080)            /*!<Output Compare 3 Clear Enable */

#define  TIM_CCMR2_CC4S                      ((uint16_t)0x0300)            /*!<CC4S[1:0] bits (Capture/Compare 4 Selection) */
#define  TIM_CCMR2_CC4S_0                    ((uint16_t)0x0100)            /*!<Bit 0 */
#define  TIM_CCMR2_CC4S_1                    ((uint16_t)0x0200)            /*!<Bit 1 */

#define  TIM_CCMR2_OC4FE                     ((uint16_t)0x0400)            /*!<Output Compare 4 Fast enable */
#define  TIM_CCMR2_OC4PE                     ((uint16_t)0x0800)            /*!<Output Compare 4 Preload enable */

#define  TIM_CCMR2_OC4M                      ((uint16_t)0x7000)            /*!<OC4M[2:0] bits (Output Compare 4 Mode) */
#define  TIM_CCMR2_OC4M_0                    ((uint16_t)0x1000)            /*!<Bit 0 */
#define  TIM_CCMR2_OC4M_1                    ((uint16_t)0x2000)            /*!<Bit 1 */
#define  TIM_CCMR2_OC4M_2                    ((uint16_t)0x4000)            /*!<Bit 2 */

#define  TIM_CCMR2_OC4CE                     ((uint16_t)0x8000)            /*!<Output Compare 4 Clear Enable */

/*----------------------------------------------------------------------------*/

#define  TIM_CCMR2_IC3PSC                    ((uint16_t)0x000C)            /*!<IC3PSC[1:0] bits (Input Capture 3 Prescaler) */
#define  TIM_CCMR2_IC3PSC_0                  ((uint16_t)0x0004)            /*!<Bit 0 */
#define  TIM_CCMR2_IC3PSC_1                  ((uint16_t)0x0008)            /*!<Bit 1 */

#define  TIM_CCMR2_IC3F                      ((uint16_t)0x00F0)            /*!<IC3F[3:0] bits (Input Capture 3 Filter) */
#define  TIM_CCMR2_IC3F_0                    ((uint16_t)0x0010)            /*!<Bit 0 */
#define  TIM_CCMR2_IC3F_1                    ((uint16_t)0x0020)            /*!<Bit 1 */
#define  TIM_CCMR2_IC3F_2                    ((uint16_t)0x0040)            /*!<Bit 2 */
#define  TIM_CCMR2_IC3F_3                    ((uint16_t)0x0080)            /*!<Bit 3 */

#define  TIM_CCMR2_IC4PSC                    ((uint16_t)0x0C00)            /*!<IC4PSC[1:0] bits (Input Capture 4 Prescaler) */
#define  TIM_CCMR2_IC4PSC_0                  ((uint16_t)0x0400)            /*!<Bit 0 */
#define  TIM_CCMR2_IC4PSC_1                  ((uint16_t)0x0800)            /*!<Bit 1 */

#define  TIM_CCMR2_IC4F                      ((uint16_t)0xF000)            /*!<IC4F[3:0] bits (Input Capture 4 Filter) */
#define  TIM_CCMR2_IC4F_0                    ((uint16_t)0x1000)            /*!<Bit 0 */
#define  TIM_CCMR2_IC4F_1                    ((uint16_t)0x2000)            /*!<Bit 1 */
#define  TIM_CCMR2_IC4F_2                    ((uint16_t)0x4000)            /*!<Bit 2 */
#define  TIM_CCMR2_IC4F_3                    ((uint16_t)0x8000)            /*!<Bit 3 */

/*******************  Bit definition for TIM_CCER register  *******************/
#define  TIM_CCER_CC1E                       ((uint16_t)0x0001)            /*!<Capture/Compare 1 output enable */
#define  TIM_CCER_CC1P                       ((uint16_t)0x0002)            /*!<Capture/Compare 1 output Polarity */
#define  TIM_CCER_CC1NE                      ((uint16_t)0x0004)            /*!<Capture/Compare 1 Complementary output enable */
#define  TIM_CCER_CC1NP                      ((uint16_t)0x0008)            /*!<Capture/Compare 1 Complementary output Polarity */
#define  TIM_CCER_CC2E                       ((uint16_t)0x0010)            /*!<Capture/Compare 2 output enable */
#define  TIM_CCER_CC2P                       ((uint16_t)0x0020)            /*!<Capture/Compare 2 output Polarity */
#define  TIM_CCER_CC2NE                      ((uint16_t)0x0040)            /*!<Capture/Compare 2 Complementary output enable */
#define  TIM_CCER_CC2NP                      ((uint16_t)0x0080)            /*!<Capture/Compare 2 Complementary output Polarity */
#define  TIM_CCER_CC3E                       ((uint16_t)0x0100)            /*!<Capture/Compare 3 output enable */
#define  TIM_CCER_CC3P                       ((uint16_t)0x0200)            /*!<Capture/Compare 3 output Polarity */
#define  TIM_CCER_CC3NE                      ((uint16_t)0x0400)            /*!<Capture/Compare 3 Complementary output enable */
#define  TIM_CCER_CC3NP                      ((uint16_t)0x0800)            /*!<Capture/Compare 3 Complementary output Polarity */
#define  TIM_CCER_CC4E                       ((uint16_t)0x1000)            /*!<Capture/Compare 4 output enable */
#define  TIM_CCER_CC4P                       ((uint16_t)0x2000)            /*!<Capture/Compare 4 output Polarity */
#define  TIM_CCER_CC4NP                      ((uint16_t)0x8000)            /*!<Capture/Compare 4 Complementary output Polarity */

/*******************  Bit definition for TIM_CNT register  ********************/
#define  TIM_CNT_CNT                         ((uint16_t)0xFFFF)            /*!<Counter Value */

/*******************  Bit definition for TIM_PSC register  ********************/
#define  TIM_PSC_PSC                         ((uint16_t)0xFFFF)            /*!<Prescaler Value */

/*******************  Bit definition for TIM_ARR register  ********************/
#define  TIM_ARR_ARR                         ((uint16_t)0xFFFF)            /*!<actual auto-reload Value */

/*******************  Bit definition for TIM_RCR register  ********************/
#define  TIM_RCR_REP                         ((uint8_t)0xFF)               /*!<Repetition Counter Value */

/*******************  Bit definition for TIM_CCR1 register  *******************/
#define  TIM_CCR1_CCR1                       ((uint16_t)0xFFFF)            /*!<Capture/Compare 1 Value */

/*******************  Bit definition for TIM_CCR2 register  *******************/
#define  TIM_CCR2_CCR2                       ((uint16_t)0xFFFF)            /*!<Capture/Compare 2 Value */

/*******************  Bit definition for TIM_CCR3 register  *******************/
#define  TIM_CCR3_CCR3                       ((uint16_t)0xFFFF)            /*!<Capture/Compare 3 Value */

/*******************  Bit definition for TIM_CCR4 register  *******************/
#define  TIM_CCR4_CCR4                       ((uint16_t)0xFFFF)            /*!<Capture/Compare 4 Value */

/*******************  Bit definition for TIM_DCR register  ********************/
#define  TIM_DCR_DBA                         ((uint16_t)0x001F)            /*!<DBA[4:0] bits (DMA Base Address) */
#define  TIM_DCR_DBA_0                       ((uint16_t)0x0001)            /*!<Bit 0 */
#define  TIM_DCR_DBA_1                       ((uint16_t)0x0002)            /*!<Bit 1 */
#define  TIM_DCR_DBA_2                       ((uint16_t)0x0004)            /*!<Bit 2 */
#define  TIM_DCR_DBA_3                       ((uint16_t)0x0008)            /*!<Bit 3 */
#define  TIM_DCR_DBA_4                       ((uint16_t)0x0010)            /*!<Bit 4 */

#define  TIM_DCR_DBL                         ((uint16_t)0x1F00)            /*!<DBL[4:0] bits (DMA Burst Length) */
#define  TIM_DCR_DBL_0                       ((uint16_t)0x0100)            /*!<Bit 0 */
#define  TIM_DCR_DBL_1                       ((uint16_t)0x0200)            /*!<Bit 1 */
#define  TIM_DCR_DBL_2                       ((uint16_t)0x0400)            /*!<Bit 2 */
#define  TIM_DCR_DBL_3                       ((uint16_t)0x0800)            /*!<Bit 3 */
#define  TIM_DCR_DBL_4                       ((uint16_t)0x1000)            /*!<Bit 4 */

/*******************  Bit definition for TIM_DMAR register  *******************/
#define  TIM_DMAR_DMAB                       ((uint16_t)0xFFFF)            /*!<DMA register for burst accesses */

/*******************  Bit definition for TIM_OR register  *********************/
#define  TIM_OR_TI1RMP                       ((uint16_t)0x0003)            /*!<Option register for TI1 Remapping */
#define  TIM_OR_TI1RMP_0                     ((uint16_t)0x0001)            /*!<Bit 0 */
#define  TIM_OR_TI1RMP_1                     ((uint16_t)0x0002)            /*!<Bit 1 */

/******************************************************************************/
/*                                                                            */
/*         Universal Synchronous Asynchronous Receiver Transmitter            */
/*                                                                            */
/******************************************************************************/

/*******************  Bit definition for USART_SR register  *******************/
#define  USART_SR_PE                         ((uint16_t)0x0001)            /*!< Parity Error */
#define  USART_SR_FE                         ((uint16_t)0x0002)            /*!< Framing Error */
#define  USART_SR_NE                         ((uint16_t)0x0004)            /*!< Noise Error Flag */
#define  USART_SR_ORE                        ((uint16_t)0x0008)            /*!< OverRun Error */
#define  USART_SR_IDLE                       ((uint16_t)0x0010)            /*!< IDLE line detected */
#define  USART_SR_RXNE                       ((uint16_t)0x0020)            /*!< Read Data Register Not Empty */
#define  USART_SR_TC                         ((uint16_t)0x0040)            /*!< Transmission Complete */
#define  USART_SR_TXE                        ((uint16_t)0x0080)            /*!< Transmit Data Register Empty */
#define  USART_SR_LBD                        ((uint16_t)0x0100)            /*!< LIN Break Detection Flag */
#define  USART_SR_CTS                        ((uint16_t)0x0200)            /*!< CTS Flag */

/*******************  Bit definition for USART_DR register  *******************/
#define  USART_DR_DR                         ((uint16_t)0x01FF)            /*!< Data value */

/******************  Bit definition for USART_BRR register  *******************/
#define  USART_BRR_DIV_FRACTION              ((uint16_t)0x000F)            /*!< Fraction of USARTDIV */
#define  USART_BRR_DIV_MANTISSA              ((uint16_t)0xFFF0)            /*!< Mantissa of USARTDIV */

/******************  Bit definition for USART_CR1 register  *******************/
#define  USART_CR1_SBK                       ((uint16_t)0x0001)            /*!< Send Break */
#define  USART_CR1_RWU                       ((uint16_t)0x0002)            /*!< Receiver wakeup */
#define  USART_CR1_RE                        ((uint16_t)0x0004)            /*!< Receiver Enable */
#define  USART_CR1_TE                        ((uint16_t)0x0008)            /*!< Transmitter Enable */
#define  USART_CR1_IDLEIE                    ((uint16_t)0x0010)            /*!< IDLE Interrupt Enable */
#define  USART_CR1_RXNEIE                    ((uint16_t)0x0020)            /*!< RXNE Interrupt Enable */
#define  USART_CR1_TCIE                      ((uint16_t)0x0040)            /*!< Transmission Complete Interrupt Enable */
#define  USART_CR1_TXEIE                     ((uint16_t)0x0080)            /*!< PE Interrupt Enable */
#define  USART_CR1_PEIE                      ((uint16_t)0x0100)            /*!< PE Interrupt Enable */
#define  USART_CR1_PS                        ((uint16_t)0x0200)            /*!< Parity Selection */
#define  USART_CR1_PCE                       ((uint16_t)0x0400)            /*!< Parity Control Enable */
#define  USART_CR1_WAKE                      ((uint16_t)0x0800)            /*!< Wakeup method */
#define  USART_CR1_M                         ((uint16_t)0x1000)            /*!< Word length */
#define  USART_CR1_UE                        ((uint16_t)0x2000)            /*!< USART Enable */
#define  USART_CR1_OVER8                     ((uint16_t)0x8000)            /*!< Oversampling mode */

/******************  Bit definition for USART_CR2 register  *******************/
#define  USART_CR2_ADD                       ((uint16_t)0x000F)            /*!< Address of the USART node */
#define  USART_CR2_LBDL                      ((uint16_t)0x0020)            /*!< LIN Break Detection Length */
#define  USART_CR2_LBDIE                     ((uint16_t)0x0040)            /*!< LIN Break Detection Interrupt Enable */
#define  USART_CR2_LBCL                      ((uint16_t)0x0100)            /*!< Last Bit Clock pulse */
#define  USART_CR2_CPHA                      ((uint16_t)0x0200)            /*!< Clock Phase */
#define  USART_CR2_CPOL                      ((uint16_t)0x0400)            /*!< Clock Polarity */
#define  USART_CR2_CLKEN                     ((uint16_t)0x0800)            /*!< Clock Enable */

#define  USART_CR2_STOP                      ((uint16_t)0x3000)            /*!< STOP[1:0] bits (STOP bits) */
#define  USART_CR2_STOP_0                    ((uint16_t)0x1000)            /*!< Bit 0 */
#define  USART_CR2_STOP_1                    ((uint16_t)0x2000)            /*!< Bit 1 */

#define  USART_CR2_LINEN                     ((uint16_t)0x4000)            /*!< LIN mode enable */

/******************  Bit definition for USART_CR3 register  *******************/
#define  USART_CR3_EIE                       ((uint16_t)0x0001)            /*!< Error Interrupt Enable */
#define  USART_CR3_IREN                      ((uint16_t)0x0002)            /*!< IrDA mode Enable */
#define  USART_CR3_IRLP                      ((uint16_t)0x0004)            /*!< IrDA Low-Power */
#define  USART_CR3_HDSEL                     ((uint16_t)0x0008)            /*!< Half-Duplex Selection */
#define  USART_CR3_NACK                      ((uint16_t)0x0010)            /*!< Smartcard NACK enable */
#define  USART_CR3_SCEN                      ((uint16_t)0x0020)            /*!< Smartcard mode enable */
#define  USART_CR3_DMAR                      ((uint16_t)0x0040)            /*!< DMA Enable Receiver */
#define  USART_CR3_DMAT                      ((uint16_t)0x0080)            /*!< DMA Enable Transmitter */
#define  USART_CR3_RTSE                      ((uint16_t)0x0100)            /*!< RTS Enable */
#define  USART_CR3_CTSE                      ((uint16_t)0x0200)            /*!< CTS Enable */
#define  USART_CR3_CTSIE                     ((uint16_t)0x0400)            /*!< CTS Interrupt Enable */
#define  USART_CR3_ONEBIT                    ((uint16_t)0x0800)            /*!< One sample bit method enable */

/******************  Bit definition for USART_GTPR register  ******************/
#define  USART_GTPR_PSC                      ((uint16_t)0x00FF)            /*!< PSC[7:0] bits (Prescaler value) */
#define  USART_GTPR_PSC_0                    ((uint16_t)0x0001)            /*!< Bit 0 */
#define  USART_GTPR_PSC_1                    ((uint16_t)0x0002)            /*!< Bit 1 */
#define  USART_GTPR_PSC_2                    ((uint16_t)0x0004)            /*!< Bit 2 */
#define  USART_GTPR_PSC_3                    ((uint16_t)0x0008)            /*!< Bit 3 */
#define  USART_GTPR_PSC_4                    ((uint16_t)0x0010)            /*!< Bit 4 */
#define  USART_GTPR_PSC_5                    ((uint16_t)0x0020)            /*!< Bit 5 */
#define  USART_GTPR_PSC_6                    ((uint16_t)0x0040)            /*!< Bit 6 */
#define  USART_GTPR_PSC_7                    ((uint16_t)0x0080)            /*!< Bit 7 */

#define  USART_GTPR_GT                       ((uint16_t)0xFF00)            /*!< Guard time value */

/******************************************************************************/
/*                                                                            */
/*                                   USB                                      */
/*                                                                            */
/******************************************************************************/

/*!<Endpoint-specific registers */
/*******************  Bit definition for USB_EP0R register  *******************/
#define  USB_EP0R_EA                         ((uint16_t)0x000F)            /*!<Endpoint Address */

#define  USB_EP0R_STAT_TX                    ((uint16_t)0x0030)            /*!<STAT_TX[1:0] bits (Status bits, for transmission transfers) */
#define  USB_EP0R_STAT_TX_0                  ((uint16_t)0x0010)            /*!<Bit 0 */
#define  USB_EP0R_STAT_TX_1                  ((uint16_t)0x0020)            /*!<Bit 1 */

#define  USB_EP0R_DTOG_TX                    ((uint16_t)0x0040)            /*!<Data Toggle, for transmission transfers */
#define  USB_EP0R_CTR_TX                     ((uint16_t)0x0080)            /*!<Correct Transfer for transmission */
#define  USB_EP0R_EP_KIND                    ((uint16_t)0x0100)            /*!<Endpoint Kind */

#define  USB_EP0R_EP_TYPE                    ((uint16_t)0x0600)            /*!<EP_TYPE[1:0] bits (Endpoint type) */
#define  USB_EP0R_EP_TYPE_0                  ((uint16_t)0x0200)            /*!<Bit 0 */
#define  USB_EP0R_EP_TYPE_1                  ((uint16_t)0x0400)            /*!<Bit 1 */

#define  USB_EP0R_SETUP                      ((uint16_t)0x0800)            /*!<Setup transaction completed */

#define  USB_EP0R_STAT_RX                    ((uint16_t)0x3000)            /*!<STAT_RX[1:0] bits (Status bits, for reception transfers) */
#define  USB_EP0R_STAT_RX_0                  ((uint16_t)0x1000)            /*!<Bit 0 */
#define  USB_EP0R_STAT_RX_1                  ((uint16_t)0x2000)            /*!<Bit 1 */

#define  USB_EP0R_DTOG_RX                    ((uint16_t)0x4000)            /*!<Data Toggle, for reception transfers */
#define  USB_EP0R_CTR_RX                     ((uint16_t)0x8000)            /*!<Correct Transfer for reception */

/*******************  Bit definition for USB_EP1R register  *******************/
#define  USB_EP1R_EA                         ((uint16_t)0x000F)            /*!<Endpoint Address */

#define  USB_EP1R_STAT_TX                    ((uint16_t)0x0030)            /*!<STAT_TX[1:0] bits (Status bits, for transmission transfers) */
#define  USB_EP1R_STAT_TX_0                  ((uint16_t)0x0010)            /*!<Bit 0 */
#define  USB_EP1R_STAT_TX_1                  ((uint16_t)0x0020)            /*!<Bit 1 */

#define  USB_EP1R_DTOG_TX                    ((uint16_t)0x0040)            /*!<Data Toggle, for transmission transfers */
#define  USB_EP1R_CTR_TX                     ((uint16_t)0x0080)            /*!<Correct Transfer for transmission */
#define  USB_EP1R_EP_KIND                    ((uint16_t)0x0100)            /*!<Endpoint Kind */

#define  USB_EP1R_EP_TYPE                    ((uint16_t)0x0600)            /*!<EP_TYPE[1:0] bits (Endpoint type) */
#define  USB_EP1R_EP_TYPE_0                  ((uint16_t)0x0200)            /*!<Bit 0 */
#define  USB_EP1R_EP_TYPE_1                  ((uint16_t)0x0400)            /*!<Bit 1 */

#define  USB_EP1R_SETUP                      ((uint16_t)0x0800)            /*!<Setup transaction completed */

#define  USB_EP1R_STAT_RX                    ((uint16_t)0x3000)            /*!<STAT_RX[1:0] bits (Status bits, for reception transfers) */
#define  USB_EP1R_STAT_RX_0                  ((uint16_t)0x1000)            /*!<Bit 0 */
#define  USB_EP1R_STAT_RX_1                  ((uint16_t)0x2000)            /*!<Bit 1 */

#define  USB_EP1R_DTOG_RX                    ((uint16_t)0x4000)            /*!<Data Toggle, for reception transfers */
#define  USB_EP1R_CTR_RX                     ((uint16_t)0x8000)            /*!<Correct Transfer for reception */

/*******************  Bit definition for USB_EP2R register  *******************/
#define  USB_EP2R_EA                         ((uint16_t)0x000F)            /*!<Endpoint Address */

#define  USB_EP2R_STAT_TX                    ((uint16_t)0x0030)            /*!<STAT_TX[1:0] bits (Status bits, for transmission transfers) */
#define  USB_EP2R_STAT_TX_0                  ((uint16_t)0x0010)            /*!<Bit 0 */
#define  USB_EP2R_STAT_TX_1                  ((uint16_t)0x0020)            /*!<Bit 1 */

#define  USB_EP2R_DTOG_TX                    ((uint16_t)0x0040)            /*!<Data Toggle, for transmission transfers */
#define  USB_EP2R_CTR_TX                     ((uint16_t)0x0080)            /*!<Correct Transfer for transmission */
#define  USB_EP2R_EP_KIND                    ((uint16_t)0x0100)            /*!<Endpoint Kind */

#define  USB_EP2R_EP_TYPE                    ((uint16_t)0x0600)            /*!<EP_TYPE[1:0] bits (Endpoint type) */
#define  USB_EP2R_EP_TYPE_0                  ((uint16_t)0x0200)            /*!<Bit 0 */
#define  USB_EP2R_EP_TYPE_1                  ((uint16_t)0x0400)            /*!<Bit 1 */

#define  USB_EP2R_SETUP                      ((uint16_t)0x0800)            /*!<Setup transaction completed */

#define  USB_EP2R_STAT_RX                    ((uint16_t)0x3000)            /*!<STAT_RX[1:0] bits (Status bits, for reception transfers) */
#define  USB_EP2R_STAT_RX_0                  ((uint16_t)0x1000)            /*!<Bit 0 */
#define  USB_EP2R_STAT_RX_1                  ((uint16_t)0x2000)            /*!<Bit 1 */

#define  USB_EP2R_DTOG_RX                    ((uint16_t)0x4000)            /*!<Data Toggle, for reception transfers */
#define  USB_EP2R_CTR_RX                     ((uint16_t)0x8000)            /*!<Correct Transfer for reception */

/*******************  Bit definition for USB_EP3R register  *******************/
#define  USB_EP3R_EA                         ((uint16_t)0x000F)            /*!<Endpoint Address */

#define  USB_EP3R_STAT_TX                    ((uint16_t)0x0030)            /*!<STAT_TX[1:0] bits (Status bits, for transmission transfers) */
#define  USB_EP3R_STAT_TX_0                  ((uint16_t)0x0010)            /*!<Bit 0 */
#define  USB_EP3R_STAT_TX_1                  ((uint16_t)0x0020)            /*!<Bit 1 */

#define  USB_EP3R_DTOG_TX                    ((uint16_t)0x0040)            /*!<Data Toggle, for transmission transfers */
#define  USB_EP3R_CTR_TX                     ((uint16_t)0x0080)            /*!<Correct Transfer for transmission */
#define  USB_EP3R_EP_KIND                    ((uint16_t)0x0100)            /*!<Endpoint Kind */

#define  USB_EP3R_EP_TYPE                    ((uint16_t)0x0600)            /*!<EP_TYPE[1:0] bits (Endpoint type) */
#define  USB_EP3R_EP_TYPE_0                  ((uint16_t)0x0200)            /*!<Bit 0 */
#define  USB_EP3R_EP_TYPE_1                  ((uint16_t)0x0400)            /*!<Bit 1 */

#define  USB_EP3R_SETUP                      ((uint16_t)0x0800)            /*!<Setup transaction completed */

#define  USB_EP3R_STAT_RX                    ((uint16_t)0x3000)            /*!<STAT_RX[1:0] bits (Status bits, for reception transfers) */
#define  USB_EP3R_STAT_RX_0                  ((uint16_t)0x1000)            /*!<Bit 0 */
#define  USB_EP3R_STAT_RX_1                  ((uint16_t)0x2000)            /*!<Bit 1 */

#define  USB_EP3R_DTOG_RX                    ((uint16_t)0x4000)            /*!<Data Toggle, for reception transfers */
#define  USB_EP3R_CTR_RX                     ((uint16_t)0x8000)            /*!<Correct Transfer for reception */

/*******************  Bit definition for USB_EP4R register  *******************/
#define  USB_EP4R_EA                         ((uint16_t)0x000F)            /*!<Endpoint Address */

#define  USB_EP4R_STAT_TX                    ((uint16_t)0x0030)            /*!<STAT_TX[1:0] bits (Status bits, for transmission transfers) */
#define  USB_EP4R_STAT_TX_0                  ((uint16_t)0x0010)            /*!<Bit 0 */
#define  USB_EP4R_STAT_TX_1                  ((uint16_t)0x0020)            /*!<Bit 1 */

#define  USB_EP4R_DTOG_TX                    ((uint16_t)0x0040)            /*!<Data Toggle, for transmission transfers */
#define  USB_EP4R_CTR_TX                     ((uint16_t)0x0080)            /*!<Correct Transfer for transmission */
#define  USB_EP4R_EP_KIND                    ((uint16_t)0x0100)            /*!<Endpoint Kind */

#define  USB_EP4R_EP_TYPE                    ((uint16_t)0x0600)            /*!<EP_TYPE[1:0] bits (Endpoint type) */
#define  USB_EP4R_EP_TYPE_0                  ((uint16_t)0x0200)            /*!<Bit 0 */
#define  USB_EP4R_EP_TYPE_1                  ((uint16_t)0x0400)            /*!<Bit 1 */

#define  USB_EP4R_SETUP                      ((uint16_t)0x0800)            /*!<Setup transaction completed */

#define  USB_EP4R_STAT_RX                    ((uint16_t)0x3000)            /*!<STAT_RX[1:0] bits (Status bits, for reception transfers) */
#define  USB_EP4R_STAT_RX_0                  ((uint16_t)0x1000)            /*!<Bit 0 */
#define  USB_EP4R_STAT_RX_1                  ((uint16_t)0x2000)            /*!<Bit 1 */

#define  USB_EP4R_DTOG_RX                    ((uint16_t)0x4000)            /*!<Data Toggle, for reception transfers */
#define  USB_EP4R_CTR_RX                     ((uint16_t)0x8000)            /*!<Correct Transfer for reception */

/*******************  Bit definition for USB_EP5R register  *******************/
#define  USB_EP5R_EA                         ((uint16_t)0x000F)            /*!<Endpoint Address */

#define  USB_EP5R_STAT_TX                    ((uint16_t)0x0030)            /*!<STAT_TX[1:0] bits (Status bits, for transmission transfers) */
#define  USB_EP5R_STAT_TX_0                  ((uint16_t)0x0010)            /*!<Bit 0 */
#define  USB_EP5R_STAT_TX_1                  ((uint16_t)0x0020)            /*!<Bit 1 */

#define  USB_EP5R_DTOG_TX                    ((uint16_t)0x0040)            /*!<Data Toggle, for transmission transfers */
#define  USB_EP5R_CTR_TX                     ((uint16_t)0x0080)            /*!<Correct Transfer for transmission */
#define  USB_EP5R_EP_KIND                    ((uint16_t)0x0100)            /*!<Endpoint Kind */

#define  USB_EP5R_EP_TYPE                    ((uint16_t)0x0600)            /*!<EP_TYPE[1:0] bits (Endpoint type) */
#define  USB_EP5R_EP_TYPE_0                  ((uint16_t)0x0200)            /*!<Bit 0 */
#define  USB_EP5R_EP_TYPE_1                  ((uint16_t)0x0400)            /*!<Bit 1 */

#define  USB_EP5R_SETUP                      ((uint16_t)0x0800)            /*!<Setup transaction completed */

#define  USB_EP5R_STAT_RX                    ((uint16_t)0x3000)            /*!<STAT_RX[1:0] bits (Status bits, for reception transfers) */
#define  USB_EP5R_STAT_RX_0                  ((uint16_t)0x1000)            /*!<Bit 0 */
#define  USB_EP5R_STAT_RX_1                  ((uint16_t)0x2000)            /*!<Bit 1 */

#define  USB_EP5R_DTOG_RX                    ((uint16_t)0x4000)            /*!<Data Toggle, for reception transfers */
#define  USB_EP5R_CTR_RX                     ((uint16_t)0x8000)            /*!<Correct Transfer for reception */

/*******************  Bit definition for USB_EP6R register  *******************/
#define  USB_EP6R_EA                         ((uint16_t)0x000F)            /*!<Endpoint Address */

#define  USB_EP6R_STAT_TX                    ((uint16_t)0x0030)            /*!<STAT_TX[1:0] bits (Status bits, for transmission transfers) */
#define  USB_EP6R_STAT_TX_0                  ((uint16_t)0x0010)            /*!<Bit 0 */
#define  USB_EP6R_STAT_TX_1                  ((uint16_t)0x0020)            /*!<Bit 1 */

#define  USB_EP6R_DTOG_TX                    ((uint16_t)0x0040)            /*!<Data Toggle, for transmission transfers */
#define  USB_EP6R_CTR_TX                     ((uint16_t)0x0080)            /*!<Correct Transfer for transmission */
#define  USB_EP6R_EP_KIND                    ((uint16_t)0x0100)            /*!<Endpoint Kind */

#define  USB_EP6R_EP_TYPE                    ((uint16_t)0x0600)            /*!<EP_TYPE[1:0] bits (Endpoint type) */
#define  USB_EP6R_EP_TYPE_0                  ((uint16_t)0x0200)            /*!<Bit 0 */
#define  USB_EP6R_EP_TYPE_1                  ((uint16_t)0x0400)            /*!<Bit 1 */

#define  USB_EP6R_SETUP                      ((uint16_t)0x0800)            /*!<Setup transaction completed */

#define  USB_EP6R_STAT_RX                    ((uint16_t)0x3000)            /*!<STAT_RX[1:0] bits (Status bits, for reception transfers) */
#define  USB_EP6R_STAT_RX_0                  ((uint16_t)0x1000)            /*!<Bit 0 */
#define  USB_EP6R_STAT_RX_1                  ((uint16_t)0x2000)            /*!<Bit 1 */

#define  USB_EP6R_DTOG_RX                    ((uint16_t)0x4000)            /*!<Data Toggle, for reception transfers */
#define  USB_EP6R_CTR_RX                     ((uint16_t)0x8000)            /*!<Correct Transfer for reception */

/*******************  Bit definition for USB_EP7R register  *******************/
#define  USB_EP7R_EA                         ((uint16_t)0x000F)            /*!<Endpoint Address */

#define  USB_EP7R_STAT_TX                    ((uint16_t)0x0030)            /*!<STAT_TX[1:0] bits (Status bits, for transmission transfers) */
#define  USB_EP7R_STAT_TX_0                  ((uint16_t)0x0010)            /*!<Bit 0 */
#define  USB_EP7R_STAT_TX_1                  ((uint16_t)0x0020)            /*!<Bit 1 */

#define  USB_EP7R_DTOG_TX                    ((uint16_t)0x0040)            /*!<Data Toggle, for transmission transfers */
#define  USB_EP7R_CTR_TX                     ((uint16_t)0x0080)            /*!<Correct Transfer for transmission */
#define  USB_EP7R_EP_KIND                    ((uint16_t)0x0100)            /*!<Endpoint Kind */

#define  USB_EP7R_EP_TYPE                    ((uint16_t)0x0600)            /*!<EP_TYPE[1:0] bits (Endpoint type) */
#define  USB_EP7R_EP_TYPE_0                  ((uint16_t)0x0200)            /*!<Bit 0 */
#define  USB_EP7R_EP_TYPE_1                  ((uint16_t)0x0400)            /*!<Bit 1 */

#define  USB_EP7R_SETUP                      ((uint16_t)0x0800)            /*!<Setup transaction completed */

#define  USB_EP7R_STAT_RX                    ((uint16_t)0x3000)            /*!<STAT_RX[1:0] bits (Status bits, for reception transfers) */
#define  USB_EP7R_STAT_RX_0                  ((uint16_t)0x1000)            /*!<Bit 0 */
#define  USB_EP7R_STAT_RX_1                  ((uint16_t)0x2000)            /*!<Bit 1 */

#define  USB_EP7R_DTOG_RX                    ((uint16_t)0x4000)            /*!<Data Toggle, for reception transfers */
#define  USB_EP7R_CTR_RX                     ((uint16_t)0x8000)            /*!<Correct Transfer for reception */

/*!<Common registers */
/*******************  Bit definition for USB_CNTR register  *******************/
#define  USB_CNTR_FRES                       ((uint16_t)0x0001)            /*!<Force USB Reset */
#define  USB_CNTR_PDWN                       ((uint16_t)0x0002)            /*!<Power down */
#define  USB_CNTR_LP_MODE                    ((uint16_t)0x0004)            /*!<Low-power mode */
#define  USB_CNTR_FSUSP                      ((uint16_t)0x0008)            /*!<Force suspend */
#define  USB_CNTR_RESUME                     ((uint16_t)0x0010)            /*!<Resume request */
#define  USB_CNTR_ESOFM                      ((uint16_t)0x0100)            /*!<Expected Start Of Frame Interrupt Mask */
#define  USB_CNTR_SOFM                       ((uint16_t)0x0200)            /*!<Start Of Frame Interrupt Mask */
#define  USB_CNTR_RESETM                     ((uint16_t)0x0400)            /*!<RESET Interrupt Mask */
#define  USB_CNTR_SUSPM                      ((uint16_t)0x0800)            /*!<Suspend mode Interrupt Mask */
#define  USB_CNTR_WKUPM                      ((uint16_t)0x1000)            /*!<Wakeup Interrupt Mask */
#define  USB_CNTR_ERRM                       ((uint16_t)0x2000)            /*!<Error Interrupt Mask */
#define  USB_CNTR_PMAOVRM                    ((uint16_t)0x4000)            /*!<Packet Memory Area Over / Underrun Interrupt Mask */
#define  USB_CNTR_CTRM                       ((uint16_t)0x8000)            /*!<Correct Transfer Interrupt Mask */

/*******************  Bit definition for USB_ISTR register  *******************/
#define  USB_ISTR_EP_ID                      ((uint16_t)0x000F)            /*!<Endpoint Identifier */
#define  USB_ISTR_DIR                        ((uint16_t)0x0010)            /*!<Direction of transaction */
#define  USB_ISTR_ESOF                       ((uint16_t)0x0100)            /*!<Expected Start Of Frame */
#define  USB_ISTR_SOF                        ((uint16_t)0x0200)            /*!<Start Of Frame */
#define  USB_ISTR_RESET                      ((uint16_t)0x0400)            /*!<USB RESET request */
#define  USB_ISTR_SUSP                       ((uint16_t)0x0800)            /*!<Suspend mode request */
#define  USB_ISTR_WKUP                       ((uint16_t)0x1000)            /*!<Wake up */
#define  USB_ISTR_ERR                        ((uint16_t)0x2000)            /*!<Error */
#define  USB_ISTR_PMAOVR                     ((uint16_t)0x4000)            /*!<Packet Memory Area Over / Underrun */
#define  USB_ISTR_CTR                        ((uint16_t)0x8000)            /*!<Correct Transfer */

/*******************  Bit definition for USB_FNR register  ********************/
#define  USB_FNR_FN                          ((uint16_t)0x07FF)            /*!<Frame Number */
#define  USB_FNR_LSOF                        ((uint16_t)0x1800)            /*!<Lost SOF */
#define  USB_FNR_LCK                         ((uint16_t)0x2000)            /*!<Locked */
#define  USB_FNR_RXDM                        ((uint16_t)0x4000)            /*!<Receive Data - Line Status */
#define  USB_FNR_RXDP                        ((uint16_t)0x8000)            /*!<Receive Data + Line Status */

/******************  Bit definition for USB_DADDR register  *******************/
#define  USB_DADDR_ADD                       ((uint8_t)0x7F)               /*!<ADD[6:0] bits (Device Address) */
#define  USB_DADDR_ADD0                      ((uint8_t)0x01)               /*!<Bit 0 */
#define  USB_DADDR_ADD1                      ((uint8_t)0x02)               /*!<Bit 1 */
#define  USB_DADDR_ADD2                      ((uint8_t)0x04)               /*!<Bit 2 */
#define  USB_DADDR_ADD3                      ((uint8_t)0x08)               /*!<Bit 3 */
#define  USB_DADDR_ADD4                      ((uint8_t)0x10)               /*!<Bit 4 */
#define  USB_DADDR_ADD5                      ((uint8_t)0x20)               /*!<Bit 5 */
#define  USB_DADDR_ADD6                      ((uint8_t)0x40)               /*!<Bit 6 */

#define  USB_DADDR_EF                        ((uint8_t)0x80)               /*!<Enable Function */

/******************  Bit definition for USB_BTABLE register  ******************/    
#define  USB_BTABLE_BTABLE                   ((uint16_t)0xFFF8)            /*!<Buffer Table */

/*!< Buffer descriptor table */
/*****************  Bit definition for USB_ADDR0_TX register  *****************/
#define  USB_ADDR0_TX_ADDR0_TX               ((uint16_t)0xFFFE)            /*!< Transmission Buffer Address 0 */

/*****************  Bit definition for USB_ADDR1_TX register  *****************/
#define  USB_ADDR1_TX_ADDR1_TX               ((uint16_t)0xFFFE)            /*!< Transmission Buffer Address 1 */

/*****************  Bit definition for USB_ADDR2_TX register  *****************/
#define  USB_ADDR2_TX_ADDR2_TX               ((uint16_t)0xFFFE)            /*!< Transmission Buffer Address 2 */

/*****************  Bit definition for USB_ADDR3_TX register  *****************/
#define  USB_ADDR3_TX_ADDR3_TX               ((uint16_t)0xFFFE)            /*!< Transmission Buffer Address 3 */

/*****************  Bit definition for USB_ADDR4_TX register  *****************/
#define  USB_ADDR4_TX_ADDR4_TX               ((uint16_t)0xFFFE)            /*!< Transmission Buffer Address 4 */

/*****************  Bit definition for USB_ADDR5_TX register  *****************/
#define  USB_ADDR5_TX_ADDR5_TX               ((uint16_t)0xFFFE)            /*!< Transmission Buffer Address 5 */

/*****************  Bit definition for USB_ADDR6_TX register  *****************/
#define  USB_ADDR6_TX_ADDR6_TX               ((uint16_t)0xFFFE)            /*!< Transmission Buffer Address 6 */

/*****************  Bit definition for USB_ADDR7_TX register  *****************/
#define  USB_ADDR7_TX_ADDR7_TX               ((uint16_t)0xFFFE)            /*!< Transmission Buffer Address 7 */

/*----------------------------------------------------------------------------*/

/*****************  Bit definition for USB_COUNT0_TX register  ****************/
#define  USB_COUNT0_TX_COUNT0_TX             ((uint16_t)0x03FF)            /*!< Transmission Byte Count 0 */

/*****************  Bit definition for USB_COUNT1_TX register  ****************/
#define  USB_COUNT1_TX_COUNT1_TX             ((uint16_t)0x03FF)            /*!< Transmission Byte Count 1 */

/*****************  Bit definition for USB_COUNT2_TX register  ****************/
#define  USB_COUNT2_TX_COUNT2_TX             ((uint16_t)0x03FF)            /*!< Transmission Byte Count 2 */

/*****************  Bit definition for USB_COUNT3_TX register  ****************/
#define  USB_COUNT3_TX_COUNT3_TX             ((uint16_t)0x03FF)            /*!< Transmission Byte Count 3 */

/*****************  Bit definition for USB_COUNT4_TX register  ****************/
#define  USB_COUNT4_TX_COUNT4_TX             ((uint16_t)0x03FF)            /*!< Transmission Byte Count 4 */

/*****************  Bit definition for USB_COUNT5_TX register  ****************/
#define  USB_COUNT5_TX_COUNT5_TX             ((uint16_t)0x03FF)            /*!< Transmission Byte Count 5 */

/*****************  Bit definition for USB_COUNT6_TX register  ****************/
#define  USB_COUNT6_TX_COUNT6_TX             ((uint16_t)0x03FF)            /*!< Transmission Byte Count 6 */

/*****************  Bit definition for USB_COUNT7_TX register  ****************/
#define  USB_COUNT7_TX_COUNT7_TX             ((uint16_t)0x03FF)            /*!< Transmission Byte Count 7 */

/*----------------------------------------------------------------------------*/

/****************  Bit definition for USB_COUNT0_TX_0 register  ***************/
#define  USB_COUNT0_TX_0_COUNT0_TX_0         ((uint32_t)0x000003FF)        /*!< Transmission Byte Count 0 (low) */

/****************  Bit definition for USB_COUNT0_TX_1 register  ***************/
#define  USB_COUNT0_TX_1_COUNT0_TX_1         ((uint32_t)0x03FF0000)        /*!< Transmission Byte Count 0 (high) */

/****************  Bit definition for USB_COUNT1_TX_0 register  ***************/
#define  USB_COUNT1_TX_0_COUNT1_TX_0          ((uint32_t)0x000003FF)        /*!< Transmission Byte Count 1 (low) */

/****************  Bit definition for USB_COUNT1_TX_1 register  ***************/
#define  USB_COUNT1_TX_1_COUNT1_TX_1          ((uint32_t)0x03FF0000)        /*!< Transmission Byte Count 1 (high) */

/****************  Bit definition for USB_COUNT2_TX_0 register  ***************/
#define  USB_COUNT2_TX_0_COUNT2_TX_0         ((uint32_t)0x000003FF)        /*!< Transmission Byte Count 2 (low) */

/****************  Bit definition for USB_COUNT2_TX_1 register  ***************/
#define  USB_COUNT2_TX_1_COUNT2_TX_1         ((uint32_t)0x03FF0000)        /*!< Transmission Byte Count 2 (high) */

/****************  Bit definition for USB_COUNT3_TX_0 register  ***************/
#define  USB_COUNT3_TX_0_COUNT3_TX_0         ((uint16_t)0x000003FF)        /*!< Transmission Byte Count 3 (low) */

/****************  Bit definition for USB_COUNT3_TX_1 register  ***************/
#define  USB_COUNT3_TX_1_COUNT3_TX_1         ((uint16_t)0x03FF0000)        /*!< Transmission Byte Count 3 (high) */

/****************  Bit definition for USB_COUNT4_TX_0 register  ***************/
#define  USB_COUNT4_TX_0_COUNT4_TX_0         ((uint32_t)0x000003FF)        /*!< Transmission Byte Count 4 (low) */

/****************  Bit definition for USB_COUNT4_TX_1 register  ***************/
#define  USB_COUNT4_TX_1_COUNT4_TX_1         ((uint32_t)0x03FF0000)        /*!< Transmission Byte Count 4 (high) */

/****************  Bit definition for USB_COUNT5_TX_0 register  ***************/
#define  USB_COUNT5_TX_0_COUNT5_TX_0         ((uint32_t)0x000003FF)        /*!< Transmission Byte Count 5 (low) */

/****************  Bit definition for USB_COUNT5_TX_1 register  ***************/
#define  USB_COUNT5_TX_1_COUNT5_TX_1         ((uint32_t)0x03FF0000)        /*!< Transmission Byte Count 5 (high) */

/****************  Bit definition for USB_COUNT6_TX_0 register  ***************/
#define  USB_COUNT6_TX_0_COUNT6_TX_0         ((uint32_t)0x000003FF)        /*!< Transmission Byte Count 6 (low) */

/****************  Bit definition for USB_COUNT6_TX_1 register  ***************/
#define  USB_COUNT6_TX_1_COUNT6_TX_1         ((uint32_t)0x03FF0000)        /*!< Transmission Byte Count 6 (high) */

/****************  Bit definition for USB_COUNT7_TX_0 register  ***************/
#define  USB_COUNT7_TX_0_COUNT7_TX_0         ((uint32_t)0x000003FF)        /*!< Transmission Byte Count 7 (low) */

/****************  Bit definition for USB_COUNT7_TX_1 register  ***************/
#define  USB_COUNT7_TX_1_COUNT7_TX_1         ((uint32_t)0x03FF0000)        /*!< Transmission Byte Count 7 (high) */

/*----------------------------------------------------------------------------*/

/*****************  Bit definition for USB_ADDR0_RX register  *****************/
#define  USB_ADDR0_RX_ADDR0_RX               ((uint16_t)0xFFFE)            /*!< Reception Buffer Address 0 */

/*****************  Bit definition for USB_ADDR1_RX register  *****************/
#define  USB_ADDR1_RX_ADDR1_RX               ((uint16_t)0xFFFE)            /*!< Reception Buffer Address 1 */

/*****************  Bit definition for USB_ADDR2_RX register  *****************/
#define  USB_ADDR2_RX_ADDR2_RX               ((uint16_t)0xFFFE)            /*!< Reception Buffer Address 2 */

/*****************  Bit definition for USB_ADDR3_RX register  *****************/
#define  USB_ADDR3_RX_ADDR3_RX               ((uint16_t)0xFFFE)            /*!< Reception Buffer Address 3 */

/*****************  Bit definition for USB_ADDR4_RX register  *****************/
#define  USB_ADDR4_RX_ADDR4_RX               ((uint16_t)0xFFFE)            /*!< Reception Buffer Address 4 */

/*****************  Bit definition for USB_ADDR5_RX register  *****************/
#define  USB_ADDR5_RX_ADDR5_RX               ((uint16_t)0xFFFE)            /*!< Reception Buffer Address 5 */

/*****************  Bit definition for USB_ADDR6_RX register  *****************/
#define  USB_ADDR6_RX_ADDR6_RX               ((uint16_t)0xFFFE)            /*!< Reception Buffer Address 6 */

/*****************  Bit definition for USB_ADDR7_RX register  *****************/
#define  USB_ADDR7_RX_ADDR7_RX               ((uint16_t)0xFFFE)            /*!< Reception Buffer Address 7 */

/*----------------------------------------------------------------------------*/

/*****************  Bit definition for USB_COUNT0_RX register  ****************/
#define  USB_COUNT0_RX_COUNT0_RX             ((uint16_t)0x03FF)            /*!< Reception Byte Count */

#define  USB_COUNT0_RX_NUM_BLOCK             ((uint16_t)0x7C00)            /*!< NUM_BLOCK[4:0] bits (Number of blocks) */
#define  USB_COUNT0_RX_NUM_BLOCK_0           ((uint16_t)0x0400)            /*!< Bit 0 */
#define  USB_COUNT0_RX_NUM_BLOCK_1           ((uint16_t)0x0800)            /*!< Bit 1 */
#define  USB_COUNT0_RX_NUM_BLOCK_2           ((uint16_t)0x1000)            /*!< Bit 2 */
#define  USB_COUNT0_RX_NUM_BLOCK_3           ((uint16_t)0x2000)            /*!< Bit 3 */
#define  USB_COUNT0_RX_NUM_BLOCK_4           ((uint16_t)0x4000)            /*!< Bit 4 */

#define  USB_COUNT0_RX_BLSIZE                ((uint16_t)0x8000)            /*!< BLock SIZE */

/*****************  Bit definition for USB_COUNT1_RX register  ****************/
#define  USB_COUNT1_RX_COUNT1_RX             ((uint16_t)0x03FF)            /*!< Reception Byte Count */

#define  USB_COUNT1_RX_NUM_BLOCK             ((uint16_t)0x7C00)            /*!< NUM_BLOCK[4:0] bits (Number of blocks) */
#define  USB_COUNT1_RX_NUM_BLOCK_0           ((uint16_t)0x0400)            /*!< Bit 0 */
#define  USB_COUNT1_RX_NUM_BLOCK_1           ((uint16_t)0x0800)            /*!< Bit 1 */
#define  USB_COUNT1_RX_NUM_BLOCK_2           ((uint16_t)0x1000)            /*!< Bit 2 */
#define  USB_COUNT1_RX_NUM_BLOCK_3           ((uint16_t)0x2000)            /*!< Bit 3 */
#define  USB_COUNT1_RX_NUM_BLOCK_4           ((uint16_t)0x4000)            /*!< Bit 4 */

#define  USB_COUNT1_RX_BLSIZE                ((uint16_t)0x8000)            /*!< BLock SIZE */

/*****************  Bit definition for USB_COUNT2_RX register  ****************/
#define  USB_COUNT2_RX_COUNT2_RX             ((uint16_t)0x03FF)            /*!< Reception Byte Count */

#define  USB_COUNT2_RX_NUM_BLOCK             ((uint16_t)0x7C00)            /*!< NUM_BLOCK[4:0] bits (Number of blocks) */
#define  USB_COUNT2_RX_NUM_BLOCK_0           ((uint16_t)0x0400)            /*!< Bit 0 */
#define  USB_COUNT2_RX_NUM_BLOCK_1           ((uint16_t)0x0800)            /*!< Bit 1 */
#define  USB_COUNT2_RX_NUM_BLOCK_2           ((uint16_t)0x1000)            /*!< Bit 2 */
#define  USB_COUNT2_RX_NUM_BLOCK_3           ((uint16_t)0x2000)            /*!< Bit 3 */
#define  USB_COUNT2_RX_NUM_BLOCK_4           ((uint16_t)0x4000)            /*!< Bit 4 */

#define  USB_COUNT2_RX_BLSIZE                ((uint16_t)0x8000)            /*!< BLock SIZE */

/*****************  Bit definition for USB_COUNT3_RX register  ****************/
#define  USB_COUNT3_RX_COUNT3_RX             ((uint16_t)0x03FF)            /*!< Reception Byte Count */

#define  USB_COUNT3_RX_NUM_BLOCK             ((uint16_t)0x7C00)            /*!< NUM_BLOCK[4:0] bits (Number of blocks) */
#define  USB_COUNT3_RX_NUM_BLOCK_0           ((uint16_t)0x0400)            /*!< Bit 0 */
#define  USB_COUNT3_RX_NUM_BLOCK_1           ((uint16_t)0x0800)            /*!< Bit 1 */
#define  USB_COUNT3_RX_NUM_BLOCK_2           ((uint16_t)0x1000)            /*!< Bit 2 */
#define  USB_COUNT3_RX_NUM_BLOCK_3           ((uint16_t)0x2000)            /*!< Bit 3 */
#define  USB_COUNT3_RX_NUM_BLOCK_4           ((uint16_t)0x4000)            /*!< Bit 4 */

#define  USB_COUNT3_RX_BLSIZE                ((uint16_t)0x8000)            /*!< BLock SIZE */

/*****************  Bit definition for USB_COUNT4_RX register  ****************/
#define  USB_COUNT4_RX_COUNT4_RX             ((uint16_t)0x03FF)            /*!< Reception Byte Count */

#define  USB_COUNT4_RX_NUM_BLOCK             ((uint16_t)0x7C00)            /*!< NUM_BLOCK[4:0] bits (Number of blocks) */
#define  USB_COUNT4_RX_NUM_BLOCK_0           ((uint16_t)0x0400)            /*!< Bit 0 */
#define  USB_COUNT4_RX_NUM_BLOCK_1           ((uint16_t)0x0800)            /*!< Bit 1 */
#define  USB_COUNT4_RX_NUM_BLOCK_2           ((uint16_t)0x1000)            /*!< Bit 2 */
#define  USB_COUNT4_RX_NUM_BLOCK_3           ((uint16_t)0x2000)            /*!< Bit 3 */
#define  USB_COUNT4_RX_NUM_BLOCK_4           ((uint16_t)0x4000)            /*!< Bit 4 */

#define  USB_COUNT4_RX_BLSIZE                ((uint16_t)0x8000)            /*!< BLock SIZE */

/*****************  Bit definition for USB_COUNT5_RX register  ****************/
#define  USB_COUNT5_RX_COUNT5_RX             ((uint16_t)0x03FF)            /*!< Reception Byte Count */

#define  USB_COUNT5_RX_NUM_BLOCK             ((uint16_t)0x7C00)            /*!< NUM_BLOCK[4:0] bits (Number of blocks) */
#define  USB_COUNT5_RX_NUM_BLOCK_0           ((uint16_t)0x0400)            /*!< Bit 0 */
#define  USB_COUNT5_RX_NUM_BLOCK_1           ((uint16_t)0x0800)            /*!< Bit 1 */
#define  USB_COUNT5_RX_NUM_BLOCK_2           ((uint16_t)0x1000)            /*!< Bit 2 */
#define  USB_COUNT5_RX_NUM_BLOCK_3           ((uint16_t)0x2000)            /*!< Bit 3 */
#define  USB_COUNT5_RX_NUM_BLOCK_4           ((uint16_t)0x4000)            /*!< Bit 4 */

#define  USB_COUNT5_RX_BLSIZE                ((uint16_t)0x8000)            /*!< BLock SIZE */

/*****************  Bit definition for USB_COUNT6_RX register  ****************/
#define  USB_COUNT6_RX_COUNT6_RX             ((uint16_t)0x03FF)            /*!< Reception Byte Count */

#define  USB_COUNT6_RX_NUM_BLOCK             ((uint16_t)0x7C00)            /*!< NUM_BLOCK[4:0] bits (Number of blocks) */
#define  USB_COUNT6_RX_NUM_BLOCK_0           ((uint16_t)0x0400)            /*!< Bit 0 */
#define  USB_COUNT6_RX_NUM_BLOCK_1           ((uint16_t)0x0800)            /*!< Bit 1 */
#define  USB_COUNT6_RX_NUM_BLOCK_2           ((uint16_t)0x1000)            /*!< Bit 2 */
#define  USB_COUNT6_RX_NUM_BLOCK_3           ((uint16_t)0x2000)            /*!< Bit 3 */
#define  USB_COUNT6_RX_NUM_BLOCK_4           ((uint16_t)0x4000)            /*!< Bit 4 */

#define  USB_COUNT6_RX_BLSIZE                ((uint16_t)0x8000)            /*!< BLock SIZE */

/*****************  Bit definition for USB_COUNT7_RX register  ****************/
#define  USB_COUNT7_RX_COUNT7_RX             ((uint16_t)0x03FF)            /*!< Reception Byte Count */

#define  USB_COUNT7_RX_NUM_BLOCK             ((uint16_t)0x7C00)            /*!< NUM_BLOCK[4:0] bits (Number of blocks) */
#define  USB_COUNT7_RX_NUM_BLOCK_0           ((uint16_t)0x0400)            /*!< Bit 0 */
#define  USB_COUNT7_RX_NUM_BLOCK_1           ((uint16_t)0x0800)            /*!< Bit 1 */
#define  USB_COUNT7_RX_NUM_BLOCK_2           ((uint16_t)0x1000)            /*!< Bit 2 */
#define  USB_COUNT7_RX_NUM_BLOCK_3           ((uint16_t)0x2000)            /*!< Bit 3 */
#define  USB_COUNT7_RX_NUM_BLOCK_4           ((uint16_t)0x4000)            /*!< Bit 4 */

#define  USB_COUNT7_RX_BLSIZE                ((uint16_t)0x8000)            /*!< BLock SIZE */

/*----------------------------------------------------------------------------*/

/****************  Bit definition for USB_COUNT0_RX_0 register  ***************/
#define  USB_COUNT0_RX_0_COUNT0_RX_0         ((uint32_t)0x000003FF)        /*!< Reception Byte Count (low) */

#define  USB_COUNT0_RX_0_NUM_BLOCK_0         ((uint32_t)0x00007C00)        /*!< NUM_BLOCK_0[4:0] bits (Number of blocks) (low) */
#define  USB_COUNT0_RX_0_NUM_BLOCK_0_0       ((uint32_t)0x00000400)        /*!< Bit 0 */
#define  USB_COUNT0_RX_0_NUM_BLOCK_0_1       ((uint32_t)0x00000800)        /*!< Bit 1 */
#define  USB_COUNT0_RX_0_NUM_BLOCK_0_2       ((uint32_t)0x00001000)        /*!< Bit 2 */
#define  USB_COUNT0_RX_0_NUM_BLOCK_0_3       ((uint32_t)0x00002000)        /*!< Bit 3 */
#define  USB_COUNT0_RX_0_NUM_BLOCK_0_4       ((uint32_t)0x00004000)        /*!< Bit 4 */

#define  USB_COUNT0_RX_0_BLSIZE_0            ((uint32_t)0x00008000)        /*!< BLock SIZE (low) */

/****************  Bit definition for USB_COUNT0_RX_1 register  ***************/
#define  USB_COUNT0_RX_1_COUNT0_RX_1         ((uint32_t)0x03FF0000)        /*!< Reception Byte Count (high) */

#define  USB_COUNT0_RX_1_NUM_BLOCK_1         ((uint32_t)0x7C000000)        /*!< NUM_BLOCK_1[4:0] bits (Number of blocks) (high) */
#define  USB_COUNT0_RX_1_NUM_BLOCK_1_0       ((uint32_t)0x04000000)        /*!< Bit 1 */
#define  USB_COUNT0_RX_1_NUM_BLOCK_1_1       ((uint32_t)0x08000000)        /*!< Bit 1 */
#define  USB_COUNT0_RX_1_NUM_BLOCK_1_2       ((uint32_t)0x10000000)        /*!< Bit 2 */
#define  USB_COUNT0_RX_1_NUM_BLOCK_1_3       ((uint32_t)0x20000000)        /*!< Bit 3 */
#define  USB_COUNT0_RX_1_NUM_BLOCK_1_4       ((uint32_t)0x40000000)        /*!< Bit 4 */

#define  USB_COUNT0_RX_1_BLSIZE_1            ((uint32_t)0x80000000)        /*!< BLock SIZE (high) */

/****************  Bit definition for USB_COUNT1_RX_0 register  ***************/
#define  USB_COUNT1_RX_0_COUNT1_RX_0         ((uint32_t)0x000003FF)        /*!< Reception Byte Count (low) */

#define  USB_COUNT1_RX_0_NUM_BLOCK_0         ((uint32_t)0x00007C00)        /*!< NUM_BLOCK_0[4:0] bits (Number of blocks) (low) */
#define  USB_COUNT1_RX_0_NUM_BLOCK_0_0       ((uint32_t)0x00000400)        /*!< Bit 0 */
#define  USB_COUNT1_RX_0_NUM_BLOCK_0_1       ((uint32_t)0x00000800)        /*!< Bit 1 */
#define  USB_COUNT1_RX_0_NUM_BLOCK_0_2       ((uint32_t)0x00001000)        /*!< Bit 2 */
#define  USB_COUNT1_RX_0_NUM_BLOCK_0_3       ((uint32_t)0x00002000)        /*!< Bit 3 */
#define  USB_COUNT1_RX_0_NUM_BLOCK_0_4       ((uint32_t)0x00004000)        /*!< Bit 4 */

#define  USB_COUNT1_RX_0_BLSIZE_0            ((uint32_t)0x00008000)        /*!< BLock SIZE (low) */

/****************  Bit definition for USB_COUNT1_RX_1 register  ***************/
#define  USB_COUNT1_RX_1_COUNT1_RX_1         ((uint32_t)0x03FF0000)        /*!< Reception Byte Count (high) */

#define  USB_COUNT1_RX_1_NUM_BLOCK_1         ((uint32_t)0x7C000000)        /*!< NUM_BLOCK_1[4:0] bits (Number of blocks) (high) */
#define  USB_COUNT1_RX_1_NUM_BLOCK_1_0       ((uint32_t)0x04000000)        /*!< Bit 0 */
#define  USB_COUNT1_RX_1_NUM_BLOCK_1_1       ((uint32_t)0x08000000)        /*!< Bit 1 */
#define  USB_COUNT1_RX_1_NUM_BLOCK_1_2       ((uint32_t)0x10000000)        /*!< Bit 2 */
#define  USB_COUNT1_RX_1_NUM_BLOCK_1_3       ((uint32_t)0x20000000)        /*!< Bit 3 */
#define  USB_COUNT1_RX_1_NUM_BLOCK_1_4       ((uint32_t)0x40000000)        /*!< Bit 4 */

#define  USB_COUNT1_RX_1_BLSIZE_1            ((uint32_t)0x80000000)        /*!< BLock SIZE (high) */

/****************  Bit definition for USB_COUNT2_RX_0 register  ***************/
#define  USB_COUNT2_RX_0_COUNT2_RX_0         ((uint32_t)0x000003FF)        /*!< Reception Byte Count (low) */

#define  USB_COUNT2_RX_0_NUM_BLOCK_0         ((uint32_t)0x00007C00)        /*!< NUM_BLOCK_0[4:0] bits (Number of blocks) (low) */
#define  USB_COUNT2_RX_0_NUM_BLOCK_0_0       ((uint32_t)0x00000400)        /*!< Bit 0 */
#define  USB_COUNT2_RX_0_NUM_BLOCK_0_1       ((uint32_t)0x00000800)        /*!< Bit 1 */
#define  USB_COUNT2_RX_0_NUM_BLOCK_0_2       ((uint32_t)0x00001000)        /*!< Bit 2 */
#define  USB_COUNT2_RX_0_NUM_BLOCK_0_3       ((uint32_t)0x00002000)        /*!< Bit 3 */
#define  USB_COUNT2_RX_0_NUM_BLOCK_0_4       ((uint32_t)0x00004000)        /*!< Bit 4 */

#define  USB_COUNT2_RX_0_BLSIZE_0            ((uint32_t)0x00008000)        /*!< BLock SIZE (low) */

/****************  Bit definition for USB_COUNT2_RX_1 register  ***************/
#define  USB_COUNT2_RX_1_COUNT2_RX_1         ((uint32_t)0x03FF0000)        /*!< Reception Byte Count (high) */

#define  USB_COUNT2_RX_1_NUM_BLOCK_1         ((uint32_t)0x7C000000)        /*!< NUM_BLOCK_1[4:0] bits (Number of blocks) (high) */
#define  USB_COUNT2_RX_1_NUM_BLOCK_1_0       ((uint32_t)0x04000000)        /*!< Bit 0 */
#define  USB_COUNT2_RX_1_NUM_BLOCK_1_1       ((uint32_t)0x08000000)        /*!< Bit 1 */
#define  USB_COUNT2_RX_1_NUM_BLOCK_1_2       ((uint32_t)0x10000000)        /*!< Bit 2 */
#define  USB_COUNT2_RX_1_NUM_BLOCK_1_3       ((uint32_t)0x20000000)        /*!< Bit 3 */
#define  USB_COUNT2_RX_1_NUM_BLOCK_1_4       ((uint32_t)0x40000000)        /*!< Bit 4 */

#define  USB_COUNT2_RX_1_BLSIZE_1            ((uint32_t)0x80000000)        /*!< BLock SIZE (high) */

/****************  Bit definition for USB_COUNT3_RX_0 register  ***************/
#define  USB_COUNT3_RX_0_COUNT3_RX_0         ((uint32_t)0x000003FF)        /*!< Reception Byte Count (low) */

#define  USB_COUNT3_RX_0_NUM_BLOCK_0         ((uint32_t)0x00007C00)        /*!< NUM_BLOCK_0[4:0] bits (Number of blocks) (low) */
#define  USB_COUNT3_RX_0_NUM_BLOCK_0_0       ((uint32_t)0x00000400)        /*!< Bit 0 */
#define  USB_COUNT3_RX_0_NUM_BLOCK_0_1       ((uint32_t)0x00000800)        /*!< Bit 1 */
#define  USB_COUNT3_RX_0_NUM_BLOCK_0_2       ((uint32_t)0x00001000)        /*!< Bit 2 */
#define  USB_COUNT3_RX_0_NUM_BLOCK_0_3       ((uint32_t)0x00002000)        /*!< Bit 3 */
#define  USB_COUNT3_RX_0_NUM_BLOCK_0_4       ((uint32_t)0x00004000)        /*!< Bit 4 */

#define  USB_COUNT3_RX_0_BLSIZE_0            ((uint32_t)0x00008000)        /*!< BLock SIZE (low) */

/****************  Bit definition for USB_COUNT3_RX_1 register  ***************/
#define  USB_COUNT3_RX_1_COUNT3_RX_1         ((uint32_t)0x03FF0000)        /*!< Reception Byte Count (high) */

#define  USB_COUNT3_RX_1_NUM_BLOCK_1         ((uint32_t)0x7C000000)        /*!< NUM_BLOCK_1[4:0] bits (Number of blocks) (high) */
#define  USB_COUNT3_RX_1_NUM_BLOCK_1_0       ((uint32_t)0x04000000)        /*!< Bit 0 */
#define  USB_COUNT3_RX_1_NUM_BLOCK_1_1       ((uint32_t)0x08000000)        /*!< Bit 1 */
#define  USB_COUNT3_RX_1_NUM_BLOCK_1_2       ((uint32_t)0x10000000)        /*!< Bit 2 */
#define  USB_COUNT3_RX_1_NUM_BLOCK_1_3       ((uint32_t)0x20000000)        /*!< Bit 3 */
#define  USB_COUNT3_RX_1_NUM_BLOCK_1_4       ((uint32_t)0x40000000)        /*!< Bit 4 */

#define  USB_COUNT3_RX_1_BLSIZE_1            ((uint32_t)0x80000000)        /*!< BLock SIZE (high) */

/****************  Bit definition for USB_COUNT4_RX_0 register  ***************/
#define  USB_COUNT4_RX_0_COUNT4_RX_0         ((uint32_t)0x000003FF)        /*!< Reception Byte Count (low) */

#define  USB_COUNT4_RX_0_NUM_BLOCK_0         ((uint32_t)0x00007C00)        /*!< NUM_BLOCK_0[4:0] bits (Number of blocks) (low) */
#define  USB_COUNT4_RX_0_NUM_BLOCK_0_0      ((uint32_t)0x00000400)        /*!< Bit 0 */
#define  USB_COUNT4_RX_0_NUM_BLOCK_0_1      ((uint32_t)0x00000800)        /*!< Bit 1 */
#define  USB_COUNT4_RX_0_NUM_BLOCK_0_2      ((uint32_t)0x00001000)        /*!< Bit 2 */
#define  USB_COUNT4_RX_0_NUM_BLOCK_0_3      ((uint32_t)0x00002000)        /*!< Bit 3 */
#define  USB_COUNT4_RX_0_NUM_BLOCK_0_4      ((uint32_t)0x00004000)        /*!< Bit 4 */

#define  USB_COUNT4_RX_0_BLSIZE_0            ((uint32_t)0x00008000)        /*!< BLock SIZE (low) */

/****************  Bit definition for USB_COUNT4_RX_1 register  ***************/
#define  USB_COUNT4_RX_1_COUNT4_RX_1         ((uint32_t)0x03FF0000)        /*!< Reception Byte Count (high) */

#define  USB_COUNT4_RX_1_NUM_BLOCK_1         ((uint32_t)0x7C000000)        /*!< NUM_BLOCK_1[4:0] bits (Number of blocks) (high) */
#define  USB_COUNT4_RX_1_NUM_BLOCK_1_0       ((uint32_t)0x04000000)        /*!< Bit 0 */
#define  USB_COUNT4_RX_1_NUM_BLOCK_1_1       ((uint32_t)0x08000000)        /*!< Bit 1 */
#define  USB_COUNT4_RX_1_NUM_BLOCK_1_2       ((uint32_t)0x10000000)        /*!< Bit 2 */
#define  USB_COUNT4_RX_1_NUM_BLOCK_1_3       ((uint32_t)0x20000000)        /*!< Bit 3 */
#define  USB_COUNT4_RX_1_NUM_BLOCK_1_4       ((uint32_t)0x40000000)        /*!< Bit 4 */

#define  USB_COUNT4_RX_1_BLSIZE_1            ((uint32_t)0x80000000)        /*!< BLock SIZE (high) */

/****************  Bit definition for USB_COUNT5_RX_0 register  ***************/
#define  USB_COUNT5_RX_0_COUNT5_RX_0         ((uint32_t)0x000003FF)        /*!< Reception Byte Count (low) */

#define  USB_COUNT5_RX_0_NUM_BLOCK_0         ((uint32_t)0x00007C00)        /*!< NUM_BLOCK_0[4:0] bits (Number of blocks) (low) */
#define  USB_COUNT5_RX_0_NUM_BLOCK_0_0       ((uint32_t)0x00000400)        /*!< Bit 0 */
#define  USB_COUNT5_RX_0_NUM_BLOCK_0_1       ((uint32_t)0x00000800)        /*!< Bit 1 */
#define  USB_COUNT5_RX_0_NUM_BLOCK_0_2       ((uint32_t)0x00001000)        /*!< Bit 2 */
#define  USB_COUNT5_RX_0_NUM_BLOCK_0_3       ((uint32_t)0x00002000)        /*!< Bit 3 */
#define  USB_COUNT5_RX_0_NUM_BLOCK_0_4       ((uint32_t)0x00004000)        /*!< Bit 4 */

#define  USB_COUNT5_RX_0_BLSIZE_0            ((uint32_t)0x00008000)        /*!< BLock SIZE (low) */

/****************  Bit definition for USB_COUNT5_RX_1 register  ***************/
#define  USB_COUNT5_RX_1_COUNT5_RX_1         ((uint32_t)0x03FF0000)        /*!< Reception Byte Count (high) */

#define  USB_COUNT5_RX_1_NUM_BLOCK_1         ((uint32_t)0x7C000000)        /*!< NUM_BLOCK_1[4:0] bits (Number of blocks) (high) */
#define  USB_COUNT5_RX_1_NUM_BLOCK_1_0       ((uint32_t)0x04000000)        /*!< Bit 0 */
#define  USB_COUNT5_RX_1_NUM_BLOCK_1_1       ((uint32_t)0x08000000)        /*!< Bit 1 */
#define  USB_COUNT5_RX_1_NUM_BLOCK_1_2       ((uint32_t)0x10000000)        /*!< Bit 2 */
#define  USB_COUNT5_RX_1_NUM_BLOCK_1_3       ((uint32_t)0x20000000)        /*!< Bit 3 */
#define  USB_COUNT5_RX_1_NUM_BLOCK_1_4       ((uint32_t)0x40000000)        /*!< Bit 4 */

#define  USB_COUNT5_RX_1_BLSIZE_1            ((uint32_t)0x80000000)        /*!< BLock SIZE (high) */

/***************  Bit definition for USB_COUNT6_RX_0  register  ***************/
#define  USB_COUNT6_RX_0_COUNT6_RX_0         ((uint32_t)0x000003FF)        /*!< Reception Byte Count (low) */

#define  USB_COUNT6_RX_0_NUM_BLOCK_0         ((uint32_t)0x00007C00)        /*!< NUM_BLOCK_0[4:0] bits (Number of blocks) (low) */
#define  USB_COUNT6_RX_0_NUM_BLOCK_0_0       ((uint32_t)0x00000400)        /*!< Bit 0 */
#define  USB_COUNT6_RX_0_NUM_BLOCK_0_1       ((uint32_t)0x00000800)        /*!< Bit 1 */
#define  USB_COUNT6_RX_0_NUM_BLOCK_0_2       ((uint32_t)0x00001000)        /*!< Bit 2 */
#define  USB_COUNT6_RX_0_NUM_BLOCK_0_3       ((uint32_t)0x00002000)        /*!< Bit 3 */
#define  USB_COUNT6_RX_0_NUM_BLOCK_0_4       ((uint32_t)0x00004000)        /*!< Bit 4 */

#define  USB_COUNT6_RX_0_BLSIZE_0            ((uint32_t)0x00008000)        /*!< BLock SIZE (low) */

/****************  Bit definition for USB_COUNT6_RX_1 register  ***************/
#define  USB_COUNT6_RX_1_COUNT6_RX_1         ((uint32_t)0x03FF0000)        /*!< Reception Byte Count (high) */

#define  USB_COUNT6_RX_1_NUM_BLOCK_1         ((uint32_t)0x7C000000)        /*!< NUM_BLOCK_1[4:0] bits (Number of blocks) (high) */
#define  USB_COUNT6_RX_1_NUM_BLOCK_1_0       ((uint32_t)0x04000000)        /*!< Bit 0 */
#define  USB_COUNT6_RX_1_NUM_BLOCK_1_1       ((uint32_t)0x08000000)        /*!< Bit 1 */
#define  USB_COUNT6_RX_1_NUM_BLOCK_1_2       ((uint32_t)0x10000000)        /*!< Bit 2 */
#define  USB_COUNT6_RX_1_NUM_BLOCK_1_3       ((uint32_t)0x20000000)        /*!< Bit 3 */
#define  USB_COUNT6_RX_1_NUM_BLOCK_1_4       ((uint32_t)0x40000000)        /*!< Bit 4 */

#define  USB_COUNT6_RX_1_BLSIZE_1            ((uint32_t)0x80000000)        /*!< BLock SIZE (high) */

/***************  Bit definition for USB_COUNT7_RX_0 register  ****************/
#define  USB_COUNT7_RX_0_COUNT7_RX_0         ((uint32_t)0x000003FF)        /*!< Reception Byte Count (low) */

#define  USB_COUNT7_RX_0_NUM_BLOCK_0         ((uint32_t)0x00007C00)        /*!< NUM_BLOCK_0[4:0] bits (Number of blocks) (low) */
#define  USB_COUNT7_RX_0_NUM_BLOCK_0_0       ((uint32_t)0x00000400)        /*!< Bit 0 */
#define  USB_COUNT7_RX_0_NUM_BLOCK_0_1       ((uint32_t)0x00000800)        /*!< Bit 1 */
#define  USB_COUNT7_RX_0_NUM_BLOCK_0_2       ((uint32_t)0x00001000)        /*!< Bit 2 */
#define  USB_COUNT7_RX_0_NUM_BLOCK_0_3       ((uint32_t)0x00002000)        /*!< Bit 3 */
#define  USB_COUNT7_RX_0_NUM_BLOCK_0_4       ((uint32_t)0x00004000)        /*!< Bit 4 */

#define  USB_COUNT7_RX_0_BLSIZE_0            ((uint32_t)0x00008000)        /*!< BLock SIZE (low) */

/***************  Bit definition for USB_COUNT7_RX_1 register  ****************/
#define  USB_COUNT7_RX_1_COUNT7_RX_1         ((uint32_t)0x03FF0000)        /*!< Reception Byte Count (high) */

#define  USB_COUNT7_RX_1_NUM_BLOCK_1         ((uint32_t)0x7C000000)        /*!< NUM_BLOCK_1[4:0] bits (Number of blocks) (high) */
#define  USB_COUNT7_RX_1_NUM_BLOCK_1_0       ((uint32_t)0x04000000)        /*!< Bit 0 */
#define  USB_COUNT7_RX_1_NUM_BLOCK_1_1       ((uint32_t)0x08000000)        /*!< Bit 1 */
#define  USB_COUNT7_RX_1_NUM_BLOCK_1_2       ((uint32_t)0x10000000)        /*!< Bit 2 */
#define  USB_COUNT7_RX_1_NUM_BLOCK_1_3       ((uint32_t)0x20000000)        /*!< Bit 3 */
#define  USB_COUNT7_RX_1_NUM_BLOCK_1_4       ((uint32_t)0x40000000)        /*!< Bit 4 */

#define  USB_COUNT7_RX_1_BLSIZE_1            ((uint32_t)0x80000000)        /*!< BLock SIZE (high) */

/******************************************************************************/
/*                                                                            */
/*                            Window WATCHDOG                                 */
/*                                                                            */
/******************************************************************************/

/*******************  Bit definition for WWDG_CR register  ********************/
#define  WWDG_CR_T                           ((uint8_t)0x7F)               /*!< T[6:0] bits (7-Bit counter (MSB to LSB)) */
#define  WWDG_CR_T0                          ((uint8_t)0x01)               /*!< Bit 0 */
#define  WWDG_CR_T1                          ((uint8_t)0x02)               /*!< Bit 1 */
#define  WWDG_CR_T2                          ((uint8_t)0x04)               /*!< Bit 2 */
#define  WWDG_CR_T3                          ((uint8_t)0x08)               /*!< Bit 3 */
#define  WWDG_CR_T4                          ((uint8_t)0x10)               /*!< Bit 4 */
#define  WWDG_CR_T5                          ((uint8_t)0x20)               /*!< Bit 5 */
#define  WWDG_CR_T6                          ((uint8_t)0x40)               /*!< Bit 6 */

#define  WWDG_CR_WDGA                        ((uint8_t)0x80)               /*!< Activation bit */

/*******************  Bit definition for WWDG_CFR register  *******************/
#define  WWDG_CFR_W                          ((uint16_t)0x007F)            /*!< W[6:0] bits (7-bit window value) */
#define  WWDG_CFR_W0                         ((uint16_t)0x0001)            /*!< Bit 0 */
#define  WWDG_CFR_W1                         ((uint16_t)0x0002)            /*!< Bit 1 */
#define  WWDG_CFR_W2                         ((uint16_t)0x0004)            /*!< Bit 2 */
#define  WWDG_CFR_W3                         ((uint16_t)0x0008)            /*!< Bit 3 */
#define  WWDG_CFR_W4                         ((uint16_t)0x0010)            /*!< Bit 4 */
#define  WWDG_CFR_W5                         ((uint16_t)0x0020)            /*!< Bit 5 */
#define  WWDG_CFR_W6                         ((uint16_t)0x0040)            /*!< Bit 6 */

#define  WWDG_CFR_WDGTB                      ((uint16_t)0x0180)            /*!< WDGTB[1:0] bits (Timer Base) */
#define  WWDG_CFR_WDGTB0                     ((uint16_t)0x0080)            /*!< Bit 0 */
#define  WWDG_CFR_WDGTB1                     ((uint16_t)0x0100)            /*!< Bit 1 */

#define  WWDG_CFR_EWI                        ((uint16_t)0x0200)            /*!< Early Wakeup Interrupt */

/*******************  Bit definition for WWDG_SR register  ********************/
#define  WWDG_SR_EWIF                        ((uint8_t)0x01)               /*!< Early Wakeup Interrupt Flag */

/******************************************************************************/
/*                                                                            */
/*                               SystemTick                                   */
/*                                                                            */
/******************************************************************************/

/*****************  Bit definition for SysTick_CTRL register  *****************/
#define  SysTick_CTRL_ENABLE                 ((uint32_t)0x00000001)        /*!< Counter enable */
#define  SysTick_CTRL_TICKINT                ((uint32_t)0x00000002)        /*!< Counting down to 0 pends the SysTick handler */
#define  SysTick_CTRL_CLKSOURCE              ((uint32_t)0x00000004)        /*!< Clock source */
#define  SysTick_CTRL_COUNTFLAG              ((uint32_t)0x00010000)        /*!< Count Flag */

/*****************  Bit definition for SysTick_LOAD register  *****************/
#define  SysTick_LOAD_RELOAD                 ((uint32_t)0x00FFFFFF)        /*!< Value to load into the SysTick Current Value Register when the counter reaches 0 */

/*****************  Bit definition for SysTick_VAL register  ******************/
#define  SysTick_VAL_CURRENT                 ((uint32_t)0x00FFFFFF)        /*!< Current value at the time the register is accessed */

/*****************  Bit definition for SysTick_CALIB register  ****************/
#define  SysTick_CALIB_TENMS                 ((uint32_t)0x00FFFFFF)        /*!< Reload value to use for 10ms timing */
#define  SysTick_CALIB_SKEW                  ((uint32_t)0x40000000)        /*!< Calibration value is not exactly 10 ms */
#define  SysTick_CALIB_NOREF                 ((uint32_t)0x80000000)        /*!< The reference clock is not provided */

/******************************************************************************/
/*                                                                            */
/*                  Nested Vectored Interrupt Controller                      */
/*                                                                            */
/******************************************************************************/

/******************  Bit definition for NVIC_ISER register  *******************/
#define  NVIC_ISER_SETENA                    ((uint32_t)0xFFFFFFFF)        /*!< Interrupt set enable bits */
#define  NVIC_ISER_SETENA_0                  ((uint32_t)0x00000001)        /*!< bit 0 */
#define  NVIC_ISER_SETENA_1                  ((uint32_t)0x00000002)        /*!< bit 1 */
#define  NVIC_ISER_SETENA_2                  ((uint32_t)0x00000004)        /*!< bit 2 */
#define  NVIC_ISER_SETENA_3                  ((uint32_t)0x00000008)        /*!< bit 3 */
#define  NVIC_ISER_SETENA_4                  ((uint32_t)0x00000010)        /*!< bit 4 */
#define  NVIC_ISER_SETENA_5                  ((uint32_t)0x00000020)        /*!< bit 5 */
#define  NVIC_ISER_SETENA_6                  ((uint32_t)0x00000040)        /*!< bit 6 */
#define  NVIC_ISER_SETENA_7                  ((uint32_t)0x00000080)        /*!< bit 7 */
#define  NVIC_ISER_SETENA_8                  ((uint32_t)0x00000100)        /*!< bit 8 */
#define  NVIC_ISER_SETENA_9                  ((uint32_t)0x00000200)        /*!< bit 9 */
#define  NVIC_ISER_SETENA_10                 ((uint32_t)0x00000400)        /*!< bit 10 */
#define  NVIC_ISER_SETENA_11                 ((uint32_t)0x00000800)        /*!< bit 11 */
#define  NVIC_ISER_SETENA_12                 ((uint32_t)0x00001000)        /*!< bit 12 */
#define  NVIC_ISER_SETENA_13                 ((uint32_t)0x00002000)        /*!< bit 13 */
#define  NVIC_ISER_SETENA_14                 ((uint32_t)0x00004000)        /*!< bit 14 */
#define  NVIC_ISER_SETENA_15                 ((uint32_t)0x00008000)        /*!< bit 15 */
#define  NVIC_ISER_SETENA_16                 ((uint32_t)0x00010000)        /*!< bit 16 */
#define  NVIC_ISER_SETENA_17                 ((uint32_t)0x00020000)        /*!< bit 17 */
#define  NVIC_ISER_SETENA_18                 ((uint32_t)0x00040000)        /*!< bit 18 */
#define  NVIC_ISER_SETENA_19                 ((uint32_t)0x00080000)        /*!< bit 19 */
#define  NVIC_ISER_SETENA_20                 ((uint32_t)0x00100000)        /*!< bit 20 */
#define  NVIC_ISER_SETENA_21                 ((uint32_t)0x00200000)        /*!< bit 21 */
#define  NVIC_ISER_SETENA_22                 ((uint32_t)0x00400000)        /*!< bit 22 */
#define  NVIC_ISER_SETENA_23                 ((uint32_t)0x00800000)        /*!< bit 23 */
#define  NVIC_ISER_SETENA_24                 ((uint32_t)0x01000000)        /*!< bit 24 */
#define  NVIC_ISER_SETENA_25                 ((uint32_t)0x02000000)        /*!< bit 25 */
#define  NVIC_ISER_SETENA_26                 ((uint32_t)0x04000000)        /*!< bit 26 */
#define  NVIC_ISER_SETENA_27                 ((uint32_t)0x08000000)        /*!< bit 27 */
#define  NVIC_ISER_SETENA_28                 ((uint32_t)0x10000000)        /*!< bit 28 */
#define  NVIC_ISER_SETENA_29                 ((uint32_t)0x20000000)        /*!< bit 29 */
#define  NVIC_ISER_SETENA_30                 ((uint32_t)0x40000000)        /*!< bit 30 */
#define  NVIC_ISER_SETENA_31                 ((uint32_t)0x80000000)        /*!< bit 31 */

/******************  Bit definition for NVIC_ICER register  *******************/
#define  NVIC_ICER_CLRENA                   ((uint32_t)0xFFFFFFFF)        /*!< Interrupt clear-enable bits */
#define  NVIC_ICER_CLRENA_0                  ((uint32_t)0x00000001)        /*!< bit 0 */
#define  NVIC_ICER_CLRENA_1                  ((uint32_t)0x00000002)        /*!< bit 1 */
#define  NVIC_ICER_CLRENA_2                  ((uint32_t)0x00000004)        /*!< bit 2 */
#define  NVIC_ICER_CLRENA_3                  ((uint32_t)0x00000008)        /*!< bit 3 */
#define  NVIC_ICER_CLRENA_4                  ((uint32_t)0x00000010)        /*!< bit 4 */
#define  NVIC_ICER_CLRENA_5                  ((uint32_t)0x00000020)        /*!< bit 5 */
#define  NVIC_ICER_CLRENA_6                  ((uint32_t)0x00000040)        /*!< bit 6 */
#define  NVIC_ICER_CLRENA_7                  ((uint32_t)0x00000080)        /*!< bit 7 */
#define  NVIC_ICER_CLRENA_8                  ((uint32_t)0x00000100)        /*!< bit 8 */
#define  NVIC_ICER_CLRENA_9                  ((uint32_t)0x00000200)        /*!< bit 9 */
#define  NVIC_ICER_CLRENA_10                 ((uint32_t)0x00000400)        /*!< bit 10 */
#define  NVIC_ICER_CLRENA_11                 ((uint32_t)0x00000800)        /*!< bit 11 */
#define  NVIC_ICER_CLRENA_12                 ((uint32_t)0x00001000)        /*!< bit 12 */
#define  NVIC_ICER_CLRENA_13                 ((uint32_t)0x00002000)        /*!< bit 13 */
#define  NVIC_ICER_CLRENA_14                 ((uint32_t)0x00004000)        /*!< bit 14 */
#define  NVIC_ICER_CLRENA_15                 ((uint32_t)0x00008000)        /*!< bit 15 */
#define  NVIC_ICER_CLRENA_16                 ((uint32_t)0x00010000)        /*!< bit 16 */
#define  NVIC_ICER_CLRENA_17                 ((uint32_t)0x00020000)        /*!< bit 17 */
#define  NVIC_ICER_CLRENA_18                 ((uint32_t)0x00040000)        /*!< bit 18 */
#define  NVIC_ICER_CLRENA_19                 ((uint32_t)0x00080000)        /*!< bit 19 */
#define  NVIC_ICER_CLRENA_20                 ((uint32_t)0x00100000)        /*!< bit 20 */
#define  NVIC_ICER_CLRENA_21                 ((uint32_t)0x00200000)        /*!< bit 21 */
#define  NVIC_ICER_CLRENA_22                 ((uint32_t)0x00400000)        /*!< bit 22 */
#define  NVIC_ICER_CLRENA_23                 ((uint32_t)0x00800000)        /*!< bit 23 */
#define  NVIC_ICER_CLRENA_24                 ((uint32_t)0x01000000)        /*!< bit 24 */
#define  NVIC_ICER_CLRENA_25                 ((uint32_t)0x02000000)        /*!< bit 25 */
#define  NVIC_ICER_CLRENA_26                 ((uint32_t)0x04000000)        /*!< bit 26 */
#define  NVIC_ICER_CLRENA_27                 ((uint32_t)0x08000000)        /*!< bit 27 */
#define  NVIC_ICER_CLRENA_28                 ((uint32_t)0x10000000)        /*!< bit 28 */
#define  NVIC_ICER_CLRENA_29                 ((uint32_t)0x20000000)        /*!< bit 29 */
#define  NVIC_ICER_CLRENA_30                 ((uint32_t)0x40000000)        /*!< bit 30 */
#define  NVIC_ICER_CLRENA_31                 ((uint32_t)0x80000000)        /*!< bit 31 */

/******************  Bit definition for NVIC_ISPR register  *******************/
#define  NVIC_ISPR_SETPEND                   ((uint32_t)0xFFFFFFFF)        /*!< Interrupt set-pending bits */
#define  NVIC_ISPR_SETPEND_0                 ((uint32_t)0x00000001)        /*!< bit 0 */
#define  NVIC_ISPR_SETPEND_1                 ((uint32_t)0x00000002)        /*!< bit 1 */
#define  NVIC_ISPR_SETPEND_2                 ((uint32_t)0x00000004)        /*!< bit 2 */
#define  NVIC_ISPR_SETPEND_3                 ((uint32_t)0x00000008)        /*!< bit 3 */
#define  NVIC_ISPR_SETPEND_4                 ((uint32_t)0x00000010)        /*!< bit 4 */
#define  NVIC_ISPR_SETPEND_5                 ((uint32_t)0x00000020)        /*!< bit 5 */
#define  NVIC_ISPR_SETPEND_6                 ((uint32_t)0x00000040)        /*!< bit 6 */
#define  NVIC_ISPR_SETPEND_7                 ((uint32_t)0x00000080)        /*!< bit 7 */
#define  NVIC_ISPR_SETPEND_8                 ((uint32_t)0x00000100)        /*!< bit 8 */
#define  NVIC_ISPR_SETPEND_9                 ((uint32_t)0x00000200)        /*!< bit 9 */
#define  NVIC_ISPR_SETPEND_10                ((uint32_t)0x00000400)        /*!< bit 10 */
#define  NVIC_ISPR_SETPEND_11                ((uint32_t)0x00000800)        /*!< bit 11 */
#define  NVIC_ISPR_SETPEND_12                ((uint32_t)0x00001000)        /*!< bit 12 */
#define  NVIC_ISPR_SETPEND_13                ((uint32_t)0x00002000)        /*!< bit 13 */
#define  NVIC_ISPR_SETPEND_14                ((uint32_t)0x00004000)        /*!< bit 14 */
#define  NVIC_ISPR_SETPEND_15                ((uint32_t)0x00008000)        /*!< bit 15 */
#define  NVIC_ISPR_SETPEND_16                ((uint32_t)0x00010000)        /*!< bit 16 */
#define  NVIC_ISPR_SETPEND_17                ((uint32_t)0x00020000)        /*!< bit 17 */
#define  NVIC_ISPR_SETPEND_18                ((uint32_t)0x00040000)        /*!< bit 18 */
#define  NVIC_ISPR_SETPEND_19                ((uint32_t)0x00080000)        /*!< bit 19 */
#define  NVIC_ISPR_SETPEND_20                ((uint32_t)0x00100000)        /*!< bit 20 */
#define  NVIC_ISPR_SETPEND_21                ((uint32_t)0x00200000)        /*!< bit 21 */
#define  NVIC_ISPR_SETPEND_22                ((uint32_t)0x00400000)        /*!< bit 22 */
#define  NVIC_ISPR_SETPEND_23                ((uint32_t)0x00800000)        /*!< bit 23 */
#define  NVIC_ISPR_SETPEND_24                ((uint32_t)0x01000000)        /*!< bit 24 */
#define  NVIC_ISPR_SETPEND_25                ((uint32_t)0x02000000)        /*!< bit 25 */
#define  NVIC_ISPR_SETPEND_26                ((uint32_t)0x04000000)        /*!< bit 26 */
#define  NVIC_ISPR_SETPEND_27                ((uint32_t)0x08000000)        /*!< bit 27 */
#define  NVIC_ISPR_SETPEND_28                ((uint32_t)0x10000000)        /*!< bit 28 */
#define  NVIC_ISPR_SETPEND_29                ((uint32_t)0x20000000)        /*!< bit 29 */
#define  NVIC_ISPR_SETPEND_30                ((uint32_t)0x40000000)        /*!< bit 30 */
#define  NVIC_ISPR_SETPEND_31                ((uint32_t)0x80000000)        /*!< bit 31 */

/******************  Bit definition for NVIC_ICPR register  *******************/
#define  NVIC_ICPR_CLRPEND                   ((uint32_t)0xFFFFFFFF)        /*!< Interrupt clear-pending bits */
#define  NVIC_ICPR_CLRPEND_0                 ((uint32_t)0x00000001)        /*!< bit 0 */
#define  NVIC_ICPR_CLRPEND_1                 ((uint32_t)0x00000002)        /*!< bit 1 */
#define  NVIC_ICPR_CLRPEND_2                 ((uint32_t)0x00000004)        /*!< bit 2 */
#define  NVIC_ICPR_CLRPEND_3                 ((uint32_t)0x00000008)        /*!< bit 3 */
#define  NVIC_ICPR_CLRPEND_4                 ((uint32_t)0x00000010)        /*!< bit 4 */
#define  NVIC_ICPR_CLRPEND_5                 ((uint32_t)0x00000020)        /*!< bit 5 */
#define  NVIC_ICPR_CLRPEND_6                 ((uint32_t)0x00000040)        /*!< bit 6 */
#define  NVIC_ICPR_CLRPEND_7                 ((uint32_t)0x00000080)        /*!< bit 7 */
#define  NVIC_ICPR_CLRPEND_8                 ((uint32_t)0x00000100)        /*!< bit 8 */
#define  NVIC_ICPR_CLRPEND_9                 ((uint32_t)0x00000200)        /*!< bit 9 */
#define  NVIC_ICPR_CLRPEND_10                ((uint32_t)0x00000400)        /*!< bit 10 */
#define  NVIC_ICPR_CLRPEND_11                ((uint32_t)0x00000800)        /*!< bit 11 */
#define  NVIC_ICPR_CLRPEND_12                ((uint32_t)0x00001000)        /*!< bit 12 */
#define  NVIC_ICPR_CLRPEND_13                ((uint32_t)0x00002000)        /*!< bit 13 */
#define  NVIC_ICPR_CLRPEND_14                ((uint32_t)0x00004000)        /*!< bit 14 */
#define  NVIC_ICPR_CLRPEND_15                ((uint32_t)0x00008000)        /*!< bit 15 */
#define  NVIC_ICPR_CLRPEND_16                ((uint32_t)0x00010000)        /*!< bit 16 */
#define  NVIC_ICPR_CLRPEND_17                ((uint32_t)0x00020000)        /*!< bit 17 */
#define  NVIC_ICPR_CLRPEND_18                ((uint32_t)0x00040000)        /*!< bit 18 */
#define  NVIC_ICPR_CLRPEND_19                ((uint32_t)0x00080000)        /*!< bit 19 */
#define  NVIC_ICPR_CLRPEND_20                ((uint32_t)0x00100000)        /*!< bit 20 */
#define  NVIC_ICPR_CLRPEND_21                ((uint32_t)0x00200000)        /*!< bit 21 */
#define  NVIC_ICPR_CLRPEND_22                ((uint32_t)0x00400000)        /*!< bit 22 */
#define  NVIC_ICPR_CLRPEND_23                ((uint32_t)0x00800000)        /*!< bit 23 */
#define  NVIC_ICPR_CLRPEND_24                ((uint32_t)0x01000000)        /*!< bit 24 */
#define  NVIC_ICPR_CLRPEND_25                ((uint32_t)0x02000000)        /*!< bit 25 */
#define  NVIC_ICPR_CLRPEND_26                ((uint32_t)0x04000000)        /*!< bit 26 */
#define  NVIC_ICPR_CLRPEND_27                ((uint32_t)0x08000000)        /*!< bit 27 */
#define  NVIC_ICPR_CLRPEND_28                ((uint32_t)0x10000000)        /*!< bit 28 */
#define  NVIC_ICPR_CLRPEND_29                ((uint32_t)0x20000000)        /*!< bit 29 */
#define  NVIC_ICPR_CLRPEND_30                ((uint32_t)0x40000000)        /*!< bit 30 */
#define  NVIC_ICPR_CLRPEND_31                ((uint32_t)0x80000000)        /*!< bit 31 */

/******************  Bit definition for NVIC_IABR register  *******************/
#define  NVIC_IABR_ACTIVE                    ((uint32_t)0xFFFFFFFF)        /*!< Interrupt active flags */
#define  NVIC_IABR_ACTIVE_0                  ((uint32_t)0x00000001)        /*!< bit 0 */
#define  NVIC_IABR_ACTIVE_1                  ((uint32_t)0x00000002)        /*!< bit 1 */
#define  NVIC_IABR_ACTIVE_2                  ((uint32_t)0x00000004)        /*!< bit 2 */
#define  NVIC_IABR_ACTIVE_3                  ((uint32_t)0x00000008)        /*!< bit 3 */
#define  NVIC_IABR_ACTIVE_4                  ((uint32_t)0x00000010)        /*!< bit 4 */
#define  NVIC_IABR_ACTIVE_5                  ((uint32_t)0x00000020)        /*!< bit 5 */
#define  NVIC_IABR_ACTIVE_6                  ((uint32_t)0x00000040)        /*!< bit 6 */
#define  NVIC_IABR_ACTIVE_7                  ((uint32_t)0x00000080)        /*!< bit 7 */
#define  NVIC_IABR_ACTIVE_8                  ((uint32_t)0x00000100)        /*!< bit 8 */
#define  NVIC_IABR_ACTIVE_9                  ((uint32_t)0x00000200)        /*!< bit 9 */
#define  NVIC_IABR_ACTIVE_10                 ((uint32_t)0x00000400)        /*!< bit 10 */
#define  NVIC_IABR_ACTIVE_11                 ((uint32_t)0x00000800)        /*!< bit 11 */
#define  NVIC_IABR_ACTIVE_12                 ((uint32_t)0x00001000)        /*!< bit 12 */
#define  NVIC_IABR_ACTIVE_13                 ((uint32_t)0x00002000)        /*!< bit 13 */
#define  NVIC_IABR_ACTIVE_14                 ((uint32_t)0x00004000)        /*!< bit 14 */
#define  NVIC_IABR_ACTIVE_15                 ((uint32_t)0x00008000)        /*!< bit 15 */
#define  NVIC_IABR_ACTIVE_16                 ((uint32_t)0x00010000)        /*!< bit 16 */
#define  NVIC_IABR_ACTIVE_17                 ((uint32_t)0x00020000)        /*!< bit 17 */
#define  NVIC_IABR_ACTIVE_18                 ((uint32_t)0x00040000)        /*!< bit 18 */
#define  NVIC_IABR_ACTIVE_19                 ((uint32_t)0x00080000)        /*!< bit 19 */
#define  NVIC_IABR_ACTIVE_20                 ((uint32_t)0x00100000)        /*!< bit 20 */
#define  NVIC_IABR_ACTIVE_21                 ((uint32_t)0x00200000)        /*!< bit 21 */
#define  NVIC_IABR_ACTIVE_22                 ((uint32_t)0x00400000)        /*!< bit 22 */
#define  NVIC_IABR_ACTIVE_23                 ((uint32_t)0x00800000)        /*!< bit 23 */
#define  NVIC_IABR_ACTIVE_24                 ((uint32_t)0x01000000)        /*!< bit 24 */
#define  NVIC_IABR_ACTIVE_25                 ((uint32_t)0x02000000)        /*!< bit 25 */
#define  NVIC_IABR_ACTIVE_26                 ((uint32_t)0x04000000)        /*!< bit 26 */
#define  NVIC_IABR_ACTIVE_27                 ((uint32_t)0x08000000)        /*!< bit 27 */
#define  NVIC_IABR_ACTIVE_28                 ((uint32_t)0x10000000)        /*!< bit 28 */
#define  NVIC_IABR_ACTIVE_29                 ((uint32_t)0x20000000)        /*!< bit 29 */
#define  NVIC_IABR_ACTIVE_30                 ((uint32_t)0x40000000)        /*!< bit 30 */
#define  NVIC_IABR_ACTIVE_31                 ((uint32_t)0x80000000)        /*!< bit 31 */

/******************  Bit definition for NVIC_PRI0 register  *******************/
#define  NVIC_IPR0_PRI_0                     ((uint32_t)0x000000FF)        /*!< Priority of interrupt 0 */
#define  NVIC_IPR0_PRI_1                     ((uint32_t)0x0000FF00)        /*!< Priority of interrupt 1 */
#define  NVIC_IPR0_PRI_2                     ((uint32_t)0x00FF0000)        /*!< Priority of interrupt 2 */
#define  NVIC_IPR0_PRI_3                     ((uint32_t)0xFF000000)        /*!< Priority of interrupt 3 */

/******************  Bit definition for NVIC_PRI1 register  *******************/
#define  NVIC_IPR1_PRI_4                     ((uint32_t)0x000000FF)        /*!< Priority of interrupt 4 */
#define  NVIC_IPR1_PRI_5                     ((uint32_t)0x0000FF00)        /*!< Priority of interrupt 5 */
#define  NVIC_IPR1_PRI_6                     ((uint32_t)0x00FF0000)        /*!< Priority of interrupt 6 */
#define  NVIC_IPR1_PRI_7                     ((uint32_t)0xFF000000)        /*!< Priority of interrupt 7 */

/******************  Bit definition for NVIC_PRI2 register  *******************/
#define  NVIC_IPR2_PRI_8                     ((uint32_t)0x000000FF)        /*!< Priority of interrupt 8 */
#define  NVIC_IPR2_PRI_9                     ((uint32_t)0x0000FF00)        /*!< Priority of interrupt 9 */
#define  NVIC_IPR2_PRI_10                    ((uint32_t)0x00FF0000)        /*!< Priority of interrupt 10 */
#define  NVIC_IPR2_PRI_11                    ((uint32_t)0xFF000000)        /*!< Priority of interrupt 11 */

/******************  Bit definition for NVIC_PRI3 register  *******************/
#define  NVIC_IPR3_PRI_12                    ((uint32_t)0x000000FF)        /*!< Priority of interrupt 12 */
#define  NVIC_IPR3_PRI_13                    ((uint32_t)0x0000FF00)        /*!< Priority of interrupt 13 */
#define  NVIC_IPR3_PRI_14                    ((uint32_t)0x00FF0000)        /*!< Priority of interrupt 14 */
#define  NVIC_IPR3_PRI_15                    ((uint32_t)0xFF000000)        /*!< Priority of interrupt 15 */

/******************  Bit definition for NVIC_PRI4 register  *******************/
#define  NVIC_IPR4_PRI_16                    ((uint32_t)0x000000FF)        /*!< Priority of interrupt 16 */
#define  NVIC_IPR4_PRI_17                    ((uint32_t)0x0000FF00)        /*!< Priority of interrupt 17 */
#define  NVIC_IPR4_PRI_18                    ((uint32_t)0x00FF0000)        /*!< Priority of interrupt 18 */
#define  NVIC_IPR4_PRI_19                    ((uint32_t)0xFF000000)        /*!< Priority of interrupt 19 */

/******************  Bit definition for NVIC_PRI5 register  *******************/
#define  NVIC_IPR5_PRI_20                    ((uint32_t)0x000000FF)        /*!< Priority of interrupt 20 */
#define  NVIC_IPR5_PRI_21                    ((uint32_t)0x0000FF00)        /*!< Priority of interrupt 21 */
#define  NVIC_IPR5_PRI_22                    ((uint32_t)0x00FF0000)        /*!< Priority of interrupt 22 */
#define  NVIC_IPR5_PRI_23                    ((uint32_t)0xFF000000)        /*!< Priority of interrupt 23 */

/******************  Bit definition for NVIC_PRI6 register  *******************/
#define  NVIC_IPR6_PRI_24                    ((uint32_t)0x000000FF)        /*!< Priority of interrupt 24 */
#define  NVIC_IPR6_PRI_25                    ((uint32_t)0x0000FF00)        /*!< Priority of interrupt 25 */
#define  NVIC_IPR6_PRI_26                    ((uint32_t)0x00FF0000)        /*!< Priority of interrupt 26 */
#define  NVIC_IPR6_PRI_27                    ((uint32_t)0xFF000000)        /*!< Priority of interrupt 27 */

/******************  Bit definition for NVIC_PRI7 register  *******************/
#define  NVIC_IPR7_PRI_28                    ((uint32_t)0x000000FF)        /*!< Priority of interrupt 28 */
#define  NVIC_IPR7_PRI_29                    ((uint32_t)0x0000FF00)        /*!< Priority of interrupt 29 */
#define  NVIC_IPR7_PRI_30                    ((uint32_t)0x00FF0000)        /*!< Priority of interrupt 30 */
#define  NVIC_IPR7_PRI_31                    ((uint32_t)0xFF000000)        /*!< Priority of interrupt 31 */

/******************  Bit definition for SCB_CPUID register  *******************/
#define  SCB_CPUID_REVISION                  ((uint32_t)0x0000000F)        /*!< Implementation defined revision number */
#define  SCB_CPUID_PARTNO                    ((uint32_t)0x0000FFF0)        /*!< Number of processor within family */
#define  SCB_CPUID_Constant                  ((uint32_t)0x000F0000)        /*!< Reads as 0x0F */
#define  SCB_CPUID_VARIANT                   ((uint32_t)0x00F00000)        /*!< Implementation defined variant number */
#define  SCB_CPUID_IMPLEMENTER               ((uint32_t)0xFF000000)        /*!< Implementer code. ARM is 0x41 */

/*******************  Bit definition for SCB_ICSR register  *******************/
#define  SCB_ICSR_VECTACTIVE                 ((uint32_t)0x000001FF)        /*!< Active ISR number field */
#define  SCB_ICSR_RETTOBASE                  ((uint32_t)0x00000800)        /*!< All active exceptions minus the IPSR_current_exception yields the empty set */
#define  SCB_ICSR_VECTPENDING                ((uint32_t)0x003FF000)        /*!< Pending ISR number field */
#define  SCB_ICSR_ISRPENDING                 ((uint32_t)0x00400000)        /*!< Interrupt pending flag */
#define  SCB_ICSR_ISRPREEMPT                 ((uint32_t)0x00800000)        /*!< It indicates that a pending interrupt becomes active in the next running cycle */
#define  SCB_ICSR_PENDSTCLR                  ((uint32_t)0x02000000)        /*!< Clear pending SysTick bit */
#define  SCB_ICSR_PENDSTSET                  ((uint32_t)0x04000000)        /*!< Set pending SysTick bit */
#define  SCB_ICSR_PENDSVCLR                  ((uint32_t)0x08000000)        /*!< Clear pending pendSV bit */
#define  SCB_ICSR_PENDSVSET                  ((uint32_t)0x10000000)        /*!< Set pending pendSV bit */
#define  SCB_ICSR_NMIPENDSET                 ((uint32_t)0x80000000)        /*!< Set pending NMI bit */

/*******************  Bit definition for SCB_VTOR register  *******************/
#define  SCB_VTOR_TBLOFF                     ((uint32_t)0x1FFFFF80)        /*!< Vector table base offset field */
#define  SCB_VTOR_TBLBASE                    ((uint32_t)0x20000000)        /*!< Table base in code(0) or RAM(1) */

/*!<*****************  Bit definition for SCB_AIRCR register  *******************/
#define  SCB_AIRCR_VECTRESET                 ((uint32_t)0x00000001)        /*!< System Reset bit */
#define  SCB_AIRCR_VECTCLRACTIVE             ((uint32_t)0x00000002)        /*!< Clear active vector bit */
#define  SCB_AIRCR_SYSRESETREQ               ((uint32_t)0x00000004)        /*!< Requests chip control logic to generate a reset */

#define  SCB_AIRCR_PRIGROUP                  ((uint32_t)0x00000700)        /*!< PRIGROUP[2:0] bits (Priority group) */
#define  SCB_AIRCR_PRIGROUP_0                ((uint32_t)0x00000100)        /*!< Bit 0 */
#define  SCB_AIRCR_PRIGROUP_1                ((uint32_t)0x00000200)        /*!< Bit 1 */
#define  SCB_AIRCR_PRIGROUP_2                ((uint32_t)0x00000400)        /*!< Bit 2  */

/* prority group configuration */
#define  SCB_AIRCR_PRIGROUP0                 ((uint32_t)0x00000000)        /*!< Priority group=0 (7 bits of pre-emption priority, 1 bit of subpriority) */
#define  SCB_AIRCR_PRIGROUP1                 ((uint32_t)0x00000100)        /*!< Priority group=1 (6 bits of pre-emption priority, 2 bits of subpriority) */
#define  SCB_AIRCR_PRIGROUP2                 ((uint32_t)0x00000200)        /*!< Priority group=2 (5 bits of pre-emption priority, 3 bits of subpriority) */
#define  SCB_AIRCR_PRIGROUP3                 ((uint32_t)0x00000300)        /*!< Priority group=3 (4 bits of pre-emption priority, 4 bits of subpriority) */
#define  SCB_AIRCR_PRIGROUP4                 ((uint32_t)0x00000400)        /*!< Priority group=4 (3 bits of pre-emption priority, 5 bits of subpriority) */
#define  SCB_AIRCR_PRIGROUP5                 ((uint32_t)0x00000500)        /*!< Priority group=5 (2 bits of pre-emption priority, 6 bits of subpriority) */
#define  SCB_AIRCR_PRIGROUP6                 ((uint32_t)0x00000600)        /*!< Priority group=6 (1 bit of pre-emption priority, 7 bits of subpriority) */
#define  SCB_AIRCR_PRIGROUP7                 ((uint32_t)0x00000700)        /*!< Priority group=7 (no pre-emption priority, 8 bits of subpriority) */

#define  SCB_AIRCR_ENDIANESS                 ((uint32_t)0x00008000)        /*!< Data endianness bit */
#define  SCB_AIRCR_VECTKEY                   ((uint32_t)0xFFFF0000)        /*!< Register key (VECTKEY) - Reads as 0xFA05 (VECTKEYSTAT) */

/*******************  Bit definition for SCB_SCR register  ********************/
#define  SCB_SCR_SLEEPONEXIT                 ((uint8_t)0x02)               /*!< Sleep on exit bit */
#define  SCB_SCR_SLEEPDEEP                   ((uint8_t)0x04)               /*!< Sleep deep bit */
#define  SCB_SCR_SEVONPEND                   ((uint8_t)0x10)               /*!< Wake up from WFE */

/********************  Bit definition for SCB_CCR register  *******************/
#define  SCB_CCR_NONBASETHRDENA              ((uint16_t)0x0001)            /*!< Thread mode can be entered from any level in Handler mode by controlled return value */
#define  SCB_CCR_USERSETMPEND                ((uint16_t)0x0002)            /*!< Enables user code to write the Software Trigger Interrupt register to trigger (pend) a Main exception */
#define  SCB_CCR_UNALIGN_TRP                 ((uint16_t)0x0008)            /*!< Trap for unaligned access */
#define  SCB_CCR_DIV_0_TRP                   ((uint16_t)0x0010)            /*!< Trap on Divide by 0 */
#define  SCB_CCR_BFHFNMIGN                   ((uint16_t)0x0100)            /*!< Handlers running at priority -1 and -2 */
#define  SCB_CCR_STKALIGN                    ((uint16_t)0x0200)            /*!< On exception entry, the SP used prior to the exception is adjusted to be 8-byte aligned */

/*******************  Bit definition for SCB_SHPR register ********************/
#define  SCB_SHPR_PRI_N                      ((uint32_t)0x000000FF)        /*!< Priority of system handler 4,8, and 12. Mem Manage, reserved and Debug Monitor */
#define  SCB_SHPR_PRI_N1                     ((uint32_t)0x0000FF00)        /*!< Priority of system handler 5,9, and 13. Bus Fault, reserved and reserved */
#define  SCB_SHPR_PRI_N2                     ((uint32_t)0x00FF0000)        /*!< Priority of system handler 6,10, and 14. Usage Fault, reserved and PendSV */
#define  SCB_SHPR_PRI_N3                     ((uint32_t)0xFF000000)        /*!< Priority of system handler 7,11, and 15. Reserved, SVCall and SysTick */

/******************  Bit definition for SCB_SHCSR register  *******************/
#define  SCB_SHCSR_MEMFAULTACT               ((uint32_t)0x00000001)        /*!< MemManage is active */
#define  SCB_SHCSR_BUSFAULTACT               ((uint32_t)0x00000002)        /*!< BusFault is active */
#define  SCB_SHCSR_USGFAULTACT               ((uint32_t)0x00000008)        /*!< UsageFault is active */
#define  SCB_SHCSR_SVCALLACT                 ((uint32_t)0x00000080)        /*!< SVCall is active */
#define  SCB_SHCSR_MONITORACT                ((uint32_t)0x00000100)        /*!< Monitor is active */
#define  SCB_SHCSR_PENDSVACT                 ((uint32_t)0x00000400)        /*!< PendSV is active */
#define  SCB_SHCSR_SYSTICKACT                ((uint32_t)0x00000800)        /*!< SysTick is active */
#define  SCB_SHCSR_USGFAULTPENDED            ((uint32_t)0x00001000)        /*!< Usage Fault is pended */
#define  SCB_SHCSR_MEMFAULTPENDED            ((uint32_t)0x00002000)        /*!< MemManage is pended */
#define  SCB_SHCSR_BUSFAULTPENDED            ((uint32_t)0x00004000)        /*!< Bus Fault is pended */
#define  SCB_SHCSR_SVCALLPENDED              ((uint32_t)0x00008000)        /*!< SVCall is pended */
#define  SCB_SHCSR_MEMFAULTENA               ((uint32_t)0x00010000)        /*!< MemManage enable */
#define  SCB_SHCSR_BUSFAULTENA               ((uint32_t)0x00020000)        /*!< Bus Fault enable */
#define  SCB_SHCSR_USGFAULTENA               ((uint32_t)0x00040000)        /*!< UsageFault enable */

/*******************  Bit definition for SCB_CFSR register  *******************/
/*!< MFSR */
#define  SCB_CFSR_IACCVIOL                   ((uint32_t)0x00000001)        /*!< Instruction access violation */
#define  SCB_CFSR_DACCVIOL                   ((uint32_t)0x00000002)        /*!< Data access violation */
#define  SCB_CFSR_MUNSTKERR                  ((uint32_t)0x00000008)        /*!< Unstacking error */
#define  SCB_CFSR_MSTKERR                    ((uint32_t)0x00000010)        /*!< Stacking error */
#define  SCB_CFSR_MMARVALID                  ((uint32_t)0x00000080)        /*!< Memory Manage Address Register address valid flag */
/*!< BFSR */
#define  SCB_CFSR_IBUSERR                    ((uint32_t)0x00000100)        /*!< Instruction bus error flag */
#define  SCB_CFSR_PRECISERR                  ((uint32_t)0x00000200)        /*!< Precise data bus error */
#define  SCB_CFSR_IMPRECISERR                ((uint32_t)0x00000400)        /*!< Imprecise data bus error */
#define  SCB_CFSR_UNSTKERR                   ((uint32_t)0x00000800)        /*!< Unstacking error */
#define  SCB_CFSR_STKERR                     ((uint32_t)0x00001000)        /*!< Stacking error */
#define  SCB_CFSR_BFARVALID                  ((uint32_t)0x00008000)        /*!< Bus Fault Address Register address valid flag */
/*!< UFSR */
#define  SCB_CFSR_UNDEFINSTR                 ((uint32_t)0x00010000)        /*!< The processor attempt to excecute an undefined instruction */
#define  SCB_CFSR_INVSTATE                   ((uint32_t)0x00020000)        /*!< Invalid combination of EPSR and instruction */
#define  SCB_CFSR_INVPC                      ((uint32_t)0x00040000)        /*!< Attempt to load EXC_RETURN into pc illegally */
#define  SCB_CFSR_NOCP                       ((uint32_t)0x00080000)        /*!< Attempt to use a coprocessor instruction */
#define  SCB_CFSR_UNALIGNED                  ((uint32_t)0x01000000)        /*!< Fault occurs when there is an attempt to make an unaligned memory access */
#define  SCB_CFSR_DIVBYZERO                  ((uint32_t)0x02000000)        /*!< Fault occurs when SDIV or DIV instruction is used with a divisor of 0 */

/*******************  Bit definition for SCB_HFSR register  *******************/
#define  SCB_HFSR_VECTTBL                    ((uint32_t)0x00000002)        /*!< Fault occures because of vector table read on exception processing */
#define  SCB_HFSR_FORCED                     ((uint32_t)0x40000000)        /*!< Hard Fault activated when a configurable Fault was received and cannot activate */
#define  SCB_HFSR_DEBUGEVT                   ((uint32_t)0x80000000)        /*!< Fault related to debug */

/*******************  Bit definition for SCB_DFSR register  *******************/
#define  SCB_DFSR_HALTED                     ((uint8_t)0x01)               /*!< Halt request flag */
#define  SCB_DFSR_BKPT                       ((uint8_t)0x02)               /*!< BKPT flag */
#define  SCB_DFSR_DWTTRAP                    ((uint8_t)0x04)               /*!< Data Watchpoint and Trace (DWT) flag */
#define  SCB_DFSR_VCATCH                     ((uint8_t)0x08)               /*!< Vector catch flag */
#define  SCB_DFSR_EXTERNAL                   ((uint8_t)0x10)               /*!< External debug request flag */

/*******************  Bit definition for SCB_MMFAR register  ******************/
#define  SCB_MMFAR_ADDRESS                   ((uint32_t)0xFFFFFFFF)        /*!< Mem Manage fault address field */

/*******************  Bit definition for SCB_BFAR register  *******************/
#define  SCB_BFAR_ADDRESS                    ((uint32_t)0xFFFFFFFF)        /*!< Bus fault address field */

/*******************  Bit definition for SCB_afsr register  *******************/
#define  SCB_AFSR_IMPDEF                     ((uint32_t)0xFFFFFFFF)        /*!< Implementation defined */
/**
  * @}
  */

 /**
  * @}
  */ 

#ifdef USE_STDPERIPH_DRIVER
  #include "stm32l1xx_conf.h"
#endif

/** @addtogroup Exported_macro
  * @{
  */

#define SET_BIT(REG, BIT)     ((REG) |= (BIT))

#define CLEAR_BIT(REG, BIT)   ((REG) &= ~(BIT))

#define READ_BIT(REG, BIT)    ((REG) & (BIT))

#define CLEAR_REG(REG)        ((REG) = (0x0))

#define WRITE_REG(REG, VAL)   ((REG) = (VAL))

#define READ_REG(REG)         ((REG))

#define MODIFY_REG(REG, CLEARMASK, SETMASK)  WRITE_REG((REG), (((READ_REG(REG)) & (~(CLEARMASK))) | (SETMASK)))

/**
  * @}
  */

#ifdef __cplusplus
}
#endif

#endif /* __STM32L1XX_H */

/**
  * @}
  */

  /**
  * @}
  */

/******************* (C) COPYRIGHT 2010 STMicroelectronics *****END OF FILE****/
