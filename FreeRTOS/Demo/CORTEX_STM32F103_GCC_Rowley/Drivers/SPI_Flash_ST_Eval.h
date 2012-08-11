/******************** (C) COPYRIGHT 2009 STMicroelectronics ********************
* File Name          : spi_flash.h
* Author             : MCD Application Team
* Version            : V2.0.0
* Date               : 04/27/2009
* Description        : Header for spi_flash.c file.
********************************************************************************
* THE PRESENT FIRMWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
* WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
* AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT,
* INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE
* CONTENT OF SUCH FIRMWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING
* INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __SPI_FLASH_H
#define __SPI_FLASH_H

/* Includes ------------------------------------------------------------------*/
#include "stm32f10x.h"
#include "stm32f10x_spi.h"
#include "stm32f10x_gpio.h"
#include "stm32f10x_rcc.h"

#define uint32_t unsigned long
#define uint8_t unsigned char
#define uint16_t unsigned short

/* Exported types ------------------------------------------------------------*/
/* Exported constants --------------------------------------------------------*/
/* Uncomment the line corresponding to the STMicroelectronics evaluation board
   used to run the example */
#if !defined (USE_STM3210B_EVAL) &&  !defined (USE_STM3210E_EVAL)
 //#define USE_STM3210B_EVAL
 #define USE_STM3210E_EVAL
#endif

#ifdef USE_STM3210B_EVAL
 #define GPIO_CS                  GPIOA
 #define RCC_APB2Periph_GPIO_CS   RCC_APB2Periph_GPIOA
 #define GPIO_Pin_CS              GPIO_Pin_4 
#else /* USE_STM3210E_EVAL */
 #define GPIO_CS                  GPIOB
 #define RCC_APB2Periph_GPIO_CS   RCC_APB2Periph_GPIOB
 #define GPIO_Pin_CS              GPIO_Pin_2 
#endif

/* Exported macro ------------------------------------------------------------*/
/* Select SPI FLASH: Chip Select pin low  */
#define SPI_FLASH_CS_LOW()       __asm volatile( "NOP" );__asm volatile( "NOP" );__asm volatile( "NOP" );__asm volatile( "NOP" );GPIO_ResetBits(GPIO_CS, GPIO_Pin_CS);__asm volatile( "NOP" );__asm volatile( "NOP" );__asm volatile( "NOP" );__asm volatile( "NOP" )
/* Deselect SPI FLASH: Chip Select pin high */
#define SPI_FLASH_CS_HIGH()      __asm volatile( "NOP" );__asm volatile( "NOP" );__asm volatile( "NOP" );__asm volatile( "NOP" );GPIO_SetBits(GPIO_CS, GPIO_Pin_CS);__asm volatile( "NOP" );__asm volatile( "NOP" );__asm volatile( "NOP" );__asm volatile( "NOP" )

/* Exported functions ------------------------------------------------------- */
/*----- High layer function -----*/
void SPI_FLASH_Init(void);
void SPI_FLASH_SectorErase(uint32_t SectorAddr);
void SPI_FLASH_BulkErase(void);
void SPI_FLASH_PageWrite(uint8_t* pBuffer, uint32_t WriteAddr, uint16_t NumByteToWrite);
void SPI_FLASH_BufferWrite(uint8_t* pBuffer, uint32_t WriteAddr, uint16_t NumByteToWrite);
void SPI_FLASH_BufferRead(uint8_t* pBuffer, uint32_t ReadAddr, uint16_t NumByteToRead);
uint32_t SPI_FLASH_ReadID(void);
void SPI_FLASH_StartReadSequence(uint32_t ReadAddr);

/*----- Low layer function -----*/
uint8_t SPI_FLASH_ReadByte(void);
uint8_t SPI_FLASH_SendByte(uint8_t byte);
uint16_t SPI_FLASH_SendHalfWord(uint16_t HalfWord);
void SPI_FLASH_WriteEnable(void);
void SPI_FLASH_WaitForWriteEnd(void);

#endif /* __SPI_FLASH_H */

/******************* (C) COPYRIGHT 2009 STMicroelectronics *****END OF FILE****/
