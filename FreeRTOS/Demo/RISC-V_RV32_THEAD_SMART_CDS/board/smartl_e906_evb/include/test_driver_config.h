/*
 * Copyright (C) 2017-2019 Alibaba Group Holding Limited. All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/******************************************************************************
 * @file     test_driver_config.h
 * @brief    head file for driver config
 * @version  V1.0
 * @date     02. June 2017
 ******************************************************************************/
#ifndef _TEST_DRIVER_CONFIG_H_
#define _TEST_DRIVER_CONFIG_H_

#include "pin.h"
#include "pin_name.h"

#ifdef __cplusplus
extern "C" {
#endif

#define TEST_TIMER  1
#define TEST_USART  1
//#define TEST_SPU_USART  1
//#define TEST_USI_USART  1
#define TEST_GPIO   1
//#define TEST_EFLASH 1
//#define TEST_SPIFLASH 1
//#define TEST_IIC        1
//#define TEST_SPU_IIC    1
//#define TEST_USI_IIC    1
//#define TEST_SPI        1
//#define TEST_SPU_SPI    1
//#define TEST_USI_SPI    1
//#define TEST_CRC    1
//#define TEST_AES    1
//#define TEST_TRNG   1
//#define TEST_RSA    1
//#define TEST_SHA    1
//#define TEST_PWM    1
//#define TEST_DMAC   1
//#define TEST_ETH    1
//#define TEST_RTC    1
//#define TEST_WDT    1
//#define TEST_I2S    1

/* AES case config */
#define AES_CBC_128_EN      0x1
#define AES_CBC_192_EN      0x1
#define AES_CBC_256_EN      0x1
#define AES_ECB_128_EN      0x1
#define AES_ECB_192_EN      0x1
#define AES_ECB_256_EN      0x1
#define AES_BIG_ENDIAN      0x1
#define AES_LITTLE_ENDIAN   0x1
#define AES_CRYPTO_EN       0x1
#define AES_SET_KEY_EN      0x1
#define AES_CONFIG_EN       0x1

/* CRC case config */
#define CRC_CALCULATE_EN    0x1
#define CRC_CONFIG_EN       0x1
#define CRC_FUNC_EN         0x1
#define CRC_MODBUS_16       0x1
#define CRC_IBM_16          0x1
#define CRC_MAXIM_16        0x1
#define CRC_USB_16          0x1
#define CRC_CCITT_16        0x1
#define CRC_X25_16          0x1
#define CRC_XMODEM_16       0x0
#define CRC_DNP_16          0x0
#define CRC_CCITT_FALSE_16  0x0
#define CRC_MAXIM_8         0x1
#define CRC_ROHC_8          0x1
#define CRC_NONE_8          0x0
#define CRC_ITU_8           0x0
#define CRC_NONE_32         0x0
#define CRC_PMEQ_32         0x0

/* EFLASH case config */
#define EFLASH_GET_INFO_EN  0x1
#define EFLASH_ERASE_EN     0x1
#define EFLASH_PROGRAM_EN   0x1
#define EFLASH_PROGRAM_INTERFACE_EN         0x1
#define EFLASH_READ_INTERFACE_EN            0x1
#define EFLASH_ERASE_SECTOR_INTERFACE_EN    0x1

/* SPIFLASH case config */
#define SPIFLASH_GET_INFO_EN  0x1
#define SPIFLASH_ERASE_EN     0x1
#define SPIFLASH_PROGRAM_EN   0x1
#define SPIFLASH_PROGRAM_INTERFACE_EN         0x1
#define SPIFLASH_READ_INTERFACE_EN            0x1
#define SPIFLASH_ERASE_SECTOR_INTERFACE_EN    0x1


/* GPIO case config */
#define GPIO_GET_VALUE_EN       0x1
#define GPIO_SET_VALUE_EN       0x1
#define GPIO_RISNG_EDGE_EN      0x1
#define GPIO_FALLING_EDGE_EN    0x1
#define GPIO_HIGH_LEVEL_EN      0x1
#define GPIO_LOW_LEVEL_EN       0x1
#define GPIO_PORT_CONFIG_EN     0x1
#define GPIO_PIN_IRQ_SET_EN     0x1
#define GPIO_TEST_INTERFACE_EN  0x1

#define test_gpio_port  CTS_GPIO_TEST_PORT
#define test_gpio_pin   TEST_GPIO_PIN

/* RSA case config */
#define RSA_SIGN_VERIFY_EN          0x1
#define RSA_ENCRYPT_DECRYPT_EN      0x1
#define RSA_DECRYPT_INTERFACE_EN    0x1
#define RSA_ENCRYPT_INTERFACE_EN    0x1
#define RSA_SIGN_INTERFACE_EN       0x1
#define RSA_VERIFY_INTERFACE_EN     0x1
#define RSA_CONFIG_INTERFACE_EN     0x1

/* TRNG case config */
#define TRNG_GET_NUM_EN             0x1
#define TRNG_GET_DATA_INTERFACE_EN  0x1

/* SHA case config */
#define SHA1_8BIT_EN            0x1
#define SHA1_512BIT_EN          0x1
#define SHA1_576BIT_EN          0x1
#define SHA1_1024BIT_EN         0x1
#define SHA1_1088BIT_EN         0x1
#define SHA224_1024BIT_EN       0x1
#define SHA256_1024BIT_EN       0x1
#define SHA384_1024BIT_EN       0x1
#define SHA512_1024BIT_EN       0x1
#define SHA_HASH_BIG_ENDIAN     0x1
#define SHA_HASH_LITTLE_ENDIAN  0x0
#define SHA_UPDATE_INTERFACE_EN 0x1
#define SHA_CONFIG_INTERFACE_EN 0x1
#define SHA_FINISH_INTERFACE_EN 0x1
#define SHA_START_INTERFACE_EN  0x1

/* DMAC case config*/
#define DMA_MEM2MEM_EN                0x1
#define DMAC_CONFIG_INTERFACE_EN      0x1
#define DMAC_START_INTERFACE_EN       0x1
#define DMAC_STOP_INTERFACE_EN        0x1
#define DMAC_ALLOC_INTERFACE_EN       0x1
#define DMAC_RELEASE_INTERFACE_EN     0x1
#define DMAC_GET_STATUS_INTERFACE_EN  0x1

/* RTC case config */
#define RTC_TEST_TIMEOUT_EN     0x01
#define RTC_TEST_LEAP_YEAR_EN   0x01
#define RTC_TEST_INTERFACE_EN   0x01

/* PWM case config */
#define PWM_TEST_INTERFACE_EN   0x1
#define PWM_TEST_FUN_EN         0x1

/* TIMER case config */
#define TIMER_TEST_FREE_RUNNING 0x1
#define TIMER_TEST_USER_DEFINED 0x1
#define TIMER_TEST_INTERFACE_EN 0x1

/* USART case config */
#define USART_TEST_FUN_EN       0x1
#define USART_TEST_INTERFACE_EN 0x1

/* WDT case config */
#define WDT_FUN_FEEDOG_EN       0x1
#define WDT_FUN_SYSRESET_EN     0x1
#define WDT_TEST_INTERFACE_EN   0x1

/* IIC case config */
#define IIC_TEST_AT24C64_WRITE_READ_EN         0x1
#define IIC_TEST_ABORT_TRANSFER_INTERFACE_EN   0x1
#define IIC_TEST_CONFIG_INTERFACE_EN           0x1

/* SPI case config */
#define SPI_TEST_W25Q64FV_RDID_EN           0x1
#define SPI_TEST_W25Q64FV_SECTOR_ERASE_EN   0x1
#define SPI_TEST_W25Q64FV_PROGRAM_EN        0x1
#define SPI_TEST_W25Q64FV_READ_EN           0x1
#define SPI_TEST_CONFIG_INTERFACE_EN         0x1

#define NET_TEST_FUN_EN         0x1
#define NET_TEST_INTERFACE_EN   0x1

/* I2S case config */
#define I2S_TEST_INTERFACE_EN 0x1

#ifdef __cplusplus
}
#endif

#endif
