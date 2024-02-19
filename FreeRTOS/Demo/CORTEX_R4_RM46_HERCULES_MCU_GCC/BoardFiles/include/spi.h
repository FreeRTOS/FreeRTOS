/** @file spi.h
 *   @brief SPI Driver Definition File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 */

/*
 * Copyright (C) 2009-2018 Texas Instruments Incorporated - www.ti.com
 *
 *
 *  Redistribution and use in source and binary forms, with or without
 *  modification, are permitted provided that the following conditions
 *  are met:
 *
 *    Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 *    Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the
 *    distribution.
 *
 *    Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 *  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 *  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 *  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 *  A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 *  OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 *  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 *  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 *  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 *  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 *  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 *  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 */

#ifndef __SPI_H__
#define __SPI_H__

#include "reg_spi.h"

#ifdef __cplusplus
extern "C" {
#endif

/** @enum chipSelect
 *   @brief Transfer Group Chip Select
 */
enum spiChipSelect
{
    SPI_CS_NONE = 0xFFU,
    SPI_CS_0 = 0xFEU,
    SPI_CS_1 = 0xFDU,
    SPI_CS_2 = 0xFBU,
    SPI_CS_3 = 0xF7U,
    SPI_CS_4 = 0xEFU,
    SPI_CS_5 = 0xDFU,
    SPI_CS_6 = 0xBFU,
    SPI_CS_7 = 0x7FU
};

/** @enum spiPinSelect
 *   @brief spi Pin Select
 */
enum spiPinSelect
{
    SPI_PIN_CS0 = 0U,
    SPI_PIN_CS1 = 1U,
    SPI_PIN_CS2 = 2U,
    SPI_PIN_CS3 = 3U,
    SPI_PIN_CS4 = 4U,
    SPI_PIN_CS5 = 5U,
    SPI_PIN_CS6 = 6U,
    SPI_PIN_CS7 = 7U,
    SPI_PIN_ENA = 8U,
    SPI_PIN_CLK = 9U,
    SPI_PIN_SIMO = 10U,
    SPI_PIN_SOMI = 11U,
    SPI_PIN_SIMO_1 = 17U,
    SPI_PIN_SIMO_2 = 18U,
    SPI_PIN_SIMO_3 = 19U,
    SPI_PIN_SIMO_4 = 20U,
    SPI_PIN_SIMO_5 = 21U,
    SPI_PIN_SIMO_6 = 22U,
    SPI_PIN_SIMO_7 = 23U,
    SPI_PIN_SOMI_1 = 25U,
    SPI_PIN_SOMI_2 = 26U,
    SPI_PIN_SOMI_3 = 27U,
    SPI_PIN_SOMI_4 = 28U,
    SPI_PIN_SOMI_5 = 29U,
    SPI_PIN_SOMI_6 = 30U,
    SPI_PIN_SOMI_7 = 31U
};

/** @enum dataformat
 *   @brief SPI dataformat register select
 */
typedef enum dataformat
{
    SPI_FMT_0 = 0U,
    SPI_FMT_1 = 1U,
    SPI_FMT_2 = 2U,
    SPI_FMT_3 = 3U
} SPIDATAFMT_t;

/** @struct spiDAT1RegConfig
 *   @brief SPI data register configuration
 */
typedef struct spiDAT1RegConfig
{
    boolean CS_HOLD;
    boolean WDEL;
    SPIDATAFMT_t DFSEL;
    uint8 CSNR;
} spiDAT1_t;

/** @enum SpiTxRxDataStatus
 *   @brief SPI Data Status
 */
typedef enum SpiTxRxDataStatus
{
    SPI_READY = 0U,
    SPI_PENDING = 1U,
    SPI_COMPLETED = 2U
} SpiDataStatus_t;

/* USER CODE BEGIN (0) */
/* USER CODE END */

typedef struct spi_config_reg
{
    uint32 CONFIG_GCR1;
    uint32 CONFIG_INT0;
    uint32 CONFIG_LVL;
    uint32 CONFIG_PC0;
    uint32 CONFIG_PC1;
    uint32 CONFIG_PC6;
    uint32 CONFIG_PC7;
    uint32 CONFIG_PC8;
    uint32 CONFIG_DELAY;
    uint32 CONFIG_FMT0;
    uint32 CONFIG_FMT1;
    uint32 CONFIG_FMT2;
    uint32 CONFIG_FMT3;
} spi_config_reg_t;

#define SPI2_GCR1_CONFIGVALUE ( 0x01000000U | ( uint32 ) ( ( uint32 ) 1U << 1U ) | 1U )

#define SPI2_INT0_CONFIGVALUE                                                   \
    ( ( uint32 ) ( ( uint32 ) 0U << 24U ) | ( uint32 ) ( ( uint32 ) 0U << 8U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( uint32 ) 0U << 4U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 3U ) | ( uint32 ) ( ( uint32 ) 0U << 2U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 1U ) | ( uint32 ) ( ( uint32 ) 0U << 0U ) )
#define SPI2_LVL_CONFIGVALUE                                                    \
    ( ( uint32 ) ( ( uint32 ) 0U << 9U ) | ( uint32 ) ( ( uint32 ) 0U << 8U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( uint32 ) 0U << 4U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 3U ) | ( uint32 ) ( ( uint32 ) 0U << 2U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 1U ) | ( uint32 ) ( ( uint32 ) 0U << 0U ) )

#define SPI2_PC0_CONFIGVALUE                                                      \
    ( ( uint32 ) ( ( uint32 ) 1U << 0U ) | ( uint32 ) ( ( uint32 ) 1U << 1U )     \
      | ( uint32 ) ( ( uint32 ) 1U << 8U ) | ( uint32 ) ( ( uint32 ) 1U << 9U )   \
      | ( uint32 ) ( ( uint32 ) 1U << 10U ) | ( uint32 ) ( ( uint32 ) 1U << 16U ) \
      | ( uint32 ) ( ( uint32 ) 1U << 11U ) | ( uint32 ) ( ( uint32 ) 1U << 24U ) )
#define SPI2_PC1_CONFIGVALUE                                                      \
    ( ( uint32 ) ( ( uint32 ) 1U << 0U ) | ( uint32 ) ( ( uint32 ) 1U << 1U )     \
      | ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) ( ( uint32 ) 1U << 9U )   \
      | ( uint32 ) ( ( uint32 ) 1U << 10U ) | ( uint32 ) ( ( uint32 ) 1U << 16U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 11U ) | ( uint32 ) ( ( uint32 ) 0U << 24U ) )
#define SPI2_PC6_CONFIGVALUE                                                      \
    ( ( uint32 ) ( ( uint32 ) 0U << 0U ) | ( uint32 ) ( ( uint32 ) 0U << 1U )     \
      | ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) ( ( uint32 ) 0U << 9U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 10U ) | ( uint32 ) ( ( uint32 ) 0U << 16U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 11U ) | ( uint32 ) ( ( uint32 ) 0U << 24U ) )
#define SPI2_PC7_CONFIGVALUE                                                      \
    ( ( uint32 ) ( ( uint32 ) 0U << 0U ) | ( uint32 ) ( ( uint32 ) 0U << 1U )     \
      | ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) ( ( uint32 ) 0U << 9U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 10U ) | ( uint32 ) ( ( uint32 ) 0U << 16U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 11U ) | ( uint32 ) ( ( uint32 ) 0U << 24U ) )
#define SPI2_PC8_CONFIGVALUE                                                      \
    ( ( uint32 ) ( ( uint32 ) 1U << 0U ) | ( uint32 ) ( ( uint32 ) 1U << 1U )     \
      | ( uint32 ) ( ( uint32 ) 1U << 8U ) | ( uint32 ) ( ( uint32 ) 1U << 9U )   \
      | ( uint32 ) ( ( uint32 ) 1U << 10U ) | ( uint32 ) ( ( uint32 ) 1U << 16U ) \
      | ( uint32 ) ( ( uint32 ) 1U << 11U ) | ( uint32 ) ( ( uint32 ) 1U << 24U ) )

#define SPI2_DELAY_CONFIGVALUE                                                  \
    ( ( uint32 ) ( ( uint32 ) 0U << 24U ) | ( uint32 ) ( ( uint32 ) 0U << 16U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) ( ( uint32 ) 0U << 0U ) )

#define SPI2_FMT0_CONFIGVALUE                                                      \
    ( ( uint32 ) ( ( uint32 ) 0U << 24U ) | ( uint32 ) ( ( uint32 ) 0U << 23U )    \
      | ( uint32 ) ( ( uint32 ) 0U << 22U ) | ( uint32 ) ( ( uint32 ) 0U << 21U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 20U ) | ( uint32 ) ( ( uint32 ) 0U << 17U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 16U ) | ( uint32 ) ( ( uint32 ) 109U << 8U ) \
      | ( uint32 ) ( ( uint32 ) 16U << 0U ) )
#define SPI2_FMT1_CONFIGVALUE                                                      \
    ( ( uint32 ) ( ( uint32 ) 0U << 24U ) | ( uint32 ) ( ( uint32 ) 0U << 23U )    \
      | ( uint32 ) ( ( uint32 ) 0U << 22U ) | ( uint32 ) ( ( uint32 ) 0U << 21U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 20U ) | ( uint32 ) ( ( uint32 ) 0U << 17U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 16U ) | ( uint32 ) ( ( uint32 ) 109U << 8U ) \
      | ( uint32 ) ( ( uint32 ) 16U << 0U ) )
#define SPI2_FMT2_CONFIGVALUE                                                      \
    ( ( uint32 ) ( ( uint32 ) 0U << 24U ) | ( uint32 ) ( ( uint32 ) 0U << 23U )    \
      | ( uint32 ) ( ( uint32 ) 0U << 22U ) | ( uint32 ) ( ( uint32 ) 0U << 21U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 20U ) | ( uint32 ) ( ( uint32 ) 0U << 17U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 16U ) | ( uint32 ) ( ( uint32 ) 109U << 8U ) \
      | ( uint32 ) ( ( uint32 ) 16U << 0U ) )
#define SPI2_FMT3_CONFIGVALUE                                                      \
    ( ( uint32 ) ( ( uint32 ) 0U << 24U ) | ( uint32 ) ( ( uint32 ) 0U << 23U )    \
      | ( uint32 ) ( ( uint32 ) 0U << 22U ) | ( uint32 ) ( ( uint32 ) 0U << 21U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 20U ) | ( uint32 ) ( ( uint32 ) 0U << 17U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 16U ) | ( uint32 ) ( ( uint32 ) 109U << 8U ) \
      | ( uint32 ) ( ( uint32 ) 16U << 0U ) )

#define SPI4_GCR1_CONFIGVALUE ( 0x01000000U | ( uint32 ) ( ( uint32 ) 1U << 1U ) | 1U )

#define SPI4_INT0_CONFIGVALUE                                                   \
    ( ( uint32 ) ( ( uint32 ) 0U << 24U ) | ( uint32 ) ( ( uint32 ) 0U << 8U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( uint32 ) 0U << 4U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 3U ) | ( uint32 ) ( ( uint32 ) 0U << 2U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 1U ) | ( uint32 ) ( ( uint32 ) 0U << 0U ) )
#define SPI4_LVL_CONFIGVALUE                                                    \
    ( ( uint32 ) ( ( uint32 ) 0U << 9U ) | ( uint32 ) ( ( uint32 ) 0U << 8U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( uint32 ) 0U << 4U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 3U ) | ( uint32 ) ( ( uint32 ) 0U << 2U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 1U ) | ( uint32 ) ( ( uint32 ) 0U << 0U ) )

#define SPI4_PC0_CONFIGVALUE                                                      \
    ( ( uint32 ) ( ( uint32 ) 1U << 0U ) | ( uint32 ) ( ( uint32 ) 1U << 8U )     \
      | ( uint32 ) ( ( uint32 ) 1U << 9U ) | ( uint32 ) ( ( uint32 ) 1U << 10U )  \
      | ( uint32 ) ( ( uint32 ) 1U << 16U ) | ( uint32 ) ( ( uint32 ) 1U << 11U ) \
      | ( uint32 ) ( ( uint32 ) 1U << 24U ) )
#define SPI4_PC1_CONFIGVALUE                                                      \
    ( ( uint32 ) ( ( uint32 ) 1U << 0U ) | ( uint32 ) ( ( uint32 ) 0U << 8U )     \
      | ( uint32 ) ( ( uint32 ) 1U << 9U ) | ( uint32 ) ( ( uint32 ) 1U << 10U )  \
      | ( uint32 ) ( ( uint32 ) 1U << 16U ) | ( uint32 ) ( ( uint32 ) 0U << 11U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 24U ) )
#define SPI4_PC6_CONFIGVALUE                                                      \
    ( ( uint32 ) ( ( uint32 ) 0U << 0U ) | ( uint32 ) ( ( uint32 ) 0U << 8U )     \
      | ( uint32 ) ( ( uint32 ) 0U << 9U ) | ( uint32 ) ( ( uint32 ) 0U << 10U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 16U ) | ( uint32 ) ( ( uint32 ) 0U << 11U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 24U ) )
#define SPI4_PC7_CONFIGVALUE                                                      \
    ( ( uint32 ) ( ( uint32 ) 0U << 0U ) | ( uint32 ) ( ( uint32 ) 0U << 8U )     \
      | ( uint32 ) ( ( uint32 ) 0U << 9U ) | ( uint32 ) ( ( uint32 ) 0U << 10U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 16U ) | ( uint32 ) ( ( uint32 ) 0U << 11U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 24U ) )
#define SPI4_PC8_CONFIGVALUE                                                      \
    ( ( uint32 ) ( ( uint32 ) 1U << 0U ) | ( uint32 ) ( ( uint32 ) 1U << 8U )     \
      | ( uint32 ) ( ( uint32 ) 1U << 9U ) | ( uint32 ) ( ( uint32 ) 1U << 10U )  \
      | ( uint32 ) ( ( uint32 ) 1U << 16U ) | ( uint32 ) ( ( uint32 ) 1U << 11U ) \
      | ( uint32 ) ( ( uint32 ) 1U << 24U ) )

#define SPI4_DELAY_CONFIGVALUE                                                  \
    ( ( uint32 ) ( ( uint32 ) 0U << 24U ) | ( uint32 ) ( ( uint32 ) 0U << 16U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) ( ( uint32 ) 0U << 0U ) )

#define SPI4_FMT0_CONFIGVALUE                                                      \
    ( ( uint32 ) ( ( uint32 ) 0U << 24U ) | ( uint32 ) ( ( uint32 ) 0U << 23U )    \
      | ( uint32 ) ( ( uint32 ) 0U << 22U ) | ( uint32 ) ( ( uint32 ) 0U << 21U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 20U ) | ( uint32 ) ( ( uint32 ) 0U << 17U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 16U ) | ( uint32 ) ( ( uint32 ) 109U << 8U ) \
      | ( uint32 ) ( ( uint32 ) 16U << 0U ) )
#define SPI4_FMT1_CONFIGVALUE                                                      \
    ( ( uint32 ) ( ( uint32 ) 0U << 24U ) | ( uint32 ) ( ( uint32 ) 0U << 23U )    \
      | ( uint32 ) ( ( uint32 ) 0U << 22U ) | ( uint32 ) ( ( uint32 ) 0U << 21U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 20U ) | ( uint32 ) ( ( uint32 ) 0U << 17U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 16U ) | ( uint32 ) ( ( uint32 ) 109U << 8U ) \
      | ( uint32 ) ( ( uint32 ) 16U << 0U ) )
#define SPI4_FMT2_CONFIGVALUE                                                      \
    ( ( uint32 ) ( ( uint32 ) 0U << 24U ) | ( uint32 ) ( ( uint32 ) 0U << 23U )    \
      | ( uint32 ) ( ( uint32 ) 0U << 22U ) | ( uint32 ) ( ( uint32 ) 0U << 21U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 20U ) | ( uint32 ) ( ( uint32 ) 0U << 17U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 16U ) | ( uint32 ) ( ( uint32 ) 109U << 8U ) \
      | ( uint32 ) ( ( uint32 ) 16U << 0U ) )
#define SPI4_FMT3_CONFIGVALUE                                                      \
    ( ( uint32 ) ( ( uint32 ) 0U << 24U ) | ( uint32 ) ( ( uint32 ) 0U << 23U )    \
      | ( uint32 ) ( ( uint32 ) 0U << 22U ) | ( uint32 ) ( ( uint32 ) 0U << 21U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 20U ) | ( uint32 ) ( ( uint32 ) 0U << 17U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 16U ) | ( uint32 ) ( ( uint32 ) 109U << 8U ) \
      | ( uint32 ) ( ( uint32 ) 16U << 0U ) )

/**
 *  @defgroup SPI SPI
 *  @brief Serial Peripheral Interface Module.
 *
 *  SPI is a high-speed synchronous serial input/output port that allows a serial bit
 * stream of programmed length (2 to 16 bits) to be shifted in and out of the device at a
 * programmed bit-transfer rate.
 *
 *    Related Files
 *   - reg_spi.h
 *   - spi.h
 *   - spi.c
 *  @addtogroup SPI
 *  @{
 */

/* SPI Interface Functions */
void spiInit( void );
void spiSetFunctional( spiBASE_t * spi, uint32 port );
void spiEnableNotification( spiBASE_t * spi, uint32 flags );
void spiDisableNotification( spiBASE_t * spi, uint32 flags );
uint32 spiTransmitData( spiBASE_t * spi,
                        spiDAT1_t * dataconfig_t,
                        uint32 blocksize,
                        uint16 * srcbuff );
void spiSendData( spiBASE_t * spi,
                  spiDAT1_t * dataconfig_t,
                  uint32 blocksize,
                  uint16 * srcbuff );
uint32 spiReceiveData( spiBASE_t * spi,
                       spiDAT1_t * dataconfig_t,
                       uint32 blocksize,
                       uint16 * destbuff );
void spiGetData( spiBASE_t * spi,
                 spiDAT1_t * dataconfig_t,
                 uint32 blocksize,
                 uint16 * destbuff );
uint32 spiTransmitAndReceiveData( spiBASE_t * spi,
                                  spiDAT1_t * dataconfig_t,
                                  uint32 blocksize,
                                  uint16 * srcbuff,
                                  uint16 * destbuff );
void spiSendAndGetData( spiBASE_t * spi,
                        spiDAT1_t * dataconfig_t,
                        uint32 blocksize,
                        uint16 * srcbuff,
                        uint16 * destbuff );
void spiEnableLoopback( spiBASE_t * spi, loopBackType_t Loopbacktype );
void spiDisableLoopback( spiBASE_t * spi );
SpiDataStatus_t SpiTxStatus( spiBASE_t * spi );
SpiDataStatus_t SpiRxStatus( spiBASE_t * spi );
void spi2GetConfigValue( spi_config_reg_t * config_reg, config_value_type_t type );
void spi4GetConfigValue( spi_config_reg_t * config_reg, config_value_type_t type );

/** @fn void spiNotification(spiBASE_t *spi, uint32 flags)
 *   @brief Interrupt callback
 *   @param[in] spi   - Spi module base address
 *   @param[in] flags - Copy of error interrupt flags
 *
 * This is a callback that is provided by the application and is called upon
 * an interrupt.  The parameter passed to the callback is a copy of the
 * interrupt flag register.
 */
void spiNotification( spiBASE_t * spi, uint32 flags );

/** @fn void spiEndNotification(spiBASE_t *spi)
 *   @brief Interrupt callback for End of TX or RX data length.
 *   @param[in] spi   - Spi module base address
 *
 * This is a callback that is provided by the application and is called upon
 * an interrupt at the End of TX or RX data length.
 */
void spiEndNotification( spiBASE_t * spi );

/**@}*/
/* USER CODE BEGIN (1) */
/* USER CODE END */

#ifdef __cplusplus
}
#endif /*extern "C" */

#endif /* ifndef __SPI_H__ */
