/****************************************************************************//**
 * @file     i2s.h
 * @version  V3.00
 * @brief    M2351 series I2S driver header file
 *
 * @copyright (C) 2016 Nuvoton Technology Corp. All rights reserved.
*****************************************************************************/
#ifndef __I2S_H__
#define __I2S_H__

#ifdef __cplusplus
extern "C"
{
#endif


/** @addtogroup Standard_Driver Standard Driver
  @{
*/

/** @addtogroup I2S_Driver I2S Driver
  @{
*/

/** @addtogroup I2S_EXPORTED_CONSTANTS I2S Exported Constants
  @{
*/
#define I2S_DATABIT_8           (0UL << I2S_CTL0_DATWIDTH_Pos)       /*!< I2S data width is 8-bit  \hideinitializer */
#define I2S_DATABIT_16          (1UL << I2S_CTL0_DATWIDTH_Pos)       /*!< I2S data width is 16-bit  \hideinitializer */
#define I2S_DATABIT_24          (2UL << I2S_CTL0_DATWIDTH_Pos)       /*!< I2S data width is 24-bit  \hideinitializer */
#define I2S_DATABIT_32          (3UL << I2S_CTL0_DATWIDTH_Pos)       /*!< I2S data width is 32-bit  \hideinitializer */

/* Audio Format */
#define I2S_ENABLE_MONO         I2S_CTL0_MONO_Msk                    /*!< Mono channel  \hideinitializer */
#define I2S_DISABLE_MONO        (0UL)                                /*!< Stereo channel  \hideinitializer */
#define I2S_MONO                I2S_ENABLE_MONO
#define I2S_STEREO              I2S_DISABLE_MONO


/* I2S Data Format */
#define I2S_FORMAT_I2S          (0UL << I2S_CTL0_FORMAT_Pos)         /*!< I2S data format  \hideinitializer */
#define I2S_FORMAT_I2S_MSB      (1UL << I2S_CTL0_FORMAT_Pos)         /*!< I2S MSB data format  \hideinitializer */
#define I2S_FORMAT_I2S_LSB      (2UL << I2S_CTL0_FORMAT_Pos)         /*!< I2S LSB data format  \hideinitializer */
#define I2S_FORMAT_PCM          (4UL << I2S_CTL0_FORMAT_Pos)         /*!< PCM data format  \hideinitializer */
#define I2S_FORMAT_PCM_MSB      (5UL << I2S_CTL0_FORMAT_Pos)         /*!< PCM MSB data format  \hideinitializer */
#define I2S_FORMAT_PCM_LSB      (6UL << I2S_CTL0_FORMAT_Pos)         /*!< PCM LSB data format  \hideinitializer */

/* I2S Data Format */
#define I2S_ORDER_AT_MSB        0UL                                  /*!< Channel data is at MSB  \hideinitializer */
#define I2S_ORDER_AT_LSB        I2S_CTL0_ORDER_Msk                   /*!< Channel data is at LSB  \hideinitializer */

/* I2S TDM Channel Number */
#define I2S_TDM_2CH             0UL                                  /*!< Use TDM 2 channel  \hideinitializer */
#define I2S_TDM_4CH             1UL                                  /*!< Use TDM 4 channel  \hideinitializer */
#define I2S_TDM_6CH             2UL                                  /*!< Use TDM 6 channel  \hideinitializer */
#define I2S_TDM_8CH             3UL                                  /*!< Use TDM 8 channel  \hideinitializer */

/* I2S TDM Channel Width */
#define I2S_TDM_WIDTH_8BIT      0UL                                  /*!< TDM channel witch is 8-bit  \hideinitializer */
#define I2S_TDM_WIDTH_16BIT     1UL                                  /*!< TDM channel witch is 16-bit  \hideinitializer */
#define I2S_TDM_WIDTH_24BIT     2UL                                  /*!< TDM channel witch is 24-bit  \hideinitializer */
#define I2S_TDM_WIDTH_32BIT     3UL                                  /*!< TDM channel witch is 32-bit  \hideinitializer */

/* I2S TDM Sync Width */
#define I2S_TDM_SYNC_ONE_BCLK       0UL                              /*!< TDM sync widht is one BLCK period  \hideinitializer */
#define I2S_TDM_SYNC_ONE_CHANNEL    1UL                              /*!< TDM sync widht is one channel period  \hideinitializer */

/* I2S Operation mode */
#define I2S_MODE_SLAVE          I2S_CTL0_SLAVE_Msk                   /*!< As slave mode  \hideinitializer */
#define I2S_MODE_MASTER         0UL                                  /*!< As master mode  \hideinitializer */

/* I2S FIFO Threshold */
#define I2S_FIFO_TX_LEVEL_WORD_0    0UL                              /*!< TX threshold is 0 word  \hideinitializer */
#define I2S_FIFO_TX_LEVEL_WORD_1    (1UL << I2S_CTL1_TXTH_Pos)       /*!< TX threshold is 1 word  \hideinitializer */
#define I2S_FIFO_TX_LEVEL_WORD_2    (2UL << I2S_CTL1_TXTH_Pos)       /*!< TX threshold is 2 words  \hideinitializer */
#define I2S_FIFO_TX_LEVEL_WORD_3    (3UL << I2S_CTL1_TXTH_Pos)       /*!< TX threshold is 3 words  \hideinitializer */
#define I2S_FIFO_TX_LEVEL_WORD_4    (4UL << I2S_CTL1_TXTH_Pos)       /*!< TX threshold is 4 words  \hideinitializer */
#define I2S_FIFO_TX_LEVEL_WORD_5    (5UL << I2S_CTL1_TXTH_Pos)       /*!< TX threshold is 5 words  \hideinitializer */
#define I2S_FIFO_TX_LEVEL_WORD_6    (6UL << I2S_CTL1_TXTH_Pos)       /*!< TX threshold is 6 words  \hideinitializer */
#define I2S_FIFO_TX_LEVEL_WORD_7    (7UL << I2S_CTL1_TXTH_Pos)       /*!< TX threshold is 7 words  \hideinitializer */
#define I2S_FIFO_TX_LEVEL_WORD_8    (8UL << I2S_CTL1_TXTH_Pos)       /*!< TX threshold is 8 words  \hideinitializer */
#define I2S_FIFO_TX_LEVEL_WORD_9    (9UL << I2S_CTL1_TXTH_Pos)       /*!< TX threshold is 9 words  \hideinitializer */
#define I2S_FIFO_TX_LEVEL_WORD_10   (10UL << I2S_CTL1_TXTH_Pos)      /*!< TX threshold is 10 words  \hideinitializer */
#define I2S_FIFO_TX_LEVEL_WORD_11   (11UL << I2S_CTL1_TXTH_Pos)      /*!< TX threshold is 11 words  \hideinitializer */
#define I2S_FIFO_TX_LEVEL_WORD_12   (12UL << I2S_CTL1_TXTH_Pos)      /*!< TX threshold is 12 words  \hideinitializer */
#define I2S_FIFO_TX_LEVEL_WORD_13   (13UL << I2S_CTL1_TXTH_Pos)      /*!< TX threshold is 13 words  \hideinitializer */
#define I2S_FIFO_TX_LEVEL_WORD_14   (14UL << I2S_CTL1_TXTH_Pos)      /*!< TX threshold is 14 words  \hideinitializer */
#define I2S_FIFO_TX_LEVEL_WORD_15   (15UL << I2S_CTL1_TXTH_Pos)      /*!< TX threshold is 15 words  \hideinitializer */

#define I2S_FIFO_RX_LEVEL_WORD_1    0UL                              /*!< RX threshold is 1 word  \hideinitializer */
#define I2S_FIFO_RX_LEVEL_WORD_2    (1UL << I2S_CTL1_RXTH_Pos)       /*!< RX threshold is 2 words  \hideinitializer */
#define I2S_FIFO_RX_LEVEL_WORD_3    (2UL << I2S_CTL1_RXTH_Pos)       /*!< RX threshold is 3 words  \hideinitializer */
#define I2S_FIFO_RX_LEVEL_WORD_4    (3UL << I2S_CTL1_RXTH_Pos)       /*!< RX threshold is 4 words  \hideinitializer */
#define I2S_FIFO_RX_LEVEL_WORD_5    (4UL << I2S_CTL1_RXTH_Pos)       /*!< RX threshold is 5 words  \hideinitializer */
#define I2S_FIFO_RX_LEVEL_WORD_6    (5UL << I2S_CTL1_RXTH_Pos)       /*!< RX threshold is 6 words  \hideinitializer */
#define I2S_FIFO_RX_LEVEL_WORD_7    (6UL << I2S_CTL1_RXTH_Pos)       /*!< RX threshold is 7 words  \hideinitializer */
#define I2S_FIFO_RX_LEVEL_WORD_8    (7UL << I2S_CTL1_RXTH_Pos)       /*!< RX threshold is 8 words  \hideinitializer */
#define I2S_FIFO_RX_LEVEL_WORD_9    (8UL << I2S_CTL1_RXTH_Pos)       /*!< RX threshold is 9 words  \hideinitializer */
#define I2S_FIFO_RX_LEVEL_WORD_10   (9UL << I2S_CTL1_RXTH_Pos)       /*!< RX threshold is 10 words  \hideinitializer */
#define I2S_FIFO_RX_LEVEL_WORD_11   (10UL << I2S_CTL1_RXTH_Pos)      /*!< RX threshold is 11 words  \hideinitializer */
#define I2S_FIFO_RX_LEVEL_WORD_12   (11UL << I2S_CTL1_RXTH_Pos)      /*!< RX threshold is 12 words  \hideinitializer */
#define I2S_FIFO_RX_LEVEL_WORD_13   (12UL << I2S_CTL1_RXTH_Pos)      /*!< RX threshold is 13 words  \hideinitializer */
#define I2S_FIFO_RX_LEVEL_WORD_14   (13UL << I2S_CTL1_RXTH_Pos)      /*!< RX threshold is 14 words  \hideinitializer */
#define I2S_FIFO_RX_LEVEL_WORD_15   (14UL << I2S_CTL1_RXTH_Pos)      /*!< RX threshold is 15 words  \hideinitializer */
#define I2S_FIFO_RX_LEVEL_WORD_16   (15UL << I2S_CTL1_RXTH_Pos)      /*!< RX threshold is 16 words  \hideinitializer */

/* I2S Record Channel */
#define I2S_MONO_RIGHT          0UL                                  /*!< Record mono right channel  \hideinitializer */
#define I2S_MONO_LEFT           I2S_CTL0_RXLCH_Msk                   /*!< Record mono left channel  \hideinitializer */

/* I2S Channel */
#define I2S_RIGHT               0UL                                  /*!< Select right channel  \hideinitializer */
#define I2S_LEFT                1UL                                  /*!< Select left channel  \hideinitializer */

/*@}*/ /* end of group I2S_EXPORTED_CONSTANTS */

/** @addtogroup I2S_EXPORTED_FUNCTIONS I2S Exported Functions
  @{
*/
/*---------------------------------------------------------------------------------------------------------*/
/* inline functions                                                                                        */
/*---------------------------------------------------------------------------------------------------------*/

/* Declare these inline functions here to avoid MISRA C 2004 rule 8.1 error */
__STATIC_INLINE void I2S_ENABLE_TX_ZCD(I2S_T *i2s, uint32_t u32ChMask);
__STATIC_INLINE void I2S_DISABLE_TX_ZCD(I2S_T *i2s, uint32_t u32ChMask);
__STATIC_INLINE void I2S_SET_MONO_RX_CHANNEL(I2S_T *i2s, uint32_t u32Ch);

/**
  * @brief  Enable zero cross detect function.
  * @param[in] i2s is the base address of I2S module.
  * @param[in] u32ChMask is the mask for channel number (valid value is from (1~8).
  * @return none
  * \hideinitializer
  */
__STATIC_INLINE void I2S_ENABLE_TX_ZCD(I2S_T *i2s, uint32_t u32ChMask)
{
    if((u32ChMask > 0UL) && (u32ChMask < 9UL))
    {
        i2s->CTL1 |= (1UL << (u32ChMask - 1UL));
    }
}

/**
  * @brief  Disable zero cross detect function.
  * @param[in] i2s is the base address of I2S module.
  * @param[in] u32ChMask is the mask for channel number (valid value is from (1~8).
  * @return none
  * \hideinitializer
  */
__STATIC_INLINE void I2S_DISABLE_TX_ZCD(I2S_T *i2s, uint32_t u32ChMask)
{
    if((u32ChMask > 0UL) && (u32ChMask < 9UL))
    {
        i2s->CTL1 &= ~(1UL << (u32ChMask - 1UL));
    }
}

/**
  * @brief  Enable I2S Tx DMA function. I2S requests DMA to transfer data to Tx FIFO.
  * @param[in] i2s is the base address of I2S module.
  * @return none
  * \hideinitializer
  */
#define I2S_ENABLE_TXDMA(i2s)  ( (i2s)->CTL0 |= I2S_CTL0_TXPDMAEN_Msk )

/**
  * @brief  Disable I2S Tx DMA function. I2S requests DMA to transfer data to Tx FIFO.
  * @param[in] i2s is the base address of I2S module.
  * @return none
  * \hideinitializer
  */
#define I2S_DISABLE_TXDMA(i2s) ( (i2s)->CTL0 &= ~I2S_CTL0_TXPDMAEN_Msk )

/**
  * @brief  Enable I2S Rx DMA function. I2S requests DMA to transfer data from Rx FIFO.
  * @param[in] i2s is the base address of I2S module.
  * @return none
  * \hideinitializer
  */
#define I2S_ENABLE_RXDMA(i2s) ( (i2s)->CTL0 |= I2S_CTL0_RXPDMAEN_Msk )

/**
  * @brief  Disable I2S Rx DMA function. I2S requests DMA to transfer data from Rx FIFO.
  * @param[in] i2s is the base address of I2S module.
  * @return none
  * \hideinitializer
  */
#define I2S_DISABLE_RXDMA(i2s) ( (i2s)->CTL0 &= ~I2S_CTL0_RXPDMAEN_Msk )

/**
  * @brief  Enable I2S Tx function .
  * @param[in] i2s is the base address of I2S module.
  * @return none
  * \hideinitializer
  */
#define I2S_ENABLE_TX(i2s) ( (i2s)->CTL0 |= I2S_CTL0_TXEN_Msk )

/**
  * @brief  Disable I2S Tx function .
  * @param[in] i2s is the base address of I2S module.
  * @return none
  * \hideinitializer
  */
#define I2S_DISABLE_TX(i2s) ( (i2s)->CTL0 &= ~I2S_CTL0_TXEN_Msk )

/**
  * @brief  Enable I2S Rx function .
  * @param[in] i2s is the base address of I2S module.
  * @return none
  * \hideinitializer
  */
#define I2S_ENABLE_RX(i2s) ( (i2s)->CTL0 |= I2S_CTL0_RXEN_Msk )

/**
  * @brief  Disable I2S Rx function .
  * @param[in] i2s is the base address of I2S module.
  * @return none
  * \hideinitializer
  */
#define I2S_DISABLE_RX(i2s) ( (i2s)->CTL0 &= ~I2S_CTL0_RXEN_Msk )

/**
  * @brief  Enable Tx Mute function .
  * @param[in] i2s is the base address of I2S module.
  * @return none
  * \hideinitializer
  */
#define I2S_ENABLE_TX_MUTE(i2s)  ( (i2s)->CTL0 |= I2S_CTL0_MUTE_Msk )

/**
  * @brief  Disable Tx Mute function .
  * @param[in] i2s is the base address of I2S module.
  * @return none
  * \hideinitializer
  */
#define I2S_DISABLE_TX_MUTE(i2s) ( (i2s)->CTL0 &= ~I2S_CTL0_MUTE_Msk )

/**
  * @brief  Clear Tx FIFO. Internal pointer is reset to FIFO start point.
  * @param[in] i2s is the base address of I2S module.
  * @return none
  * \hideinitializer
  */
#define I2S_CLR_TX_FIFO(i2s) ( (i2s)->CTL0 |= I2S_CTL0_TXFBCLR_Msk )

/**
  * @brief  Clear Rx FIFO. Internal pointer is reset to FIFO start point.
  * @param[in] i2s is the base address of I2S module.
  * @return none
  * \hideinitializer
  */
#define I2S_CLR_RX_FIFO(i2s) ( (i2s)->CTL0 |= I2S_CTL0_RXFBCLR_Msk )

/**
  * @brief  This function sets the recording source channel when mono mode is used.
  * @param[in] i2s is the base address of I2S module.
  * @param[in] u32Ch left or right channel. Valid values are:
  *                - \ref I2S_MONO_LEFT
  *                - \ref I2S_MONO_RIGHT
  * @return none
  * \hideinitializer
  */
__STATIC_INLINE void I2S_SET_MONO_RX_CHANNEL(I2S_T *i2s, uint32_t u32Ch)
{
    u32Ch == I2S_MONO_LEFT ?
    (i2s->CTL0 |= I2S_CTL0_RXLCH_Msk) :
    (i2s->CTL0 &= ~I2S_CTL0_RXLCH_Msk);
}

/**
  * @brief  Write data to I2S Tx FIFO.
  * @param[in] i2s is the base address of I2S module.
  * @param[in] u32Data: The data written to FIFO.
  * @return none
  * \hideinitializer
  */
#define I2S_WRITE_TX_FIFO(i2s, u32Data)  ( (i2s)->TXFIFO = (u32Data) )

/**
  * @brief  Read Rx FIFO.
  * @param[in] i2s is the base address of I2S module.
  * @return Data in Rx FIFO.
  * \hideinitializer
  */
#define I2S_READ_RX_FIFO(i2s) ( (i2s)->RXFIFO )

/**
  * @brief  This function gets the interrupt flag according to the mask parameter.
  * @param[in] i2s is the base address of I2S module.
  * @param[in] u32Mask is the mask for the all interrupt flags.
  * @return The masked bit value of interrupt flag.
  * \hideinitializer
  */
#define I2S_GET_INT_FLAG(i2s, u32Mask) ( (i2s)->STATUS0 & (u32Mask) )

/**
  * @brief  This function clears the interrupt flag according to the mask parameter.
  * @param[in] i2s is the base address of I2S module.
  * @param[in] u32Mask is the mask for the all interrupt flags.
  * @return none
  * \hideinitializer
  */
#define I2S_CLR_INT_FLAG(i2s, u32Mask) ( (i2s)->STATUS0 |= (u32Mask) )

/**
  * @brief  This function gets the zero crossing interrupt flag according to the mask parameter.
  * @param[in] i2s is the base address of I2S module.
  * @param[in] u32Mask is the mask for the all interrupt flags.
  * @return The masked bit value of interrupt flag.
  * \hideinitializer
  */
#define I2S_GET_ZC_INT_FLAG(i2s, u32Mask) ( (i2s)->STATUS1 & (u32Mask) )

/**
  * @brief  This function clears the zero crossing interrupt flag according to the mask parameter.
  * @param[in] i2s is the base address of I2S module.
  * @param[in] u32Mask is the mask for the all interrupt flags.
  * @return none
  * \hideinitializer
  */
#define I2S_CLR_ZC_INT_FLAG(i2s, u32Mask) ( (i2s)->STATUS1 |= (u32Mask) )

/**
  * @brief  Get transmit FIFO level
  * @param[in] i2s is the base address of I2S module.
  * @return FIFO level
  * \hideinitializer
  */
#define I2S_GET_TX_FIFO_LEVEL(i2s) ( (((i2s)->STATUS1 & I2S_STATUS1_TXCNT_Msk) >> I2S_STATUS1_TXCNT_Pos) & 0xF )

/**
  * @brief  Get receive FIFO level
  * @param[in] i2s is the base address of I2S module.
  * @return FIFO level
  * \hideinitializer
  */
#define I2S_GET_RX_FIFO_LEVEL(i2s) ( (((i2s)->STATUS1 & I2S_STATUS1_RXCNT_Msk) >> I2S_STATUS1_RXCNT_Pos) & 0xF )

uint32_t I2S_Open(I2S_T *i2s, uint32_t u32MasterSlave, uint32_t u32SampleRate, uint32_t u32WordWidth, uint32_t u32MonoData, uint32_t u32DataFormat);
void I2S_Close(I2S_T *i2s);
void I2S_EnableInt(I2S_T *i2s, uint32_t u32Mask);
void I2S_DisableInt(I2S_T *i2s, uint32_t u32Mask);
uint32_t I2S_EnableMCLK(I2S_T *i2s, uint32_t u32BusClock);
void I2S_DisableMCLK(I2S_T *i2s);
void I2S_SetFIFO(I2S_T *i2s, uint32_t u32TxThreshold, uint32_t u32RxThreshold);
void I2S_ConfigureTDM(I2S_T *i2s, uint32_t u32ChannelWidth, uint32_t u32ChannelNum, uint32_t u32SyncWidth);

/*@}*/ /* end of group I2S_EXPORTED_FUNCTIONS */


/*@}*/ /* end of group I2S_Driver */

/*@}*/ /* end of group Standard_Driver */

#ifdef __cplusplus
}
#endif

#endif /* __I2S_H__ */

/*** (C) COPYRIGHT 2016 Nuvoton Technology Corp. ***/
