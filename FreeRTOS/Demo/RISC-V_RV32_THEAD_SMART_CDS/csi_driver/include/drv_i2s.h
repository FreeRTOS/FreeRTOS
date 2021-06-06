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
 * @file     drv_i2s.h
 * @brief    header file for i2s driver
 * @version  V1.0
 * @date     02. June 2017
 * @model    i2s
 ******************************************************************************/

#ifndef _DRV_I2S_H_
#define _DRV_I2S_H_


#include <stdint.h>
#include <stdbool.h>
#include <drv_common.h>

#ifdef __cplusplus
extern "C" {
#endif
/// definition for i2s handle.
typedef void *i2s_handle_t;

/****** i2s specific error codes *****/
typedef enum {
    I2S_ERROR_SYNCHRONIZATION   = (DRV_ERROR_SPECIFIC + 1),  ///< Specified Synchronization not supported
    I2S_ERROR_PROTOCOL,                                      ///< Specified Protocol not supported
    I2S_ERROR_DATA_SIZE,                                     ///< Specified Data size not supported
    I2S_ERROR_BIT_ORDER,                                     ///< Specified Bit order not supported
    I2S_ERROR_MONO_MODE,                                     ///< Specified Mono mode not supported
    I2S_ERROR_COMPANDING,                                    ///< Specified Companding not supported
    I2S_ERROR_CLOCK_POLARITY,                                ///< Specified Clock polarity not supported
    I2S_ERROR_AUDIO_FREQ,                                    ///< Specified Audio frequency not supported
    I2S_ERROR_MCLK_PIN,                                      ///< Specified MCLK Pin setting not supported
    I2S_ERROR_MCLK_PRESCALER,                                ///< Specified MCLK Prescaler not supported
    I2S_ERROR_FRAME_LENGHT,                                  ///< Specified Frame length not supported
    I2S_ERROR_FRAME_SYNC_WIDTH,                              ///< Specified Frame Sync width not supported
    I2S_ERROR_FRAME_SYNC_POLARITY,                           ///< Specified Frame Sync polarity not supported
    I2S_ERROR_FRAME_SYNC_EARLY,                              ///< Specified Frame Sync early not supported
    I2S_ERROR_SLOT_COUNT,                                    ///< Specified Slot count not supported
    I2S_ERROR_SLOT_SIZE,                                     ///< Specified Slot size not supported
    I2S_ERROR_SLOT_OFFESET                                   ///< Specified Slot offset not supported
} i2s_error_e;

typedef enum {
    I2S_MODE_TX_MASTER,             ///< i2s transmitter master mode
    I2S_MODE_TX_SLAVE,              ///< i2s transmitter slave mode
    I2S_MODE_RX_MASTER,             ///< i2s receiver master mode
    I2S_MODE_RX_SLAVE,              ///< i2s receiver slave mode
    ///< full duplex mode only for idx0, if used full duplex mode, rx and tx must used same rate, mclk_freq, sclk_freq.
    I2S_MODE_FULL_DUPLEX_MASTER,    ///< i2s full duplex master mode
    I2S_MODE_FULL_DUPLEX_SLAVE,     ///< i2s full duplex slave mode
} i2s_mode_e;

typedef enum {
    I2S_PROTOCOL_I2S,           ///< i2s bus
    I2S_PROTOCOL_MSB_JUSTIFIED, ///< MSB (left) justified
    I2S_PROTOCOL_LSB_JUSTIFIED, ///< LSB (right) justified
    I2S_PROTOCOL_PCM,
} i2s_protocol_e;

typedef enum {
    I2S_SAMPLE_16BIT,
    I2S_SAMPLE_24BIT,
    I2S_SAMPLE_32BIT,
} i2s_sample_width_e;

typedef enum {
    I2S_LEFT_POLARITY_LOW,
    I2S_LEFT_POLARITY_HITH,
} i2s_left_channel_polarity_e;

typedef enum {
    I2S_SCLK_32FS,      ///< SCLK Freq = 32 * sample_rate, freq must >= sample_rate * sample_witch
    I2S_SCLK_48FS,
    I2S_SCLK_64FS,
    I2S_SCLK_16FS,
} i2s_sclk_freq_e;

typedef enum {
    I2S_MCLK_256FS = 256,
    I2S_MCLK_384FS = 384,
} i2s_mclk_freq_e;

/**
\brief I2S Status
*/
typedef struct {
    uint32_t tx_runing      : 1;        ///< Transmitter runing flag
    uint32_t rx_runing      : 1;        ///< Receiver runing flag
    uint32_t tx_fifo_empty  : 1;        ///< Transmit data underflow detected (cleared on start of next send operation)
    uint32_t rx_fifo_full   : 1;        ///< Receive data overflow detected (cleared on start of next receive operation)
    uint32_t frame_error    : 1;        ///< Sync Frame error detected (cleared on start of next send/receive operation)
} i2s_status_t;

/****** I2S Event *****/
typedef enum {
    I2S_EVENT_SEND_COMPLETE        = (0x01 << 0),  ///< Send completed
    I2S_EVENT_RECEIVE_COMPLETE     = (0x01 << 1),  ///< Receive completed
    I2S_EVENT_TX_BUFFER_EMPYT      = (0x01 << 2),  ///< Transmit buffer empty
    I2S_EVENT_TX_UNDERFLOW         = (0x01 << 3),  ///< Transmit data not available
    I2S_EVENT_RX_BUFFER_FULL       = (0x01 << 4),
    I2S_EVENT_RX_OVERFLOW          = (0x01 << 5),  ///< Receive data overflow
    I2S_EVENT_FRAME_ERROR          = (0x01 << 6),  ///< Sync Frame error in Slave mode (optional)
} i2s_event_e;

/**
\brief i2s ctrl cmd.
*/
typedef enum {
    I2S_STREAM_PAUSE,
    I2S_STREAM_RESUME,
    I2S_STREAM_STOP,
    I2S_STREAM_START,
} i2s_ctrl_e;

/**
\brief i2s Driver Capabilities.
*/
typedef struct {
    uint32_t    protocol_user       : 1;    ///< supports user defined Protocol
    uint32_t    protocol_i2s        : 1;    ///< supports I2S Protocol
    uint32_t    protocol_justified  : 1;    ///< supports MSB/LSB justified Protocol
    uint32_t    protocol_pcm        : 1;
    uint32_t    mono_mode           : 1;    ///< supports Mono mode
    uint32_t    full_duplex         : 1;
    uint32_t    mclk_pin            : 1;    ///< supports MCLK (Master Clock) pin
    uint32_t    event_frame_error   : 1;    ///< supports Frame error event: ARM_SAI_EVENT_FRAME_ERROR
} i2s_capabilities_t;

typedef enum {
    I2S_RX_RIGHT_CHANNEL,
    I2S_RX_LEFT_CHANNEL,
} i2s_rx_mono_channel;

typedef struct {
    i2s_mode_e mode;
    i2s_protocol_e protocol;
    i2s_sample_width_e width;
    i2s_left_channel_polarity_e left_polarity;  ///< set ws signel left channle polarity
    i2s_sclk_freq_e sclk_freq;                  ///< I2S sclk freq select. example:32fs = 32 * sample_rate
    i2s_mclk_freq_e mclk_freq;                  ///< I2S mclk freq select. example:256fs = 256 * sample_rate
    int32_t tx_mono_enable;                     ///< used for tx or full duplex mode, tx mono mode enable. 1 eanble, 0 disable
    int32_t rx_mono_enable;                     ///< used for rx or full duplex mode,rx mono mode enable. 1 eanble, 0 disable
    i2s_rx_mono_channel rx_mono_select_ch;      ///< used for rx or full duplex mode,
} i2s_config_type_t;

typedef struct {
    i2s_config_type_t cfg;
    uint32_t rate;
    uint32_t tx_period;         ///< i2s send bytes tigger cb
    uint32_t rx_period;         ///< i2s receive bytes tigger cb
    uint8_t *tx_buf;                ///< i2s send buf
    uint32_t tx_buf_length;         ///< i2s send buf length
    uint8_t *rx_buf;                ///< i2s recv buf
    uint32_t rx_buf_length;         ///< i2s recv buf length
} i2s_config_t;

typedef void (*i2s_event_cb_t)(int32_t idx, i2s_event_e event, void *arg);  ///< Pointer to \ref i2s_event_cb_t : i2s Event call back.

/**
  \brief       Initialize I2S Interface. 1. Initializes the resources needed for the I2S index 2.registers event callback function
  \param[in]   idx  i2s index
  \param[in]   cb_event  Pointer to \ref i2s_event_cb_t
  \param[in]   cb_arg    event callback arg
  \return      pointer to i2s instances
*/
i2s_handle_t csi_i2s_initialize(int32_t idx, i2s_event_cb_t cb_event, void *cb_arg);

/**
  \brief       De-initialize I2S Interface. stops operation and releases the software resources used by the interface
  \param[in]   handle i2s handle to operate.
  \return      0 for success, negative for error code
*/
int32_t csi_i2s_uninitialize(i2s_handle_t handle);

/**
  \brief       enable the i2s module
  \param[in]   handle i2s handle to operate.
  \param[in]   en: 1 enable, 0 disable
  \return      none
*/
void csi_i2s_enable(i2s_handle_t handle, int en);

/**
  \brief       Get driver capabilities.
  \param[in]   idx i2s index.
  \return      \ref i2s_capabilities_t
*/
i2s_capabilities_t csi_i2s_get_capabilities(int32_t idx);

/**
  \brief       config i2s attributes.
  \param[in]   handle    i2s handle to operate.
  \param[in]   config    i2s config.
  \return      0 for success, negative for error code
*/
int32_t csi_i2s_config(i2s_handle_t handle, i2s_config_t *config);

/**
  \brief       sending data to i2s transmitter.
  \param[in]   handle       i2s handle to operate.
  \param[in]   data         Pointer to buffer for data to send
  \param[in]   data_size    size of tranmitter data
  \return      send data size.(bytes)
*/
uint32_t csi_i2s_send(i2s_handle_t handle, const uint8_t *data, uint32_t length);

/**
  \brief       receiving data from i2s receiver.
  \param[in]   handle       i2s handle to operate.
  \param[in]   data         Pointer to buffer for data to receive from i2s receiver
  \param[in]   data_size    size of receiver data
  \return      receive data size.(bytes)
*/
uint32_t csi_i2s_receive(i2s_handle_t handle, uint8_t *buf, uint32_t length);

/**
  \brief       control the i2s transfer.
  \param[in]   handle       i2s handle to operate.
  \param[in]   cmd          i2s ctrl command
  \return      0 for success, negative for error code
*/
int32_t csi_i2s_send_ctrl(i2s_handle_t handle, i2s_ctrl_e cmd);

/**
  \brief       control the i2s receive.
  \param[in]   handle       i2s handle to operate.
  \param[in]   cmd          i2s ctrl command
  \return      0 for success, negative for error code
*/
int32_t csi_i2s_receive_ctrl(i2s_handle_t handle, i2s_ctrl_e cmd);

/**
  \brief       Get i2s status.
  \param[in]   handle i2s handle to operate.
  \return      i2s status \ref i2s_status_e
*/
i2s_status_t csi_i2s_get_status(i2s_handle_t handle);

/**
  \brief       control I2S power.
  \param[in]   handle  i2s handle to operate.
  \param[in]   state   power state.\ref csi_power_stat_e.
  \return      error code
*/
int32_t csi_i2s_power_control(i2s_handle_t handle, csi_power_stat_e state);

#ifdef __cplusplus
}
#endif

#endif /* _DRV_I2S_H_ */

