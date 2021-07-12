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
 * @file     drv_spiflash.h
 * @brief    header file for spiflash driver
 * @version  V1.0
 * @date     02. June 2017
 * @model    spiflash
 ******************************************************************************/
#ifndef _CSI_SPIFLASH_H_
#define _CSI_SPIFLASH_H_


#include <stdint.h>
#include <drv_common.h>

#ifdef __cplusplus
extern "C" {
#endif

/// definition for spiflash handle.
typedef void *spiflash_handle_t;

/**
\brief Flash information
*/
typedef struct {
    uint32_t          start;              ///< Chip Start address
    uint32_t          end;                ///< Chip End address (start+size-1)
    uint32_t          sector_count;       ///< Number of sectors
    uint32_t          sector_size;        ///< Uniform sector size in bytes (0=sector_info used)
    uint32_t          page_size;          ///< Optimal programming page size in bytes
    uint32_t          program_unit;       ///< Smallest programmable unit in bytes
    uint8_t           erased_value;       ///< Contents of erased memory (usually 0xFF)
} spiflash_info_t;

/**
\brief Flash Status
*/
typedef struct {
    uint32_t busy  : 1;                   ///< Flash busy flag
    uint32_t error : 1;                   ///< Read/Program/Erase error flag (cleared on start of next operation)
} spiflash_status_t;

/****** SPIFLASH Event *****/
typedef enum {
    SPIFLASH_EVENT_READY           = 0,  ///< Flash Ready
    SPIFLASH_EVENT_ERROR,                ///< Read/Program/Erase Error
} spiflash_event_e;

typedef enum {
    SPIFLASH_DATA_1_LINE  = 1,
    SPIFLASH_DATA_2_LINES = 2,
    SPIFLASH_DATA_4_LINES = 4
} spiflash_data_line_e;

typedef void (*spiflash_event_cb_t)(int32_t idx, spiflash_event_e event);   ///< Pointer to \ref spiflash_event_cb_t : SPIFLASH Event call back.

/**
\brief Flash Driver Capabilities.
*/
typedef struct {
    uint32_t event_ready  : 1;            ///< Signal Flash Ready event
    uint32_t data_width   : 2;            ///< Data width: 0=8-bit, 1=16-bit, 2=32-bit
    uint32_t erase_chip   : 1;            ///< Supports EraseChip operation
} spiflash_capabilities_t;

// Function documentation

/**
  \brief       Initialize SPIFLASH Interface. 1. Initializes the resources needed for the SPIFLASH interface 2.registers event callback function
  \param[in]   idx  device id
  \param[in]   cb_event  Pointer to \ref spiflash_event_cb_t
  \return      pointer to spiflash handle
*/
spiflash_handle_t csi_spiflash_initialize(int32_t idx, spiflash_event_cb_t cb_event);

/**
  \brief       De-initialize SPIFLASH Interface. stops operation and releases the software resources used by the interface
  \param[in]   handle  spiflash handle to operate.
  \return      error code
*/
int32_t csi_spiflash_uninitialize(spiflash_handle_t handle);

/**
  \brief       Get driver capabilities.
  \param[in]   handle spiflash handle to operate.
  \return      \ref spiflash_capabilities_t
*/
spiflash_capabilities_t csi_spiflash_get_capabilities(int32_t idx);

/**
  \brief       Set QSPI data line
  \param[in]   handle spiflash handle to operate
  \param[in]   line   spiflash data line mode
  \return      error code
*/
int32_t csi_spiflash_config_data_line(spiflash_handle_t handle, spiflash_data_line_e line);

/**
  \brief       Read data from Flash.
  \param[in]   handle  spiflash handle to operate.
  \param[in]   addr  Data address.
  \param[out]  data  Pointer to a buffer storing the data read from Flash.
  \param[in]   cnt   Number of data items to read.
  \return      number of data items read or error code
*/
int32_t csi_spiflash_read(spiflash_handle_t handle, uint32_t addr, void *data, uint32_t cnt);

/**
  \brief       Program data to Flash.
  \param[in]   handle  spiflash handle to operate.
  \param[in]   addr  Data address.
  \param[in]   data  Pointer to a buffer containing the data to be programmed to Flash..
  \param[in]   cnt   Number of data items to program.
  \return      number of data items programmed or error code
*/
int32_t csi_spiflash_program(spiflash_handle_t handle, uint32_t addr, const void *data, uint32_t cnt);

/**
  \brief       Erase Flash Sector.
  \param[in]   handle  spiflash handle to operate.
  \param[in]   addr  Sector address
  \return      error code
*/
int32_t csi_spiflash_erase_sector(spiflash_handle_t handle, uint32_t addr);

/**
  \brief       Erase complete Flash.
  \param[in]   handle  spiflash handle to operate.
  \return      error code
*/
int32_t csi_spiflash_erase_chip(spiflash_handle_t handle);

/**
  \brief       Flash power down.
  \param[in]   handle  spiflash handle to operate.
  \return      error code
*/
int32_t csi_spiflash_power_down(spiflash_handle_t handle);

/**
  \brief       Flash release power down.
  \param[in]   handle  spiflash handle to operate.
  \return      error code
*/
int32_t csi_spiflash_release_power_down(spiflash_handle_t handle);

/**
  \brief       Get Flash information.
  \param[in]   handle  spiflash handle to operate.
  \return      Pointer to Flash information \ref spiflash_info_t
*/
spiflash_info_t *csi_spiflash_get_info(spiflash_handle_t handle);

/**
  \brief       Get SPIFLASH status.
  \param[in]   handle  spiflash handle to operate.
  \return      SPIFLASH status \ref spiflash_status_t
*/
spiflash_status_t csi_spiflash_get_status(spiflash_handle_t handle);

#ifdef __cplusplus
}
#endif

#endif /* _CSI_SPIFLASH_H_ */
