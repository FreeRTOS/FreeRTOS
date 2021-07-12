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
 * @file     drv_eflash.h
 * @brief    header file for eflash driver
 * @version  V1.0
 * @date     02. June 2017
 * @model    eflash
 ******************************************************************************/
#ifndef _CSI_EFLASH_H_
#define _CSI_EFLASH_H_


#include <stdint.h>
#include <drv_common.h>

#ifdef __cplusplus
extern "C" {
#endif

/// definition for eflash handle.
typedef void *eflash_handle_t;

/**
\brief Flash information
*/
typedef struct {
    uint32_t          start;              ///< Chip Start address
    uint32_t          end;                ///< Chip End address (start+size-1)
    uint32_t          sector_count;       ///< Number of sectors
    uint32_t          sector_size;        ///< Uniform sector size in bytes
    uint32_t          page_size;          ///< Optimal programming page size in bytes
    uint32_t          program_unit;       ///< Smallest programmable unit in bytes
    uint8_t           erased_value;       ///< Contents of erased memory (usually 0xFF)
} eflash_info_t;

/**
\brief Flash Status
*/
typedef struct {
    uint32_t busy  : 1;                   ///< Flash busy flag
    uint32_t error : 1;                   ///< Read/Program/Erase error flag (cleared on start of next operation)
} eflash_status_t;

/****** EFLASH Event *****/
typedef enum {
    EFLASH_EVENT_READY           = 0,  ///< Flash Ready
    EFLASH_EVENT_ERROR,                ///< Read/Program/Erase Error
} eflash_event_e;

typedef void (*eflash_event_cb_t)(int32_t idx, eflash_event_e event);   ///< Pointer to \ref eflash_event_cb_t : EFLASH Event call back.

/**
\brief Flash Driver Capabilities.
*/
typedef struct {
    uint32_t event_ready  : 1;            ///< Signal Flash Ready event
    uint32_t data_width   : 2;            ///< Data width: 0=8-bit, 1=16-bit, 2=32-bit
    uint32_t erase_chip   : 1;            ///< Supports EraseChip operation
} eflash_capabilities_t;

// Function documentation

/**
  \brief       Initialize EFLASH Interface. 1. Initializes the resources needed for the EFLASH interface 2.registers event callback function
  \param[in]   idx  device id
  \param[in]   cb_event  event callback function \ref eflash_event_cb_t
  \return      pointer to eflash handle
*/
eflash_handle_t csi_eflash_initialize(int32_t idx, eflash_event_cb_t cb_event);

/**
  \brief       De-initialize EFLASH Interface. stops operation and releases the software resources used by the interface
  \param[in]   handle  eflash handle to operate.
  \return      error code
*/
int32_t csi_eflash_uninitialize(eflash_handle_t handle);

/**
  \brief       Get driver capabilities.
  \param[in]   idx  device id
  \return      \ref eflash_capabilities_t
*/
eflash_capabilities_t csi_eflash_get_capabilities(int32_t idx);

/**
  \brief       control eflash power.
  \param[in]   handle  eflash handle to operate.
  \param[in]   state   power state.\ref csi_power_stat_e.
  \return      error code
*/
int32_t csi_eflash_power_control(eflash_handle_t handle, csi_power_stat_e state);

/**
  \brief       Read data from Flash.
  \param[in]   handle  eflash handle to operate.
  \param[in]   addr  Data address.
  \param[out]  data  Pointer to a buffer storing the data read from Flash.
  \param[in]   cnt   Number of data items to read.
  \return      number of data items read or error code
*/
int32_t csi_eflash_read(eflash_handle_t handle, uint32_t addr, void *data, uint32_t cnt);

/**
  \brief       Program data to Flash.
  \param[in]   handle  eflash handle to operate.
  \param[in]   addr  Data address.
  \param[in]   data  Pointer to a buffer containing the data to be programmed to Flash.
  \param[in]   cnt   Number of data items to program.
  \return      number of data items programmed or error code
*/
int32_t csi_eflash_program(eflash_handle_t handle, uint32_t addr, const void *data, uint32_t cnt);

/**
  \brief       Erase Flash Sector.
  \param[in]   handle  eflash handle to operate.
  \param[in]   addr  Sector address
  \return      error code
*/
int32_t csi_eflash_erase_sector(eflash_handle_t handle, uint32_t addr);

/**
  \brief       Erase complete Flash.
  \param[in]   handle  eflash handle to operate.
  \return      error code
*/
int32_t csi_eflash_erase_chip(eflash_handle_t handle);

/**
  \brief       Get Flash information.
  \param[in]   handle  eflash handle to operate.
  \return      Pointer to Flash information \ref eflash_info_t
*/
eflash_info_t *csi_eflash_get_info(eflash_handle_t handle);

/**
  \brief       Get FLASH status.
  \param[in]   handle  eflash handle to operate.
  \return      EFLASH status \ref eflash_status_t
*/
eflash_status_t csi_eflash_get_status(eflash_handle_t handle);

#ifdef __cplusplus
}
#endif

#endif /* _CSI_EFLASH_H_ */
