/*
 * Copyright (C) 2017 C-SKY Microsystems Co., Ltd. All rights reserved.
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
 * @file     drv_flash.c
 * @brief    header file for flash driver
 * @version  V1.0
 * @date     02. June 2017
 ******************************************************************************/

#ifndef _CSI_FLASH_H_
#define _CSI_FLASH_H_

#ifdef __cplusplus
extern "C" {
#endif

#include <stdint.h>
#include <drv_common.h>


typedef struct  {
    uint32_t base;
    void    *priv;
} csi_flash_t;

/**
\brief Flash Sector information
*/
typedef struct {
    uint32_t start;                       ///< Sector Start address
    uint32_t end;                         ///< Sector End address (start+size-1)
} const flash_sector;

/**
\brief Flash information
*/
typedef struct {
    flash_sector     *sector_info;        ///< Sector layout information (NULL=Uniform sectors)
    uint32_t          sector_count;       ///< Number of sectors
    uint32_t          sector_size;        ///< Uniform sector size in bytes (0=sector_info used)
    uint32_t          page_size;          ///< Optimal programming page size in bytes
    uint32_t          program_unit;       ///< Smallest programmable unit in bytes
    uint8_t           erased_value;       ///< Contents of erased memory (usually 0xFF)
} flash_info_t;

/**
\brief Flash Status
*/
typedef struct {
    uint32_t busy  : 1;                   ///< Flash busy flag
    uint32_t error : 1;                   ///< Read/Program/Erase error flag (cleared on start of next operation)
} flash_status_t;

/****** FLASH Event *****/
typedef enum {
    FLASH_EVENT_READY           = 0,  ///< Flash Ready
    FLASH_EVENT_ERROR              ,  ///< Read/Program/Erase Error
} flash_event_e;

typedef void (*flash_event_cb_t)(flash_event_e event);   ///< Pointer to \ref flash_event_cb_t : FLASH Event call back.

/**
\brief Flash Driver Capabilities.
*/
typedef struct {
    uint32_t event_ready  : 1;            ///< Signal Flash Ready event
    uint32_t data_width   : 2;            ///< Data width: 0=8-bit, 1=16-bit, 2=32-bit
    uint32_t erase_chip   : 1;            ///< Supports EraseChip operation
} flash_capabilities_t;




/**
  \brief       get flash instance count.
  \return      flash instance count
*/
int32_t drv_flash_get_instance_count(void);

/**
  \brief       get flash instance .
  \param[in]   idx   must not exceed return value of drv_flash_get_instance_count()
  \return      pointer to flash instance
*/
csi_flash_t *drv_flash_get_instance(int32_t idx);

/**
  \brief       Get driver capabilities.
  \param[in]   instance flash instance to operate.
  \return      \ref flash_capabilities_t
*/
flash_capabilities_t drv_flash_get_capabilities(const csi_flash_t *instance);

/**
  \brief       Initialize FLASH Interface. 1. Initializes the resources needed for the FLASH interface 2.registers event callback function
  \param[in]   instance  flash instance to operate.
  \param[in]   cb_event  Pointer to \ref flash_event_cb_t
  \return      error code
*/
int32_t drv_flash_initialize(const csi_flash_t *instance, flash_event_cb_t cb_event);

/**
  \brief       De-initialize FLASH Interface. stops operation and releases the software resources used by the interface
  \param[in]   instance  flash instance to operate.
  \return      error code
*/
int32_t drv_flash_uninitialize(const csi_flash_t *instance);

/**
  \brief       Get Flash information.
  \param[in]   instance  flash instance to operate.
  \return      Pointer to Flash information \ref flash_info_t
*/
flash_info_t *drv_flash_get_info(const csi_flash_t *instance);

/**
  \brief       Read data from Flash.
  \param[in]   instance  flash instance to operate.
  \param[in]   addr  Data address.
  \param[in]   data  Pointer to a buffer storing the data read from Flash.
  \param[in]   cnt   Number of data items to read.
  \return      number of data items read or error code
*/
int32_t drv_flash_read(const csi_flash_t *instance, uint32_t addr, void *data, uint32_t cnt);

/**
  \brief       Program data to Flash.
  \param[in]   instance  flash instance to operate.
  \param[in]   addr  Data address.
  \param[in]   data  Pointer to a buffer containing the data to be programmed to Flash..
  \param[in]   cnt   Number of data items to program.
  \return      number of data items programmed or error code
*/
int32_t drv_flash_program(const csi_flash_t *instance, uint32_t addr, const void *data, uint32_t cnt);

/**
  \brief       Erase Flash Sector.
  \param[in]   instance  flash instance to operate.
  \param[in]   addr  Sector address
  \return      error code
*/
int32_t drv_flash_erase_sector(const csi_flash_t *instance, uint32_t addr);

/**
  \brief       Erase complete Flash.
  \param[in]   instance  flash instance to operate.
  \return      error code
*/
int32_t drv_flash_erase_chip(const csi_flash_t *instance);

/**
  \brief       Get FLASH status.
  \param[in]   instance  flash instance to operate.
  \return      FLASH status \ref flash_status_t
*/
flash_status_t drv_flash_get_status(const csi_flash_t *instance);

#ifdef __cplusplus
}
#endif

#endif /* _CSI_FLASH_H_ */
