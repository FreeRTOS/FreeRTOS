/*
 * Copyright (C) 2017-2019 Alibaba Group Holding Limited
 */

/******************************************************************************
 * @file     drv_trng.h
 * @brief    header file for trng driver
 * @version  V1.0
 * @date     02. June 2017
 * @model    trng
 ******************************************************************************/
#ifndef _CSI_TRNG_H_
#define _CSI_TRNG_H_

#include "drv_common.h"

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/// definition for trng handle.
typedef void *trng_handle_t;
/****** TRNG specific error codes *****/
typedef enum {
    TRNG_ERROR_MODE = (DRV_ERROR_SPECIFIC + 1)  ///< Specified Mode not supported
} trng_error_e;

/**
\brief TRNG Status
*/
typedef struct {
    uint32_t busy                : 1;
    uint32_t data_valid          : 1;        ///< Data is valid flag
} trng_status_t;

/****** TRNG Event *****/
typedef enum {
    TRNG_EVENT_DATA_GENERATE_COMPLETE       = 0        ///< True random number generates completely
} trng_event_e;
typedef void (*trng_event_cb_t)(int32_t idx, trng_event_e event);   ///< Pointer to \ref trng_event_cb_t : TRNG Event call back.

/**
\brief TRNG Device Driver Capabilities.
*/
typedef struct {
    uint32_t lowper_mode         : 1;        ///< supports low power mode
} trng_capabilities_t;

// Function documentation

/**
  \brief       Initialize TRNG Interface. 1. Initializes the resources needed for the TRNG interface 2.registers event callback function
  \param[in]   idx device id
  \param[in]   cb_event  event call back function \ref trng_event_cb_t
  \return      pointer to trng handle
*/
trng_handle_t csi_trng_initialize(int32_t idx, trng_event_cb_t cb_event);

/**
  \brief       De-initialize TRNG Interface. stops operation and releases the software resources used by the interface
  \param[in]   handle  trng handle to operate.
  \return      error code
*/
int32_t csi_trng_uninitialize(trng_handle_t handle);

/**
  \brief       control trng power.
  \param[in]   handle  trng handle to operate.
  \param[in]   state   power state.\ref csi_power_stat_e.
  \return      error code
*/
int32_t csi_trng_power_control(trng_handle_t handle, csi_power_stat_e state);

/**
  \brief       Get driver capabilities.
  \param[in]   idx device id.
  \return      \ref trng_capabilities_t
*/
trng_capabilities_t csi_trng_get_capabilities(int32_t idx);

/**
  \brief       Get data from the TRNG.
  \param[in]   handle  trng handle to operate.
  \param[out]  data  Pointer to buffer with data get from TRNG
  \param[in]   num   Number of data items to obtain
  \return      error code
*/
int32_t csi_trng_get_data(trng_handle_t handle, void *data, uint32_t num);

/**
  \brief       Get TRNG status.
  \param[in]   handle  trng handle to operate.
  \return      TRNG status \ref trng_status_t
*/
trng_status_t csi_trng_get_status(trng_handle_t handle);


#ifdef __cplusplus
}
#endif

#endif /* _CSI_TRNG_H_ */
