/*
 * Copyright (C) 2017-2019 Alibaba Group Holding Limited
 */


/******************************************************************************
 * @file     drv_crc.h
 * @brief    Header File for CRC Driver
 * @version  V1.0
 * @date     02. June 2017
 * @model    crc
 ******************************************************************************/
#ifndef _CSI_CRC_H_
#define _CSI_CRC_H_


#include <stdint.h>
#include <drv_errno.h>
#include <drv_common.h>

#ifdef __cplusplus
extern "C" {
#endif

/****** CRC specific error codes *****/
#define CRC_ERROR_MODE                (DRV_ERROR_SPECIFIC + 1)     ///< Specified Mode not supported

/// definition for crc handle.
typedef void *crc_handle_t;

/*----- CRC Control Codes: Mode -----*/
typedef enum {
    CRC_MODE_CRC8                   = 0,   ///< Mode CRC8
    CRC_MODE_CRC16,                        ///< Mode CRC16
    CRC_MODE_CRC32                         ///< Mode CRC32
} crc_mode_e;

/*----- CRC Control Codes: Mode Parameters: Key length -----*/
typedef enum {
    CRC_STANDARD_CRC_ROHC         = 0,    ///< Standard CRC RHOC
    CRC_STANDARD_CRC_MAXIM,               ///< Standard CRC MAXIAM
    CRC_STANDARD_CRC_X25,                 ///< Standard CRC X25
    CRC_STANDARD_CRC_CCITT,               ///< Standard CRC CCITT
    CRC_STANDARD_CRC_CCITT_FALSE,         ///< Standard CRC CCITT-FALSE
    CRC_STANDARD_CRC_USB,                 ///< Standard CRC USB
    CRC_STANDARD_CRC_IBM,                 ///< Standard CRC IBM
    CRC_STANDARD_CRC_MODBUS,              ///< Standard CRC MODBUS
    CRC_STANDARD_CRC_ITU,                 ///< Standard CRC ITU
    CRC_STANDARD_CRC_PMEQ_2,              ///< Standard CRC PMEQ_2
    CRC_STANDARD_CRC_XMODEM,              ///< Standard CRC XMODEM
    CRC_STANDARD_CRC_DNP,                 ///< Standard CRC DNP
    CRC_STANDARD_CRC_NONE,                ///< Standard CRC NONE
} crc_standard_crc_e;

/**
\brief CRC Status
*/
typedef struct {
    uint32_t busy             : 1;        ///< busy flag
} crc_status_t;

/****** CRC Event *****/
typedef enum {
    CRC_EVENT_CALCULATE_COMPLETE  = 0,  ///< Calculate completed
} crc_event_e;

typedef void (*crc_event_cb_t)(int32_t idx, crc_event_e event);   ///< Pointer to \ref crc_event_cb_t : CRC Event call back.

/**
\brief CRC Device Driver Capabilities.
*/
typedef struct {
    uint32_t ROHC               : 1;      ///< supports ROHC mode
    uint32_t MAXIM              : 1;      ///< supports MAXIM mode
    uint32_t X25                : 1;      ///< supports X25 mode
    uint32_t CCITT              : 1;      ///< supports CCITT mode
    uint32_t CCITT_FALSE        : 1;      ///< supports CCITT-FALSE mode
    uint32_t USB                : 1;      ///< supports USB mode
    uint32_t IBM                : 1;      ///< supports IBM mode
    uint32_t MODBUS             : 1;      ///< supports MODBUS mode
    uint32_t ITU                : 1;      ///< supports ITU mode
    uint32_t PMEQ_2             : 1;      ///< supports PMEQ_2 mode
    uint32_t XMODEM             : 1;      ///< supports XMODEM mode
    uint32_t DNP                : 1;      ///< supports DNP mode
    uint32_t NONE               : 1;      ///< supports NONE mode
} crc_capabilities_t;

// Function documentation

/**
  \brief       Initialize CRC Interface. 1. Initializes the resources needed for the CRC interface 2.registers event callback function
  \param[in]   idx  device id
  \param[in]   cb_event event callback function \ref crc_event_cb_t
  \return      return crc handle if success
*/
crc_handle_t csi_crc_initialize(int32_t idx, crc_event_cb_t cb_event);

/**
  \brief       De-initialize CRC Interface. stops operation and releases the software resources used by the interface
  \param[in]   handle  crc handle to operate.
  \return      error code
*/
int32_t csi_crc_uninitialize(crc_handle_t handle);

/**
  \brief       control crc power.
  \param[in]   handle  crc handle to operate.
  \param[in]   state   power state.\ref csi_power_stat_e.
  \return      error code
*/
int32_t csi_crc_power_control(crc_handle_t handle, csi_power_stat_e state);

/**
  \brief       Get driver capabilities.
  \param[in]   idx  device id
  \return      \ref crc_capabilities_t
*/
crc_capabilities_t csi_crc_get_capabilities(int32_t idx);

/**
  \brief       config crc mode.
  \param[in]   handle  crc handle to operate.
  \param[in]   mode      \ref crc_mode_e
  \param[in]   standard  \ref crc_standard_crc_e
  \return      error code
*/
int32_t csi_crc_config(crc_handle_t handle,
                       crc_mode_e mode,
                       crc_standard_crc_e standard
                      );

/**
  \brief       calculate crc. this function will pad zero if input data is not word aligned
  \param[in]   handle  crc handle to operate.
  \param[in]   in      Pointer to the input data
  \param[out]  out     Pointer to the result.
  \param[in]   len     intput data len.
  \return      error code
*/
int32_t csi_crc_calculate(crc_handle_t handle, const void *in, void *out, uint32_t len);

/**
  \brief       Get CRC status.
  \param[in]   handle  crc handle to operate.
  \return      CRC status \ref crc_status_t
*/
crc_status_t csi_crc_get_status(crc_handle_t handle);


#ifdef __cplusplus
}
#endif

#endif /* _CSI_CRC_H_ */
