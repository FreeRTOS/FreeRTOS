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
 * @file     drv_iic.h
 * @brief    header file for iic driver
 * @version  V1.0
 * @date     02. June 2017
 * @model    iic
 ******************************************************************************/

#ifndef _CSI_IIC_H_
#define _CSI_IIC_H_


#include <stdint.h>
#include <stdbool.h>
#include <drv_common.h>

#ifdef __cplusplus
extern "C" {
#endif
/// definition for iic handle.
typedef void *iic_handle_t;

/*----- IIC Control Codes: Mode -----*/
typedef enum {
    IIC_MODE_MASTER,             ///< IIC Master
    IIC_MODE_SLAVE               ///< IIC Slave
} iic_mode_e;

/*----- IIC Control Codes: IIC Bus Speed -----*/
typedef enum {
    IIC_BUS_SPEED_STANDARD  = 0, ///< Standard Speed (100kHz)
    IIC_BUS_SPEED_FAST      = 1, ///< Fast Speed     (400kHz)
    IIC_BUS_SPEED_FAST_PLUS = 2, ///< Fast+ Speed    (  1MHz)
    IIC_BUS_SPEED_HIGH      = 3  ///< High Speed     (3.4MHz)
} iic_speed_e;

/*----- IIC Control Codes: IIC Address Mode -----*/
typedef enum {
    IIC_ADDRESS_7BIT        = 0,  ///< 7-bit address mode
    IIC_ADDRESS_10BIT       = 1   ///< 10-bit address mode
} iic_address_mode_e;

/**
\brief IIC Status
*/
typedef struct {
    uint32_t busy             : 1;        ///< Transmitter/Receiver busy flag
    uint32_t mode             : 1;        ///< Mode: 0=Slave, 1=Master
    uint32_t direction        : 1;        ///< Direction: 0=Transmitter, 1=Receiver
    uint32_t general_call     : 1;        ///< General Call(address 0) indication (cleared on start of next Slave operation)
    uint32_t arbitration_lost : 1;        ///< Master lost arbitration(in case of multi-masters) (cleared on start of next Master operation)
    uint32_t bus_error        : 1;        ///< Bus error detected (cleared on start of next Master/Slave operation)
} iic_status_t;

/****** IIC Event *****/
typedef enum {
    IIC_EVENT_TRANSFER_DONE        = 0,  ///< Master/Slave Transmit/Receive finished
    IIC_EVENT_TRANSFER_INCOMPLETE  = 1,  ///< Master/Slave Transmit/Receive incomplete transfer
    IIC_EVENT_SLAVE_TRANSMIT       = 2,  ///< Slave Transmit operation requested
    IIC_EVENT_SLAVE_RECEIVE        = 3,  ///< Slave Receive operation requested
    IIC_EVENT_ADDRESS_NACK         = 4,  ///< Address not acknowledged from Slave
    IIC_EVENT_GENERAL_CALL         = 5,  ///< General Call indication
    IIC_EVENT_ARBITRATION_LOST     = 6,  ///< Master lost arbitration
    IIC_EVENT_BUS_ERROR            = 7,  ///< Bus error detected (START/STOP at illegal position)
    IIC_EVENT_BUS_CLEAR            = 8   ///< Bus clear finished
} iic_event_e;

typedef void (*iic_event_cb_t)(int32_t idx, iic_event_e event);  ///< Pointer to \ref iic_event_cb_t : IIC Event call back.

/**
\brief IIC Driver Capabilities.
*/
typedef struct  {
    uint32_t address_10_bit : 1;          ///< supports 10-bit addressing
} iic_capabilities_t;

/**
  \brief       Initialize IIC Interface specified by pins. \n
               1. Initializes the resources needed for the IIC interface 2.registers event callback function
  \param[in]   idx iic index
  \param[in]   cb_event event callback function \ref iic_event_cb_t
  \return      0 for success, negative for error code
*/
iic_handle_t csi_iic_initialize(int32_t idx, iic_event_cb_t cb_event);

/**
  \brief       De-initialize IIC Interface. stops operation and releases the software resources used by the interface
  \param[in]   handle  iic handle to operate.
  \return      0 for success, negative for error code
*/
int32_t csi_iic_uninitialize(iic_handle_t handle);

/**
  \brief       Get driver capabilities.
  \param[in]   idx iic index
  \return      \ref iic_capabilities_t
*/
iic_capabilities_t csi_iic_get_capabilities(int32_t idx);

/**
  \brief       config iic attributes.
  \param[in]   handle    iic handle to operate.
  \param[in]   mode      iic mode \ref iic_mode_e. if negative, then this attribute not changed.
  \param[in]   speed     iic speed \ref iic_speed_e. if negative, then this attribute not changed.
  \param[in]   addr_mode iic address mode \ref iic_address_mode_e. if negative, then this attribute not changed.
  \param[in]   slave_addr iic address of slave. if negative, then this attribute not changed.
  \return      0 for success, negative for error code
*/
int32_t csi_iic_config(iic_handle_t handle,
                       iic_mode_e mode,
                       iic_speed_e speed,
                       iic_address_mode_e addr_mode,
                       int32_t slave_addr);

/**
  \brief       Start transmitting data as IIC Master.
               This function is non-blocking,\ref iic_event_e is signaled when transfer completes or error happens.
               \ref csi_iic_get_status can get operating status.
  \param[in]   handle         iic handle to operate.
  \param[in]   devaddr        iic addrress of slave device. |_BIT[7:1]devaddr_|_BIT[0]R/W_|
                              eg: BIT[7:0] = 0xA0, devaddr = 0x50.
  \param[in]   data           data to send to IIC Slave
  \param[in]   num            Number of data items to send
  \param[in]   xfer_pending   Transfer operation is pending - Stop condition will not be generated
                              Master generates STOP condition (if xfer_pending is "false")
  \return      0 for success, negative for error code
*/
int32_t csi_iic_master_send(iic_handle_t handle, uint32_t devaddr, const void *data, uint32_t num, bool xfer_pending);

/**
  \brief       Start receiving data as IIC Master.
               This function is non-blocking,\ref iic_event_e is signaled when transfer completes or error happens.
               \ref csi_iic_get_status can get operating status.
  \param[in]   handle  iic handle to operate.
  \param[in]   devaddr        iic addrress of slave device.
  \param[out]  data    Pointer to buffer for data to receive from IIC receiver
  \param[in]   num     Number of data items to receive
  \param[in]   xfer_pending   Transfer operation is pending - Stop condition will not be generated
  \return      0 for success, negative for error code
*/
int32_t csi_iic_master_receive(iic_handle_t handle, uint32_t devaddr, void *data, uint32_t num, bool xfer_pending);

/**
  \brief       Start transmitting data as IIC Slave.
               This function is non-blocking,\ref iic_event_e is signaled when transfer completes or error happens.
               \ref csi_iic_get_status can get operating status.
  \param[in]   handle  iic handle to operate.
  \param[in]   data  Pointer to buffer with data to transmit to IIC Master
  \param[in]   num   Number of data items to send
  \return      0 for success, negative for error code
*/
int32_t csi_iic_slave_send(iic_handle_t handle, const void *data, uint32_t num);

/**
  \brief       Start receiving data as IIC Slave.
               This function is non-blocking,\ref iic_event_e is signaled when transfer completes or error happens.
               \ref csi_iic_get_status can get operating status.
  \param[in]   handle  iic handle to operate.
  \param[out]  data  Pointer to buffer for data to receive from IIC Master
  \param[in]   num   Number of data items to receive
  \return      0 for success, negative for error code
*/
int32_t csi_iic_slave_receive(iic_handle_t handle, void *data, uint32_t num);

/**
  \brief       abort transfer.
  \param[in]   handle  iic handle to operate.
  \return      0 for success, negative for error code
*/
int32_t csi_iic_abort_transfer(iic_handle_t handle);

/**
  \brief       Get IIC status.
  \param[in]   handle  iic handle to operate.
  \return      IIC status \ref iic_status_t
*/
iic_status_t csi_iic_get_status(iic_handle_t handle);

/**
  \brief       control IIC power.
  \param[in]   handle  iic handle to operate.
  \param[in]   state   power state.\ref csi_power_stat_e.
  \return      error code
*/
int32_t csi_iic_power_control(iic_handle_t handle, csi_power_stat_e state);

/**
  \brief       config iic mode.
  \param[in]   handle  iic handle to operate.
  \param[in]   mode      \ref iic_mode_e
  \return      error code
*/
int32_t csi_iic_config_mode(iic_handle_t handle, iic_mode_e mode);

/**
  \brief       config iic speed.
  \param[in]   handle  iic handle to operate.
  \param[in]   speed     \ref iic_speed_e
  \return      error code
*/
int32_t csi_iic_config_speed(iic_handle_t handle, iic_speed_e speed);

/**
  \brief       config iic address mode.
  \param[in]   handle  iic handle to operate.
  \param[in]   addr_mode \ref iic_address_mode_e
  \return      error code
*/
int32_t csi_iic_config_addr_mode(iic_handle_t handle, iic_address_mode_e addr_mode);


/**
  \brief       config iic slave address.
  \param[in]   handle  iic handle to operate.
  \param[in]   slave_addr slave address
  \return      error code
*/
int32_t csi_iic_config_slave_addr(iic_handle_t handle, int32_t slave_addr);

/**
  \brief       Get IIC transferred data count.
  \param[in]   handle  iic handle to operate.
  \return      the number of the currently transferred data items
*/
uint32_t csi_iic_get_data_count(iic_handle_t handle);

/**
  \brief       Send START command.
  \param[in]   handle  iic handle to operate.
  \return      error code
*/
int32_t csi_iic_send_start(iic_handle_t handle);

/**
  \brief       Send STOP command.
  \param[in]   handle  iic handle to operate.
  \return      error code
*/
int32_t csi_iic_send_stop(iic_handle_t handle);

/**
  \brief       Reset IIC peripheral.
  \param[in]   handle  iic handle to operate.
  \return      error code
*/
int32_t csi_iic_reset(iic_handle_t handle);


#ifdef __cplusplus
}
#endif

#endif /* _CSI_IIC_H_ */
