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
 * @file     drv_pwm.h
 * @brief    header file for pwm driver
 * @version  V1.0
 * @date     19. Feb 2019
 * @model    pwm
 ******************************************************************************/

#ifndef _CSI_PWM_H_
#define _CSI_PWM_H_


#include <stdint.h>
#include <drv_common.h>

#ifdef __cplusplus
extern "C" {
#endif

/// definition for pwm handle.
typedef void *pwm_handle_t;

/****** PWM specific error codes *****/
typedef enum {
    EDRV_PWM_MODE  = (DRV_ERROR_SPECIFIC + 1),     ///< Specified Mode not supported
} csi_pwm_error_e;

/*----- PWM Input Capture Mode -----*/
typedef enum {
    PWM_INPUT_MODE_EDGE_TIME  = 0,                 ///< Input Edge Time Mode
    PWM_INPUT_MODE_EDGE_COUNT = 1                  ///< Input Edge Count Mode
} pwm_input_mode_e;

typedef enum {
    PWM_INPUT_EVENT_MODE_POSEDGE = 0,              ///< Posedge Edge
    PWM_INPUT_EVENT_MODE_NEGEDGE = 1,              ///< Negedge Edge
    PWM_INPUT_EVENT_MODE_BOTHEDGE = 2              ///< Both Edge
} pwm_input_event_mode_e;

typedef struct {
    pwm_input_mode_e input_mode;                   ///< Input Mode
    pwm_input_event_mode_e event_mode;             ///< Input Event Mode
    uint32_t count;                                ///< Capture Mode Count
} pwm_input_config_t;

typedef enum {
    PWM_CAPTURE_EVENT_COUNT = 0,                   ///< Capture Count Event
    PWM_CAPTURE_EVENT_TIME  = 1,                   ///< Capture Time Event
    PWM_TIMER_EVENT_TIMEOUT = 2                    ///< Timer Timeout Event
} pwm_event_e;

typedef void (*pwm_event_cb_t)(int32_t ch, pwm_event_e event, uint32_t val);

/**
  \brief       Initialize PWM Interface. 1. Initializes the resources needed for the PWM interface 2.registers event callback function
  \param[in]   idx pwm idx
  \return      handle pwm handle to operate.
*/
pwm_handle_t csi_pwm_initialize(uint32_t idx);

/**
  \brief       De-initialize PWM Interface. stops operation and releases the software resources used by the interface
  \param[in]   handle pwm handle to operate.
*/
void csi_pwm_uninitialize(pwm_handle_t handle);
/**
  \brief       control pwm power.
  \param[in]   handle  pwm handle to operate.
  \param[in]   state   power state.\ref csi_power_stat_e.
  \return      error code
*/
int32_t csi_pwm_power_control(pwm_handle_t handle, csi_power_stat_e state);

/**
  \brief       config pwm mode.
  \param[in]   handle           pwm handle to operate.
  \param[in]   channel          channel num.
  \param[in]   period_us        the PWM period in us
  \param[in]   pulse_width_us   the PMW pulse width in us
  \return      error code
*/
int32_t csi_pwm_config(pwm_handle_t handle,
                       uint8_t channel,
                       uint32_t period_us,
                       uint32_t pulse_width_us);

/**
  \brief       start generate pwm signal.
  \param[in]   handle   pwm handle to operate.
  \param[in]   channel  channel num.
*/
void csi_pwm_start(pwm_handle_t handle, uint8_t channel);

/**
  \brief       stop generate pwm signal.
  \param[in]   handle   pwm handle to operate.
  \param[in]   channel  channel num.
*/
void csi_pwm_stop(pwm_handle_t handle, uint8_t channel);

/**
  \brief       config pwm clock division.
  \param[in]   handle   pwm handle to operate.
  \param[in]   channel  channel num.
  \param[in]   div      clock div.
*/
void drv_pwm_config_clockdiv(pwm_handle_t handle, uint8_t channel, uint32_t div);

/**
  \brief       get pwm clock division.
  \param[in]   handle   pwm handle to operate.
  \param[in]   channel  channel num.
  \return      clock div.
*/
uint32_t drv_pwm_get_clockdiv(pwm_handle_t handle, uint8_t channel);

/**
  \brief       config pwm clock division.
  \param[in]   handle   pwm handle to operate.
  \param[in]   channel  channel num.
  \param[in]   cb_event event callback.
*/
void drv_pwm_config_cb(pwm_handle_t handle, uint8_t channel, pwm_event_cb_t cb_event);

/**
  \brief       set pwm timeout.
  \param[in]   handle pwm handle to operate.
  \param[in]   channel  channel num.
  \param[in]   timeout the timeout value in microseconds(us).
*/
void drv_pwm_timer_set_timeout(pwm_handle_t handle, uint8_t channel, uint32_t timeout);

/**
  \brief       start pwm timer.
  \param[in]   handle pwm handle to operate.
  \param[in]   channel  chnnel num.
*/
void drv_pwm_timer_start(pwm_handle_t handle, uint8_t channel);

/**
  \brief       stop pWM timer.
  \param[in]   handle pwm handle to operate.
  \param[in]   channel  chnnel num.
*/
void drv_pwm_timer_stop(pwm_handle_t handle, uint8_t channel);

/**
  \brief       get pwm timer current value
  \param[in]   handle pwm handle to operate.
  \param[in]   channel   channel num.
  \param[out]  value     timer current value
*/
void drv_pwm_timer_get_current_value(pwm_handle_t handle, uint8_t channel, uint32_t *value);

/**
  \brief       get pwm timer reload value
  \param[in]   handle pwm handle to operate.
  \param[in]   channel   channel num.
  \param[out]  value    timer reload value
*/
void drv_pwm_timer_get_load_value(pwm_handle_t handle, uint8_t channel, uint32_t *value);

/**
  \brief       config pwm capture mode.
  \param[in]   handle   pwm handle to operate.
  \param[in]   channel  channel num.
  \param[in]   config   capture config.
*/
void drv_pwm_capture_config(pwm_handle_t handle, uint8_t channel, pwm_input_config_t *config);

/**
  \brief       start pwm capture.
  \param[in]   handle   pwm handle to operate.
  \param[in]   channel  channel num.
*/
void drv_pwm_capture_start(pwm_handle_t handle, uint8_t channel);

/**
  \brief       stop pwm capture.
  \param[in]   handle   pwm handle to operate.
  \param[in]   channel  channel num.
*/
void drv_pwm_capture_stop(pwm_handle_t handle, uint8_t channel);

#ifdef __cplusplus
}
#endif

#endif /* _CSI_PWM_H_ */
