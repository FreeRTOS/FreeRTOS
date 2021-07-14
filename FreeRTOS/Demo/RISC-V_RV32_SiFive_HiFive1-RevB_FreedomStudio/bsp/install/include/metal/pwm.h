/* Copyright 2020 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__PWM_H
#define METAL__PWM_H

/*! @brief Enums for PWM running modes. */
typedef enum {
    METAL_PWM_CONTINUOUS = 0,
    METAL_PWM_ONE_SHOT = 1
} metal_pwm_run_mode_t;

/*! @brief Enums for Phase correct PWM. */
typedef enum {
    METAL_PWM_PHASE_CORRECT_DISABLE = 0,
    METAL_PWM_PHASE_CORRECT_ENABLE = 1,
} metal_pwm_phase_correct_t;

/*! @brief Enums for Interrupts enable/disable. */
typedef enum {
    METAL_PWM_INTERRUPT_DISABLE = 0,
    METAL_PWM_INTERRUPT_ENABLE = 1,
} metal_pwm_interrupt_t;

struct metal_pwm;

/*! @brief vtable for PWM. */
struct metal_pwm_vtable {
    int (*enable)(struct metal_pwm *pwm);
    int (*disable)(struct metal_pwm *pwm);
    int (*set_freq)(struct metal_pwm *pwm, unsigned int idx, unsigned int freq);
    int (*set_duty)(struct metal_pwm *pwm, unsigned int idx, unsigned int duty,
                    metal_pwm_phase_correct_t phase_corr);
    unsigned int (*get_duty)(struct metal_pwm *pwm, unsigned int idx);
    unsigned int (*get_freq)(struct metal_pwm *pwm, unsigned int idx);
    int (*trigger)(struct metal_pwm *pwm, unsigned int idx,
                   metal_pwm_run_mode_t mode);
    int (*stop)(struct metal_pwm *pwm, unsigned int idx);
    int (*cfg_interrupt)(struct metal_pwm *pwm, metal_pwm_interrupt_t flag);
    int (*clr_interrupt)(struct metal_pwm *pwm, unsigned int idx);
    struct metal_interrupt *(*get_interrupt_controller)(struct metal_pwm *pwm);
    int (*get_interrupt_id)(struct metal_pwm *pwm, unsigned int idx);
};

/*! @brief A handle for a PWM device. */
struct metal_pwm {
    const struct metal_pwm_vtable *vtable;
};

/*! @brief Gets a PWM device handle.
 * @param device_num The index of the desired PWM device.
 * @return A handle to the PWM device, or NULL if the device does not exist.*/
struct metal_pwm *metal_pwm_get_device(unsigned int device_num);

/*! @brief Enables PWM operation.
 * @param pwm The handle for the PWM device to initialize.
 * @return 0 If no error.*/
inline int metal_pwm_enable(struct metal_pwm *pwm) {
    return pwm->vtable->enable(pwm);
}

/*! @brief Disables PWM operation.
 * @param pwm The handle for the PWM device to be disabled.
 * @return 0 If no error.*/
inline int metal_pwm_disable(struct metal_pwm *pwm) {
    return pwm->vtable->disable(pwm);
}

/*! @brief Sets frequency in Hz for a given PWM instance.
 * @param pwm PWM device handle.
 * @param idx PWM channel id.
 * @param freq PWM frequency in Hz.
 * @return 0 If no error.*/
inline int metal_pwm_set_freq(struct metal_pwm *pwm, unsigned int idx,
                              unsigned int freq) {
    return pwm->vtable->set_freq(pwm, idx, freq);
}

/*! @brief Sets duty cycle in percent values [0 - 100] for a given PWM instance.
 * Phase correct mode provides center aligned PWM waveform output.
 * @param pwm PWM device handle.
 * @param idx PWM channel id.
 * @param duty PWM duty cycle value.
 * @param phase_corr Enable / Disable phase correct mode.
 * @return 0 If no error.*/
inline int metal_pwm_set_duty(struct metal_pwm *pwm, unsigned int idx,
                              unsigned int duty,
                              metal_pwm_phase_correct_t phase_corr) {
    return pwm->vtable->set_duty(pwm, idx, duty, phase_corr);
}

/*! @brief Gets duty cycle in percent values [0 - 100] for a given PWM instance.
 * @param pwm PWM device handle.
 * @param idx PWM channel id.
 * @return PWM duty cycle value.*/
inline unsigned int metal_pwm_get_duty(struct metal_pwm *pwm,
                                       unsigned int idx) {
    return pwm->vtable->get_duty(pwm, idx);
}

/*! @brief Gets frequency in Hz for a given PWM instance.
 * @param pwm PWM device handle.
 * @param idx PWM channel id.
 * @return PWM frequency in Hz.*/
inline unsigned int metal_pwm_get_freq(struct metal_pwm *pwm,
                                       unsigned int idx) {
    return pwm->vtable->get_freq(pwm, idx);
}

/*! @brief Starts a PWM instance in selected run mode (continuous/one shot).
 * @param pwm PWM device handle.
 * @param idx PWM channel id.
 * @return 0 If no error.*/
inline int metal_pwm_trigger(struct metal_pwm *pwm, unsigned int idx,
                             metal_pwm_run_mode_t mode) {
    return pwm->vtable->trigger(pwm, idx, mode);
}

/*! @brief Stops a running PWM instance in continuous mode.
 * @param pwm PWM device handle.
 * @param idx PWM channel id.
 * @return 0 If no error.*/
inline int metal_pwm_stop(struct metal_pwm *pwm, unsigned int idx) {
    return pwm->vtable->stop(pwm, idx);
}

/*! @brief Enable or Disable PWM interrupts.
 * @param pwm PWM device handle.
 * @param flag PWM interrupt enable flag.
 * @return 0 If no error.*/
inline int metal_pwm_cfg_interrupt(struct metal_pwm *pwm,
                                   metal_pwm_interrupt_t flag) {
    return pwm->vtable->cfg_interrupt(pwm, flag);
}

/*! @brief Clears pending interrupt flags.
 * @param pwm PWM device handle.
 * @param idx PWM channel id.
 * @return 0 If no error.*/
inline int metal_pwm_clr_interrupt(struct metal_pwm *pwm, unsigned int idx) {
    return pwm->vtable->clr_interrupt(pwm, idx);
}

/*! @brief Get the interrupt controller of the PWM peripheral.
 * The interrupt controller must be initialized before any interrupts can be
 * registered or enabled with it.
 * @param pwm PWM device handle.
 * @return The handle for the PWM interrupt controller.*/
inline struct metal_interrupt *
metal_pwm_interrupt_controller(struct metal_pwm *pwm) {
    return pwm->vtable->get_interrupt_controller(pwm);
}

/*! @brief Get the interrupt ID of the PWM peripheral.
 * @param pwm PWM device handle.
 * @param idx PWM channel id.
 * @return The PWM interrupt id.*/
inline int metal_pwm_get_interrupt_id(struct metal_pwm *pwm, unsigned int idx) {
    return pwm->vtable->get_interrupt_id(pwm, idx);
}

#endif
