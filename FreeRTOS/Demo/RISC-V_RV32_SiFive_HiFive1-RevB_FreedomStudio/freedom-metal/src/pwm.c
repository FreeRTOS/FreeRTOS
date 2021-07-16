/* Copyright 2020 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/machine.h>
#include <metal/pwm.h>

extern inline int metal_pwm_enable(struct metal_pwm *pwm);
extern inline int metal_pwm_disable(struct metal_pwm *pwm);
extern inline int metal_pwm_set_freq(struct metal_pwm *pwm, unsigned int idx,
                                     unsigned int freq);
extern inline int metal_pwm_set_duty(struct metal_pwm *pwm, unsigned int idx,
                                     unsigned int duty,
                                     metal_pwm_phase_correct_t phase_corr);
extern inline unsigned int metal_pwm_get_duty(struct metal_pwm *pwm,
                                              unsigned int idx);
extern inline unsigned int metal_pwm_get_freq(struct metal_pwm *pwm,
                                              unsigned int idx);
extern inline int metal_pwm_trigger(struct metal_pwm *pwm, unsigned int idx,
                                    metal_pwm_run_mode_t mode);
extern inline int metal_pwm_stop(struct metal_pwm *pwm, unsigned int idx);
extern inline int metal_pwm_cfg_interrupt(struct metal_pwm *pwm,
                                          metal_pwm_interrupt_t flag);
extern inline int metal_pwm_clr_interrupt(struct metal_pwm *pwm,
                                          unsigned int idx);
extern struct metal_interrupt *
metal_pwm_interrupt_controller(struct metal_pwm *pwm);
extern int metal_pwm_get_interrupt_id(struct metal_pwm *pwm, unsigned int idx);

struct metal_pwm *metal_pwm_get_device(unsigned int device_num) {
#if __METAL_DT_MAX_PWMS > 0
    if (device_num < __METAL_DT_MAX_PWMS) {
        return (struct metal_pwm *)__metal_pwm_table[device_num];
    }
#endif
    return NULL;
}
