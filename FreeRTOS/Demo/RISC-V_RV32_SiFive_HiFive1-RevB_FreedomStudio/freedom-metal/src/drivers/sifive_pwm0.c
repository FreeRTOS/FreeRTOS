/* Copyright 2020 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/machine/platform.h>

#ifdef METAL_SIFIVE_PWM0
#include <metal/clock.h>
#include <metal/compiler.h>
#include <metal/drivers/sifive_gpio0.h>
#include <metal/drivers/sifive_pwm0.h>
#include <metal/io.h>
#include <metal/machine.h>
#include <metal/time.h>
#include <stdio.h>

/* Register fields */
#define METAL_PWMCFG_STICKY (1UL << 8)
#define METAL_PWMCFG_ZEROCMP (1UL << 9)
#define METAL_PWMCFG_DEGLITCH (1UL << 10)
#define METAL_PWMCFG_ENALWAYS (1UL << 12)
#define METAL_PWMCFG_ENONESHOT (1UL << 13)
#define METAL_PWMCFG_CMPCENTER(x) (1UL << (16 + x))
#define METAL_PWMCFG_CMPIP(x) (1UL << (28 + x))
#define METAL_SIFIVE_PWM0_PWMCMP(x) (METAL_SIFIVE_PWM0_PWMCMP0 + (x * 4))

/* Macros to access registers */
#define METAL_PWM_REG(offset) ((base + offset))
#define METAL_PWM_REGW(offset)                                                 \
    (__METAL_ACCESS_ONCE((__metal_io_u32 *)METAL_PWM_REG(offset)))

/* Macro to get PWM compare count */
#define METAL_PWM_GETCMPVAL(duty) (duty * pwm->count_val) / 100U
/* Max duty cycle value */
#define METAL_PWM_MAXDUTY 100UL
/* Max pre-scalar value */
#define METAL_PWM_MAXPRESCAL 15UL

/* Check endianess */
#if __BYTE_ORDER__ != __ORDER_LITTLE_ENDIAN__
#error *** Unsupported endianess ***
#endif

#if (METAL_MAX_PWM0_NCMP > METAL_MAX_PWM_CHANNELS)
#error *** METAL_MAX_PWM_CHANNELS exceeded ***
#endif

/* Return values */
#define METAL_PWM_RET_OK 0
#define METAL_PWM_RET_ERR -1

static void pre_rate_change_callback(void *priv) {
    struct metal_pwm *gpwm = priv;
    /* Disable active PWM instance. */
    gpwm->vtable->stop(gpwm, 0);
}

static void post_rate_change_callback(void *priv) {
    struct __metal_driver_sifive_pwm0 *pwm = priv;
    struct metal_pwm *gpwm = priv;
    unsigned long base = __metal_driver_sifive_pwm0_control_base(gpwm);
    unsigned int cmp_count = __metal_driver_sifive_pwm0_comparator_count(gpwm);
    unsigned int idx = 0;
    unsigned int duty;

    /* Check if PWM frequency was set */
    if (pwm->freq != 0) {
        /* Set frequency after clock rate change */
        gpwm->vtable->set_freq(gpwm, 0, pwm->freq);

        /* Set duty cycle after clock rate change */
        while (++idx < cmp_count) {
            duty = pwm->duty[idx];
            if (duty != 0) {
                METAL_PWM_REGW(METAL_SIFIVE_PWM0_PWMCMP(idx)) =
                    METAL_PWM_GETCMPVAL(duty);
            }
        }
    }
}

static int __metal_driver_sifive_pwm0_enable(struct metal_pwm *gpwm) {
    struct __metal_driver_sifive_gpio0 *pinmux =
        __metal_driver_sifive_pwm0_pinmux(gpwm);
    unsigned long base = __metal_driver_sifive_pwm0_control_base(gpwm);
    struct __metal_driver_sifive_pwm0 *pwm = (void *)gpwm;
    int ret = METAL_PWM_RET_ERR;

    if (base != 0) {

        if ((pinmux != NULL) && (gpwm != NULL)) {
            /* Configure PWM I/O pins */
            long pinmux_output_selector =
                __metal_driver_sifive_pwm0_pinmux_output_selector(gpwm);
            long pinmux_source_selector =
                __metal_driver_sifive_pwm0_pinmux_source_selector(gpwm);

            pinmux->gpio.vtable->enable_io((struct metal_gpio *)pinmux,
                                           pinmux_output_selector,
                                           pinmux_source_selector);
        }

        /* Initialize default values */
        pwm->max_count =
            (1UL << __metal_driver_sifive_pwm0_compare_width(gpwm)) - 1;
        pwm->freq = 0;
        pwm->count_val = 0;
        METAL_PWM_REGW(METAL_SIFIVE_PWM0_PWMCFG) = 0;
        ret = METAL_PWM_RET_OK;
    }
    return ret;
}

static int __metal_driver_sifive_pwm0_disable(struct metal_pwm *gpwm) {
    struct __metal_driver_sifive_gpio0 *pinmux =
        __metal_driver_sifive_pwm0_pinmux(gpwm);
    int ret = METAL_PWM_RET_ERR;

    if (gpwm != NULL) {

        if (pinmux != NULL) {
            /* Disable PWM I/O pins */
            long pinmux_source_selector =
                __metal_driver_sifive_pwm0_pinmux_source_selector(gpwm);
            pinmux->gpio.vtable->disable_io((struct metal_gpio *)pinmux,
                                            pinmux_source_selector);
        }

        ret = METAL_PWM_RET_OK;
    }
    return ret;
}

static int __metal_driver_sifive_pwm0_set_freq(struct metal_pwm *gpwm,
                                               unsigned int idx,
                                               unsigned int freq) {
    struct metal_clock *clock = __metal_driver_sifive_pwm0_clock(gpwm);
    unsigned long base = __metal_driver_sifive_pwm0_control_base(gpwm);
    unsigned int cmp_count = __metal_driver_sifive_pwm0_comparator_count(gpwm);
    struct __metal_driver_sifive_pwm0 *pwm = (void *)gpwm;
    unsigned int clock_rate;
    unsigned int count;
    unsigned int prescale = 0;
    int ret = METAL_PWM_RET_ERR;

    if ((clock != NULL) && (gpwm != NULL) && (idx < cmp_count)) {
        clock_rate = clock->vtable->get_rate_hz(clock);
        /* Register clock rate change call-backs */
        if (pwm->freq == 0) {
            pwm->pre_rate_change_callback.callback = &pre_rate_change_callback;
            pwm->pre_rate_change_callback.priv = pwm;
            metal_clock_register_pre_rate_change_callback(
                clock, &(pwm->pre_rate_change_callback));

            pwm->post_rate_change_callback.callback =
                &post_rate_change_callback;
            pwm->post_rate_change_callback.priv = pwm;
            metal_clock_register_post_rate_change_callback(
                clock, &(pwm->post_rate_change_callback));
        }

        /* Calculate count value for given PWM frequency */
        do {
            count = (clock_rate / (1UL << prescale)) / freq;
        } while ((count > pwm->max_count) &&
                 (prescale++ < METAL_PWM_MAXPRESCAL));

        pwm->freq = (clock_rate / (1UL << prescale)) / count;
        pwm->count_val = --count;

        /* Update values into registers */
        METAL_PWM_REGW(METAL_SIFIVE_PWM0_PWMCMP0) = count;
        METAL_PWM_REGW(METAL_SIFIVE_PWM0_PWMCFG) |= (prescale & 0x0FUL);
        ret = METAL_PWM_RET_OK;

#if defined(METAL_PWM_DEBUG)
        printf("PWM requested freq:%u set freq:%u \n", freq, pwm->freq);
        printf("CPU Clk:%u Prescale:%u Count:%u \n", clock_rate, prescale,
               count);
#endif
    }
    return ret;
}

static int
__metal_driver_sifive_pwm0_set_duty(struct metal_pwm *gpwm, unsigned int idx,
                                    unsigned int duty,
                                    metal_pwm_phase_correct_t phase_corr) {
    struct __metal_driver_sifive_pwm0 *pwm = (void *)gpwm;
    unsigned long base = __metal_driver_sifive_pwm0_control_base(gpwm);
    unsigned int cmp_count = __metal_driver_sifive_pwm0_comparator_count(gpwm);
    int ret = METAL_PWM_RET_ERR;

    /* Check if duty value is within limits, duty cycle cannot be set for
     * PWMCMP0 */
    if ((idx > 0) && (idx < cmp_count) && (duty <= METAL_PWM_MAXDUTY)) {
        /* Calculate PWM compare count value for given duty cycle */
        METAL_PWM_REGW(METAL_SIFIVE_PWM0_PWMCMP(idx)) =
            METAL_PWM_GETCMPVAL(duty);
        pwm->duty[idx] = duty;

        /* Enable / Disable phase correct PWM mode */
        if (phase_corr == METAL_PWM_PHASE_CORRECT_ENABLE) {
            METAL_PWM_REGW(METAL_SIFIVE_PWM0_PWMCFG) |=
                METAL_PWMCFG_CMPCENTER(idx);
        } else {
            METAL_PWM_REGW(METAL_SIFIVE_PWM0_PWMCFG) &=
                ~METAL_PWMCFG_CMPCENTER(idx);
        }
        ret = METAL_PWM_RET_OK;
    }
    return ret;
}

static unsigned int __metal_driver_sifive_pwm0_get_duty(struct metal_pwm *gpwm,
                                                        unsigned int idx) {
    struct __metal_driver_sifive_pwm0 *pwm = (void *)gpwm;
    unsigned int cmp_count = __metal_driver_sifive_pwm0_comparator_count(gpwm);
    unsigned int duty = 0;

    /* Check for valid parameters and get configured duty cycle value */
    if ((pwm != NULL) && (idx > 0) && (idx < cmp_count)) {
        duty = pwm->duty[idx];
    }
    return duty;
}

static unsigned int __metal_driver_sifive_pwm0_get_freq(struct metal_pwm *gpwm,
                                                        unsigned int idx) {
    struct __metal_driver_sifive_pwm0 *pwm = (void *)gpwm;
    unsigned int freq = 0;

    (void)idx; /* Unused parameter, no support for per channel frequency */

    /* Check for valid parameters and get configured PWM frequency value */
    if (pwm != NULL) {
        freq = pwm->freq;
    }
    return freq;
}

static int __metal_driver_sifive_pwm0_trigger(struct metal_pwm *gpwm,
                                              unsigned int idx,
                                              metal_pwm_run_mode_t mode) {
    unsigned long base = __metal_driver_sifive_pwm0_control_base(gpwm);
    int ret = METAL_PWM_RET_ERR;

    (void)idx; /* Unused parameter,for later use */

    if (base != 0) {
        /* Configure for requested PWM run mode */
        if (mode == METAL_PWM_CONTINUOUS) {
            METAL_PWM_REGW(METAL_SIFIVE_PWM0_PWMCFG) |= METAL_PWMCFG_DEGLITCH |
                                                        METAL_PWMCFG_ZEROCMP |
                                                        METAL_PWMCFG_ENALWAYS;
        } else {
            METAL_PWM_REGW(METAL_SIFIVE_PWM0_PWMCFG) |= METAL_PWMCFG_DEGLITCH |
                                                        METAL_PWMCFG_ZEROCMP |
                                                        METAL_PWMCFG_ENONESHOT;
        }
        ret = METAL_PWM_RET_OK;
    }
    return ret;
}

static int __metal_driver_sifive_pwm0_stop(struct metal_pwm *gpwm,
                                           unsigned int idx) {
    unsigned long base = __metal_driver_sifive_pwm0_control_base(gpwm);
    int ret = METAL_PWM_RET_ERR;

    (void)idx; /* Unused parameter,for later use */

    if (base != 0) {
        /* Disable always running mode */
        METAL_PWM_REGW(METAL_SIFIVE_PWM0_PWMCFG) &= ~METAL_PWMCFG_ENALWAYS;
        ret = METAL_PWM_RET_OK;
    }
    return ret;
}

static int
__metal_driver_sifive_pwm0_cfg_interrupt(struct metal_pwm *gpwm,
                                         metal_pwm_interrupt_t flag) {
    unsigned long base = __metal_driver_sifive_pwm0_control_base(gpwm);
    int ret = METAL_PWM_RET_ERR;

    if (base != 0) {
        if (flag == METAL_PWM_INTERRUPT_ENABLE) {
            /* Enable sticky bit, to make sure interrupts are not forgotten */
            METAL_PWM_REGW(METAL_SIFIVE_PWM0_PWMCFG) |= METAL_PWMCFG_STICKY;
        } else {
            METAL_PWM_REGW(METAL_SIFIVE_PWM0_PWMCFG) &= ~METAL_PWMCFG_STICKY;
        }
        ret = METAL_PWM_RET_OK;
    }
    return ret;
}

static int __metal_driver_sifive_pwm0_clr_interrupt(struct metal_pwm *gpwm,
                                                    unsigned int idx) {
    unsigned long base = __metal_driver_sifive_pwm0_control_base(gpwm);
    unsigned int cmp_count = __metal_driver_sifive_pwm0_comparator_count(gpwm);
    int ret = METAL_PWM_RET_ERR;

    if ((base != 0) && (idx < cmp_count)) {
        /* Clear interrupt pending bit for given PWM comparator */
        METAL_PWM_REGW(METAL_SIFIVE_PWM0_PWMCFG) &= ~METAL_PWMCFG_CMPIP(idx);
        ret = METAL_PWM_RET_OK;
    }
    return ret;
}

static struct metal_interrupt *
__metal_driver_sifive_pwm0_interrupt_controller(struct metal_pwm *gpwm) {
    return __metal_driver_sifive_pwm0_interrupt_parent(gpwm);
}

static int __metal_driver_sifive_pwm0_interrupt_id(struct metal_pwm *gpwm,
                                                   unsigned int idx) {
    return __metal_driver_sifive_pwm0_interrupt_lines(gpwm, idx);
}

__METAL_DEFINE_VTABLE(__metal_driver_vtable_sifive_pwm0) = {
    .pwm.enable = __metal_driver_sifive_pwm0_enable,
    .pwm.disable = __metal_driver_sifive_pwm0_disable,
    .pwm.set_duty = __metal_driver_sifive_pwm0_set_duty,
    .pwm.set_freq = __metal_driver_sifive_pwm0_set_freq,
    .pwm.get_duty = __metal_driver_sifive_pwm0_get_duty,
    .pwm.get_freq = __metal_driver_sifive_pwm0_get_freq,
    .pwm.trigger = __metal_driver_sifive_pwm0_trigger,
    .pwm.stop = __metal_driver_sifive_pwm0_stop,
    .pwm.cfg_interrupt = __metal_driver_sifive_pwm0_cfg_interrupt,
    .pwm.clr_interrupt = __metal_driver_sifive_pwm0_clr_interrupt,
    .pwm.get_interrupt_controller =
        __metal_driver_sifive_pwm0_interrupt_controller,
    .pwm.get_interrupt_id = __metal_driver_sifive_pwm0_interrupt_id,
};

#endif /* METAL_SIFIVE_PWM0 */

typedef int no_empty_translation_units;
