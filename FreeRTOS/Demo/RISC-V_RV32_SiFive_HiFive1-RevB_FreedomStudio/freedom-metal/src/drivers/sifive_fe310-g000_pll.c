/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/machine/platform.h>

#ifdef METAL_SIFIVE_FE310_G000_PLL

#include <limits.h>
#include <stdio.h>

#include <metal/init.h>
#include <metal/machine.h>
#include <metal/machine/platform.h>

#include <metal/drivers/sifive_fe310-g000_pll.h>
#include <stdlib.h>

#define PLL_R 0x00000007UL
#define PLL_F 0x000003F0UL
#define PLL_Q 0x00000C00UL
#define PLL_SEL 0x00010000UL
#define PLL_REFSEL 0x00020000UL
#define PLL_BYPASS 0x00040000UL
#define PLL_LOCK 0x80000000UL

#define DIV_DIV 0x0000003FUL
#define DIV_1 0x00000100UL

#define PLL_R_SHIFT(r) ((r << 0) & PLL_R)
#define PLL_F_SHIFT(f) ((f << 4) & PLL_F)
#define PLL_Q_SHIFT(q) ((q << 10) & PLL_Q)
#define PLL_DIV_SHIFT(d) ((d << 0) & DIV_DIV)

struct pll_config_t {
    unsigned long multiplier;
    unsigned long divisor;
    unsigned long min_input_rate;
    unsigned long max_input_rate;
    unsigned long r;
    unsigned long f;
    unsigned long q;
    long d; /* < 0 if disabled */
};

static const struct pll_config_t pll_configs[] = {
    /*
     * multiplier
     * ^  divisor
     * |  ^      min_input_rate
     * |  |      ^        max_input_rate
     * |  |      |        ^      r
     * |  |      |        |      ^   f
     * |  |      |        |      |   ^  q
     * |  |      |        |      |   |  ^   d
     * |  |      |        |      |   |  |   ^
     * |  |      |        |      |   |  |   | */
    {1, 32, 12000000, 24000000, 1, 31, 3, 63},
    {1, 32, 24000000, 48000000, 3, 31, 2, 63},
    {1, 16, 6000000, 12000000, 0, 31, 3, 63},
    {1, 16, 12000000, 24000000, 1, 31, 2, 63},
    {1, 16, 24000000, 48000000, 3, 31, 2, 31},
    {1, 8, 6000000, 12000000, 0, 31, 3, 31},
    {1, 8, 12000000, 24000000, 1, 31, 2, 31},
    {1, 8, 24000000, 48000000, 3, 31, 2, 15},
    {1, 4, 6000000, 12000000, 0, 31, 3, 15},
    {1, 4, 12000000, 24000000, 1, 31, 2, 15},
    {1, 4, 24000000, 48000000, 3, 31, 2, 7},
    {1, 2, 6000000, 12000000, 0, 31, 2, 15},
    {1, 2, 12000000, 24000000, 1, 31, 1, 15},
    {1, 2, 24000000, 48000000, 3, 31, 1, 7},
    {2, 1, 6000000, 12000000, 0, 31, 1, 7},
    {2, 1, 12000000, 24000000, 1, 31, 1, 3},
    {2, 1, 24000000, 48000000, 3, 31, 3, -1},
    {4, 1, 6000000, 12000000, 0, 31, 3, 0},
    {4, 1, 12000000, 24000000, 1, 31, 3, -1},
    {4, 1, 24000000, 48000000, 3, 31, 2, -1},
    {6, 1, 6000000, 10666666, 0, 35, 1, 2},
    {6, 1, 10666666, 12000000, 0, 23, 3, -1},
    {6, 1, 12000000, 16000000, 1, 47, 3, -1},
    {6, 1, 16000000, 18000000, 1, 23, 2, -1},
    {6, 1, 18000000, 21333333, 2, 35, 2, -1},
    {8, 1, 6000000, 12000000, 0, 31, 3, -1},
    {8, 1, 12000000, 24000000, 1, 31, 2, -1},
    {8, 1, 24000000, 48000000, 3, 31, 1, -1},
    {10, 1, 6000000, 9600000, 0, 39, 3, -1},
    {10, 1, 9600000, 12000000, 0, 19, 2, -1},
    {10, 1, 12000000, 19200000, 1, 39, 2, -1},
    {10, 1, 19200000, 24000000, 1, 19, 1, -1},
    {10, 1, 24000000, 38400000, 3, 39, 1, -1},
    {12, 1, 6000000, 8000000, 0, 47, 3, -1},
    {12, 1, 8000000, 12000000, 0, 23, 2, -1},
    {12, 1, 12000000, 16000000, 1, 47, 2, -1},
    {12, 1, 16000000, 24000000, 1, 23, 1, -1},
    {12, 1, 24000000, 30000000, 3, 47, 1, -1},
    {12, 1, 30000000, 32000000, 3, 47, 1, -1},
    {14, 1, 6000000, 6857142, 0, 55, 3, -1},
    {14, 1, 6857143, 12000000, 0, 27, 2, -1},
    {14, 1, 12000000, 13714285, 1, 55, 2, -1},
    {14, 1, 13714286, 24000000, 1, 27, 1, -1},
    {14, 1, 24000000, 27428571, 3, 55, 1, -1},
    {16, 1, 6000000, 12000000, 0, 31, 2, -1},
    {16, 1, 12000000, 24000000, 1, 31, 1, -1},
    {18, 1, 6000000, 10666666, 0, 35, 2, -1},
    {18, 1, 10666667, 12000000, 0, 17, 1, -1},
    {18, 1, 12000000, 21333333, 1, 35, 1, -1},
    {20, 1, 6000000, 9600000, 0, 39, 2, -1},
    {20, 1, 9600000, 12000000, 0, 19, 1, -1},
    {20, 1, 12000000, 19200000, 1, 39, 1, -1},
    {22, 1, 6000000, 8727272, 0, 43, 2, -1},
    {22, 1, 8727273, 12000000, 0, 21, 1, -1},
    {22, 1, 12000000, 17454545, 1, 43, 1, -1},
    {24, 1, 6000000, 8000000, 0, 47, 2, -1},
    {24, 1, 8000000, 12000000, 0, 23, 1, -1},
    {24, 1, 12000000, 16000000, 1, 47, 1, -1},
    {26, 1, 6000000, 7384615, 0, 51, 2, -1},
    {26, 1, 7384616, 12000000, 0, 25, 1, -1},
    {26, 1, 12000000, 14768230, 1, 51, 1, -1},
    {28, 1, 6000000, 6857142, 0, 55, 2, -1},
    {28, 1, 6857143, 12000000, 0, 27, 1, -1},
    {28, 1, 12000000, 13714285, 1, 55, 1, -1},
    {30, 1, 6000000, 6400000, 0, 59, 2, -1},
    {30, 1, 6400000, 12000000, 0, 29, 1, -1},
    {30, 1, 12000000, 12800000, 1, 59, 1, -1},
    {32, 1, 6000000, 12000000, 0, 31, 1, -1}};

#define PLL_CONFIG_NOT_VALID -1

void __metal_driver_sifive_fe310_g000_pll_init(
    struct __metal_driver_sifive_fe310_g000_pll *pll);

/* Given the rate of the PLL input frequency and a PLL configuration, what
 * will the resulting PLL output frequency be?
 * Arguments:
 *  - pll_input_rate the PLL input frequency in hertz
 *  - config the PLL configuration
 * Returns:
 *  - PLL_CONFIG_NOT_VALID if the configuration is not valid for the input
 * frequency
 *  - the output frequency, in hertz */
static long get_pll_config_freq(unsigned long pll_input_rate,
                                const struct pll_config_t *config) {
    if (pll_input_rate < config->min_input_rate ||
        pll_input_rate > config->max_input_rate)
        return PLL_CONFIG_NOT_VALID;

    return pll_input_rate * config->multiplier / config->divisor;
}

#ifdef __METAL_DT_SIFIVE_FE310_G000_PLL_HANDLE

METAL_CONSTRUCTOR(metal_sifive_fe310_g000_pll_init) {
    long init_rate = __metal_driver_sifive_fe310_g000_pll_init_rate();
    /* If the PLL init_rate is zero, don't initialize the PLL */
    if (init_rate != 0)
        __metal_driver_sifive_fe310_g000_pll_init(
            __METAL_DT_SIFIVE_FE310_G000_PLL_HANDLE);
}

#endif /* __METAL_DT_SIFIVE_FE310_G000__PLL_HANDLE */

void __metal_driver_sifive_fe310_g000_pll_init(
    struct __metal_driver_sifive_fe310_g000_pll *pll) {
    struct metal_clock *pllref =
        __metal_driver_sifive_fe310_g000_pll_pllref(&(pll->clock));
    long init_rate = __metal_driver_sifive_fe310_g000_pll_init_rate();
    long config_offset = __metal_driver_sifive_fe310_g000_pll_config_offset();
    long base = __metal_driver_sifive_fe310_g000_prci_base();

    __metal_io_u32 *pllcfg = (__metal_io_u32 *)(base + config_offset);

    /* If the PLL clock has had a _pre_rate_change_callback configured, call it
     */
    _metal_clock_call_all_callbacks(pll->clock._pre_rate_change_callback);

    /* If we're running off of the PLL, switch off before we start configuring
     * it*/
    if ((__METAL_ACCESS_ONCE(pllcfg) & PLL_SEL) != 0)
        __METAL_ACCESS_ONCE(pllcfg) &= ~(PLL_SEL);

    /* Make sure we're running off of the external oscillator for stability */
    if (pllref != NULL)
        __METAL_ACCESS_ONCE(pllcfg) |= PLL_REFSEL;

    /* Configure the PLL to run at the requested init frequency.
     * Using the vtable instead of the user API because we want to control
     * when the callbacks occur. */
    pll->clock.vtable->set_rate_hz(&(pll->clock), init_rate);

    /* If the PLL clock has had a rate_change_callback configured, call it */
    _metal_clock_call_all_callbacks(pll->clock._post_rate_change_callback);
}

long __metal_driver_sifive_fe310_g000_pll_get_rate_hz(
    const struct metal_clock *clock) {
    struct metal_clock *pllref =
        __metal_driver_sifive_fe310_g000_pll_pllref(clock);
    struct metal_clock *pllsel0 =
        __metal_driver_sifive_fe310_g000_pll_pllsel0(clock);
    long config_offset =
        __metal_driver_sifive_fe310_g000_pll_config_offset(clock);
    struct __metal_driver_sifive_fe310_g000_prci *config_base =
        __metal_driver_sifive_fe310_g000_pll_config_base(clock);
    long divider_offset =
        __metal_driver_sifive_fe310_g000_pll_divider_offset(clock);
    struct __metal_driver_sifive_fe310_g000_prci *divider_base =
        __metal_driver_sifive_fe310_g000_pll_divider_base(clock);
    const struct __metal_driver_vtable_sifive_fe310_g000_prci *vtable =
        __metal_driver_sifive_fe310_g000_prci_vtable();

    long cfg = vtable->get_reg(config_base, config_offset);
    long div = vtable->get_reg(divider_base, divider_offset);

    /* At the end of the PLL there's one big mux: it either selects the HFROSC
     * (bypassing the PLL entirely) or uses the PLL. */
    if (__METAL_GET_FIELD(cfg, PLL_SEL) == 0)
        return metal_clock_get_rate_hz(pllsel0);

    /* There's a clock mux before the PLL that selects between the HFROSC adn
     * the HFXOSC as the PLL's input clock. */
    long ref_hz = metal_clock_get_rate_hz(
        __METAL_GET_FIELD(cfg, PLL_REFSEL) ? pllref : pllsel0);

    /* It's possible to bypass the PLL, which is an internal bpyass.  This
     * still obays the PLL's input clock mu. */
    if (__METAL_GET_FIELD(cfg, PLL_BYPASS))
        return ref_hz;

    /* Logically the PLL is a three stage div-mul-div. */
    long div_r = __METAL_GET_FIELD(cfg, PLL_R) + 1;
    long mul_f = 2 * (__METAL_GET_FIELD(cfg, PLL_F) + 1);
    if (__METAL_GET_FIELD(cfg, PLL_Q) == 0)
        return -1;
    long div_q = 1 << __METAL_GET_FIELD(cfg, PLL_Q);

    /* In addition to the dividers inherent in the PLL, there's an additional
     * clock divider that lives after the PLL and lets us pick a more
     * interesting range of frequencies. */
    long pllout = (((ref_hz / div_r) * mul_f) / div_q);
    if (__METAL_GET_FIELD(div, DIV_1))
        return pllout;

    return pllout / (2 * (__METAL_GET_FIELD(div, DIV_DIV) + 1));
}

/* Find a valid configuration for the PLL which is closest to the desired
 * output frequency.
 * Arguments:
 *  - ref_hz PLL input frequency
 *  - rate desired PLL output frequency
 * Returns:
 *  -1 if no valid configuration is available
 *  the index into pll_configs of a valid configuration */
static int find_closest_config(long ref_hz, long rate) {
    int closest_index = -1;
    long closest_diff = LONG_MAX;

    /* We're probably trying for a fast output frequency, so start from
     * the high end of the configs. */
    for (int i = (sizeof(pll_configs) / sizeof(pll_configs[0])) - 1; i >= 0;
         i--) {
        long config_freq = get_pll_config_freq(ref_hz, &(pll_configs[i]));
        if (config_freq != PLL_CONFIG_NOT_VALID) {
            long freq_diff = labs(config_freq - rate);

            if (freq_diff < closest_diff) {
                closest_index = i;
                closest_diff = freq_diff;
            }
        }
    }

    return closest_index;
}

/* The PLL needs 100 usec to stabilize before we test PLL_LOCK. Since LFROSC
 * on all targets with the FE310-G000 PLL runs at 32768 Hz, we need to wait
 * at least
 *
 *   ceil(100 usec * 32768 ticks/sec * 1 sec / 1000000 usec) = 4 ticks
 *
 * of mtime before we test PLL_LOCK.
 *
 * TODO: Determine the mtime timebase at compile or runtime and use that
 * here.
 */
#define PLL_LOCK_WAIT_TICKS 4

/* Configure the PLL and wait for it to lock */
static void configure_pll(__metal_io_u32 *pllcfg, __metal_io_u32 *plloutdiv,
                          const struct pll_config_t *config) {
    __METAL_ACCESS_ONCE(pllcfg) &= ~(PLL_R);
    __METAL_ACCESS_ONCE(pllcfg) |= PLL_R_SHIFT(config->r);

    __METAL_ACCESS_ONCE(pllcfg) &= ~(PLL_F);
    __METAL_ACCESS_ONCE(pllcfg) |= PLL_F_SHIFT(config->f);

    __METAL_ACCESS_ONCE(pllcfg) &= ~(PLL_Q);
    __METAL_ACCESS_ONCE(pllcfg) |= PLL_Q_SHIFT(config->q);

    if (config->d < 0) {
        /* disable final divider */
        __METAL_ACCESS_ONCE(plloutdiv) |= DIV_1;

        __METAL_ACCESS_ONCE(plloutdiv) &= ~(DIV_DIV);
        __METAL_ACCESS_ONCE(plloutdiv) |= PLL_DIV_SHIFT(1);
    } else {
        __METAL_ACCESS_ONCE(plloutdiv) &= ~(DIV_1);

        __METAL_ACCESS_ONCE(plloutdiv) &= ~(DIV_DIV);
        __METAL_ACCESS_ONCE(plloutdiv) |= PLL_DIV_SHIFT(config->d);
    }

    __METAL_ACCESS_ONCE(pllcfg) &= ~(PLL_BYPASS);

    /* Wait for the PLL to stabilize before testing it for lock */
#ifdef __METAL_DT_RISCV_CLINT0_HANDLE
    unsigned long long mtime, mtime_end;
    __metal_driver_riscv_clint0_command_request(__METAL_DT_RISCV_CLINT0_HANDLE,
                                                METAL_TIMER_MTIME_GET, &mtime);
    mtime_end = mtime + PLL_LOCK_WAIT_TICKS;
    while (mtime <= mtime_end) {
        __metal_driver_riscv_clint0_command_request(
            __METAL_DT_RISCV_CLINT0_HANDLE, METAL_TIMER_MTIME_GET, &mtime);
    }
#elif __METAL_DT_RISCV_CLIC0_HANDLE
    unsigned long long mtime, mtime_end;
    __metal_driver_sifive_clic0_command_request(__METAL_DT_RISCV_CLIC0_HANDLE,
                                                METAL_TIMER_MTIME_GET, &mtime);
    mtime_end = mtime + PLL_LOCK_WAIT_TICKS;
    while (mtime <= mtime_end) {
        __metal_driver_sifive_clic0_command_request(
            __METAL_DT_RISCV_CLIC0_HANDLE, METAL_TIMER_MTIME_GET, &mtime);
    }
#else
#pragma message(                                                               \
    No handle for CLINT or CLIC found, PLL might race with lock signal !)
#endif

    /* Wait for PLL to lock */
    while ((__METAL_ACCESS_ONCE(pllcfg) & PLL_LOCK) == 0)
        ;
}

long __metal_driver_sifive_fe310_g000_pll_set_rate_hz(struct metal_clock *clock,
                                                      long rate) {
    struct metal_clock *pllref =
        __metal_driver_sifive_fe310_g000_pll_pllref(clock);
    struct metal_clock *pllsel0 =
        __metal_driver_sifive_fe310_g000_pll_pllsel0(clock);
    long config_offset =
        __metal_driver_sifive_fe310_g000_pll_config_offset(clock);
    long divider_offset =
        __metal_driver_sifive_fe310_g000_pll_divider_offset(clock);
    long base = __metal_driver_sifive_fe310_g000_prci_base();

    __metal_io_u32 *pllcfg = (__metal_io_u32 *)(base + config_offset);
    __metal_io_u32 *plloutdiv = (__metal_io_u32 *)(base + divider_offset);

    /* We can't modify the PLL if coreclk is driven by it, so switch it off */
    if (__METAL_ACCESS_ONCE(pllcfg) & PLL_SEL)
        __METAL_ACCESS_ONCE(pllcfg) &= ~(PLL_SEL);

    /* There's a clock mux before the PLL that selects between the HFROSC and
     * the HFXOSC as the PLL's input clock. */
    long ref_hz = metal_clock_get_rate_hz(
        __METAL_ACCESS_ONCE(pllcfg) & PLL_REFSEL ? pllref : pllsel0);

    /* if the desired rate is within 75%-125% of the input clock, bypass the PLL
     */
    if ((ref_hz * 3 / 4) <= rate && (ref_hz * 5 / 4) >= rate) {
        __METAL_ACCESS_ONCE(pllcfg) |= PLL_BYPASS;
    } else {
        int config_index = find_closest_config(ref_hz, rate);
        if (config_index != -1) {
            configure_pll(pllcfg, plloutdiv, &(pll_configs[config_index]));
        } else {
            /* unable to find a valid configuration */
            __METAL_ACCESS_ONCE(pllcfg) |= PLL_BYPASS;
        }
    }

    /* Enable the PLL */
    __METAL_ACCESS_ONCE(pllcfg) |= PLL_SEL;

    return __metal_driver_sifive_fe310_g000_pll_get_rate_hz(clock);
}

#ifdef __METAL_DT_SIFIVE_FE310_G000_PLL_HANDLE
METAL_CONSTRUCTOR(use_hfxosc) {
    long init_rate = __metal_driver_sifive_fe310_g000_pll_init_rate();
    metal_clock_set_rate_hz(&__METAL_DT_SIFIVE_FE310_G000_PLL_HANDLE->clock,
                            init_rate);
}
#endif

__METAL_DEFINE_VTABLE(__metal_driver_vtable_sifive_fe310_g000_pll) = {
    .init = __metal_driver_sifive_fe310_g000_pll_init,
    .clock.get_rate_hz = __metal_driver_sifive_fe310_g000_pll_get_rate_hz,
    .clock.set_rate_hz = __metal_driver_sifive_fe310_g000_pll_set_rate_hz,
};

#endif /* METAL_SIFIVE_FE310_G000_PLL */

typedef int no_empty_translation_units;
