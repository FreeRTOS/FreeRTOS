/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/clock.h>

extern inline long metal_clock_get_rate_hz(const struct metal_clock *clk);
extern inline long metal_clock_set_rate_hz(struct metal_clock *clk, long hz);
extern inline void metal_clock_register_post_rate_change_callback(struct metal_clock *clk, metal_clock_post_rate_change_callback cb, void *priv);
extern inline void metal_clock_register_pre_rate_change_callback(struct metal_clock *clk, metal_clock_pre_rate_change_callback cb, void *priv);
