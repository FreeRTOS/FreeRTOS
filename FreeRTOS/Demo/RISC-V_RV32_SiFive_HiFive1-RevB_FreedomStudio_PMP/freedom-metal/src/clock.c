/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/clock.h>

extern __inline__ void _metal_clock_call_all_callbacks(const metal_clock_callback *const list);
extern __inline__ metal_clock_callback *_metal_clock_append_to_callbacks(metal_clock_callback *list, metal_clock_callback *const cb);

extern __inline__ long metal_clock_get_rate_hz(const struct metal_clock *clk);
extern __inline__ long metal_clock_set_rate_hz(struct metal_clock *clk, long hz);
extern __inline__ void metal_clock_register_post_rate_change_callback(struct metal_clock *clk, metal_clock_callback *cb);
extern __inline__ void metal_clock_register_pre_rate_change_callback(struct metal_clock *clk, metal_clock_callback *cb);
