/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__COMPILER_H
#define METAL__COMPILER_H

#define __METAL_DECLARE_VTABLE(type)                      \
    extern const struct type type;			  

#define __METAL_DEFINE_VTABLE(type)                       \
    const struct type type                                

#define __METAL_GET_FIELD(reg, mask)                        \
    (((reg) & (mask)) / ((mask) & ~((mask) << 1)))

/* Set field with mask for a given value */
#define __METAL_SET_FIELD(reg, mask, val) \
        (((reg) & ~(mask)) | (((val) * ((mask) & ~((mask) << 1))) & (mask)))

void _metal_trap(int ecode);

#endif
