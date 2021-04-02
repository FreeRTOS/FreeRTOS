/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * Copyright (c) 2010-2020, The Regents of the University of California
 * (Regents).  All Rights Reserved.
 */

#ifndef __HTIF_H__
#define __HTIF_H__

#include <stdint.h>

void htif_putc(char ch);

int htif_getc(void);

int htif_system_reset_check(uint32_t type, uint32_t reason);

void htif_system_reset(uint32_t type, uint32_t reason);

#endif
