/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * Copyright (c) 2010-2020, The Regents of the University of California
 * (Regents).  All Rights Reserved.
 */

#include "htif.h"

#define HTIF_DATA_BITS		48
#define HTIF_DATA_MASK		((1ULL << HTIF_DATA_BITS) - 1)
#define HTIF_DATA_SHIFT		0
#define HTIF_CMD_BITS		8
#define HTIF_CMD_MASK		((1ULL << HTIF_CMD_BITS) - 1)
#define HTIF_CMD_SHIFT		48
#define HTIF_DEV_BITS		8
#define HTIF_DEV_MASK		((1ULL << HTIF_DEV_BITS) - 1)
#define HTIF_DEV_SHIFT		56

#define HTIF_DEV_SYSTEM		0
#define HTIF_DEV_CONSOLE	1

#define HTIF_CONSOLE_CMD_GETC	0
#define HTIF_CONSOLE_CMD_PUTC	1

#define TOHOST_CMD(dev, cmd, payload) \
	(((uint64_t)(dev) << HTIF_DEV_SHIFT) | \
	 ((uint64_t)(cmd) << HTIF_CMD_SHIFT) | \
	 (uint64_t)(payload))
#define FROMHOST_DEV(fromhost_value) \
	((uint64_t)((fromhost_value) >> HTIF_DEV_SHIFT) & HTIF_DEV_MASK)
#define FROMHOST_CMD(fromhost_value) \
	((uint64_t)((fromhost_value) >> HTIF_CMD_SHIFT) & HTIF_CMD_MASK)
#define FROMHOST_DATA(fromhost_value) \
	((uint64_t)((fromhost_value) >> HTIF_DATA_SHIFT) & HTIF_DATA_MASK)

#define PK_SYS_write 64

volatile uint64_t tohost __attribute__((section(".htif")));
volatile uint64_t fromhost __attribute__((section(".htif")));
static int htif_console_buf;

static void __check_fromhost()
{
	uint64_t fh = fromhost;
	if (!fh)
		return;
	fromhost = 0;

	/* this should be from the console */
	if (FROMHOST_DEV(fh) != HTIF_DEV_CONSOLE)
		__builtin_trap();
	switch (FROMHOST_CMD(fh)) {
		case HTIF_CONSOLE_CMD_GETC:
			htif_console_buf = 1 + (uint8_t)FROMHOST_DATA(fh);
			break;
		case HTIF_CONSOLE_CMD_PUTC:
			break;
		default:
			__builtin_trap();
	}
}

static int initialized = 0;
static void __set_tohost(uint64_t dev, uint64_t cmd, uint64_t data)
{
	if (!initialized) {
		tohost = 0;
		initialized = 1;
	}
	while (tohost)
		__check_fromhost();
	uint64_t tohost_cmd = TOHOST_CMD(dev, cmd, data);
#if __riscv_xlen == 32
	/* Technically this isn't supported by spike, but in practice it works
	 * almost all the time. See
	 * https://github.com/riscv/riscv-isa-sim/issues/364 */

	/* Make sure to write the most-significant word first. */
	/* Assume little-endian. */
	((uint32_t *) &tohost)[1] = tohost_cmd >> 32;
	((uint32_t *) &tohost)[0] = tohost_cmd & 0xffffffff;
#else
	tohost = tohost_cmd;
#endif
}

void htif_putc(char ch)
{
	__set_tohost(HTIF_DEV_CONSOLE, HTIF_CONSOLE_CMD_PUTC, ch);
}

int htif_getc(void)
{
	int ch;

	__check_fromhost();
	ch = htif_console_buf;
	if (ch >= 0) {
		htif_console_buf = -1;
		__set_tohost(HTIF_DEV_CONSOLE, HTIF_CONSOLE_CMD_GETC, 0);
	}

	return ch - 1;
}

int htif_system_reset_check(uint32_t type, uint32_t reason)
{
	return 1;
}

void htif_system_reset(uint32_t type, uint32_t reason)
{
	while (1) {
		fromhost = 0;
		tohost = 1;
	}
}
