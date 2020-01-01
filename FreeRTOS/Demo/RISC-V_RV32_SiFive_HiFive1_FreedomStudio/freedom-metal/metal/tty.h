/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__TTY_H
#define METAL__TTY_H

/*!
 * @file tty.h
 * @brief API for emulated serial teriminals
 */

/*!
 * @brief Write a character to the default output device
 *
 * Write a character to the default output device, which for most
 * targets is the UART serial port.
 *
 * putc() does CR/LF mapping.
 * putc_raw() does not.
 *
 * @param c The character to write to the terminal
 * @return 0 on success, or -1 on failure.
 */
int metal_tty_putc(int c);

/*!
 * @brief Write a raw character to the default output device
 *
 * Write a character to the default output device, which for most
 * targets is the UART serial port.
 *
 * putc() does CR/LF mapping.
 * putc_raw() does not.
 *
 * @param c The character to write to the terminal
 * @return 0 on success, or -1 on failure.
 */
int metal_tty_putc_raw(int c);

/*!
 * @brief Get a byte from the default output device
 *
 * The default output device, is typically the UART serial port.
 *
 * This call is non-blocking, if nothing is ready c==-1
 * if something is ready, then c=[0x00 to 0xff] byte value.
 *
 * @return 0 on success, or -1 on failure.
 */
int metal_tty_getc(int *c);

#endif
