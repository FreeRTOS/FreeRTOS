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
 * @param c The character to write to the terminal
 * @return 0 on success, or -1 on failure.
 */
int metal_tty_putc(unsigned char c);

#endif
