/* serial 
 * 
 * Copyright (C) 2025 Advanced Micro Devices, Inc. or its affiliates. All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 *
 */


#include "stdint.h"
#include "io.h"
#include "freertos_serial.h"

#define COM_BASE                        0x3F8
#define COM_PORT_DATA                   COM_BASE + 0
#define COM_PORT_INTERRUPT_ENABLE       COM_BASE + 1
#define COM_PORT_FIFO_CONTROL           COM_BASE + 2
#define COM_PORT_LINE_CONTROL           COM_BASE + 3
#define COM_PORT_MODEM_CONTROL          COM_BASE + 4
#define COM_PORT_LINE_STATUS            COM_BASE + 5
#define COM_PORT_MODEM_STATUS           COM_BASE + 6
#define COM_PORT_SCRATCH_REGISTER       COM_BASE + 7
#define BAUD_115200                     1
#define BAUD_57600                      2
#define BAUD_9600                       12
#define BAUD_300                        384
void init_serial() {
    outb(COM_PORT_INTERRUPT_ENABLE, 0x1);
    outb(COM_PORT_LINE_CONTROL, 0x80);
    outb(COM_PORT_DATA, BAUD_115200);
    outb(COM_PORT_DATA+1, BAUD_115200>>8);
    outb(COM_PORT_LINE_CONTROL, 0x7); //8 data bits (0-1 set), one stop bit (2 set), no parity (3-5 clear), DLB (7 clear)
    outb(COM_PORT_MODEM_CONTROL, 0);
    outb(COM_PORT_FIFO_CONTROL, 0xC7);
}

void serial_send(char c) {
    if (c == '\n')
       serial_send('\r');
    int line_state = 0;
    do {
       line_state = inb(COM_PORT_LINE_STATUS) & 0x20;
    } while (line_state == 0);
    outb(COM_PORT_DATA, c);
}
char serial_recv() {
    return (char)inb(COM_PORT_DATA);
}
char serial_iir() {
    return (char)inb(COM_PORT_FIFO_CONTROL);
}
char serial_lsr() {
    return (char)inb(COM_PORT_LINE_STATUS);
}
