/*
 * FreeRTOS V202011.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * https://www.FreeRTOS.org
 * https://www.gihub.com/FreeRTOS
 *
 */
#ifdef __cplusplus
extern "C" {
#endif

#include <sys/types.h>

typedef struct UART_t {
    volatile uint32_t DATA;
    volatile uint32_t STATE;
    volatile uint32_t CTRL;
    volatile uint32_t INTSTATUS;
    volatile uint32_t BAUDDIV;
} UART_t;

#define UART0_ADDR ((UART_t *)(0x40004000))
#define UART_DR(baseaddr) (*(unsigned int *)(baseaddr))

#define UART_STATE_TXFULL (1 << 0)
#define UART_CTRL_TX_EN (1 << 0)
#define UART_CTRL_RX_EN (1 << 1)

static char *heap_end = 0;
extern unsigned long _heap_bottom;
extern unsigned long _heap_top;
extern unsigned long g_ulBase;

void uart_init()
{
    UART0_ADDR->BAUDDIV = 16;
    UART0_ADDR->CTRL = UART_CTRL_TX_EN;
}

int _close(int file){
    return -1;
}

int _fstat(int file){
    return 0;
}

int _isatty(int file){
    return 1;
}

int _lseek(int file, int buf, int dir){
    return 0;
}

int _open(const char *name, int flags, int mode){
    return -1;
}

int _read(int file, char *buf, int len){
     return -1;
}

int _write(int file, char *buf, int len){
    int todo;
 
    for (todo = 0; todo < len; todo++){
        UART_DR(UART0_ADDR) = *buf++;
    }
    return len;
}

caddr_t _sbrk(unsigned int incr){
    char *prev_heap_end;

    if (heap_end == 0){
        heap_end = (caddr_t)&_heap_bottom;
    }

    prev_heap_end = heap_end;

    if (heap_end + incr > (caddr_t)&_heap_top){
        return (caddr_t)0;
    }

    heap_end += incr;

    return (caddr_t) prev_heap_end;
}

#ifdef __cplusplus
}
#endif
