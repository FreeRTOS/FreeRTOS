/*
 * FreeRTOS V202212.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
 * https://github.com/FreeRTOS
 *
 */
#ifdef __cplusplus
extern "C" {
#endif

#include <sys/types.h>

typedef struct UART_t
{
    volatile uint32_t DATA;
    volatile uint32_t STATE;
    volatile uint32_t CTRL;
    volatile uint32_t INTSTATUS;
    volatile uint32_t BAUDDIV;
} UART_t;

#define UART0_ADDR           ( ( UART_t * ) ( 0x40004000 ) )
#define UART_DR( baseaddr )    ( *( unsigned int * ) ( baseaddr ) )

#define UART_STATE_TXFULL    ( 1 << 0 )
#define UART_CTRL_TX_EN      ( 1 << 0 )
#define UART_CTRL_RX_EN      ( 1 << 1 )

/**
 * @brief initializes the UART emulated hardware
 */
void uart_init(void)
{
    UART0_ADDR->BAUDDIV = 16;
    UART0_ADDR->CTRL = UART_CTRL_TX_EN;
}

#ifdef __PICOLIBC__

#include <stdio.h>

/**
 * @brief  Write byte to the UART channel to be displayed on the command line
 *         with qemu
 * @param [in] c     byte to send
 * @param [in] file  ignored
 * @returns the character written (cast to unsigned so it is not an error value)
 */

int
_uart_putc(char c, FILE *file)
{
    ( void ) file;
    UART_DR( UART0_ADDR ) = c;
    return (unsigned char) c;
}

static FILE __stdio = FDEV_SETUP_STREAM(_uart_putc, NULL, NULL, _FDEV_SETUP_WRITE);

FILE *const stdout = &__stdio;

#else

extern unsigned long _heap_bottom;
extern unsigned long _heap_top;

static char * heap_end = ( char * ) &_heap_bottom;

/**
 * @brief not used anywhere in the code
 * @todo  implement if necessary
 *
 */
int _fstat( int file )
{
    ( void ) file;
    return 0;
}

/**
 * @brief not used anywhere in the code
 * @todo  implement if necessary
 *
 */
int _read( int file,
           char * buf,
           int len )
{
    ( void ) file;
    ( void ) buf;
    ( void ) len;
    return -1;
}

/**
 * @brief  Write bytes to the UART channel to be displayed on the command line
 *         with qemu
 * @param [in] file  ignored
 * @param [in] buf   buffer to send
 * @param [in] len   length of the buffer
 * @returns the number of bytes written
 */
int _write( int file,
            char * buf,
            int len )
{
    int todo;

    ( void ) file;

    for( todo = 0; todo < len; todo++ )
    {
        UART_DR( UART0_ADDR ) = *buf++;
    }

    return len;
}

/**
 * @brief function called by malloc and friends to reserve memory on the heap
 * @param [in] incr the amount of bytes to increase or decrease
 * @returns the previous top of the heap
 * @note uses a global variable <b>heap_end</b> to keep track of the previous top
 */
void * _sbrk( int incr )
{
    void * prev_heap_end = heap_end;

    if( ( heap_end + incr ) > ( char * ) &_heap_top )
    {
        return ( void * ) -1;
    }

    heap_end += incr;

    return prev_heap_end;
}

void _close( int fd )
{
    ( void ) fd;
}

int _lseek( int filedes,
            int offset,
            int whence )
{
    ( void ) filedes;
    ( void ) offset;
    ( void ) whence;

    return 0;
}

int _isatty()
{
    return 0;
}

__attribute__( ( naked ) )
void _exit( int exit_code )
{
    ( void ) exit_code;
    /* Force qemu to exit using ARM Semihosting */
    __asm volatile (
        "mov r1, r0\n"
        "cmp r1, #0\n"
        "bne .notclean\n"
        "ldr r1, =0x20026\n" /* ADP_Stopped_ApplicationExit, a clean exit */
        ".notclean:\n"
        "movs r0, #0x18\n"   /* SYS_EXIT */
        "bkpt 0xab\n"
        "end: b end\n"
        );
}

void _kill( pid_t pid,
            int sig )
{
    ( void ) pid;
    ( void ) sig;
}

int _getpid( void )
{
    return 1;
}

#endif

#ifdef __cplusplus
}
#endif
