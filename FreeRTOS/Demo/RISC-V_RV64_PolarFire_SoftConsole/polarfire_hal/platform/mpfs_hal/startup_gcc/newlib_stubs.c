/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */

/*******************************************************************************
 * @file newlib_stubs.c
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief Stubs for Newlib system calls.
 *
 */
#include <sys/times.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <errno.h>
#include <unistd.h>
#include "../mss_hal.h"

/*==============================================================================
 * Redirection of standard output to a SmartFusion2 MSS UART.
 *------------------------------------------------------------------------------
 * A default implementation for the redirection of the output of printf() to a
 * UART is provided at the bottom of this file. This redirection is enabled by
 * adding the symbol/define MICROCHIP_STDIO_THRU_MMUART0 or
 * MICROCHIP_STDIO_THRU_MMUART0 to your project settings and specifying the baud
 * rate using the MICROCHIP_STDIO_BAUD_RATE define.
 */
#ifdef MICROCHIP_STDIO_THRU_MMUART0
#ifndef MICROCHIP_STDIO_THRU_UART
#define MICROCHIP_STDIO_THRU_UART
#endif
#endif  /* MICROCHIP_STDIO_THRU_MMUART0 */

#ifdef MICROCHIP_STDIO_THRU_MMUART1
#ifndef MICROCHIP_STDIO_THRU_UART
#define MICROCHIP_STDIO_THRU_UART
#endif
#endif  /* MICROCHIP_STDIO_THRU_MMUART1 */

/*
 * Select which MMUART will be used for stdio and what baud rate will be used.
 * Default to 57600 baud if no baud rate is specified using the
 * MICROCHIP_STDIO_BAUD_RATE #define.
 */
#ifdef MICROCHIP_STDIO_THRU_UART
#include "drivers/mss/mss_mmuart/mss_uart.h"

#ifndef MICROCHIP_STDIO_BAUD_RATE
#define MICROCHIP_STDIO_BAUD_RATE  MSS_UART_115200_BAUD
#endif

#ifdef MICROCHIP_STDIO_THRU_MMUART0
static mss_uart_instance_t * const gp_my_uart = &g_mss_uart0;
#else
static mss_uart_instance_t * const gp_my_uart = &g_mss_uart1;
#endif

/*------------------------------------------------------------------------------
 * Global flag used to indicate if the UART driver needs to be initialized.
 */
static int g_stdio_uart_init_done = 0;

#endif /* MICROCHIP_STDIO_THRU_UART */

/*==============================================================================
 * Environment variables.
 * A pointer to a list of environment variables and their values. For a minimal
 * environment, this empty list is adequate:
 */
char *__env[1] = { 0 };
char **environ = __env;


/*==============================================================================
 * Close a file.
 */
int _close(int file);
int _close(int file)
{
    (void)file;
    return -1;
}

/*==============================================================================
 * Transfer control to a new process.
 */
int _execve(char *name, char **argv, char **env);
int _execve(char *name, char **argv, char **env)
{
    (void)name;
    (void)argv;
    (void)env;
    errno = ENOMEM;
    return -1;
}

/*==============================================================================
 * Exit a program without cleaning up files.
 */
void _exit( int code )
{
    (void)code;
    /* Should we force a system reset? */
    while( 1 )
    {
        ;
    }
}

/*==============================================================================
 * Create a new process.
 */
int _fork(void);
int _fork(void)
{
    errno = EAGAIN;
    return -1;
}

/*==============================================================================
 * Status of an open file.
 */
int _fstat(int file, struct stat *st);
int _fstat(int file, struct stat *st)
{
    (void)file;
    st->st_mode = S_IFCHR;
    return (0);
}

/*==============================================================================
 * Process-ID
 */
int _getpid(void);
int _getpid(void)
{
    return (1);
}

/*==============================================================================
 * Query whether output stream is a terminal.
 */
int _isatty(int file);
int _isatty(int file)
{
    (void)file;
    return (1);
}

/*==============================================================================
 * Send a signal.
 */
int _kill(int pid, int sig);
int _kill(int pid, int sig)
{
    (void)pid;
    (void)sig;
    errno = EINVAL;
    return (-1);
}

/*==============================================================================
 * Establish a new name for an existing file.
 */
int _link(char *old, char *new);
int _link(char *old, char *new)
{
    (void)old;
    (void)new;
    errno = EMLINK;
    return (-1);
}

/*==============================================================================
 * Set position in a file.
 */
int _lseek(int file, int ptr, int dir);
int _lseek(int file, int ptr, int dir)
{
    (void)file;
    (void)ptr;
    (void)dir;
    return (0);
}

/*==============================================================================
 * Open a file.
 */
int _open(const char *name, int flags, int mode);
int _open(const char *name, int flags, int mode)
{
    (void)name;
    (void)flags;
    (void)mode;
    return (-1);
}

/*==============================================================================
 * Read from a file.
 */
int _read(int file, char *ptr, int len);
int _read(int file, char *ptr, int len)
{
    (void)file;
    (void)ptr;
    (void)len;
    return (0);
}

/*==============================================================================
 * Write to a file. libc subroutines will use this system routine for output to
 * all files, including stdout so if you need to generate any output, for
 * example to a serial port for debugging, you should make your minimal write
 * capable of doing this.
 */
int _write_r( void * reent, int file, char * ptr, int len );
int _write_r( void * reent, int file, char * ptr, int len )
{
    (void)reent;
    (void)file;
    (void)ptr;
    (void)len;
#ifdef MICROCHIP_STDIO_THRU_UART
    /*--------------------------------------------------------------------------
     * Initialize the UART driver if it is the first time this function is
     * called.
     */
    if(!g_stdio_uart_init_done)
    {
        MSS_UART_init(gp_my_uart,
                      MICROCHIP_STDIO_BAUD_RATE,
                      MSS_UART_DATA_8_BITS | MSS_UART_NO_PARITY);

        g_stdio_uart_init_done = 1;
    }

    /*--------------------------------------------------------------------------
     * Output text to the UART.
     */
    MSS_UART_polled_tx(gp_my_uart, (uint8_t *)ptr, len);

    return len;
#else   /* MICROCHIP_STDIO_THRU_UART */
    return (0);
#endif  /* MICROCHIP_STDIO_THRU_UART */
}

/*==============================================================================
 * Increase program data space. As malloc and related functions depend on this,
 * it is useful to have a working implementation. The following suffices for a
 * standalone system; it exploits the symbol _end automatically defined by the
 * GNU linker.
 */
caddr_t _sbrk(int incr);
caddr_t _sbrk(int incr)
{
    extern char _end;       /* Defined by the linker */
    extern char __heap_start;
    extern char __heap_end;
    static char *heap_end;
    char *prev_heap_end;

    (void)__heap_start;
    (void)__heap_end;
#ifdef DEBUG_HEAP_SIZE
    char * stack_ptr = NULL;
#endif

    /*
     * Did we allocated memory for the heap in the linker script?
     * You need to set HEAP_SIZE to a non-zero value in your linker script if
     * the following assertion fires.
     */
    ASSERT(&__heap_end > &__heap_start);

    if (heap_end == NULL)
    {
      heap_end = &_end;
    }

    prev_heap_end = heap_end;

#ifdef DEBUG_HEAP_SIZE          /* add this define if you want to debug crash due to overflow of  heap */
    /* fixme- this test needs to be reworked to take account of multiple harts and TLS */
    stack_ptr = read_csr(sp);
    /* stack_ptr has just been placed on the stack, so its address in currently pointing to the stack end */
    if(heap_end < stack_ptr)
    {
        /*
         * Heap is at an address below the stack, growing up toward the stack.
         * The stack is above the heap, growing down towards the heap.
         * Make sure the stack and heap do not run into each other.
         */
        if (heap_end + incr > stack_ptr)
        {
          _write_r ((void *)0, 1, "Heap and stack collision\n", 25);
          _exit (1);
        }
    }
    else
    {
        /*
         * If the heap and stack are not growing towards each other then use the
         * _eheap linker script symbol to figure out if there is room left on
         * the heap.
         * Please note that this use case makes sense when the stack is located
         * in internal eSRAM in the 0x20000000 address range and the heap is
         * located in the external memory in the 0xA0000000 memory range.
         * Please note that external memory should not be accessed using the
         * 0x00000000 memory range to read/write variables/data because of the
         * SmartFusion2 cache design.
         */
        extern char _heap_end;     /* Defined by the linker */
        char *top_of_heap;

        top_of_heap = &_heap_end;
        if(heap_end + incr  > top_of_heap)
        {
          _write_r ((void *)0, 1, "Out of heap memory\n", 25);
          _exit (1);
        }
    }
#endif
    heap_end += incr;

    /*
     * Did we run out of heap?
     * You need to increase the heap size in the linker script if the following
     * assertion fires.
     * */
    ASSERT(heap_end <= &__heap_end);

    return ((caddr_t) prev_heap_end);
}

/*==============================================================================
 * Status of a file (by name).
 */
int _stat(char *file, struct stat *st);
int _stat(char *file, struct stat *st)
{
    (void)file;
    st->st_mode = S_IFCHR;
    return 0;
}

/*==============================================================================
 * Timing information for current process.
 */
int _times(struct tms *buf);
int _times(struct tms *buf)
{
    (void)buf;
    return (-1);
}

/*==============================================================================
 * Remove a file's directory entry.
 */
int _unlink(char *name);
int _unlink(char *name)
{
    (void)name;
    errno = ENOENT;
    return (-1);
}

/*==============================================================================
 * Wait for a child process.
 */
int _wait(int *status);
int _wait(int *status)
{
    (void)status;
    errno = ECHILD;
    return (-1);
}
