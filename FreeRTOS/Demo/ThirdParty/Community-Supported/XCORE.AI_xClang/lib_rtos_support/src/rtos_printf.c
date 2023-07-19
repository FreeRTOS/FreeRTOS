// Copyright 2019-2021 XMOS LIMITED.
// This Software is subject to the terms of the XMOS Public Licence: Version 1.

/*---------------------------------------------------*/
/* Modified from :                                   */
/* Public Domain version of printf                   */
/* Rud Merriam, Compsult, Inc. Houston, Tx.          */
/* For Embedded Systems Programming, 1991            */
/*                                                   */
/*---------------------------------------------------*/

#include <stdarg.h>
#include <syscall.h>
#include <limits.h>
#include <string.h>
#include <stdint.h>
#include <ctype.h>

#include "rtos_support.h"

#undef rtos_printf
#undef rtos_vprintf

#define LONG64 (LONG_MAX == 9223372036854775807L)
#define POINTER64 (INTPTR_MAX == 9223372036854775807L)

typedef struct {
    size_t size;
    size_t pos;
    char *str;
    int writeout;
    int32_t len;
    int32_t num1;
    int32_t num2;
    int32_t do_padding;
    int32_t left_flag;
    int32_t unsigned_flag;
    char pad_character;
} params_t;

static void outbyte(char b, params_t *par)
{
    if (par->pos < par->size) {
        par->str[par->pos] = b;
    }
    par->pos++;

    if (par->writeout && par->pos >= par->size) {
        _write(FD_STDOUT, par->str, par->size);
        par->pos = 0;
    }
}

/*---------------------------------------------------*/
/* The purpose of this routine is to output data the */
/* same as the standard printf function without the  */
/* overhead most run-time libraries involve. Usually */
/* the printf brings in many kilobytes of code and   */
/* that is unacceptable in most embedded systems.    */
/*---------------------------------------------------*/


/*---------------------------------------------------*/
/*                                                   */
/* This routine puts pad characters into the output  */
/* buffer.                                           */
/*                                                   */
static void padding(const int32_t l_flag, params_t *par)
{
    int32_t i;

    if ((par->do_padding != 0) && (l_flag != 0) && (par->len < par->num1)) {
        i=(par->len);
        for (; i<(par->num1); i++) {
            outbyte(par->pad_character, par);
        }
    }
}

/*---------------------------------------------------*/
/*                                                   */
/* This routine moves a string to the output buffer  */
/* as directed by the padding and positioning flags. */
/*                                                   */
static void outs(const char *lp, params_t *par)
{
    /* pad on left if needed                         */
    if(lp != NULL) {
        par->len = (int32_t) strlen(lp);
    }
    padding(!(par->left_flag), par);

    /* Move string to the buffer                     */
    while (((*lp) != (char)0) && ((par->num2) != 0)) {
        (par->num2)--;
        outbyte(*lp, par);
        lp += 1;
    }

    padding(par->left_flag, par);
}

/*---------------------------------------------------*/
/*                                                   */
/* This routine moves a number to the output buffer  */
/* as directed by the padding and positioning flags. */
/*                                                   */

static void outnum(const int32_t n, const int32_t base, params_t *par)
{
    int32_t negative;
    int32_t i;
    char outbuf[32];
    const char digits[] = "0123456789ABCDEF";
    uint32_t num;
    for(i = 0; i<32; i++) {
        outbuf[i] = '0';
    }

    /* Check if number is negative                   */
    if ((par->unsigned_flag == 0) && (base == 10) && (n < 0L)) {
        negative = 1;
        num =(-(n));
    }
    else{
        num = n;
        negative = 0;
    }

    /* Build number (backwards) in outbuf            */
    i = 0;
    do {
        outbuf[i] = digits[(num % base)];
        i++;
        num /= base;
    } while (num > 0);

    if (negative != 0) {
        outbuf[i] = '-';
        i++;
    }

    outbuf[i] = '\0';
    i--;

    /* Move the converted number to the buffer and   */
    /* add in the padding where needed.              */
    par->len = (int32_t)strlen(outbuf);
    padding(!(par->left_flag), par);
    while (&outbuf[i] >= outbuf) {
        outbyte(outbuf[i], par);
        i--;
    }
    padding(par->left_flag, par);
}
/*---------------------------------------------------*/
/*                                                   */
/* This routine moves a 64-bit number to the output  */
/* buffer as directed by the padding and positioning */
/* flags.                                            */
/*                                                   */
#if LONG64
static void outnum1(const int64_t n, const int32_t base, params_t *par)
{
    int32_t negative;
    int32_t i;
    char outbuf[64];
    const char digits[] = "0123456789ABCDEF";
    uint64_t num;
    for(i = 0; i<64; i++) {
        outbuf[i] = '0';
    }

    /* Check if number is negative                   */
    if ((par->unsigned_flag == 0) && (base == 10) && (n < 0L)) {
        negative = 1;
        num =(-(n));
    }
    else{
        num = (n);
        negative = 0;
    }

    /* Build number (backwards) in outbuf            */
    i = 0;
    do {
        outbuf[i] = digits[(num % base)];
        i++;
        num /= base;
    } while (num > 0);

    if (negative != 0) {
        outbuf[i] = '-';
        i++;
    }

    outbuf[i] = '\0';
    i--;

    /* Move the converted number to the buffer and   */
    /* add in the padding where needed.              */
    par->len = (int32_t)strlen(outbuf);
    padding(!(par->left_flag), par);
    while (&outbuf[i] >= outbuf) {
        outbyte(outbuf[i], par);
        i--;
    }
    padding(par->left_flag, par);
}
#endif
/*---------------------------------------------------*/
/*                                                   */
/* This routine gets a number from the format        */
/* string.                                           */
/*                                                   */
static int32_t getnum(char **linep)
{
    int32_t n;
    int32_t ResultIsDigit = 0;
    char *cptr;
    n = 0;
    cptr = *linep;
    if(cptr != NULL){
        ResultIsDigit = isdigit(((int32_t)*cptr));
    }
    while (ResultIsDigit != 0) {
        if(cptr != NULL){
            n = ((n*10) + (((int32_t)*cptr) - (int32_t)'0'));
            cptr += 1;
            if(cptr != NULL){
                ResultIsDigit = isdigit(((int32_t)*cptr));
            }
        }
        ResultIsDigit = isdigit(((int32_t)*cptr));
    }
    *linep = ((char *)(cptr));
    return(n);
}

/*---------------------------------------------------*/
/*                                                   */
/* This routine operates just like a printf/sprintf  */
/* routine. It outputs a set of data under the       */
/* control of a formatting string. Not all of the    */
/* standard C format control are supported. The ones */
/* provided are primarily those needed for embedded  */
/* systems work. Primarily the floating point        */
/* routines are omitted. Other formats could be      */
/* added easily by following the examples shown for  */
/* the supported formats.                            */
/*                                                   */

static int rtos_vsnwprintf(char *str, size_t size, int writeout, const char *fmt, va_list ap)
{
    int32_t Check;
#if LONG64
    int32_t long_flag;
#endif
    int32_t dot_flag;

    params_t par;

    char ch;
    char *ctrl = (char *)fmt;

    par.size = size;
    par.pos = 0;
    par.str = str;
    par.writeout = writeout;

    while ((ctrl != NULL) && (*ctrl != (char)0)) {

        /* move format string chars to buffer until a  */
        /* format control is found.                    */
        if (*ctrl != '%') {
            outbyte(*ctrl, &par);
            ctrl += 1;
            continue;
        }

        /* initialize all the flags for this format.   */
        dot_flag = 0;
#if LONG64
        long_flag = 0;
#endif
        par.unsigned_flag = 0;
        par.left_flag = 0;
        par.do_padding = 0;
        par.pad_character = ' ';
        par.num2=32767;
        par.num1=0;
        par.len=0;

 try_next:
        if(ctrl != NULL) {
            ctrl += 1;
        }
        if(ctrl != NULL) {
            ch = *ctrl;
        }
        else {
            ch = *ctrl;
        }

        if (isdigit((int32_t)ch) != 0) {
            if (dot_flag != 0) {
				par.num2 = getnum(&ctrl);
            }
            else {
                if (ch == '0') {
                    par.pad_character = '0';
                }
                if(ctrl != NULL) {
                    par.num1 = getnum(&ctrl);
                }
                par.do_padding = 1;
            }
            if(ctrl != NULL) {
            ctrl -= 1;
            }
            goto try_next;
        }

        if (dot_flag != 0 && ch == '*') {
			par.num2 = va_arg(ap, int32_t);
            goto try_next;
        }

        switch (tolower((int32_t)ch)) {
            case '%':
                outbyte('%', &par);
                Check = 1;
                break;

            case '-':
                par.left_flag = 1;
                Check = 0;
                break;

            case '.':
                dot_flag = 1;
                Check = 0;
                break;

            case 'l':
            #if LONG64
                long_flag = 1;
            #endif
                Check = 0;
                break;

            case 'u':
                par.unsigned_flag = 1;
                /* fall through */
            case 'i':
            case 'd':
                #if LONG64
                if (long_flag != 0){
                    outnum1((int64_t)va_arg(ap, int64_t), 10L, &par);
                }
                else {
                    outnum(va_arg(ap, int32_t), 10L, &par);
                }
                #else
                outnum(va_arg(ap, int32_t), 10L, &par);
                #endif
                Check = 1;
                break;
            case 'p':
                #if POINTER64
                par.unsigned_flag = 1;
                outnum1((int64_t)va_arg(ap, int64_t), 16L, &par);
                Check = 1;
                break;
                #endif
            case 'X':
            case 'x':
                par.unsigned_flag = 1;
                #if LONG64
                if (long_flag != 0) {
                    outnum1((int64_t)va_arg(ap, int64_t), 16L, &par);
                }
                else {
                    outnum((int32_t)va_arg(ap, int32_t), 16L, &par);
                }
                #else
                outnum((int32_t)va_arg(ap, int32_t), 16L, &par);
                #endif
                Check = 1;
                break;

            case 's':
                outs(va_arg(ap, char *), &par);
                Check = 1;
                break;

            case 'c':
                outbyte(va_arg(ap, int32_t), &par);
                Check = 1;
                break;

            case '\\':
                switch (*ctrl) {
                    case 'a':
                        outbyte((char)0x07, &par);
                        break;
                    case 'h':
                        outbyte((char)0x08, &par);
                        break;
                    case 'r':
                        outbyte((char)0x0D, &par);
                        break;
                    case 'n':
                        outbyte((char)0x0D, &par);
                        outbyte((char)0x0A, &par);
                        break;
                    default:
                        outbyte(*ctrl, &par);
                        break;
                }
                ctrl += 1;
                Check = 0;
                break;

            default:
				Check = 1;
				break;
        }
        if(Check == 1) {
            if(ctrl != NULL) {
                ctrl += 1;
            }
                continue;
        }
        goto try_next;
    }

    if (par.pos < par.size) {
        par.str[par.pos] = '\0';
    }

    return par.pos;
}
/*---------------------------------------------------*/

int rtos_snprintf(char *str, size_t size, const char *fmt, ...)
{
    int len;
    va_list ap;

    va_start(ap, fmt);
    len = rtos_vsnwprintf(str, size, 0, fmt, ap);
    va_end(ap);

    return len;
}

int rtos_sprintf(char *str, const char *fmt, ...)
{
    int len;
    va_list ap;

    va_start(ap, fmt);
    len = rtos_vsnwprintf(str, SIZE_MAX, 0, fmt, ap);
    va_end(ap);

    return len;
}

#ifndef RTOS_PRINTF_BUFSIZE
#ifdef DEBUG_PRINTF_BUFSIZE
#define RTOS_PRINTF_BUFSIZE DEBUG_PRINTF_BUFSIZE
#else
#define RTOS_PRINTF_BUFSIZE 130
#endif
#endif

int rtos_vprintf(const char *fmt, va_list ap)
{
    int len;
    uint32_t mask;
    char buf[RTOS_PRINTF_BUFSIZE];

    mask = rtos_interrupt_mask_all();
    len = rtos_vsnwprintf(buf, RTOS_PRINTF_BUFSIZE, 1, fmt, ap);

    _write(FD_STDOUT, buf, len);

    rtos_interrupt_mask_set(mask);

    return len;
}

int rtos_printf(const char *fmt, ...)
{
    int len;
    va_list ap;

    va_start(ap, fmt);
    len = rtos_vprintf(fmt, ap);
    va_end(ap);

    return len;
}
