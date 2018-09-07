/*
 * Copyright (c) 2016, Texas Instruments Incorporated
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * *  Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 * *  Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * *  Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS;
 * OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR
 * OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
/*
 *  ======== SystemP_freertos.c ========
 */
#include <ti/drivers/dpl/SystemP.h>

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>

/* -----------------------------------------------------------------------------
 *  Constants and macros
 * -----------------------------------------------------------------------------
 */
#ifndef MIN
#  define MIN(n, m)    (((n) > (m)) ? (m) : (n))
#endif

/*
 *  ======== OUTMAX ========
 *  The maximum length of the output of a base 8 number produced by formatNum
 *  plus 5 to accomodate the decimal point and 4 digits after the decimal
 *  point.
 */
#define OUTMAX      ((32 + 2) / 3) + 5
#define PTRZPAD     8
#define MAXARGS     5

/* ----------------------------------------------------------------------------
 *   Type definitions
 * ----------------------------------------------------------------------------
 */
/* ParseData */
typedef struct ParseData {
    int width;
    bool lFlag;
    bool lJust;
    int precis;
    int len;
    int zpad;
    char *end;
    char *ptr;
} ParseData;

/*
 *  Maximum sized (un)signed integer that we'll format.
 */
typedef uint32_t UNum;
typedef int32_t INum;
typedef UNum UIntMax;
typedef INum  IntMax;

static int doPrint(char *buf, size_t n, const char *fmt, va_list va);
static char *formatNum(char *ptr, UIntMax un, int zpad, int base);
static void putChar(char **bufp, char c, size_t *n);

/*
 *  ======== SystemP_snprintf ========
 */
int SystemP_snprintf(char *buf, size_t n, const char *format,...)
{
    va_list args;
    int     ret;

    va_start(args, format);
    ret = doPrint(buf, n, format, args);
    va_end(args);

    return (ret);
}

/*
 *  ======== SystemP_snprintf_va ========
 */
int SystemP_vsnprintf(char *buf, size_t n, const char *format,
        va_list va)
{
    int     ret;

    ret = doPrint(buf, n, format, va);
    return (ret);
}

/*
 *  ======== doPrint ========
 */
static int doPrint(char *buf, size_t n, const char *fmt, va_list va)
{
    ParseData parse;
    int     base;
    char    c;
    int     res = 0;
    char    outbuf[OUTMAX];

    if (fmt == (char *)NULL) {
        return (res);
    }

    while ((c = *fmt++) != '\0') {
        if (c != '%') {
            putChar(&buf, c, &n);
            res++;
        }
        else {
            c = *fmt++;
            /* check for - flag (pad on right) */
            if (c == '-') {
                parse.lJust = true;
                c = *fmt++;
            }
            else {
                parse.lJust = false;
            }
            /* check for leading 0 pad */
            if (c == '0') {
                parse.zpad = 1;
                c = *fmt++;
            }
            else {
                parse.zpad = 0;
            }

            /* allow optional field width/precision specification */
            parse.width = 0;
            parse.precis = -1;

            /* note: dont use isdigit (very large for C30) */
            if (c == '*') {
                /* Width is specified in argument, not in format string */
                parse.width = (int)va_arg(va, int);

                c = *fmt++;
                if (parse.width < 0) {
                    parse.lJust = true;
                    parse.width = -parse.width;
                }
            }
            else {
                while (c >= '0' && c <= '9') {
                    parse.width = parse.width * 10 + c - '0';
                    c = *fmt++;
                }
            }

            /* allow optional field precision specification */
            if (c == '.') {
                parse.precis = 0;
                c = *fmt++;
                if (c == '*') {
                    /* Width specified in argument, not in format string */
                    parse.precis = (int)va_arg(va, int);

                    if (parse.precis < 0) {
                        parse.precis = 0;
                    }
                    c = *fmt++;
                }
                else {
                    while (c >= '0' && c <= '9') {
                        parse.precis = parse.precis * 10 + c - '0';
                        c = *fmt++;
                    }
                }
            }

            /* setup for leading zero padding */
            if (parse.zpad) {
                parse.zpad = parse.width;
            }

            /* check for presence of l flag (e.g., %ld) */
            if (c == 'l' || c == 'L') {
                parse.lFlag = true;
                c = *fmt++;
            }
            else {
                parse.lFlag = false;
            }

            parse.ptr = outbuf;
            parse.end = outbuf + OUTMAX;
            parse.len = 0;

            if (c == 'd' || c == 'i') {
                /* signed decimal */
                IntMax val = (IntMax)va_arg(va, int32_t);

                if (parse.precis > parse.zpad) {
                    parse.zpad = parse.precis;
                }
                parse.ptr = formatNum(parse.end, val, parse.zpad, -10);
                parse.len = parse.end - parse.ptr;
            }
            /* use comma operator to optimize code generation! */
            else if (((base = 10), (c == 'u')) ||       /* unsigned decimal */
                     ((base = 16), (c == 'x')) ||       /* unsigned hex */
                     ((base = 8),  (c == 'o'))) {       /* unsigned octal */

                UIntMax val = (UIntMax)va_arg(va, uint32_t) ;

                if (parse.precis > parse.zpad) {
                    parse.zpad = parse.precis;
                }
                parse.ptr = formatNum(parse.end, val, parse.zpad, base);
                parse.len = parse.end - parse.ptr;
            }
            else if ((base = 16), (c == 'p')) {
                parse.zpad = PTRZPAD;                   /* ptrs are 0 padded */
                parse.ptr = formatNum(
                    parse.end,
                    (UIntMax)va_arg(va, uint32_t),
                    parse.zpad, base);
                *(--parse.ptr) = '@';
                parse.len = parse.end - parse.ptr;
            }
            else if (c == 'c') {
                /* character */
                *parse.ptr = (char)va_arg(va, int);
                parse.len = 1;
            }
            else if (c == 's') {
                /* string */
                parse.ptr = (char *)va_arg(va, void *);

                /* substitute (null) for NULL pointer */
                if (parse.ptr == (char *)NULL) {
                    parse.ptr = "(null)";
                }
                parse.len = strlen(parse.ptr);
                if (parse.precis != -1 && parse.precis < parse.len) {
                    parse.len = parse.precis;
                }
            }
            else if (c == 'f') {
                double d, tmp;
                bool negative = false;
                UNum fract;

                d = va_arg(va, double);

                if (d < 0.0) {
                    d = -d;
                    negative = true;
                    parse.zpad--;
                }

                /*
                 *  Assumes four digits after decimal point. We are using a
                 *  temporary double variable to force double-precision
                 *  computations without  using --fp_mode=strict flag.
                 *  See the description of that flag in the compiler's doc
                 *  for a further explanation.
                 */
                tmp = (d - (INum)d) * 1e4;
                fract = (UNum)tmp;

                parse.ptr = formatNum(parse.end, fract, 4, 10);
                *(--parse.ptr) = '.';

                parse.len = parse.end - parse.ptr;
                /* format integer part (right to left!) */
                parse.ptr = formatNum(parse.ptr, (INum)d,
                        parse.zpad - parse.len, 10);
                if (negative) {
                    *(--parse.ptr) = '-';
                }

                parse.len = parse.end - parse.ptr;
            }

            /* compute number of characters left in field */
            parse.width -= parse.len;

            if (!parse.lJust) {
                /* pad with blanks on left */
                while (--parse.width >= 0) {
                    putChar(&buf, ' ', &n);
                    res++;
                }
            }

            /* output number, character or string */
            while (parse.len--) {
                putChar(&buf, *parse.ptr++, &n);
                res++;
            }
            /* pad with blanks on right */
            if (parse.lJust) {
                while (--parse.width >= 0) {
                    putChar(&buf, ' ', &n);
                    res++;
                }
            }
        } /* if */
    } /* while */

    if (buf) {
        *buf = '\0';
    }

    return (res);
}


/*
 *  ======== formatNum ========
 *  Internal function
 *
 *  Format unsigned long number in specified base, returning pointer to
 *  converted output.
 *
 *  Note: ptr points PAST end of the buffer, and is decremented as digits
 *  are converted from right to left!
 *
 *  Note: base is negative if n is signed else n unsigned!
 *
 *  ptr  - Pointer to the end of the working buffer where the string version
 *         of the number will be placed.
 *  un   - The unsigned number to be formated
 *  base - The base to format the number into. TODO - signed?
 */
static char *formatNum(char *ptr, UIntMax un, int zpad, int base)
{
    int i = 0;
    char sign = 0;

    UIntMax n;
    n = un;

    if (base < 0) {
        /* handle signed long case */
        base = -base;
        if ((IntMax)n < 0) {
            n = -(IntMax)n;

            /* account for sign '-': ok since zpad is signed */
            --zpad;
            sign = '-';
        }
    }

    /* compute digits in number from right to left */
    do {
        *(--ptr) = "0123456789abcdef"[(int)(n % base)];
        n = n / base;
        ++i;
    } while (n);

    /* pad with leading 0s on left */
    while (i < zpad) {
        *(--ptr) = '0';
        ++i;
    }

    /* add sign indicator */
    if (sign) {
        *(--ptr) = sign;
    }
    return (ptr);
}

/*
 *  ======== putChar ========
 *  Write character `c` to the buffer and the buffer pointer.
 *
 *  Keeps track of the number of characters written into the buffer by
 *  modifying bufsize `n`. Atmost, `n` - 1 characters are written.
 */
static void putChar(char **bufp, char c, size_t *n)
{
    /* if the size == 1, don't write so we can '\0' terminate buffer */
    if ((*n) <= 1) {
        return;
    }

    /* decrement n to keep track of the number of chars written */
    (*n)--;
    *((*bufp)++) = c;
}
