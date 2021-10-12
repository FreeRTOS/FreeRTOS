/*
 * Copyright 2017, 2020 NXP
 * All rights reserved.
 *
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */
#include <math.h>
#include <stdarg.h>
#include <stdlib.h>
#include <errno.h> /* MISRA C-2012 Rule 22.9 */
#include "fsl_str.h"
#include "fsl_debug_console_conf.h"

/*******************************************************************************
 * Definitions
 ******************************************************************************/

/*! @brief The overflow value.*/
#ifndef HUGE_VAL
#define HUGE_VAL (99.e99)
#endif /* HUGE_VAL */

#ifndef MAX_FIELD_WIDTH
#define MAX_FIELD_WIDTH 99U
#endif

#if PRINTF_ADVANCED_ENABLE
/*! @brief Specification modifier flags for printf. */
enum _debugconsole_printf_flag
{
    kPRINTF_Minus             = 0x01U,  /*!< Minus FLag. */
    kPRINTF_Plus              = 0x02U,  /*!< Plus Flag. */
    kPRINTF_Space             = 0x04U,  /*!< Space Flag. */
    kPRINTF_Zero              = 0x08U,  /*!< Zero Flag. */
    kPRINTF_Pound             = 0x10U,  /*!< Pound Flag. */
    kPRINTF_LengthChar        = 0x20U,  /*!< Length: Char Flag. */
    kPRINTF_LengthShortInt    = 0x40U,  /*!< Length: Short Int Flag. */
    kPRINTF_LengthLongInt     = 0x80U,  /*!< Length: Long Int Flag. */
    kPRINTF_LengthLongLongInt = 0x100U, /*!< Length: Long Long Int Flag. */
};
#endif /* PRINTF_ADVANCED_ENABLE */

/*! @brief Specification modifier flags for scanf. */
enum _debugconsole_scanf_flag
{
    kSCANF_Suppress   = 0x2U,    /*!< Suppress Flag. */
    kSCANF_DestMask   = 0x7cU,   /*!< Destination Mask. */
    kSCANF_DestChar   = 0x4U,    /*!< Destination Char Flag. */
    kSCANF_DestString = 0x8U,    /*!< Destination String FLag. */
    kSCANF_DestSet    = 0x10U,   /*!< Destination Set Flag. */
    kSCANF_DestInt    = 0x20U,   /*!< Destination Int Flag. */
    kSCANF_DestFloat  = 0x30U,   /*!< Destination Float Flag. */
    kSCANF_LengthMask = 0x1f00U, /*!< Length Mask Flag. */
#if SCANF_ADVANCED_ENABLE
    kSCANF_LengthChar        = 0x100U, /*!< Length Char Flag. */
    kSCANF_LengthShortInt    = 0x200U, /*!< Length ShortInt Flag. */
    kSCANF_LengthLongInt     = 0x400U, /*!< Length LongInt Flag. */
    kSCANF_LengthLongLongInt = 0x800U, /*!< Length LongLongInt Flag. */
#endif                                 /* SCANF_ADVANCED_ENABLE */
#if SCANF_FLOAT_ENABLE
    kSCANF_LengthLongLongDouble = 0x1000U, /*!< Length LongLongDuoble Flag. */
#endif                                     /*PRINTF_FLOAT_ENABLE */
    kSCANF_TypeSinged = 0x2000U,           /*!< TypeSinged Flag. */
};

/*! @brief Keil: suppress ellipsis warning in va_arg usage below. */
#if defined(__CC_ARM)
#pragma diag_suppress 1256
#endif /* __CC_ARM */

/*******************************************************************************
 * Prototypes
 ******************************************************************************/
/*!
 * @brief Scanline function which ignores white spaces.
 *
 * @param[in]   s The address of the string pointer to update.
 * @return      String without white spaces.
 */
static uint32_t ScanIgnoreWhiteSpace(const char **s);

/*!
 * @brief Converts a radix number to a string and return its length.
 *
 * @param[in] numstr    Converted string of the number.
 * @param[in] nump      Pointer to the number.
 * @param[in] neg       Polarity of the number.
 * @param[in] radix     The radix to be converted to.
 * @param[in] use_caps  Used to identify %x/X output format.

 * @return Length of the converted string.
 */
static int32_t ConvertRadixNumToString(char *numstr, void *nump, int32_t neg, int32_t radix, bool use_caps);

#if PRINTF_FLOAT_ENABLE
/*!
 * @brief Converts a floating radix number to a string and return its length.
 *
 * @param[in] numstr            Converted string of the number.
 * @param[in] nump              Pointer to the number.
 * @param[in] radix             The radix to be converted to.
 * @param[in] precision_width   Specify the precision width.

 * @return Length of the converted string.
 */
static int32_t ConvertFloatRadixNumToString(char *numstr, void *nump, int32_t radix, uint32_t precision_width);

#endif /* PRINTF_FLOAT_ENABLE */

/*************Code for process formatted data*******************************/
#if PRINTF_ADVANCED_ENABLE
static uint8_t PrintGetSignChar(int64_t ival, uint32_t flags_used, char *schar)
{
    uint8_t len = 1U;
    if (ival < 0)
    {
        *schar = '-';
    }
    else
    {
        if (0U != (flags_used & (uint32_t)kPRINTF_Plus))
        {
            *schar = '+';
        }
        else if (0U != (flags_used & (uint32_t)kPRINTF_Space))
        {
            *schar = ' ';
        }
        else
        {
            *schar = '\0';
            len    = 0U;
        }
    }
    return len;
}
#endif

static uint32_t PrintGetWidth(const char **p, va_list *ap)
{
    uint32_t field_width = 0;
    uint8_t done         = 0U;
    char c;

    while (0U == done)
    {
        c = *(++(*p));
        if ((c >= '0') && (c <= '9'))
        {
            (field_width) = ((field_width)*10U) + ((uint32_t)c - (uint32_t)'0');
        }
#if PRINTF_ADVANCED_ENABLE
        else if (c == '*')
        {
            (field_width) = (uint32_t)va_arg(*ap, uint32_t);
        }
#endif /* PRINTF_ADVANCED_ENABLE */
        else
        {
            /* We've gone one char too far. */
            --(*p);
            done = 1U;
        }
    }
    return field_width;
}

static uint32_t PrintGetPrecision(const char **s, va_list *ap, bool *valid_precision_width)
{
    const char *p            = *s;
    uint32_t precision_width = 6U;
    uint8_t done             = 0U;

#if PRINTF_ADVANCED_ENABLE
    if (NULL != valid_precision_width)
    {
        *valid_precision_width = false;
    }
#endif /* PRINTF_ADVANCED_ENABLE */
    if (*++p == '.')
    {
        /* Must get precision field width, if present. */
        precision_width = 0U;
        done            = 0U;
        while (0U == done)
        {
            char c = *++p;
            if ((c >= '0') && (c <= '9'))
            {
                precision_width = (precision_width * 10U) + ((uint32_t)c - (uint32_t)'0');
#if PRINTF_ADVANCED_ENABLE
                if (NULL != valid_precision_width)
                {
                    *valid_precision_width = true;
                }
#endif /* PRINTF_ADVANCED_ENABLE */
            }
#if PRINTF_ADVANCED_ENABLE
            else if (c == '*')
            {
                precision_width = (uint32_t)va_arg(*ap, uint32_t);
                if (NULL != valid_precision_width)
                {
                    *valid_precision_width = true;
                }
            }
#endif /* PRINTF_ADVANCED_ENABLE */
            else
            {
                /* We've gone one char too far. */
                --p;
                done = 1U;
            }
        }
    }
    else
    {
        /* We've gone one char too far. */
        --p;
    }
    *s = p;
    return precision_width;
}

static uint32_t PrintIsobpu(const char c)
{
    uint32_t ret = 0U;
    if ((c == 'o') || (c == 'b') || (c == 'p') || (c == 'u'))
    {
        ret = 1U;
    }
    return ret;
}

static uint32_t PrintIsdi(const char c)
{
    uint32_t ret = 0U;
    if ((c == 'd') || (c == 'i'))
    {
        ret = 1U;
    }
    return ret;
}

static void PrintOutputdifFobpu(uint32_t flags_used,
                                uint32_t field_width,
                                uint32_t vlen,
                                char schar,
                                char *vstrp,
                                printfCb cb,
                                char *buf,
                                int32_t *count)
{
#if PRINTF_ADVANCED_ENABLE
    /* Do the ZERO pad. */
    if (0U != (flags_used & (uint32_t)kPRINTF_Zero))
    {
        if ('\0' != schar)
        {
            cb(buf, count, schar, 1);
            schar = '\0';
        }
        cb(buf, count, '0', (int)field_width - (int)vlen);
        vlen = field_width;
    }
    else
    {
        if (0U == (flags_used & (uint32_t)kPRINTF_Minus))
        {
            cb(buf, count, ' ', (int)field_width - (int)vlen);
            if ('\0' != schar)
            {
                cb(buf, count, schar, 1);
                schar = '\0';
            }
        }
    }
    /* The string was built in reverse order, now display in correct order. */
    if ('\0' != schar)
    {
        cb(buf, count, schar, 1);
    }
#else
    cb(buf, count, ' ', (int)field_width - (int)vlen);
#endif /* PRINTF_ADVANCED_ENABLE */
    while ('\0' != (*vstrp))
    {
        cb(buf, count, *vstrp--, 1);
    }
#if PRINTF_ADVANCED_ENABLE
    if (0U != (flags_used & (uint32_t)kPRINTF_Minus))
    {
        cb(buf, count, ' ', (int)field_width - (int)vlen);
    }
#endif /* PRINTF_ADVANCED_ENABLE */
}

static void PrintOutputxX(uint32_t flags_used,
                          uint32_t field_width,
                          uint32_t vlen,
                          bool use_caps,
                          char *vstrp,
                          printfCb cb,
                          char *buf,
                          int32_t *count)
{
#if PRINTF_ADVANCED_ENABLE
    uint8_t dschar = 0;
    if (0U != (flags_used & (uint32_t)kPRINTF_Zero))
    {
        if (0U != (flags_used & (uint32_t)kPRINTF_Pound))
        {
            cb(buf, count, '0', 1);
            cb(buf, count, (use_caps ? 'X' : 'x'), 1);
            dschar = 1U;
        }
        cb(buf, count, '0', (int)field_width - (int)vlen);
        vlen = field_width;
    }
    else
    {
        if (0U == (flags_used & (uint32_t)kPRINTF_Minus))
        {
            if (0U != (flags_used & (uint32_t)kPRINTF_Pound))
            {
                vlen += 2U;
            }
            cb(buf, count, ' ', (int)field_width - (int)vlen);
            if (0U != (flags_used & (uint32_t)kPRINTF_Pound))
            {
                cb(buf, count, '0', 1);
                cb(buf, count, (use_caps ? 'X' : 'x'), 1);
                dschar = 1U;
            }
        }
    }

    if ((0U != (flags_used & (uint32_t)kPRINTF_Pound)) && (0U == dschar))
    {
        cb(buf, count, '0', 1);
        cb(buf, count, (use_caps ? 'X' : 'x'), 1);
        vlen += 2U;
    }
#else
    cb(buf, count, ' ', (int)field_width - (int)vlen);
#endif /* PRINTF_ADVANCED_ENABLE */
    while ('\0' != (*vstrp))
    {
        cb(buf, count, *vstrp--, 1);
    }
#if PRINTF_ADVANCED_ENABLE
    if (0U != (flags_used & (uint32_t)kPRINTF_Minus))
    {
        cb(buf, count, ' ', (int)field_width - (int)vlen);
    }
#endif /* PRINTF_ADVANCED_ENABLE */
}

static uint32_t PrintIsfF(const char c)
{
    uint32_t ret = 0U;
    if ((c == 'f') || (c == 'F'))
    {
        ret = 1U;
    }
    return ret;
}

static uint32_t PrintIsxX(const char c)
{
    uint32_t ret = 0U;
    if ((c == 'x') || (c == 'X'))
    {
        ret = 1U;
    }
    return ret;
}

#if PRINTF_ADVANCED_ENABLE
static uint32_t PrintCheckFlags(const char **s)
{
    const char *p = *s;
    /* First check for specification modifier flags. */
    uint32_t flags_used = 0U;
    bool done           = false;
    while (false == done)
    {
        switch (*++p)
        {
            case '-':
                flags_used |= (uint32_t)kPRINTF_Minus;
                break;
            case '+':
                flags_used |= (uint32_t)kPRINTF_Plus;
                break;
            case ' ':
                flags_used |= (uint32_t)kPRINTF_Space;
                break;
            case '0':
                flags_used |= (uint32_t)kPRINTF_Zero;
                break;
            case '#':
                flags_used |= (uint32_t)kPRINTF_Pound;
                break;
            default:
                /* We've gone one char too far. */
                --p;
                done = true;
                break;
        }
    }
    *s = p;
    return flags_used;
}
#endif /* PRINTF_ADVANCED_ENABLE */

#if PRINTF_ADVANCED_ENABLE
/*
 * Check for the length modifier.
 */
static uint32_t PrintGetLengthFlag(const char **s)
{
    const char *p = *s;
    /* First check for specification modifier flags. */
    uint32_t flags_used = 0U;

    switch (/* c = */ *++p)
    {
        case 'h':
            if (*++p != 'h')
            {
                flags_used |= (uint32_t)kPRINTF_LengthShortInt;
                --p;
            }
            else
            {
                flags_used |= (uint32_t)kPRINTF_LengthChar;
            }
            break;
        case 'l':
            if (*++p != 'l')
            {
                flags_used |= (uint32_t)kPRINTF_LengthLongInt;
                --p;
            }
            else
            {
                flags_used |= (uint32_t)kPRINTF_LengthLongLongInt;
            }
            break;
        default:
            /* we've gone one char too far */
            --p;
            break;
    }
    *s = p;
    return flags_used;
}
#else
static void PrintFilterLengthFlag(const char **s)
{
    const char *p = *s;
    char ch;

    do
    {
        ch = *++p;
    } while ((ch == 'h') || (ch == 'l'));

    *s = --p;
}
#endif /* PRINTF_ADVANCED_ENABLE */

static uint8_t PrintGetRadixFromobpu(const char c)
{
    uint8_t radix;

    if (c == 'o')
    {
        radix = 8U;
    }
    else if (c == 'b')
    {
        radix = 2U;
    }
    else if (c == 'p')
    {
        radix = 16U;
    }
    else
    {
        radix = 10U;
    }
    return radix;
}

static uint32_t ScanIsWhiteSpace(const char c)
{
    uint32_t ret = 0U;
    if ((c == ' ') || (c == '\t') || (c == '\n') || (c == '\r') || (c == '\v') || (c == '\f'))
    {
        ret = 1U;
    }
    return ret;
}

static uint32_t ScanIgnoreWhiteSpace(const char **s)
{
    uint32_t count = 0U;
    char c;

    c = **s;
    while (1U == ScanIsWhiteSpace(c))
    {
        count++;
        (*s)++;
        c = **s;
    }
    return count;
}

static int32_t ConvertRadixNumToString(char *numstr, void *nump, int32_t neg, int32_t radix, bool use_caps)
{
#if PRINTF_ADVANCED_ENABLE
    int64_t a;
    int64_t b;
    int64_t c;

    uint64_t ua;
    uint64_t ub;
    uint64_t uc;
#else
    int32_t a;
    int32_t b;
    int32_t c;

    uint32_t ua;
    uint32_t ub;
    uint32_t uc;
#endif /* PRINTF_ADVANCED_ENABLE */

    int32_t nlen;
    char *nstrp;

    nlen     = 0;
    nstrp    = numstr;
    *nstrp++ = '\0';

#if !(PRINTF_ADVANCED_ENABLE > 0)
    neg = 0;
#endif

    if (0 != neg)
    {
#if PRINTF_ADVANCED_ENABLE
        a = *(int64_t *)nump;
#else
        a = *(int32_t *)nump;
#endif /* PRINTF_ADVANCED_ENABLE */
        if (a == 0)
        {
            *nstrp = '0';
            ++nlen;
            return nlen;
        }
        while (a != 0)
        {
#if PRINTF_ADVANCED_ENABLE
            b = (int64_t)a / (int64_t)radix;
            c = (int64_t)a - ((int64_t)b * (int64_t)radix);
            if (c < 0)
            {
                c = (int64_t)'0' - c;
            }
#else
            b = a / radix;
            c = a - (b * radix);
            if (c < 0)
            {
                c = (int32_t)'0' - c;
            }
#endif /* PRINTF_ADVANCED_ENABLE */
            else
            {
                c = c + (int32_t)'0';
            }
            a        = b;
            *nstrp++ = (char)c;
            ++nlen;
        }
    }
    else
    {
#if PRINTF_ADVANCED_ENABLE
        ua = *(uint64_t *)nump;
#else
        ua = *(uint32_t *)nump;
#endif /* PRINTF_ADVANCED_ENABLE */
        if (ua == 0U)
        {
            *nstrp = '0';
            ++nlen;
            return nlen;
        }
        while (ua != 0U)
        {
#if PRINTF_ADVANCED_ENABLE
            ub = (uint64_t)ua / (uint64_t)radix;
            uc = (uint64_t)ua - ((uint64_t)ub * (uint64_t)radix);
#else
            ub = ua / (uint32_t)radix;
            uc = ua - (ub * (uint32_t)radix);
#endif /* PRINTF_ADVANCED_ENABLE */

            if (uc < 10U)
            {
                uc = uc + (uint32_t)'0';
            }
            else
            {
                uc = uc - 10U + (uint32_t)(use_caps ? 'A' : 'a');
            }
            ua       = ub;
            *nstrp++ = (char)uc;
            ++nlen;
        }
    }
    return nlen;
}

#if PRINTF_FLOAT_ENABLE
static int32_t ConvertFloatRadixNumToString(char *numstr, void *nump, int32_t radix, uint32_t precision_width)
{
    int32_t a;
    int32_t b;
    int32_t c;
    int32_t i;
    double fa;
    double dc;
    double fb;
    double r;
    double fractpart;
    double intpart;

    int32_t nlen;
    char *nstrp;
    nlen     = 0;
    nstrp    = numstr;
    *nstrp++ = '\0';
    r        = *(double *)nump;
    if (0.0 == r)
    {
        *nstrp = '0';
        ++nlen;
        return nlen;
    }
    fractpart = modf((double)r, (double *)&intpart);
    /* Process fractional part. */
    for (i = 0; i < (int32_t)precision_width; i++)
    {
        fractpart *= (double)radix;
    }
    if (r >= (double)0.0)
    {
        fa = fractpart + (double)0.5;
        if (fa >= pow((double)10, (double)precision_width))
        {
            intpart++;
        }
    }
    else
    {
        fa = fractpart - (double)0.5;
        if (fa <= -pow((double)10, (double)precision_width))
        {
            intpart--;
        }
    }
    for (i = 0; i < (int32_t)precision_width; i++)
    {
        fb = fa / (double)radix;
        dc = (fa - (double)(int64_t)fb * (double)radix);
        c  = (int32_t)dc;
        if (c < 0)
        {
            c = (int32_t)'0' - c;
        }
        else
        {
            c = c + '0';
        }
        fa       = fb;
        *nstrp++ = (char)c;
        ++nlen;
    }
    *nstrp++ = (char)'.';
    ++nlen;
    a = (int32_t)intpart;
    if (a == 0)
    {
        *nstrp++ = '0';
        ++nlen;
    }
    else
    {
        while (a != 0)
        {
            b = (int32_t)a / (int32_t)radix;
            c = (int32_t)a - ((int32_t)b * (int32_t)radix);
            if (c < 0)
            {
                c = (int32_t)'0' - c;
            }
            else
            {
                c = c + '0';
            }
            a        = b;
            *nstrp++ = (char)c;
            ++nlen;
        }
    }
    return nlen;
}
#endif /* PRINTF_FLOAT_ENABLE */

/*!
 * brief This function outputs its parameters according to a formatted string.
 *
 * note I/O is performed by calling given function pointer using following
 * (*func_ptr)(c);
 *
 * param[in] fmt_ptr   Format string for printf.
 * param[in] args_ptr  Arguments to printf.
 * param[in] buf  pointer to the buffer
 * param cb print callback function pointer
 *
 * return Number of characters to be print
 */
int StrFormatPrintf(const char *fmt, va_list ap, char *buf, printfCb cb)
{
    /* va_list ap; */
    const char *p;
    char c;

    char vstr[33];
    char *vstrp  = NULL;
    int32_t vlen = 0;

    int32_t count = 0;

    uint32_t field_width;
    uint32_t precision_width;
    char *sval;
    int32_t cval;
    bool use_caps;
    uint8_t radix = 0;

#if PRINTF_ADVANCED_ENABLE
    uint32_t flags_used;
    char schar;
    int64_t ival;
    uint64_t uval = 0;
    bool valid_precision_width;
#else
    int32_t ival;
    uint32_t uval = 0;
#endif /* PRINTF_ADVANCED_ENABLE */

#if PRINTF_FLOAT_ENABLE
    double fval;
#endif /* PRINTF_FLOAT_ENABLE */

    /* Start parsing apart the format string and display appropriate formats and data. */
    p = fmt;
    while (true)
    {
        if ('\0' == *p)
        {
            break;
        }
        c = *p;
        /*
         * All formats begin with a '%' marker.  Special chars like
         * '\n' or '\t' are normally converted to the appropriate
         * character by the __compiler__.  Thus, no need for this
         * routine to account for the '\' character.
         */
        if (c != '%')
        {
            cb(buf, &count, c, 1);
            p++;
            /* By using 'continue', the next iteration of the loop is used, skipping the code that follows. */
            continue;
        }

        use_caps = true;

#if PRINTF_ADVANCED_ENABLE
        /* First check for specification modifier flags. */
        flags_used = PrintCheckFlags(&p);
#endif /* PRINTF_ADVANCED_ENABLE */

        /* Next check for minimum field width. */
        field_width = PrintGetWidth(&p, &ap);

        /* Next check for the width and precision field separator. */
#if PRINTF_ADVANCED_ENABLE
        precision_width = PrintGetPrecision(&p, &ap, &valid_precision_width);
#else
        precision_width = PrintGetPrecision(&p, &ap, NULL);
        (void)precision_width;
#endif

#if PRINTF_ADVANCED_ENABLE
        /* Check for the length modifier. */
        flags_used |= PrintGetLengthFlag(&p);
#else
        /* Filter length modifier. */
        PrintFilterLengthFlag(&p);
#endif

        /* Now we're ready to examine the format. */
        c = *++p;
        {
            if (1U == PrintIsdi(c))
            {
#if PRINTF_ADVANCED_ENABLE
                if (0U != (flags_used & (uint32_t)kPRINTF_LengthLongLongInt))
                {
                    ival = (int64_t)va_arg(ap, int64_t);
                }
                else
#endif /* PRINTF_ADVANCED_ENABLE */
                {
                    ival = (int32_t)va_arg(ap, int32_t);
                }
                vlen  = ConvertRadixNumToString(vstr, (void *)&ival, 1, 10, use_caps);
                vstrp = &vstr[vlen];
#if PRINTF_ADVANCED_ENABLE
                vlen += (int32_t)PrintGetSignChar(ival, flags_used, &schar);
                PrintOutputdifFobpu(flags_used, field_width, (uint32_t)vlen, schar, vstrp, cb, buf, &count);
#else
                PrintOutputdifFobpu(0U, field_width, (uint32_t)vlen, '\0', vstrp, cb, buf, &count);
#endif
            }
            else if (1U == PrintIsfF(c))
            {
#if PRINTF_FLOAT_ENABLE
                fval  = (double)va_arg(ap, double);
                vlen  = ConvertFloatRadixNumToString(vstr, &fval, 10, precision_width);
                vstrp = &vstr[vlen];

#if PRINTF_ADVANCED_ENABLE
                vlen += (int32_t)PrintGetSignChar(((fval < 0.0) ? ((int64_t)-1) : ((int64_t)fval)), flags_used, &schar);
                PrintOutputdifFobpu(flags_used, field_width, (uint32_t)vlen, schar, vstrp, cb, buf, &count);
#else
                PrintOutputdifFobpu(0, field_width, (uint32_t)vlen, '\0', vstrp, cb, buf, &count);
#endif

#else
                (void)va_arg(ap, double);
#endif /* PRINTF_FLOAT_ENABLE */
            }
            else if (1U == PrintIsxX(c))
            {
                if (c == 'x')
                {
                    use_caps = false;
                }
#if PRINTF_ADVANCED_ENABLE
                if (0U != (flags_used & (uint32_t)kPRINTF_LengthLongLongInt))
                {
                    uval = (uint64_t)va_arg(ap, uint64_t);
                }
                else
#endif /* PRINTF_ADVANCED_ENABLE */
                {
                    uval = (uint32_t)va_arg(ap, uint32_t);
                }
                vlen  = ConvertRadixNumToString(vstr, &uval, 0, 16, use_caps);
                vstrp = &vstr[vlen];
#if PRINTF_ADVANCED_ENABLE
                PrintOutputxX(flags_used, field_width, (uint32_t)vlen, use_caps, vstrp, cb, buf, &count);
#else
                PrintOutputxX(0U, field_width, (uint32_t)vlen, use_caps, vstrp, cb, buf, &count);
#endif
            }
            else if (1U == PrintIsobpu(c))
            {
#if PRINTF_ADVANCED_ENABLE
                if (0U != (flags_used & (uint32_t)kPRINTF_LengthLongLongInt))
                {
                    uval = (uint64_t)va_arg(ap, uint64_t);
                }
                else
#endif /* PRINTF_ADVANCED_ENABLE */
                {
                    uval = (uint32_t)va_arg(ap, uint32_t);
                }

                radix = PrintGetRadixFromobpu(c);

                vlen  = ConvertRadixNumToString(vstr, &uval, 0, (int32_t)radix, use_caps);
                vstrp = &vstr[vlen];
#if PRINTF_ADVANCED_ENABLE
                PrintOutputdifFobpu(flags_used, field_width, (uint32_t)vlen, '\0', vstrp, cb, buf, &count);
#else
                PrintOutputdifFobpu(0U, field_width, (uint32_t)vlen, '\0', vstrp, cb, buf, &count);
#endif
            }
            else if (c == 'c')
            {
                cval = (int32_t)va_arg(ap, uint32_t);
                cb(buf, &count, cval, 1);
            }
            else if (c == 's')
            {
                sval = (char *)va_arg(ap, char *);
                if (NULL != sval)
                {
#if PRINTF_ADVANCED_ENABLE
                    if (valid_precision_width)
                    {
                        vlen = (int32_t)precision_width;
                    }
                    else
                    {
                        vlen = (int32_t)strlen(sval);
                    }
#else
                    vlen = (int32_t)strlen(sval);
#endif /* PRINTF_ADVANCED_ENABLE */
#if PRINTF_ADVANCED_ENABLE
                    if (0U == (flags_used & (uint32_t)kPRINTF_Minus))
#endif /* PRINTF_ADVANCED_ENABLE */
                    {
                        cb(buf, &count, ' ', (int)field_width - (int)vlen);
                    }

#if PRINTF_ADVANCED_ENABLE
                    if (valid_precision_width)
                    {
                        while (('\0' != *sval) && (vlen > 0))
                        {
                            cb(buf, &count, *sval++, 1);
                            vlen--;
                        }
                        /* In case that vlen sval is shorter than vlen */
                        vlen = (int32_t)precision_width - vlen;
                    }
                    else
                    {
#endif /* PRINTF_ADVANCED_ENABLE */
                        while ('\0' != (*sval))
                        {
                            cb(buf, &count, *sval++, 1);
                        }
#if PRINTF_ADVANCED_ENABLE
                    }
#endif /* PRINTF_ADVANCED_ENABLE */

#if PRINTF_ADVANCED_ENABLE
                    if (0U != (flags_used & (uint32_t)kPRINTF_Minus))
                    {
                        cb(buf, &count, ' ', (int32_t)field_width - vlen);
                    }
#endif /* PRINTF_ADVANCED_ENABLE */
                }
            }
            else
            {
                cb(buf, &count, c, 1);
            }
        }
        p++;
    }

    return count;
}

#if SCANF_FLOAT_ENABLE
static uint8_t StrFormatScanIsFloat(char *c)
{
    uint8_t ret = 0U;
    if (('a' == (*c)) || ('A' == (*c)) || ('e' == (*c)) || ('E' == (*c)) || ('f' == (*c)) || ('F' == (*c)) ||
        ('g' == (*c)) || ('G' == (*c)))
    {
        ret = 1U;
    }
    return ret;
}
#endif

static uint8_t StrFormatScanIsFormatStarting(char *c)
{
    uint8_t ret = 1U;
    if ((*c != '%'))
    {
        ret = 0U;
    }
    else if (*(c + 1) == '%')
    {
        ret = 0U;
    }
    else
    {
        /*MISRA rule 15.7*/
    }

    return ret;
}

static uint8_t StrFormatScanGetBase(uint8_t base, const char *s)
{
    if (base == 0U)
    {
        if (s[0] == '0')
        {
            if ((s[1] == 'x') || (s[1] == 'X'))
            {
                base = 16;
            }
            else
            {
                base = 8;
            }
        }
        else
        {
            base = 10;
        }
    }
    return base;
}

static uint8_t StrFormatScanCheckSymbol(const char *p, int8_t *neg)
{
    uint8_t len;
    switch (*p)
    {
        case '-':
            *neg = -1;
            len  = 1;
            break;
        case '+':
            *neg = 1;
            len  = 1;
            break;
        default:
            *neg = 1;
            len  = 0;
            break;
    }
    return len;
}

static uint8_t StrFormatScanFillInteger(uint32_t flag, va_list *args_ptr, int32_t val)
{
#if SCANF_ADVANCED_ENABLE
    if (0U != (flag & (uint32_t)kSCANF_Suppress))
    {
        return 0u;
    }

    switch (flag & (uint32_t)kSCANF_LengthMask)
    {
        case (uint32_t)kSCANF_LengthChar:
            if (0U != (flag & (uint32_t)kSCANF_TypeSinged))
            {
                *va_arg(*args_ptr, signed char *) = (signed char)val;
            }
            else
            {
                *va_arg(*args_ptr, unsigned char *) = (unsigned char)val;
            }
            break;
        case (uint32_t)kSCANF_LengthShortInt:
            if (0U != (flag & (uint32_t)kSCANF_TypeSinged))
            {
                *va_arg(*args_ptr, signed short *) = (signed short)val;
            }
            else
            {
                *va_arg(*args_ptr, unsigned short *) = (unsigned short)val;
            }
            break;
        case (uint32_t)kSCANF_LengthLongInt:
            if (0U != (flag & (uint32_t)kSCANF_TypeSinged))
            {
                *va_arg(*args_ptr, signed long int *) = (signed long int)val;
            }
            else
            {
                *va_arg(*args_ptr, unsigned long int *) = (unsigned long int)val;
            }
            break;
        case (uint32_t)kSCANF_LengthLongLongInt:
            if (0U != (flag & (uint32_t)kSCANF_TypeSinged))
            {
                *va_arg(*args_ptr, signed long long int *) = (signed long long int)val;
            }
            else
            {
                *va_arg(*args_ptr, unsigned long long int *) = (unsigned long long int)val;
            }
            break;
        default:
            /* The default type is the type int. */
            if (0U != (flag & (uint32_t)kSCANF_TypeSinged))
            {
                *va_arg(*args_ptr, signed int *) = (signed int)val;
            }
            else
            {
                *va_arg(*args_ptr, unsigned int *) = (unsigned int)val;
            }
            break;
    }
#else
    /* The default type is the type int. */
    if (0U != (flag & (uint32_t)kSCANF_TypeSinged))
    {
        *va_arg(*args_ptr, signed int *) = (signed int)val;
    }
    else
    {
        *va_arg(*args_ptr, unsigned int *) = (unsigned int)val;
    }
#endif /* SCANF_ADVANCED_ENABLE */

    return 1u;
}

#if SCANF_FLOAT_ENABLE
static uint8_t StrFormatScanFillFloat(uint32_t flag, va_list *args_ptr, double fnum)
{
#if SCANF_ADVANCED_ENABLE
    if (0U != (flag & (uint32_t)kSCANF_Suppress))
    {
        return 0u;
    }
    else
#endif /* SCANF_ADVANCED_ENABLE */
    {
        if (0U != (flag & (uint32_t)kSCANF_LengthLongLongDouble))
        {
            *va_arg(*args_ptr, double *) = fnum;
        }
        else
        {
            *va_arg(*args_ptr, float *) = (float)fnum;
        }
        return 1u;
    }
}
#endif /* SCANF_FLOAT_ENABLE */

static uint8_t StrFormatScanfStringHandling(char **str, uint32_t *flag, uint32_t *field_width, uint8_t *base)
{
    uint8_t exitPending = 0U;
    char *c             = *str;

    /* Loop to get full conversion specification. */
    while (('\0' != (*c)) && (0U == (*flag & (uint32_t)kSCANF_DestMask)))
    {
#if SCANF_ADVANCED_ENABLE
        if ('*' == (*c))
        {
            if (0U != ((*flag) & (uint32_t)kSCANF_Suppress))
            {
                /* Match failure. */
                exitPending = 1U;
            }
            else
            {
                (*flag) |= (uint32_t)kSCANF_Suppress;
            }
        }
        else if ('h' == (*c))
        {
            if (0U != ((*flag) & (uint32_t)kSCANF_LengthMask))
            {
                /* Match failure. */
                exitPending = 1U;
            }
            else
            {
                if (c[1] == 'h')
                {
                    (*flag) |= (uint32_t)kSCANF_LengthChar;
                    c++;
                }
                else
                {
                    (*flag) |= (uint32_t)kSCANF_LengthShortInt;
                }
            }
        }
        else if ('l' == (*c))
        {
            if (0U != ((*flag) & (uint32_t)kSCANF_LengthMask))
            {
                /* Match failure. */
                exitPending = 1U;
            }
            else
            {
                if (c[1] == 'l')
                {
                    (*flag) |= (uint32_t)kSCANF_LengthLongLongInt;
                    c++;
                }
                else
                {
                    (*flag) |= (uint32_t)kSCANF_LengthLongInt;
                }
            }
        }
        else
#endif /* SCANF_ADVANCED_ENABLE */
#if SCANF_FLOAT_ENABLE
            if ('L' == (*c))
        {
            if (0U != ((*flag) & (uint32_t)kSCANF_LengthMask))
            {
                /* Match failure. */
                exitPending = 1U;
            }
            else
            {
                (*flag) |= (uint32_t)kSCANF_LengthLongLongDouble;
            }
        }
        else
#endif /* SCANF_FLOAT_ENABLE */
            if (((*c) >= '0') && ((*c) <= '9'))
        {
            {
                char *p;
                errno          = 0;
                (*field_width) = strtoul(c, &p, 10);
                if (0 != errno)
                {
                    *field_width = 0U;
                }
                c = p - 1;
            }
        }
        else if ('d' == (*c))
        {
            (*base) = 10U;
            (*flag) |= (uint32_t)kSCANF_TypeSinged;
            (*flag) |= (uint32_t)kSCANF_DestInt;
        }
        else if ('u' == (*c))
        {
            (*base) = 10U;
            (*flag) |= (uint32_t)kSCANF_DestInt;
        }
        else if ('o' == (*c))
        {
            (*base) = 8U;
            (*flag) |= (uint32_t)kSCANF_DestInt;
        }
        else if (('x' == (*c)))
        {
            (*base) = 16U;
            (*flag) |= (uint32_t)kSCANF_DestInt;
        }
        else if ('X' == (*c))
        {
            (*base) = 16U;
            (*flag) |= (uint32_t)kSCANF_DestInt;
        }
        else if ('i' == (*c))
        {
            (*base) = 0U;
            (*flag) |= (uint32_t)kSCANF_DestInt;
        }
#if SCANF_FLOAT_ENABLE
        else if (1U == StrFormatScanIsFloat(c))
        {
            (*flag) |= (uint32_t)kSCANF_DestFloat;
        }
#endif /* SCANF_FLOAT_ENABLE */
        else if ('c' == (*c))
        {
            (*flag) |= (uint32_t)kSCANF_DestChar;
            if (MAX_FIELD_WIDTH == (*field_width))
            {
                (*field_width) = 1;
            }
        }
        else if ('s' == (*c))
        {
            (*flag) |= (uint32_t)kSCANF_DestString;
        }
        else
        {
            exitPending = 1U;
        }

        if (1U == exitPending)
        {
            break;
        }
        else
        {
            c++;
        }
    }
    *str = c;
    return exitPending;
}

/*!
 * brief Converts an input line of ASCII characters based upon a provided
 * string format.
 *
 * param[in] line_ptr The input line of ASCII data.
 * param[in] format   Format first points to the format string.
 * param[in] args_ptr The list of parameters.
 *
 * return Number of input items converted and assigned.
 * retval IO_EOF When line_ptr is empty string "".
 */
int StrFormatScanf(const char *line_ptr, char *format, va_list args_ptr)
{
    uint8_t base;
    int8_t neg;
    /* Identifier for the format string. */
    char *c = format;
    char *buf;
    /* Flag telling the conversion specification. */
    uint32_t flag = 0;
    /* Filed width for the matching input streams. */
    uint32_t field_width;
    /* How many arguments are assigned except the suppress. */
    uint32_t nassigned = 0;
    /* How many characters are read from the input streams. */
    uint32_t n_decode = 0;

    int32_t val;

    uint8_t added;

    uint8_t exitPending = 0;

    const char *s;
#if SCANF_FLOAT_ENABLE
    char *s_temp; /* MISRA C-2012 Rule 11.3 */
#endif

    /* Identifier for the input string. */
    const char *p = line_ptr;

#if SCANF_FLOAT_ENABLE
    double fnum = 0.0;
#endif /* SCANF_FLOAT_ENABLE */
    /* Return EOF error before any conversion. */
    if (*p == '\0')
    {
        return -1;
    }

    /* Decode directives. */
    while (('\0' != (*c)) && ('\0' != (*p)))
    {
        /* Ignore all white-spaces in the format strings. */
        if (0U != ScanIgnoreWhiteSpace((const char **)((void *)&c)))
        {
            n_decode += ScanIgnoreWhiteSpace(&p);
        }
        else if (0U == StrFormatScanIsFormatStarting(c))
        {
            /* Ordinary characters. */
            c++;
            if (*p == *c)
            {
                n_decode++;
                p++;
                c++;
            }
            else
            {
                /* Match failure. Misalignment with C99, the unmatched characters need to be pushed back to stream.
                 * However, it is deserted now. */
                break;
            }
        }
        else
        {
            /* convernsion specification */
            c++;
            /* Reset. */
            flag        = 0;
            field_width = MAX_FIELD_WIDTH;
            base        = 0;
            added       = 0U;

            exitPending = StrFormatScanfStringHandling(&c, &flag, &field_width, &base);

            if (1U == exitPending)
            {
                /* Format strings are exhausted. */
                break;
            }

            /* Matching strings in input streams and assign to argument. */
            if ((flag & (uint32_t)kSCANF_DestMask) == (uint32_t)kSCANF_DestChar)
            {
                s   = (const char *)p;
                buf = va_arg(args_ptr, char *);
                while ((0U != (field_width--))
#if SCANF_ADVANCED_ENABLE
                       && ('\0' != (*p))
#endif
                )
                {
#if SCANF_ADVANCED_ENABLE
                    if (0U != (flag & (uint32_t)kSCANF_Suppress))
                    {
                        p++;
                    }
                    else
#endif
                    {
                        *buf++ = *p++;
#if SCANF_ADVANCED_ENABLE
                        added = 1u;
#endif
                    }
                    n_decode++;
                }

#if SCANF_ADVANCED_ENABLE
                if (1u == added)
#endif
                {
                    nassigned++;
                }
            }
            else if ((flag & (uint32_t)kSCANF_DestMask) == (uint32_t)kSCANF_DestString)
            {
                n_decode += ScanIgnoreWhiteSpace(&p);
                s   = p;
                buf = va_arg(args_ptr, char *);
                while ((0U != (field_width--)) && (*p != '\0') && (0U == ScanIsWhiteSpace(*p)))
                {
#if SCANF_ADVANCED_ENABLE
                    if (0U != (flag & (uint32_t)kSCANF_Suppress))
                    {
                        p++;
                    }
                    else
#endif
                    {
                        *buf++ = *p++;
#if SCANF_ADVANCED_ENABLE
                        added = 1u;
#endif
                    }
                    n_decode++;
                }

#if SCANF_ADVANCED_ENABLE
                if (1u == added)
#endif
                {
                    /* Add NULL to end of string. */
                    *buf = '\0';
                    nassigned++;
                }
            }
            else if ((flag & (uint32_t)kSCANF_DestMask) == (uint32_t)kSCANF_DestInt)
            {
                n_decode += ScanIgnoreWhiteSpace(&p);
                s    = p;
                val  = 0;
                base = StrFormatScanGetBase(base, s);

                added = StrFormatScanCheckSymbol(p, &neg);
                n_decode += added;
                p += added;
                field_width -= added;

                s = p;
                if (strlen(p) > field_width)
                {
                    char temp[12];
                    char *tempEnd;
                    (void)memcpy(temp, p, sizeof(temp) - 1U);
                    temp[sizeof(temp) - 1U] = '\0';
                    errno                   = 0;
                    val                     = (int32_t)strtoul(temp, &tempEnd, (int)base);
                    if (0 != errno)
                    {
                        break;
                    }
                    p = p + (tempEnd - temp);
                }
                else
                {
                    char *tempEnd;
                    val   = 0;
                    errno = 0;
                    val   = (int32_t)strtoul(p, &tempEnd, (int)base);
                    if (0 != errno)
                    {
                        break;
                    }
                    p = tempEnd;
                }
                n_decode += (uint32_t)p - (uint32_t)s;

                val *= neg;

                nassigned += StrFormatScanFillInteger(flag, &args_ptr, val);
            }
#if SCANF_FLOAT_ENABLE
            else if ((flag & (uint32_t)kSCANF_DestMask) == (uint32_t)kSCANF_DestFloat)
            {
                n_decode += ScanIgnoreWhiteSpace(&p);
                fnum  = 0.0;
                errno = 0;

                fnum = strtod(p, (char **)&s_temp);
                s    = s_temp; /* MISRA C-2012 Rule 11.3 */

                /* MISRA C-2012 Rule 22.9 */
                if (0 != errno)
                {
                    break;
                }

                if ((fnum < HUGE_VAL) && (fnum > -HUGE_VAL))
                {
                    n_decode = (uint32_t)n_decode + (uint32_t)s - (uint32_t)p;
                    p        = s;
                    nassigned += StrFormatScanFillFloat(flag, &args_ptr, fnum);
                }
            }
#endif /* SCANF_FLOAT_ENABLE */
            else
            {
                break;
            }
        }
    }
    return (int)nassigned;
}
