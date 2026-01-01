/* utils
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
#include "sectionapi.h"
#include "stdlib.h"
#include "stdio.h"
#include "freertos_serial.h"
#if defined(__x86_64__)
#include "syscall.h"
#endif

API_FUNCTION int strncmp(const char *s1, const char *s2, unsigned int n) {
    while ( n && *s1 && ( *s1 == *s2 ) )
    {
        ++s1;
        ++s2;
        --n;
    }
    if ( n == (unsigned int)0 )
    {
        return (int)0;
    }
    else
    {
        return ( *(unsigned char *)s1 - *(unsigned char *)s2 );
    }
}
API_FUNCTION long long rdtsc(void)
{
    unsigned hi, lo;
    __asm__ __volatile__ ("rdtsc" : "=a"(lo), "=d"(hi));
    return ( (unsigned long long)lo)|( ((unsigned long long)hi)<<32 );
}


API_FUNCTION int64_t string_to_integer(const char *s, uint32_t length) {
    int64_t result = 0;
    int64_t base = 10;

    if (length > (uint32_t)2) {
        if (s[0] == '0' && (s[1] == 'x' || s[1] == 'X')) {
            s += 2; // Skip the '0x' or '0X'
            base = 16;
        }
    }

    int count = 0;
    while (*s) {
        int value;
        if (*s >= '0' && *s <= '9') {
            value = *s - '0';
        } else if (*s >= 'a' && *s <= 'f') {
            if (base != 16){
               return result;
	    }
            value = *s - 'a' + 10;
        } else if (*s >= 'A' && *s <= 'F') {
            if (base != 16) {
               return result;
	    }
            value = *s - 'A' + 10;
        } else {
            return result;
        }
        result = (int64_t) (result * base + value);
        s++;
        count++;
        if (count >= (int) length){
            return result;
	}
    }
    return result;
}

API_FUNCTION char *strcpy(char *dest, const char *src) {
    char *dest_ptr = dest; 
    while (*src != '\0') {
        *dest = *src;
        dest++;
        src++;
    }
    *dest = '\0'; 
    return dest_ptr;
}
API_FUNCTION char *strncat(char *dest, const char *src, uint64_t n) {
    char *dest_ptr = dest;

    while (*dest_ptr != '\0') {
        dest_ptr++;
    }
    const char *src_ptr = src;
    while (n-- > 0 && *src_ptr != '\0') {
        *dest_ptr = *src_ptr;
        dest_ptr++;
        src_ptr++;
    }

    *dest_ptr = '\0';
    return dest; 
}
API_FUNCTION uint64_t strnlen(const char *str, uint64_t max_len) {
    uint64_t len = 0;

    while (len < max_len && str[len] != '\0') {
        len++;
    }

    return len;
}

API_FUNCTION char *strstr(const char *haystack, const char *needle) {
    if (*needle == '\0') {
        return (char *)haystack;
    }
    const char *hstack = haystack;
    for (; *hstack != '\0'; hstack++) {
        const char *h = haystack;
        const char *n = needle;
        while (*h == *n && *n != '\0') {
            h++;
            n++;
        }

        if (*n == '\0') {
            return (char *)haystack;
        }
    }

    return 0;
}

API_FUNCTION int isspace(int c) {
    return (c == ' '  ||  // space
            c == '\t' ||  // horizontal tab
            c == '\n' ||  // newline
            c == '\v' ||  // vertical tab
            c == '\f' ||  // form feed
            c == '\r');   // carriage return
}

API_FUNCTION unsigned long strtoul(const char *str, char **endptr, int base) {
    unsigned long result = 0;
    int sign = 1;

    while (isspace((unsigned char)*str)) {
        str++;
    }

    if (*str == '-') {
        sign = -1;
        str++;
    } else if (*str == '+') {
        str++;
    }

    if (base == 0) {
        if (*str == '0') {
            if (*(str + 1) == 'x' || *(str + 1) == 'X') {
                base = 16;
                str += 2;
            } else {
                base = 8;
                str++;
            }
        } else {
            base = 10;
        }
    }

    // Parse the digits
    while (*str) {
        int digit;

        if (*str >= '0' && *str <= '9') {
            digit = *str - '0';
        } else if (*str >= 'a' && *str <= 'z') {
            digit = *str - 'a' + 10;
        } else if (*str >= 'A' && *str <= 'Z') {
            digit = *str - 'A' + 10;
        } else {
            break;
        }

        if (digit >= base) {
            break;
        }

        result = (unsigned long)(result * base + digit);
        str++;
    }

    if (endptr) {
        *endptr = (char *)str;
    }

    return (unsigned long) sign * result;
}


API_FUNCTION int strlen(const char *str)
{
    const char *s;
    for (s = str; *s; ++s);
    return (int)(s - str);
}

API_FUNCTION void strncpy( char* _dst, const char* _src, int _n )
{
    int i = 0;
    while(i++ != _n && (*_dst++ = *_src++));
}

API_FUNCTION char * strcat(char *dest, const char *src)
{
    char *rdest = dest;

    while (*dest)
      dest++;
    while (*dest++ = *src++)
      ;
    return rdest;
}
API_FUNCTION void* memcpy(void* dest, const void* src, size_t n) {
    unsigned char* d = (unsigned char*)dest;
    const unsigned char* s = (const unsigned char*)src;

    while (n--) {
        *d++ = *s++;
    }

    return dest;
}
API_FUNCTION int memcmp(const void* ptr1, const void* ptr2, size_t n) {
    const unsigned char* p1 = (const unsigned char*)ptr1;
    const unsigned char* p2 = (const unsigned char*)ptr2;

    while (n--) {
        if (*p1 != *p2) {
            return (*p1 < *p2) ? -1 : 1;
        }
        p1++;
        p2++;
    }

    return(int) 0;
}
API_FUNCTION int strcmp(const char* str1, const char* str2) {
    while (*str1 != '\0' && *str2 != '\0') {
        if (*str1 != *str2) {
            return (*str1 - *str2);
        }
        str1++;
        str2++;
    }

    return (int)(*str1 - *str2);
}
API_FUNCTION void* memset(void* ptr, int value, size_t num) {
    unsigned char* p = (unsigned char*)ptr;

    while (num--) {
        *p++ = (unsigned char)value;
    }

    return (void*)ptr;
}

FREERTOS_SYSTEM_CALL void _putchar(char c)
{
#if defined(__x86_64__)
    extern int vPortIsPrivileged(void);
    if (vPortIsPrivileged()) {
        // We are running at kernel so directly
        // send character to io port
        serial_send(c);
    } else {
        // Make a system call to send the character
        // to io port
        syscall_writec(c);
    }
#else
    serial_send(c);
#endif
}

API_FUNCTION unsigned long __isoc23_strtoul(const char *nptr, char **endptr, int base) {
    return strtoul(nptr, endptr, base); // call the legacy one
}

#if defined(__i386__)
API_FUNCTION uint64_t __udivmoddi4(uint64_t numerator, uint64_t denominator, uint64_t *remainder) {
    uint64_t quotient = 0;
    uint64_t bit = 1;

    if (denominator == (uint64_t) 0) {
        return 0UL;
    }

    while (denominator < (uint64_t) (numerator && (denominator & (1ULL << 63))) == 0) {
        denominator <<= 1;
        bit <<= 1;
    }

    while (bit > (uint64_t) 0) {
        if (numerator >= denominator) {
            numerator -= denominator;
            quotient += bit;
        }
        denominator >>= 1;
        bit >>= 1;
    }

    if (remainder) {
        *remainder = numerator;
    }

    return quotient;
}
API_FUNCTION uint64_t __udivdi3(uint64_t num, uint64_t denom) {
    if (denom == 0UL) {
        return (uint64_t)UINT64_MAX;
    }

    uint64_t quotient = 0;
    uint64_t remainder = 0;

    for (int i = 63; i >= 0; i--) {
        remainder = (remainder << 1) | ((num >> i) & 1);

        if (remainder >= denom) {
            remainder -= denom;
            quotient |= (1ULL << i);
        }
    }

    return quotient;
}
API_FUNCTION uint64_t __umoddi3(uint64_t num, uint64_t denom) {
    if (denom == 0UL) {
        return (uint64_t)UINT64_MAX; 
    }

    uint64_t remainder = 0;

    for (int i = 63; i >= 0; i--) {
        remainder = (remainder << 1) | ((num >> i) & 1);

        if (remainder >= denom) {
            remainder -= denom;
        }
    }

    return remainder;
}

#endif
