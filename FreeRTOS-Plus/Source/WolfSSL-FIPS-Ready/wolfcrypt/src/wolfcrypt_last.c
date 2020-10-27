/* wolfcrypt_last.c
 *
 * Copyright (C) 2006-2020 wolfSSL Inc.
 *
 * This file is part of wolfSSL.
 *
 * wolfSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * wolfSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1335, USA
 */

/* This file needs to be linked last in order to work correctly */

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

/* in case user set HAVE_FIPS there */
#include <wolfssl/wolfcrypt/settings.h>

#ifdef HAVE_FIPS

#ifdef USE_WINDOWS_API
    #pragma code_seg(".fipsA$q")
    #pragma const_seg(".fipsB$q")
#endif


/* last function of text/code segment */
/* this function needs to be different than wolfCrypt_FIPS_first() */
int wolfCrypt_FIPS_last(void);
int wolfCrypt_FIPS_last(void)
{
    return 1;
}


/* read only end address */
const unsigned int wolfCrypt_FIPS_ro_end[] =
{ 0x1a2b3c4d, 0xffffffff };


#endif /* HAVE_FIPS */

