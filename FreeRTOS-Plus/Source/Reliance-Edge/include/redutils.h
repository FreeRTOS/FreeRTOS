/*             ----> DO NOT REMOVE THE FOLLOWING NOTICE <----

                   Copyright (c) 2014-2015 Datalight, Inc.
                       All Rights Reserved Worldwide.

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; use version 2 of the License.

    This program is distributed in the hope that it will be useful,
    but "AS-IS," WITHOUT ANY WARRANTY; without even the implied warranty
    of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License along
    with this program; if not, write to the Free Software Foundation, Inc.,
    51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
*/
/*  Businesses and individuals that for commercial or other reasons cannot
    comply with the terms of the GPLv2 license may obtain a commercial license
    before incorporating Reliance Edge into proprietary software for
    distribution in any form.  Visit http://www.datalight.com/reliance-edge for
    more information.
*/
/** @file
*/
#ifndef REDUTILS_H
#define REDUTILS_H


#if REDCONF_ASSERTS == 1
#define REDERROR()      RedOsAssertFail(__FILE__, __LINE__)
#define REDASSERT(EXP)  ((EXP) ? (void)0 : REDERROR())
#else
#define REDERROR()      ((void)0)
#define REDASSERT(EXP)  ((void)0)
#endif


void RedMemCpy(void *pDest, const void *pSrc, uint32_t ulLen);
void RedMemMove(void *pDest, const void *pSrc, uint32_t ulLen);
void RedMemSet(void *pDest, uint8_t bVal, uint32_t ulLen);
int32_t RedMemCmp(const void *pMem1, const void *pMem2, uint32_t ulLen);

uint32_t RedStrLen(const char *pszStr);
int32_t RedStrCmp(const char *pszStr1, const char *pszStr2);
int32_t RedStrNCmp(const char *pszStr1, const char *pszStr2, uint32_t ulLen);
void RedStrNCpy(char *pszDst, const char *pszSrc, uint32_t ulLen);

uint32_t RedCrc32Update(uint32_t ulInitCrc32, const void *pBuffer, uint32_t ulLength);
uint32_t RedCrcNode(const void *pBuffer);

#if REDCONF_API_POSIX == 1
uint32_t RedNameLen(const char *pszName);
#endif

bool RedBitGet(const uint8_t *pbBitmap, uint32_t ulBit);
void RedBitSet(uint8_t *pbBitmap, uint32_t ulBit);
void RedBitClear(uint8_t *pbBitmap, uint32_t ulBit);

#ifdef REDCONF_ENDIAN_SWAP
uint64_t RedRev64(uint64_t ullToRev);
uint32_t RedRev32(uint32_t ulToRev);
uint16_t RedRev16(uint16_t uToRev);
#endif

void RedSignOn(void);


#endif

