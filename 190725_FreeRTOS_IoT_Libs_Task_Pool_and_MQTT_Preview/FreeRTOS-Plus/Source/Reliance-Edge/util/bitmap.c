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
    @brief Implements utilities for working with bitmaps.
*/
#include <redfs.h>


/** @brief Query the state of a bit in a bitmap.

    Bits are counted from most significant to least significant.  Thus, the mask
    for bit zero is 0x80 applied to the first byte in the bitmap.

    @param pbBitmap Pointer to the bitmap.
    @param ulBit    The bit to query.

    @retval Whether the bit is set (true) or clear (false.
*/
bool RedBitGet(
    const uint8_t *pbBitmap,
    uint32_t       ulBit)
{
    bool           fRet;

    if(pbBitmap == NULL)
    {
        REDERROR();
        fRet = false;
    }
    else
    {
        fRet = (pbBitmap[ulBit >> 3U] & (0x80U >> (ulBit & 7U))) != 0U;
    }

    return fRet;
}


/** @brief Set a bit in a bitmap to one.

    Bits are counted from most significant to least significant.  Thus, the mask
    for bit zero is 0x80 applied to the first byte in the bitmap.

    @param pbBitmap Pointer to the bitmap.
    @param ulBit    The bit to set.
*/
void RedBitSet(
    uint8_t *pbBitmap,
    uint32_t ulBit)
{
    REDASSERT(pbBitmap != NULL);

    if(pbBitmap != NULL)
    {
        pbBitmap[ulBit >> 3U] |= (0x80U >> (ulBit & 7U));
    }
}


/** @brief Clear a bit in a bitmap to zero.

    Bits are counted from most significant to least significant.  Thus, the mask
    for bit zero is 0x80 applied to the first byte in the bitmap.

    @param pbBitmap Pointer to the bitmap.
    @param ulBit    The bit to clear.
*/
void RedBitClear(
    uint8_t *pbBitmap,
    uint32_t ulBit)
{
    REDASSERT(pbBitmap != NULL);

    if(pbBitmap != NULL)
    {
        pbBitmap[ulBit >> 3U] &= ~(0x80U >> (ulBit & 7U));
    }
}

