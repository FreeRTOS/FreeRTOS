/*             ----> DO NOT REMOVE THE FOLLOWING NOTICE <----
 *
 *                 Copyright (c) 2014-2015 Datalight, Inc.
 *                     All Rights Reserved Worldwide.
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; use version 2 of the License.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but "AS-IS," WITHOUT ANY WARRANTY; without even the implied warranty
 *  of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License along
 *  with this program; if not, write to the Free Software Foundation, Inc.,
 *  51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 */

/*  Businesses and individuals that for commercial or other reasons cannot
 *  comply with the terms of the GPLv2 license may obtain a commercial license
 *  before incorporating Reliance Edge into proprietary software for
 *  distribution in any form.  Visit http://www.datalight.com/reliance-edge for
 *  more information.
 */

/** @file
 *  @brief Implements routines for certain 64-bit math operations and simulated
 *         floating point.
 *
 *  RedUint64DivMod32() and RedUint64DivMod64() are derived from code at
 *  http://www.hackersdelight.org.  This web site states explicitly that "You
 *  are free to use, copy, and distribute any of the code on this web site,
 *  whether modified by you or not.  You need not give attribution."
 */
#include <redfs.h>
#include <redtestutils.h>


static uint32_t nlz64( uint64_t ullValue );


/** @brief Return a ratio value formatted as a floating point string accurate to
 *         the specified number of decimal places.
 *
 *  The  function exists to provide floating point style output without using
 *  any actual floating point types.
 *
 *  This function may scale the numbers down to avoid overflow at the high end.
 *  Likewise, potential divide-by-zero errors are internally avoided.  Here are
 *  some examples:
 *
 *  Dividend | Divisor | DecPlaces | Result
 *  -------- | ------- | --------- | ------
 *  12133    | 28545   | 2         | "0.42"
 *  1539     | 506     | 2         | "3.04"
 *
 *  To get a number formatted as a percentage, take the take the portion of the
 *  total (normally the smaller part), multiply it by 100, and pass it to this
 *  function as the Dividend, pass the "total" value to this function as the
 *  Divisor, and specify the desired number of decimal places.
 *
 *  For example, if you have a disk format overhead value of N blocks out of a
 *  total of Y blocks on the disk, and you want to display the format overhead
 *  as a percentage, you would use a function call
 *  similar to:
 *
 *  ~~~{.c}
 *  RedRatio(szBuffer, sizeof(szBuffer), N*100U, Y, 2U);
 *  ~~~
 *
 *  If N=145, Y=4096, and decimal places is 2, the resulting output would be
 *  "3.54".
 *
 *  The string returned will always be null-terminated, even if it means
 *  stomping on the least significant decimal digit.
 *
 *  If either the dividend or divisor values are zero, the string "0.0" will be
 *  returned, with the prescribed number of decimal places.
 *
 *  @note This function has "reasonable" limits which meet the needs of the
 *        various supplemental utilities which use this function.  Extremely
 *        large ratios, or using many decimal places may not function as
 *        desired.
 *
 *  Parameters:
 *  @param pBuffer      A pointer to the buffer in which to store the null
 *                      terminated results.
 *  @param ulBufferLen  The length of the output buffer.
 *  @param ullDividend  The "total" value to divide.
 *  @param ullDivisor   The portion of ullDividend for which to calculate the
 *                      ratio (may be greater than ulDividend).
 *  @param ulDecPlaces  The number of decimal places to use, from 0 to 9.
 *
 *  @return @p pBuffer.
 */
char * RedRatio( char * pBuffer,
                 uint32_t ulBufferLen,
                 uint64_t ullDividend,
                 uint64_t ullDivisor,
                 uint32_t ulDecPlaces )
{
    REDASSERT( pBuffer != NULL );
    REDASSERT( ulBufferLen > 0U );
    REDASSERT( ulDecPlaces <= 9U ); /* arbitrary */

    if( ( ullDivisor > 0U ) && ( ullDividend > 0U ) )
    {
        uint32_t ii;
        uint32_t ulFactor = 1U;
        uint64_t ullDecimal;
        uint64_t ullTemp;

        for( ii = 1U; ii <= ulDecPlaces; ii++ )
        {
            ulFactor *= 10U;
        }

        ullDecimal = RedMulDiv64( ullDividend, ulFactor, ullDivisor );

        /*  Shouldn't really be calling this function in a situation where we
         *  can overflow at this point...
         */
        REDASSERT( ullDecimal != UINT64_MAX );

        if( ullDivisor <= ullDividend )
        {
            uint32_t ulDecimal;

            ( void ) RedUint64DivMod32( ullDecimal, ulFactor, &ulDecimal );
            ullDecimal = ulDecimal;
        }

        ullTemp = RedUint64DivMod64( ullDividend, ullDivisor, NULL );

        if( ulDecPlaces > 0U )
        {
            RedSNPrintf( pBuffer, ulBufferLen, "%llu.%0*llu", ( unsigned long long ) ullTemp,
                         ( unsigned ) ulDecPlaces, ( unsigned long long ) ullDecimal );
        }
        else
        {
            RedSNPrintf( pBuffer, ulBufferLen, "%llu", ( unsigned long long ) ullTemp );
        }
    }
    else
    {
        /*  If either the dividend or divisor is zero, then just output a "0.0"
         *  string with the prescribed number of decimal places.
         */
        if( ulDecPlaces > 0U )
        {
            RedSNPrintf( pBuffer, ulBufferLen, "0.%0*u", ( unsigned ) ulDecPlaces, 0U );
        }
        else
        {
            RedStrNCpy( pBuffer, "0", ulBufferLen );
        }
    }

    /*  Ensure the returned buffer is always null-terminated
     */
    pBuffer[ ulBufferLen - 1U ] = '\0';

    return pBuffer;
}


/** @brief Multiply 64-bit and 32-bit numbers, and divide by a 64-bit number,
 *         returning a 64-bit result.
 *
 *  @note This function may return an approximate value if multiplying
 *        @p ullBase and @p ulMultplier results in a number larger than 64-bits
 *        _and_ this cannot be avoided by scaling.
 *
 *  @param ullBase      The base 64-bit number number.
 *  @param ulMultiplier The 32-bit number by which to multiply.
 *  @param ullDivisor   The 64-bit number by which to divide.
 *
 *  @return The 64-bit unsigned integer result.  Always returns zero if either
 *          @p ullBase or @p ulMultiplier are zero (regardless what
 *          @p ullDivisor is).  Returns UINT64_MAX if an overflow condition
 *          occurred, or if @p ullDivisor is zero.
 */
uint64_t RedMulDiv64( uint64_t ullBase,
                      uint32_t ulMultiplier,
                      uint64_t ullDivisor )
{
    uint64_t ullTemp;

    /*  Result would always be zero if either of these are zero.  Specifically
     *  test this case before looking for a zero divisor.
     */
    if( ( ullBase == 0U ) || ( ulMultiplier == 0U ) )
    {
        return 0U;
    }

    if( ullDivisor == 0U )
    {
        return UINT64_MAX;
    }

    /*  Since we don't have the ability (yet) to use 128-bit numbers, we jump
     *  through the following hoops (in order) to try to determine the proper
     *  results without losing precision:
     *
     *  1) Shift the divisor and one of the multiplicands as many times as is
     *     necessary to reduce the scale -- only if it can be done without
     *     losing precision.
     *  2) Divide one of the multiplicands by the divisor first, but only if it
     *     divides evenly, preserving precision.
     *  3) Same as #2, but try it for the other multiplicand.
     *  4) Last ditch, divide the larger multiplicand by the divisor first, then
     *     do the multiply.  This <WILL> lose precision.
     *
     *  These solutions are identified as CODE-PATHs #1-4 which are used to
     *  identify the matching tests in dltmain.c.
     *
     *  Note that execution might partially include CODE-PATH #1 up until
     *  shifting can no longer be done without losing precision.  In that case,
     *  one of the three remaining options will be used.
     */

    ullTemp = RedUint64DivMod32( UINT64_MAX, ulMultiplier, NULL );

    while( ullBase > ullTemp )
    {
        uint64_t ullMod;
        uint64_t ullBaseTemp;
        uint64_t ullWideMultiplier;

        /*  CODE-PATH #1
         */

        /*  So long as ulDivisor, and at least one of the other numbers, are
         *  evenly divisible by 2, we can scale the numbers so the result does
         *  not overflow the intermediate 64-bit value.
         */
        if( ( ullDivisor & 1U ) == 0U )
        {
            if( ( ullBase & 1U ) == 0U )
            {
                /*  CODE-PATH #1a
                 */
                ullDivisor >>= 1U;
                ullBase >>= 1U;
                continue;
            }

            if( ( ( ulMultiplier & 1U ) == 0U ) && ( ( ullTemp & UINT64_SUFFIX( 0x8000000000000000 ) ) == 0U ) )
            {
                /*  CODE-PATH #1b
                 */
                ullDivisor >>= 1U;
                ulMultiplier >>= 1U;
                ullTemp <<= 1U;
                continue;
            }
        }

        /*  If we get to this point, the above method (#1) cannot be used
         *  because not enough of the numbers are even long enough to scale the
         *  operands down.  We'll see if either multiplicand is evenly divisible
         *  by ulDivisor, and if so, do the divide first, then the multiply.
         *  (Note that once we get to this point, we will never exercise the
         *  while{} loop anymore.)
         */

        /*  CODE-PATH #2
         */
        ullBaseTemp = RedUint64DivMod64( ullBase, ullDivisor, &ullMod );

        if( ullMod == 0U )
        {
            /*  Evenly divides, so check that we won't overflow, and finish up.
             */
            ullBase = ullBaseTemp;

            if( ullBase > ullTemp )
            {
                return UINT64_MAX;
            }
            else
            {
                /*  We've validated that this will not overflow.
                 */
                ullBase *= ulMultiplier;
                return ullBase;
            }
        }

        /*  CODE-PATH #3
         */
        ullWideMultiplier = RedUint64DivMod64( ulMultiplier, ullDivisor, &ullMod );

        if( ullMod == 0U )
        {
            /*  Evenly divides, so check that we won't overflow, and finish up.
             */

            /*  Must recalculate ullTemp relative to ullBase
             */
            ullTemp = RedUint64DivMod64( UINT64_MAX, ullBase, NULL );

            if( ullWideMultiplier > ullTemp )
            {
                return UINT64_MAX;
            }
            else
            {
                uint32_t ulNarrowMultiplier = ( uint32_t ) ullWideMultiplier;

                /*  We've validated that this will not overflow.
                 */
                ullBase *= ulNarrowMultiplier;
                return ullBase;
            }
        }

        /*  CODE-PATH #4
         *
         *  Neither of the multipliers is evenly divisible by the divisor, so
         *  just punt and divide the larger number first, then do the final
         *  multiply.
         *
         *  All the other attempts above would preserve precision -- this is the
         *  only case where precision may be lost.
         */

        /*  If necessary reverse the ullBase and ulMultiplier operands so that
         *  ullBase contains the larger of the two values.
         */
        if( ullBase < ulMultiplier )
        {
            uint32_t ulTemp = ulMultiplier;

            ulMultiplier = ( uint32_t ) ullBase;
            ullBase = ulTemp;
        }

        ullBase = RedUint64DivMod64( ullBase, ullDivisor, NULL );
        ullTemp = RedUint64DivMod32( UINT64_MAX, ulMultiplier, NULL );

        if( ullBase > ullTemp )
        {
            return UINT64_MAX;
        }
        else
        {
            ullBase *= ulMultiplier;
            return ullBase;
        }
    }

    /*  We only get to this point if either there was never any chance of
     *  overflow, or if the pure shifting mechanism succeeded in reducing
     *  the scale so overflow is not a problem.
     */

    ullBase *= ulMultiplier;
    ullBase = RedUint64DivMod64( ullBase, ullDivisor, NULL );

    return ullBase;
}


/** @brief Divide a 64-bit value by a 32-bit value, returning the quotient and
 *         the remainder.
 *
 *  Essentially this function does the following:
 *
 *  ~~~{.c}
 *  if(pulRemainder != NULL)
 *  {
 * pulRemainder = (uint32_t)(ullDividend % ulDivisor);
 *  }
 *  return ullDividend / ulDivisor;
 *  ~~~
 *
 *  However, it does so without ever actually dividing/modulating a 64-bit
 *  value, since such operations are not allowed in all environments.
 *
 *  @param ullDividend  The value to divide.
 *  @param ulDivisor    The value to divide by.
 *  @param pulRemainder Populated with the remainder; may be NULL.
 *
 *  @return The quotient (result of the division).
 */
uint64_t RedUint64DivMod32( uint64_t ullDividend,
                            uint32_t ulDivisor,
                            uint32_t * pulRemainder )
{
    uint64_t ullQuotient;
    uint32_t ulResultRemainder;

    /*  Check for divide by zero.
     */
    if( ulDivisor == 0U )
    {
        REDERROR();

        /*  Nonsense value if no asserts.
         */
        ullQuotient = UINT64_SUFFIX( 0xFFFFFFFFFFFFFBAD );
        ulResultRemainder = 0xFFFFFBADU;
    }
    else if( ullDividend <= UINT32_MAX )
    {
        uint32_t ulDividend = ( uint32_t ) ullDividend;

        ullQuotient = ulDividend / ulDivisor;
        ulResultRemainder = ulDividend % ulDivisor;
    }
    else
    {
        uint32_t ulResultHi;
        uint32_t ulResultLo;
        uint32_t ulRemainder;
        uint8_t bIndex;
        uint32_t ulThisDivision;
        uint32_t ulMask;
        uint8_t ucNextValue;
        uint32_t ulInterimHi, ulInterimLo;
        uint32_t ulLowDword = ( uint32_t ) ullDividend;
        uint32_t ulHighDword = ( uint32_t ) ( ullDividend >> 32U );

        /*  Compute the high part and get the remainder
         */
        ulResultHi = ulHighDword / ulDivisor;
        ulResultLo = 0U;
        ulRemainder = ulHighDword % ulDivisor;

        /*  Compute the low part
         */
        ulMask = 0xFF000000U;

        for( bIndex = 0U; bIndex < sizeof( uint32_t ); bIndex++ )
        {
            ucNextValue = ( uint8_t ) ( ( ulLowDword & ulMask ) >> ( ( sizeof( uint32_t ) - 1U - bIndex ) * 8U ) );
            ulInterimHi = ulRemainder >> 24U;
            ulInterimLo = ( ulRemainder << 8U ) | ucNextValue;
            ulThisDivision = 0U;

            while( ulInterimHi != 0U )
            {
                uint64_t ullInterim = ( ( uint64_t ) ulInterimHi << 32U ) + ulInterimLo;

                ullInterim -= ulDivisor;
                ulThisDivision++;

                ulInterimHi = ( uint32_t ) ( ullInterim >> 32U );
                ulInterimLo = ( uint32_t ) ullInterim;
            }

            ulThisDivision += ulInterimLo / ulDivisor;
            ulRemainder = ulInterimLo % ulDivisor;
            ulResultLo <<= 8U;
            ulResultLo += ulThisDivision;
            ulMask >>= 8U;
        }

        ullQuotient = ( ( uint64_t ) ulResultHi << 32U ) + ulResultLo;
        ulResultRemainder = ( uint32_t ) ( ullDividend - ( ullQuotient * ulDivisor ) );
    }

    if( pulRemainder != NULL )
    {
        *pulRemainder = ulResultRemainder;
    }

    return ullQuotient;
}


/** @brief Divide a 64-bit value by a 64-bit value, returning the quotient and
 *         the remainder.
 *
 *  Essentially this function does the following:
 *
 *  ~~~{.c}
 *  if(pullRemainder != NULL)
 *  {
 * pullRemainder = ullDividend % ullDivisor;
 *  }
 *  return ullDividend / ullDivisor;
 *  ~~~
 *
 *  However, it does so without ever actually dividing/modulating a 64-bit
 *  value, since such operations are not allowed in all environments.
 *
 *  @param ullDividend   The value to divide.
 *  @param ullDivisor    The value to divide by.
 *  @param pullRemainder Populated with the remainder; may be NULL.
 *
 *  @return The quotient (result of the division).
 */
uint64_t RedUint64DivMod64( uint64_t ullDividend,
                            uint64_t ullDivisor,
                            uint64_t * pullRemainder )
{
    /*  The variables u0, u1, etc. take on only 32-bit values, but they are
     *  declared uint64_t to avoid some compiler warning messages and to avoid
     *  some unnecessary EXTRs that the compiler would put in, to convert
     *  uint64_ts to ints.
     */
    uint64_t u0;
    uint64_t u1;
    uint64_t q0;
    uint64_t q1;
    uint64_t ullQuotient;

    /*  First the procedure takes care of the case in which the divisor is a
     *  32-bit quantity.  There are two subcases: (1) If the left half of the
     *  dividend is less than the divisor, one execution of RedUint64DivMod32()
     *  is all that is required (overflow is not possible). (2) Otherwise it
     *  does two divisions, using the grade school method.
     */

    if( ( ullDivisor >> 32U ) == 0U )
    {
        if( ( ullDividend >> 32U ) < ullDivisor )
        {
            /*  If ullDividend/ullDivisor cannot overflow, just do one division.
             */
            ullQuotient = RedUint64DivMod32( ullDividend, ( uint32_t ) ullDivisor, NULL );
        }
        else
        {
            uint32_t k;

            /*  If ullDividend/ullDivisor would overflow:
             */

            /*  Break ullDividend up into two halves.
             */
            u1 = ullDividend >> 32U;
            u0 = ullDividend & 0xFFFFFFFFU;

            /*  First quotient digit and first remainder.
             */
            q1 = RedUint64DivMod32( u1, ( uint32_t ) ullDivisor, &k );

            /*  2nd quot. digit.
             */
            q0 = RedUint64DivMod32( ( ( uint64_t ) k << 32U ) + u0, ( uint32_t ) ullDivisor, NULL );

            ullQuotient = ( q1 << 32U ) + q0;
        }
    }
    else
    {
        uint64_t n;
        uint64_t v1;

        n = nlz64( ullDivisor );         /* 0 <= n <= 31. */
        v1 = ( ullDivisor << n ) >> 32U; /* Normalize the divisor so its MSB is 1. */
        u1 = ullDividend >> 1U;          /* To ensure no overflow. */

        /*  Get quotient from divide unsigned insn.
         */
        q1 = RedUint64DivMod32( u1, ( uint32_t ) v1, NULL );

        q0 = ( q1 << n ) >> 31U; /* Undo normalization and division of ullDividend by 2. */

        /*  Make q0 correct or too small by 1.
         */
        if( q0 != 0U )
        {
            q0--;
        }

        if( ( ullDividend - ( q0 * ullDivisor ) ) >= ullDivisor )
        {
            q0++; /* Now q0 is correct. */
        }

        ullQuotient = q0;
    }

    if( pullRemainder != NULL )
    {
        *pullRemainder = ullDividend - ( ullQuotient * ullDivisor );
    }

    return ullQuotient;
}


/** @brief Compute the number of leading zeroes in a 64-bit value.
 *
 *  @param ullValue The value for which to compute the NLZ.
 *
 *  @return The number of leading zeroes in @p ullValue.
 */
static uint32_t nlz64( uint64_t ullValue )
{
    uint32_t n;

    if( ullValue == 0U )
    {
        n = 64U;
    }
    else
    {
        uint64_t x = ullValue;

        n = 0U;

        if( x <= UINT64_SUFFIX( 0x00000000FFFFFFFF ) )
        {
            n += 32U;
            x <<= 32U;
        }

        if( x <= UINT64_SUFFIX( 0x0000FFFFFFFFFFFF ) )
        {
            n += 16U;
            x <<= 16U;
        }

        if( x <= UINT64_SUFFIX( 0x00FFFFFFFFFFFFFF ) )
        {
            n += 8U;
            x <<= 8U;
        }

        if( x <= UINT64_SUFFIX( 0x0FFFFFFFFFFFFFFF ) )
        {
            n += 4U;
            x <<= 4U;
        }

        if( x <= UINT64_SUFFIX( 0x3FFFFFFFFFFFFFFF ) )
        {
            n += 2U;
            x <<= 2U;
        }

        if( x <= UINT64_SUFFIX( 0x7FFFFFFFFFFFFFFF ) )
        {
            n += 1;
        }
    }

    return n;
}
