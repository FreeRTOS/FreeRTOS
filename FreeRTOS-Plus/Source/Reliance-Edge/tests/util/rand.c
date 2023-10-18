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
 *  @brief Implements a random number generator.
 */
#include <redfs.h>
#include <redtestutils.h>


/*  This is the global seed used by the random number generator when the caller
 *  has not provided a seed to either the RedRand32() or RedRand64() functions.
 */
static uint64_t ullGlobalRandomNumberSeed;

/*  Whether the above seed has been initialized.
 */
static bool fGlobalSeedInited;


/** @brief Set the global seed used by the random number generator.
 *
 *  The global seed gets used when RedRand64() or RedRand32() are called with
 *  a NULL seed argument.
 *
 *  @param ullSeed  The value to use as the global RNG seed.
 */
void RedRandSeed( uint64_t ullSeed )
{
    ullGlobalRandomNumberSeed = ullSeed;
    fGlobalSeedInited = true;
}


/** @brief Generate a 64-bit pseudo-random number.
 *
 *  The period of this random number generator is 2^64 (1.8 x 1019).  These
 *  parameters are the same as the default one-stream SPRNG lcg64 generator and
 *  it satisfies the requirements for a maximal period.
 *
 *  The tempering value is used and an AND mask and is specifically selected to
 *  favor the distribution of lower bits.
 *
 *  @param pullSeed A pointer to the seed to use.  Set this value to NULL to
 *                  use the internal global seed value.
 *
 *  @return A pseudo-random number in the range [0, UINT64_MAX].
 */
uint64_t RedRand64( uint64_t * pullSeed )
{
    const uint64_t ullA = UINT64_SUFFIX( 2862933555777941757 );
    const uint64_t ullC = UINT64_SUFFIX( 3037000493 );
    const uint64_t ullT = UINT64_SUFFIX( 4921441182957829599 );
    uint64_t ullN;
    uint64_t * pullSeedPtr;
    uint64_t ullLocalSeed;

    if( pullSeed != NULL )
    {
        ullLocalSeed = *pullSeed;
        pullSeedPtr = pullSeed;
    }
    else
    {
        if( !fGlobalSeedInited )
        {
            /*  Unfortunately, the Reliance Edge OS services don't give us much
             *  to work with to initialize the global seed.  There is no entropy
             *  abstraction, no tick count abstraction, and the timestamp
             *  abstraction uses an opaque type which is not guaranteed to be an
             *  integer.  The best we can do is use the RTC.
             *
             *  Tests using the RNG should be supplying a seed anyway, for
             *  reproducibility.
             */
            RedRandSeed( ( uint64_t ) RedOsClockGetTime() );
        }

        ullLocalSeed = ullGlobalRandomNumberSeed;
        pullSeedPtr = &ullGlobalRandomNumberSeed;
    }

    ullN = ( ullLocalSeed * ullA ) + ullC;

    *pullSeedPtr = ullN;

    /*  The linear congruential generator used above produces good pseudo-random
     *  64-bit number sequences, however, as with any LCG, the period of the
     *  lower order bits is much shorter resulting in alternately odd/even pairs
     *  in bit zero.
     *
     *  The result of the LGC above is tempered below with a series of XOR and
     *  shift operations to produce a more acceptable equidistribution of bits
     *  throughout the 64-bit range.
     */
    ullN ^= ( ullN >> 21U ) & ullT;
    ullN ^= ( ullN >> 43U ) & ullT;
    ullN ^= ( ullN << 23U ) & ~ullT;
    ullN ^= ( ullN << 31U ) & ~ullT;

    return ullN;
}


/** @brief Generate a 32-bit pseudo-random number.
 *
 *  @note   The 32-bit random number generator internally uses the 64-bit random
 *          number generator, returning the low 32-bits of the pseudo-random
 *          64-bit value.
 *
 *  @param pulSeed  A pointer to the seed to use.  Set this value to NULL to use
 *                  the internal global seed value.
 *
 *  @return A pseudo-random number in the range [0, UINT32_MAX].
 */
uint32_t RedRand32( uint32_t * pulSeed )
{
    uint64_t ullN;

    if( pulSeed != NULL )
    {
        uint64_t ullLocalSeed;

        ullLocalSeed = *pulSeed;
        ullN = RedRand64( &ullLocalSeed );
        *pulSeed = ( uint32_t ) ullLocalSeed;
    }
    else
    {
        ullN = RedRand64( NULL );
    }

    return ( uint32_t ) ullN;
}
