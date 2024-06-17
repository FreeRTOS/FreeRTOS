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
 *  @brief This header contains macros which deviate from MISRA C:2012
 */
#ifndef REDDEVIATIONS_H
#define REDDEVIATIONS_H


/** @brief Append a suffix to a constant so that it is an unsigned 64-bit value.
 *
 *  Usages of this macro deviate from MISRA C:2012 Rule 1.2 (advisory).  The
 *  rule prohibits the use of language extensions.  The ULL suffix became part
 *  of the C standard with C99.  Since this code base adheres to C89, use of
 *  this suffix is a language extension.  Reliance Edge needs to deal with
 *  64-bit quantities, which by convention are explicitly suffixed.  In at
 *  least one case, with the INODE_SIZE_MAX macro, the code needs a way to force
 *  a constant to be 64-bits even though its value is not so large that it would
 *  be automatically promoted to 64-bits.  Thus the need for this macro and the
 *  deviation.  In practice, the ULL suffix has proven to be a nearly universal
 *  extension among C89 compilers.
 *
 *  As rule 19.2 is advisory, a deviation record is not required.  This notice
 *  is the only record of the deviation.  PC-Lint does not issue an error for
 *  this deviation so there is no error inhibition option.
 *
 *  Usages of this macro also deviate from MISRA C:2012 Rule 20.10 (advisory).
 *  The rule prohibits use of the ## preprocessor operator.  The code is not
 *  obscure, and the operator is used only once, so this is deemed to be safe.
 *
 *  As rule 20.10 is advisory, a deviation record is not required.  This notice
 *  is the only record of the deviation.
 *
 *  Consistent use of this macro, even in non MISRA C code, is encouraged to
 *  make it easier to search for 64-bit values.
 *
 */
#define UINT64_SUFFIX( number )    ( number ## ULL )


/** @brief Append a suffix to a constant so that it is a signed 64-bit value.
 *
 *  Usages of this macro deviate from MISRA C:2012 Rule 1.2 (advisory).  See the
 *  description of UINT64_SUFFIX() for details.
 *
 *  Usages of this macro deviate from MISRA C:2012 Rule 20.10 (advisory).  See
 *  the description of UINT64_SUFFIX() for details.
 */
#define INT64_SUFFIX( number )    ( number ## LL )


/** @brief Cast a pointer to a const uint8_t pointer.
 *
 *  All usages of this macro deviate from MISRA C:2012 Rule 11.5 (advisory).
 *  Because there are no alignment requirements for a uint8_t pointer, this is
 *  safe.  However, it is technically a deviation from the rule.
 *
 *  As Rule 11.5 is advisory, a deviation record is not required.  This notice
 *  and the PC-Lint error inhibition option are the only records of the
 *  deviation.
 */
#define CAST_VOID_PTR_TO_CONST_UINT8_PTR( PTR )    ( ( const uint8_t * ) ( PTR ) )


/** @brief Cast a pointer to a uint8_t pointer.
 *
 *  All usages of this macro deviate from MISRA C:2012 Rule 11.5 (advisory).
 *  Because there are no alignment requirements for a uint8_t pointer, this is
 *  safe.  However, it is technically a deviation from the rule.
 *
 *  As Rule 11.5 is advisory, a deviation record is not required.  This notice
 *  and the PC-Lint error inhibition option are the only records of the
 *  deviation.
 */
#define CAST_VOID_PTR_TO_UINT8_PTR( PTR )    ( ( uint8_t * ) ( PTR ) )


/** @brief Cast a pointer to a const uint32_t pointer.
 *
 *  Usages of this macro may deviate from MISRA C:2012 Rule 11.5 (advisory).
 *  It is only used in cases where the pointer is known to be aligned, and thus
 *  it is safe to do so.
 *
 *  As Rule 11.5 is advisory, a deviation record is not required.  This notice
 *  and the PC-Lint error inhibition option are the only records of the
 *  deviation.
 *
 *  Usages of this macro may deviate from MISRA C:2012 Rule 11.3 (required).
 *  As Rule 11.3 is required, a separate deviation record is required.
 *
 *  Regarding the cast to (const void *): this is there to placate some
 *  compilers which emit warnings when a type with lower alignment requirements
 *  (such as const uint8_t *) is cast to a type with higher alignment
 *  requirements.  In the places where this macro is used, the pointer is
 *  checked to be of sufficient alignment.
 */
#define CAST_CONST_UINT32_PTR( PTR )    ( ( const uint32_t * ) ( const void * ) ( PTR ) )


/** @brief Cast a pointer to a pointer to (void **).
 *
 *  Usages of this macro deviate from MISRA C:2012 Rule 11.3 (required).
 *  It is only used for populating a node structure pointer with a buffer
 *  pointer.  Buffer pointers are 8-byte aligned, thus it is safe to do so.
 *
 *  As Rule 11.3 is required, a separate deviation record is required.
 */
#define CAST_VOID_PTR_PTR( PTRPTR )    ( ( void ** ) ( PTRPTR ) )


/** @brief Create a two-dimensional byte array which is safely aligned.
 *
 *  Usages of this macro deviate from MISRA C:2012 Rule 19.2 (advisory).
 *  A union is required to force alignment of the block buffers, which are used
 *  to access metadata nodes, which must be safely aligned for 64-bit types.
 *
 *  As rule 19.2 is advisory, a deviation record is not required.  This notice
 *  and the PC-Lint error inhibition option are the only records of the
 *  deviation.
 */
#define ALIGNED_2D_BYTE_ARRAY( un, nam, size1, size2 ) \
    union                                              \
    {                                                  \
        uint8_t nam[ size1 ][ size2 ];                 \
        uint64_t DummyAlign;                           \
    }                                                  \
    un


/** @brief Determine whether RedMemMove() must copy memory in the forward
 *         direction, instead of in the reverse.
 *
 *  In order to copy between overlapping memory regions, RedMemMove() must copy
 *  forward if the destination memory is lower, and backward if the destination
 *  memory is higher.  Failure to do so would yield incorrect results.
 *
 *  The only way to make this determination without gross inefficiency is to
 *  use pointer comparison.  Pointer comparisons are undefined unless both
 *  pointers point within the same object or array (or one element past the end
 *  of the array); see section 6.3.8 of ANSI C89.  While RedMemMove() is
 *  normally only used when memory regions overlap, which would not result in
 *  undefined behavior, it (like memmove()) is supposed to work even for non-
 *  overlapping regions, which would make this function invoke undefined
 *  behavior.  Experience has shown the pointer comparisons of this sort behave
 *  intuitively on common platforms, even though the behavior is undefined.  For
 *  those platforms where this is not the case, this implementation of memmove()
 *  should be replaced with an alternate one.
 *
 *  Usages of this macro deviate from MISRA-C:2012 Rule 18.3 (required).  As
 *  Rule 18.3 is required, a separate deviation record is required.
 */
#define MEMMOVE_MUST_COPY_FORWARD( dest, src )    ( ( dest ) < ( src ) )


/** @brief Cast a pointer to a (const DIRENT *).
 *
 *  Usages of this macro deviate from MISRA-C:2012 Rule 11.3 (required).
 *  It is used for populating a directory entry structure pointer with a
 *  buffer pointer.  Buffer pointers are 8-byte aligned, and DIRENT only
 *  requires 4-byte alignment, thus the typecast is safe.
 *
 *  As Rule 11.3 is required, a separate deviation record is required.
 */
#define CAST_CONST_DIRENT_PTR( PTR )    ( ( const DIRENT * ) ( PTR ) )


/** @brief Determine whether a pointer is aligned.
 *
 *  A pointer is aligned if its address is an even multiple of
 *  ::REDCONF_ALIGNMENT_SIZE.
 *
 *  This is used in the slice-by-8 RedCrc32Update() function, which needs to
 *  know whether a pointer is aligned, since the slice-by-8 algorithm needs to
 *  access the memory in an aligned fashion, and if the pointer is not aligned,
 *  this can result in faults or suboptimal performance (depending on platform).
 *
 *  There is no way to perform this check without deviating from MISRA C rules
 *  against casting pointers to integer types.  Usage of this macro deviates
 *  from MISRA C:2012 Rule 11.4 (advisory).  The main rationale the rule cites
 *  against converting pointers to integers is that the chosen integer type may
 *  not be able to represent the pointer; this is a non-issue here since we use
 *  uintptr_t.  The text says the rule still applies when using uintptr_t due to
 *  concern about unaligned pointers, but that is not an issue here since the
 *  integer value of the pointer is not saved and not converted back into a
 *  pointer and dereferenced.  The result of casting a pointer to a sufficiently
 *  large integer is implementation-defined, but macros similar to this one have
 *  been used by Datalight for a long time in a wide variety of environments and
 *  they have always worked as expected.
 *
 *  As Rule 11.4 is advisory, a deviation record is not required.  This notice
 *  and the PC-Lint error inhibition option are the only records of the
 *  deviation.
 *
 *  @note PC-Lint also thinks this macro as it is used below violates Rule 11.6
 *        (required).  This is a false positive, since Rule 11.6 only applies to
 *        void pointers.  Below, we use it on a pointer-to-object (uint8_t *),
 *        which is covered by Rule 11.4.
 */
#define IS_ALIGNED_PTR( ptr )    ( ( ( uintptr_t ) ( ptr ) & ( REDCONF_ALIGNMENT_SIZE - 1U ) ) == 0U )


#endif /* ifndef REDDEVIATIONS_H */
