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
 *  @brief Macros to encapsulate MISRA C:2012 deviations in OS-specific code.
 */
#ifndef REDOSDEVIATIONS_H
#define REDOSDEVIATIONS_H


#if REDCONF_OUTPUT == 1

/*  Needed for PRINT_ASSERT() and OUTPUT_CHARACTER().
 */
    #include <stdio.h>
#endif


#if ( REDCONF_ASSERTS == 1 ) && ( REDCONF_OUTPUT == 1 )

/** Print a formatted message for an assertion.
 *
 *  Usages of this macro deviate from MISRA C:2012 Rule 21.6 (required).  Using
 *  printf() is the most convenient way to output this information; and the risk
 *  of "unspecified, undefined and implementation-defined" behavior causing
 *  problems (as cited in the rationale for the rule) is small.  The driver does
 *  not depend on this string being outputted correctly.  Furthermore, use of
 *  printf() disappears when either asserts or output are disabled.
 *
 *  As Rule 21.6 is required, a separate deviation record is required.
 */
    #define PRINT_ASSERT( file, line ) \
    printf( "Assertion failed in \"%s\" at line %u\n\r", ( ( file ) == NULL ) ? "" : ( file ), ( unsigned ) ( line ) )
#endif


/** Cast a value to unsigned long.
 *
 *  Usages of this macro deviate from MISRA C:2012 Directive 4.6.  This macro is
 *  used in two places to cast a uint64_t value (used by the block device
 *  abstraction for sector numbers) to unsigned long, since third-party code
 *  which is not under the control of this project uses unsigned long for sector
 *  numbers.  The cast is guaranteed to not lose any information, since when the
 *  disk is opened the sector count is verified to be less than or equal to an
 *  unsigned long value.  The text of the directive mentions that "it might be
 *  desirable not to apply this guideline when interfacing with ... code outside
 *  the project's control", which describes the situation for this deviation.
 *
 *  As Directive 4.6 is advisory, a deviation record is not required.  This
 *  notice is the only record of the deviation.
 */
#define CAST_ULONG( ull )    ( ( unsigned long ) ( ull ) )


/** Cast a const-qualified pointer to a pointer which is *not* const-qualified.
 *
 *  Usages of this macro deviate from MISRA C:2012 Rule 11.8.  This macro is
 *  used in exactly one place in order to cope with a poorly designed
 *  third-party interface.  Reliance Edge, at every level of the stack, uses
 *  const-qualified pointers for buffers used in write operations, since the
 *  data is read from the buffer, and the buffer does not need to be modified
 *  (consistent with Rule 8.13).  One of the third-party block device interfaces
 *  that Reliance Edge interfaces with does not follow this convention: it uses
 *  an unqualified pointer for the buffer parameter of its sector write
 *  function.  This forces the need for the cast to avoid warnings.  The
 *  implementation of the sector write function is provided by the user, so it
 *  is to be hoped that the buffer is not actually modified.
 *
 *  As Rule 11.8 is required, a separate deviation record is required.
 */
#define CAST_AWAY_CONST( type, ptr )    ( ( type * ) ( ptr ) )


/** Allocate zero-initialized (cleared) memory.
 *
 *  All usages of this macro deviate from MISRA C:2012 Directive 4.12 (required)
 *  and Rule 21.3 (required).  In the context of the single place it is actually
 *  used, this macro also deviates from Rule 22.1 (required).
 *
 *  This macro is used in the FreeRTOS block device code in order to allocate a
 *  RAM disk, when that implementation of the block device is selected.  The
 *  primary rationale for all these deviations is that a) the RAM disk cannot be
 *  allocated statically (since the volume information is stored in a
 *  structure), and b) the RAM disk is primarily intended as a temporary testing
 *  tool for users who want to try out Reliance Edge before the real storage
 *  media is available.  In most real systems, Reliance Edge is used with
 *  non-volatile storage like SD/MMC or eMMC, not with RAM disks.
 *
 *  Rule 22.1 states that all resources which are allocated must also be
 *  explicitly freed.  The RAM disk is allocated and never freed, deviating from
 *  that rule.  This is done because the data in the RAM disk is emulating a
 *  non-volatile storage medium, and thus needs to persist even after the block
 *  device is closed, to allow the file system to be formatted and then mounted,
 *  or unmounted and remounted in the course of a test.  Thus the memory will
 *  remain allocated until the target device is rebooted.  This is assumed to be
 *  acceptable for the primary purpose of the RAM disk, which is preliminary
 *  testing.
 *
 *  As Directive 4.12, Rule 21.3, and Rule 22.1 are all required, separate
 *  deviation records are required.
 */
#define ALLOCATE_CLEARED_MEMORY( nelem, elsize )    calloc( nelem, elsize )


#if REDCONF_OUTPUT == 1

/** Output a character to a serial port or other display device.
 *
 *  Usages of this macro deviate from MISRA C:2012 Rule 21.6 (required).
 *  FreeRTOS does not include a standard method of printing characters, so
 *  putchar() is the most convenient and portable way to accomplish the task.
 *  The risk of "unspecified, undefined and implementation-defined" behavior
 *  causing problems (as cited in the rationale for the rule) is small.  The
 *  driver does not depend on the character being outputted correctly.
 *  Furthermore, use of putchar() disappears when output is disabled.
 *
 *  As Rule 21.6 is required, a separate deviation record is required.
 */
    #define OUTPUT_CHARACTER( ch )    ( void ) putchar( ch )
#endif


#if ( REDCONF_TASK_COUNT > 1U ) && ( REDCONF_API_POSIX == 1 )

/** Cast a TaskHandle_t (a pointer type) to uintptr_t.
 *
 *  Usage of this macro deviate from MISRA-C:2012 Rule 11.4 (advisory).  This
 *  macro is used for the FreeRTOS version of RedOsTaskId().  Some RTOSes
 *  natively use an integer for task IDs; others use pointers.  RedOsTaskId()
 *  uses integers, FreeRTOS uses pointers; to reconcile this difference, the
 *  pointer must be cast to integer.  This is fairly safe, since the resulting
 *  integer is never cast back to a pointer; and although the integer
 *  representation of a pointer is implementation-defined, the representation is
 *  irrelevant provided that unique pointers are converted to unique integers.
 *
 *  As Rule 11.4 is advisory, a deviation record is not required.  This notice
 *  is the only record of the deviation.
 */
    #define CAST_TASK_PTR_TO_UINTPTR( taskptr )    ( ( uintptr_t ) ( taskptr ) )
#endif


/** Ignore the return value of a function (cast to void)
 *
 *  Usages of this macro deviate from MISRA C:2012 Directive 4.7, which states
 *  that error information must be checked immediately after a function returns
 *  potential error information.
 *
 *  If asserts and output are enabled, then this macro is used to document that
 *  the return value of printf() is ignored.  A failure of printf() does not
 *  impact the filesystem core, nor is there anything the filesystem can do to
 *  respond to such an error (especially since it occurs within an assert).
 *  Thus, the most reasonable action is to ignore the error.
 *
 *  In the STM32 SDIO block device implementation, errors are also ignored in an
 *  IRQ interrupt handler.  This is the most reasonable action to take for two
 *  reasons: (a) it would be dangerous to spend processor time responding to the
 *  error inside the IRQ handler; (b) it has been verified that the same error
 *  is propagated to the DiskRead/Write method, which does return the error to
 *  the core.
 *
 *  In the Atmel SD/MMC block device implementation, error information from
 *  sd_mmc_read_capacity() is ignored.  This is a reasonable action because all
 *  of the possible error conditions were eliminated by a previous check.
 *  sd_mmc_read_capacity() fails under the same conditions as
 *  sd_mmc_test_unit_ready(), which was checked earlier in the same function.
 *
 *  In the mutex module, error information returned from the mutex release
 *  function is ignored when asserts are disabled.  This is a reasonable action
 *  because the mutex release function (xSemaphoreGive) is documented only to
 *  fail if the mutex was not obtained correctly, which can be demonstrably
 *  avoided.
 *
 *  As Directive 4.7 is required, a separate deviation record is required.
 */
#define IGNORE_ERRORS( fn )    ( ( void ) ( fn ) )


/** @brief Determine whether a pointer is aligned on a 32-bit boundary.
 *
 *  This is used to determine whether a data buffer meets the requirements of
 *  the underlying block device implementation.  When transferring data via
 *  DMA (Direct Memory Access) on an STM32 device, the data buffer must be cast
 *  as a uint32 pointer, and unexpected behavior may occur if the buffer is not
 *  aligned correctly.
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
 *  This deviation only occurs when using the STM32 SDIO block device
 *  implementation.
 *
 *  As Rule 11.4 is advisory, a deviation record is not required.  This notice
 *  is the only record of deviation.
 */
#define IS_UINT32_ALIGNED_PTR( ptr )    ( ( ( uintptr_t ) ( ptr ) & ( sizeof( uint32_t ) - 1U ) ) == 0U )


/** @brief Cast a 32-bit aligned void pointer to a uint32 pointer.
 *
 *  Usages of this macro deviate from MISRA C:2012 Rule 11.5 (advisory).  A
 *  cast from a void pointer to an object pointer is discouraged because of
 *  potential alignment issues.  However, this macro is only used to cast
 *  pointers that have already been tested to be 32-bit aligned, so the
 *  operation will be safe.
 *
 *  This deviation only occurs when using the STM32 SDIO block device
 *  implementation.
 *
 *  As rule 11.5 is advisory, a deviation record is not required.  This notice
 *  is the only record of the deviation.
 */
#define CAST_UINT32_PTR( ptr )    ( ( uint32_t * ) ( ptr ) )


#endif /* ifndef REDOSDEVIATIONS_H */
