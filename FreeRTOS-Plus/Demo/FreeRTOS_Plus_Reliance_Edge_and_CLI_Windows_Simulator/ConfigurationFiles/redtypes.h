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
 *  @brief Defines basic types used by Reliance Edge.
 *
 *  The following types *must* be defined by this header, either directly (using
 *  typedef) or indirectly (by including other headers, such as the C99 headers
 *  stdint.h and stdbool.h):
 *
 *  - bool: Boolean type, capable of storing true (1) or false (0)
 *  - uint8_t: Unsigned 8-bit integer
 *  - int8_t: Signed 8-bit integer
 *  - uint16_t: Unsigned 16-bit integer
 *  - int16_t: Signed 16-bit integer
 *  - uint32_t: Unsigned 32-bit integer
 *  - int32_t: Signed 32-bit integer
 *  - uint64_t: Unsigned 64-bit integer
 *  - int64_t: Signed 64-bit integer
 *  - uintptr_t: Unsigned integer capable of storing a pointer, preferably the
 *    same size as pointers themselves.
 *
 *  These types deliberately use the same names as the standard C99 types, so
 *  that if the C99 headers stdint.h and stdbool.h are available, they may be
 *  included here.
 *
 *  If the user application defines similar types, those may be reused.  For
 *  example, suppose there is an application header apptypes.h which defines
 *  types with a similar purpose but different names.  That header could be
 *  reused to define the types Reliance Edge needs:
 *
 *  ~~~{.c}
 #include <apptypes.h>
 *
 *  typedef BOOL bool;
 *  typedef BYTE uint8_t;
 *  typedef INT8 int8_t;
 *  // And so on...
 *  ~~~
 *
 *  If there are neither C99 headers nor suitable types in application headers,
 *  this header should be populated with typedefs that define the required types
 *  in terms of the standard C types.  This requires knowledge of the size of
 *  the C types on the target hardware (e.g., how big is an "int" or a pointer).
 *  Below is an example which assumes the target has 8-bit chars, 16-bit shorts,
 *  32-bit ints, 32-bit pointers, and 64-bit long longs:
 *
 *  ~~~{.c}
 *  typedef int bool;
 *  typedef unsigned char uint8_t;
 *  typedef signed char int8_t;
 *  typedef unsigned short uint16_t;
 *  typedef short int16_t;
 *  typedef unsigned int uint32_t;
 *  typedef int int32_t;
 *  typedef unsigned long long uint64_t;
 *  typedef long long int64_t;
 *  typedef uint32_t uintptr_t;
 *  ~~~
 */
#ifndef REDTYPES_H
#define REDTYPES_H


typedef int                bool;     /**< @brief Boolean type; either true or false. */

typedef unsigned __int8    uint8_t;  /**< @brief Unsigned 8-bit integer. */
typedef          __int8    int8_t;   /**< @brief Signed 8-bit integer. */

typedef unsigned __int16   uint16_t; /**< @brief Unsigned 16-bit integer. */
typedef          __int16   int16_t;  /**< @brief Signed 16-bit integer. */

typedef unsigned __int32   uint32_t; /**< @brief Unsigned 32-bit integer. */
typedef          __int32   int32_t;  /**< @brief Signed 32-bit integer. */

typedef unsigned __int64   uint64_t; /**< @brief Unsigned 64-bit integer. */
typedef          __int64   int64_t;  /**< @brief Signed 64-bit integer. */

/** @brief Unsigned integer capable of storing a pointer.
 */
#ifdef _WIN64
    typedef uint64_t       uintptr_t;
#else
    typedef uint32_t       uintptr_t;
#endif


#endif /* ifndef REDTYPES_H */
