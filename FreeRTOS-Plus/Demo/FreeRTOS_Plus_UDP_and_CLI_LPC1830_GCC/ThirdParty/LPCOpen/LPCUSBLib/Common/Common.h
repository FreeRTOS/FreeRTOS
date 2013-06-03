/*
 * @brief LPCUSB library's common macros, definitions
 *
 * @note
 * Copyright(C) NXP Semiconductors, 2012
 * Copyright(C) Dean Camera, 2011, 2012
 * All rights reserved.
 *
 * @par
 * Software that is described herein is for illustrative purposes only
 * which provides customers with programming information regarding the
 * LPC products.  This software is supplied "AS IS" without any warranties of
 * any kind, and NXP Semiconductors and its licensor disclaim any and
 * all warranties, express or implied, including all implied warranties of
 * merchantability, fitness for a particular purpose and non-infringement of
 * intellectual property rights.  NXP Semiconductors assumes no responsibility
 * or liability for the use of the software, conveys no license or rights under any
 * patent, copyright, mask work right, or any other intellectual property rights in
 * or to any products. NXP Semiconductors reserves the right to make changes
 * in the software without notification. NXP Semiconductors also makes no
 * representation or warranty that such application will be suitable for the
 * specified use without further testing or modification.
 *
 * @par
 * Permission to use, copy, modify, and distribute this software and its
 * documentation is hereby granted, under NXP Semiconductors' and its
 * licensor's relevant copyrights in the software, without fee, provided that it
 * is used in conjunction with NXP Semiconductors microcontrollers.  This
 * copyright, permission, and disclaimer notice must appear in all copies of
 * this code.
*/


/** @defgroup Group_Common Common Utility Headers - LPCUSBlib/Common/Common.h
 * @ingroup LPCUSBlib
 *  @brief Common library convenience headers, macros and functions.
 *
 *  Common utility headers containing macros, functions, enums and types which are common to all
 *  aspects of the library.
 *
 *  @{
 */

/** @defgroup Group_GlobalInt Global Interrupt Macros
 *  @brief Convenience macros for the management of interrupts globally within the device.
 *
 *  Macros and functions to create and control global interrupts within the device.
 */

#ifndef __LPCUSBlib_COMMON_H__
#define __LPCUSBlib_COMMON_H__

	/* Macros: */
		#define __INCLUDE_FROM_COMMON_H
		
	/* Includes: */
		#include <stdint.h>
		#include <stdbool.h>
		#include <string.h>
		#include <stddef.h>
		
		#if defined(USE_LUFA_CONFIG_HEADER)
			#include "LUFAConfig.h"
		#endif

		#if 1	// TODO add control macros later
			#include "../LPCUSBlibConfig.h"
		#endif

		#include "CompilerSpecific.h"
		#include "Attributes.h"
		
	/* Enable C linkage for C++ Compilers: */
		#if defined(__cplusplus)
			extern "C" {
		#endif

	/* Architecture specific utility includes: */
		#if defined(__DOXYGEN__)
			/** Type define for an unsigned integer the same width as the selected architecture's machine register.
			 *  This is distinct from the non-specific standard int data type, whose width is machine dependant but
			 *  which may not reflect the actual machine register width on some targets (e.g. LPC).
			 */
			typedef MACHINE_REG_t uint_reg_t;	
		#else
			typedef uint32_t uint_reg_t;
			#define ARCH_LITTLE_ENDIAN
			#define PROGMEM                  const
			#define pgm_read_byte(x)         (*x)
			#define memcmp_P(...)            memcmp(__VA_ARGS__)
			#define memcpy_P(...)            memcpy(__VA_ARGS__)
			#include "Endianness.h"
		#endif

	/* Public Interface - May be used in end-application: */
		/* Macros: */
			/** Macro for encasing other multi-statement macros. This should be used along with an opening brace
			 *  before the start of any multi-statement macro, so that the macros contents as a whole are treated
			 *  as a discrete block and not as a list of separate statements which may cause problems when used as
			 *  a block (such as inline \c if statements).
			 */
			#define MACROS                  do

			/** Macro for encasing other multi-statement macros. This should be used along with a preceding closing
			 *  brace at the end of any multi-statement macro, so that the macros contents as a whole are treated
			 *  as a discrete block and not as a list of separate statements which may cause problems when used as
			 *  a block (such as inline \c if statements).
			 */
			#define MACROE                  while (0)

			/** Convenience macro to determine the larger of two values.
			 *
			 *  @note This macro should only be used with operands that do not have side effects from being evaluated
			 *        multiple times.
			 *
			 *  @param     x  First value to compare
			 *  @param     y  First value to compare
			 *
			 *  @return The larger of the two input parameters
			 */
			#if !defined(MAX) || defined(__DOXYGEN__)
				#define MAX(x, y)               (((x) > (y)) ? (x) : (y))
			#endif

			/** Convenience macro to determine the smaller of two values.
			 *
			 *  @note This macro should only be used with operands that do not have side effects from being evaluated
			 *        multiple times.
			 *
			 *  @param     x  First value to compare
			 *  @param     y  First value to compare
			 *
			 *  @return The smaller of the two input parameters
			 */
			#if !defined(MIN) || defined(__DOXYGEN__)
				#define MIN(x, y)               (((x) < (y)) ? (x) : (y))
			#endif
			
			#if !defined(STRINGIFY) || defined(__DOXYGEN__)
				/** Converts the given input into a string, via the C Preprocessor. This macro puts literal quotation
				 *  marks around the input, converting the source into a string literal.
				 *
				 *  @param     x  Input to convert into a string literal.
				 *
				 *  @return String version of the input.
				 */
				#define STRINGIFY(x)            #x

				/** Converts the given input into a string after macro expansion, via the C Preprocessor. This macro puts
				 *  literal quotation marks around the expanded input, converting the source into a string literal.
				 *
				 *  @param     x  Input to expand and convert into a string literal.
				 *
				 *  @return String version of the expanded input.
				 */
				#define STRINGIFY_EXPANDED(x)   STRINGIFY(x)
			#endif

		/* Inline Functions: */
			/** Function to reverse the individual bits in a byte - i.e. bit 7 is moved to bit 0, bit 6 to bit 1,
			 *  etc.
			 *
			 *  @param     Byte  Byte of data whose bits are to be reversed.
			 */
			static inline uint8_t BitReverse(uint8_t Byte) ATTR_WARN_UNUSED_RESULT ATTR_CONST;
			static inline uint8_t BitReverse(uint8_t Byte)
			{
				Byte = (((Byte & 0xF0) >> 4) | ((Byte & 0x0F) << 4));
				Byte = (((Byte & 0xCC) >> 2) | ((Byte & 0x33) << 2));
				Byte = (((Byte & 0xAA) >> 1) | ((Byte & 0x55) << 1));

				return Byte;
			}

			/** Function to perform a blocking delay for a specified number of milliseconds. The actual delay will be
			 *  at a minimum the specified number of milliseconds, however due to loop overhead and internal calculations
			 *  may be slightly higher.
			 *
			 *  @param     Milliseconds  Number of milliseconds to delay
			 */
PRAGMA_ALWAYS_INLINE
            static inline void Delay_MS(uint16_t Milliseconds) ATTR_ALWAYS_INLINE;
			static inline void Delay_MS(uint16_t Milliseconds)
			{
				while (Milliseconds--)
				{
					volatile  uint32_t  i;

					for (i = 0; i < (4 * 1000); i++) {    /* This logic was tested. It gives app. 1 micro sec delay        */
						;
					}
				}
			}

			/** Retrieves a mask which contains the current state of the global interrupts for the device. This
			 *  value can be stored before altering the global interrupt enable state, before restoring the
			 *  flag(s) back to their previous values after a critical section using @ref SetGlobalInterruptMask().
			 *
			 *  @ingroup Group_GlobalInt
			 *
			 *  @return  Mask containing the current Global Interrupt Enable Mask bit(s).
			 */
PRAGMA_ALWAYS_INLINE
			static inline uint_reg_t GetGlobalInterruptMask(void) ATTR_ALWAYS_INLINE ATTR_WARN_UNUSED_RESULT;
			static inline uint_reg_t GetGlobalInterruptMask(void)
			{
				GCC_MEMORY_BARRIER();
				// TODO #warning GetGlobalInterruptMask() is not implemented under ARCH_LPC.
				return 0;
				//GCC_MEMORY_BARRIER();
			}

			/** Sets the global interrupt enable state of the microcontroller to the mask passed into the function.
			 *  This can be combined with @ref GetGlobalInterruptMask() to save and restore the Global Interrupt Enable
			 *  Mask bit(s) of the device after a critical section has completed.
			 *
			 *  @ingroup Group_GlobalInt
			 *
			 *  @param     GlobalIntState  Global Interrupt Enable Mask value to use
			 */
PRAGMA_ALWAYS_INLINE
			static inline void SetGlobalInterruptMask(const uint_reg_t GlobalIntState) ATTR_ALWAYS_INLINE;
			static inline void SetGlobalInterruptMask(const uint_reg_t GlobalIntState)
			{
				GCC_MEMORY_BARRIER();
				// TODO #warning SetGlobalInterruptMask() is not implemented under ARCH_LPC.			
				GCC_MEMORY_BARRIER();
			}
		
			/** Enables global interrupt handling for the device, allowing interrupts to be handled.
			 *
			 *  @ingroup Group_GlobalInt
			 */
PRAGMA_ALWAYS_INLINE
			static inline void GlobalInterruptEnable(void) ATTR_ALWAYS_INLINE;
			static inline void GlobalInterruptEnable(void)
			{
				GCC_MEMORY_BARRIER();
				// TODO #warning GlobalInterruptEnable() is not implemented under ARCH_LPC.
				GCC_MEMORY_BARRIER();
			}		

			/** Disabled global interrupt handling for the device, preventing interrupts from being handled.
			 *
			 *  @ingroup Group_GlobalInt
			 */
PRAGMA_ALWAYS_INLINE
			static inline void GlobalInterruptDisable(void) ATTR_ALWAYS_INLINE;
			static inline void GlobalInterruptDisable(void)
			{
				GCC_MEMORY_BARRIER();
				// TODO #warning GlobalInterruptDisable() is not implemented under ARCH_LPC.
				GCC_MEMORY_BARRIER();
			}

	/* Disable C linkage for C++ Compilers: */
		#if defined(__cplusplus)
			}
		#endif

#endif

/** @} */

