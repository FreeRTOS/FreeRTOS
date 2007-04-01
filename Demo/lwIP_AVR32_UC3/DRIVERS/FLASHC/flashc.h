/* This header file is part of the ATMEL FREERTOS-0.9.0 Release */

/*This file has been prepared for Doxygen automatic documentation generation.*/
/*! \file *********************************************************************
 *
 * \brief Flash Controller driver .h file.
 *
 * This file defines a useful set of functions for the flash controller
 * on AVR32A devices.
 *
 * - Compiler:           IAR EWAVR32 and GNU GCC for AVR32
 * - Supported devices:  All AVR32A devices.
 *
 * \author               Atmel Corporation: http://www.atmel.com \n
 *                       Support email: avr32@atmel.com
 *
 *****************************************************************************/

/* Copyright (c) 2007, Atmel Corporation All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * 3. The name of ATMEL may not be used to endorse or promote products derived
 * from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL ``AS IS'' AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE EXPRESSLY AND
 * SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */


#ifndef _FLASHC_H_
#define _FLASHC_H_

#if __GNUC__
#  include <avr32/io.h>
#elif __ICCAVR32__
#  include <avr32/iouc3a0512.h>
#  include <avr32/uc3a0512.h>
#else
#  error Unknown compiler
#endif

#include "compiler.h"


/*! Value returned by function when it completed successfully */
#define FLASHC_SUCCESS 0

/*! Value returned by function when it was unable to complete successfully
    for some unspecified reason */
#define FLASHC_FAILURE -1

/*! Value returned by function when the input paramters are out of range */
#define FLASHC_INVALID_INPUT 1


/*! Get Flash size */
#if __GNUC__
__attribute__((__always_inline__))
#endif
extern __inline__ unsigned int flashc_get_flash_size(void)
{
  static const unsigned int FLASHC_SIZE[1 << AVR32_FLASHC_FSR_FSZ_SIZE] =
  {
    32 << 10,
    64 << 10,
    128 << 10,
    256 << 10,
    384 << 10,
    512 << 10,
    768 << 10,
    1024 << 10
  };

  return FLASHC_SIZE[Rd_bitfield(AVR32_FLASHC.fsr, AVR32_FLASHC_FSR_FSZ_MASK)];
}

/*! Get Flash page count */
#if __GNUC__
__attribute__((__always_inline__))
#endif
extern __inline__ unsigned int flashc_get_page_count(void)
{
  return flashc_get_flash_size() / AVR32_FLASHC_PAGE_SIZE;
}

/*! Get Flash page count per region */
#if __GNUC__
__attribute__((__always_inline__))
#endif
extern __inline__ unsigned int flashc_get_page_count_per_region(void)
{
  return flashc_get_page_count() / 16;
}

/*! Wait flash ready status, the application must wait before running a new command.
 * Warning: Flash status register (FCR) is read, and error status may be automatically
 * cleared when reading FCR.
 */
#if __GNUC__
__attribute__((__always_inline__))
#endif
extern __inline__ void flashc_busy_wait(void)
{
  while (!Tst_bits(AVR32_FLASHC.fsr, AVR32_FLASHC_FSR_FRDY_MASK));
}

/*! Check if security bit is active.
 * \warning: Flash status register (FCR) is read, and error status may be automatically
 * cleared when reading FCR.
 */
#if __GNUC__
__attribute__((__always_inline__))
#endif
extern __inline__ Bool flashc_is_security_active(void)
{
  return Tst_bits(AVR32_FLASHC.fsr, AVR32_FLASHC_FSR_SECURITY_MASK);
}

/*! \brief Memcopy function
 * \param *s1 destination
 * \param *s2 source
 * \param n number of words to copy
 */
extern U32 *flashc_memcpy(U32 *s1, const U32 *s2, const U32 n);

/*! \brief Set number of wait state
 * \param ws 0 if for no-wait state,  for 1 wait-state
 * \return      FLASHC_SUCCESS, FLASHC_INVALID_INPUT or FLASHC_FAILURE
 */
extern int flashc_set_wait_state(U16 ws);

/*! \brief Page write number n. Assuming page bubuffer is already loaded.
 * \param n Page number
 */
extern void flashc_page_write_n(U16 n);

/*! \brief Page write
 * Assuming the page address is already loaded
 */
extern void flashc_page_write(U16 page_n);

/*! \brief Clear page buffer
 */
extern void flashc_clear_page_buffer(void);

/*! \brief Page erase
 * Assuming the page address is already loaded
 */
extern void flashc_erase_page(U16 page_n);

/*! \brief Erase all Pages
 */
extern void flashc_erase_all(void);

/*! \brief Erase a page and check if erase is OK
 */
extern int flashc_erase_page_and_check(U16 page_n);

/*! \brief Page load and write
 * \warning Dest is a FLASH address at a page boundary
 * (assuming the page is already erased)
 */
extern void flashc_page_copy_write(U32 *Dest, const U32 *Src) ;

/*! \brief This function allows to write up to 65535 bytes in the flash memory.
 * This function manages alignement issue (byte and page alignements).
 *
 * \param *src  Address of data to write.
 * \param dst   Start address in flash memory where write data
 * \param n     Number of word to write
 * \return      FLASHC_SUCCESS or FLASHC_FAILURE
 */
extern int flash_wr_block(U32 * src, U32 dst, U32 n);


#endif /* #ifndef _FLASHC_H_*/
