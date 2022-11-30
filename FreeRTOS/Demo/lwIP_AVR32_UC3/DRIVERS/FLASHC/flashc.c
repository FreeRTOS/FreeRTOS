/*This file is prepared for Doxygen automatic documentation generation.*/
/*! \file *********************************************************************
 *
 * \brief FLASHC driver for AVR32 UC3.
 *
 * AVR32 Flash Controller driver module.
 *
 * - Compiler:           IAR EWAVR32 and GNU GCC for AVR32
 * - Supported devices:  All AVR32 devices with a FLASHC module can be used.
 * - AppNote:
 *
 * \author               Atmel Corporation: http://www.atmel.com \n
 *                       Support and FAQ: http://support.atmel.no/
 *
 ******************************************************************************/

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


#include <avr32/io.h>
#include <stddef.h>
#include "compiler.h"
#include "flashc.h"


/*! \name FLASHC Writable Bit-Field Registers
 */
//! @{

typedef union
{
  unsigned long                 fcr;
  avr32_flashc_fcr_t            FCR;
} u_avr32_flashc_fcr_t;

typedef union
{
  unsigned long                 fcmd;
  avr32_flashc_fcmd_t           FCMD;
} u_avr32_flashc_fcmd_t;

//! @}


/*! \name Flash Properties
 */
//! @{


unsigned int flashc_get_flash_size(void)
{
  static const unsigned int FLASH_SIZE[1 << AVR32_FLASHC_FSR_FSZ_SIZE] =
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
  return FLASH_SIZE[(AVR32_FLASHC.fsr & AVR32_FLASHC_FSR_FSZ_MASK) >> AVR32_FLASHC_FSR_FSZ_OFFSET];
}


unsigned int flashc_get_page_count(void)
{
  return flashc_get_flash_size() / AVR32_FLASHC_PAGE_SIZE;
}


unsigned int flashc_get_page_count_per_region(void)
{
  return flashc_get_page_count() / AVR32_FLASHC_REGIONS;
}


unsigned int flashc_get_page_region(int page_number)
{
  return ((page_number >= 0) ? page_number : flashc_get_page_number()) / flashc_get_page_count_per_region();
}


unsigned int flashc_get_region_first_page_number(unsigned int region)
{
  return region * flashc_get_page_count_per_region();
}


//! @}


/*! \name FLASHC Control
 */
//! @{


unsigned int flashc_get_wait_state(void)
{
  return (AVR32_FLASHC.fcr & AVR32_FLASHC_FCR_FWS_MASK) >> AVR32_FLASHC_FCR_FWS_OFFSET;
}


void flashc_set_wait_state(unsigned int wait_state)
{
  u_avr32_flashc_fcr_t u_avr32_flashc_fcr = {AVR32_FLASHC.fcr};
  u_avr32_flashc_fcr.FCR.fws = wait_state;
  AVR32_FLASHC.fcr = u_avr32_flashc_fcr.fcr;
}


Bool flashc_is_ready_int_enabled(void)
{
  return ((AVR32_FLASHC.fcr & AVR32_FLASHC_FCR_FRDY_MASK) != 0);
}


void flashc_enable_ready_int(Bool enable)
{
  u_avr32_flashc_fcr_t u_avr32_flashc_fcr = {AVR32_FLASHC.fcr};
  u_avr32_flashc_fcr.FCR.frdy = (enable != FALSE);
  AVR32_FLASHC.fcr = u_avr32_flashc_fcr.fcr;
}


Bool flashc_is_lock_error_int_enabled(void)
{
  return ((AVR32_FLASHC.fcr & AVR32_FLASHC_FCR_LOCKE_MASK) != 0);
}


void flashc_enable_lock_error_int(Bool enable)
{
  u_avr32_flashc_fcr_t u_avr32_flashc_fcr = {AVR32_FLASHC.fcr};
  u_avr32_flashc_fcr.FCR.locke = (enable != FALSE);
  AVR32_FLASHC.fcr = u_avr32_flashc_fcr.fcr;
}


Bool flashc_is_prog_error_int_enabled(void)
{
  return ((AVR32_FLASHC.fcr & AVR32_FLASHC_FCR_PROGE_MASK) != 0);
}


void flashc_enable_prog_error_int(Bool enable)
{
  u_avr32_flashc_fcr_t u_avr32_flashc_fcr = {AVR32_FLASHC.fcr};
  u_avr32_flashc_fcr.FCR.proge = (enable != FALSE);
  AVR32_FLASHC.fcr = u_avr32_flashc_fcr.fcr;
}


//! @}


/*! \name FLASHC Status
 */
//! @{


Bool flashc_is_ready(void)
{
  return ((AVR32_FLASHC.fsr & AVR32_FLASHC_FSR_FRDY_MASK) != 0);
}


void flashc_default_wait_until_ready(void)
{
  while (!flashc_is_ready());
}


void (*volatile flashc_wait_until_ready)(void) = flashc_default_wait_until_ready;


/*! \brief Gets the error status of the FLASHC.
 *
 * \return The error status of the FLASHC built up from
 *         \c AVR32_FLASHC_FSR_LOCKE_MASK and \c AVR32_FLASHC_FSR_PROGE_MASK.
 *
 * \warning This hardware error status is cleared by all functions reading the
 *          Flash Status Register (FSR). This function is therefore not part of
 *          the driver's API which instead presents \ref flashc_is_lock_error
 *          and \ref flashc_is_programming_error.
 */
static unsigned int flashc_get_error_status(void)
{
  return AVR32_FLASHC.fsr & (AVR32_FLASHC_FSR_LOCKE_MASK |
                             AVR32_FLASHC_FSR_PROGE_MASK);
}


//! Sticky error status of the FLASHC.
//! This variable is updated by functions that issue FLASHC commands. It
//! contains the cumulated FLASHC error status of all the FLASHC commands issued
//! by a function.
static unsigned int flashc_error_status = 0;


Bool flashc_is_lock_error(void)
{
  return ((flashc_error_status & AVR32_FLASHC_FSR_LOCKE_MASK) != 0);
}


Bool flashc_is_programming_error(void)
{
  return ((flashc_error_status & AVR32_FLASHC_FSR_PROGE_MASK) != 0);
}


//! @}


/*! \name FLASHC Command Control
 */
//! @{


unsigned int flashc_get_command(void)
{
  return (AVR32_FLASHC.fcmd & AVR32_FLASHC_FCMD_CMD_MASK) >> AVR32_FLASHC_FCMD_CMD_OFFSET;
}


unsigned int flashc_get_page_number(void)
{
  return (AVR32_FLASHC.fcmd & AVR32_FLASHC_FCMD_PAGEN_MASK) >> AVR32_FLASHC_FCMD_PAGEN_OFFSET;
}


void flashc_issue_command(unsigned int command, int page_number)
{
  u_avr32_flashc_fcmd_t u_avr32_flashc_fcmd;
  flashc_wait_until_ready();
  u_avr32_flashc_fcmd.fcmd = AVR32_FLASHC.fcmd;
  u_avr32_flashc_fcmd.FCMD.cmd = command;
  if (page_number >= 0) u_avr32_flashc_fcmd.FCMD.pagen = page_number;
  u_avr32_flashc_fcmd.FCMD.key = AVR32_FLASHC_FCMD_KEY_KEY;
  AVR32_FLASHC.fcmd = u_avr32_flashc_fcmd.fcmd;
  flashc_error_status = flashc_get_error_status();
  flashc_wait_until_ready();
}


//! @}


/*! \name FLASHC Global Commands
 */
//! @{


void flashc_no_operation(void)
{
  flashc_issue_command(AVR32_FLASHC_FCMD_CMD_NOP, -1);
}


void flashc_erase_all(void)
{
  flashc_issue_command(AVR32_FLASHC_FCMD_CMD_EA, -1);
}


//! @}


/*! \name FLASHC Protection Mechanisms
 */
//! @{


Bool flashc_is_security_bit_active(void)
{
  return ((AVR32_FLASHC.fsr & AVR32_FLASHC_FSR_SECURITY_MASK) != 0);
}


void flashc_activate_security_bit(void)
{
  flashc_issue_command(AVR32_FLASHC_FCMD_CMD_SSB, -1);
}


unsigned int flashc_get_bootloader_protected_size(void)
{
  unsigned int bootprot = (1 << AVR32_FLASHC_FGPFR_BOOTPROT_SIZE) - 1 -
                          flashc_read_gp_fuse_bitfield(AVR32_FLASHC_FGPFR_BOOTPROT_OFFSET,
                                                       AVR32_FLASHC_FGPFR_BOOTPROT_SIZE);
  return (bootprot) ? AVR32_FLASHC_PAGE_SIZE << bootprot : 0;
}


unsigned int flashc_set_bootloader_protected_size(unsigned int bootprot_size)
{
  flashc_set_gp_fuse_bitfield(AVR32_FLASHC_FGPFR_BOOTPROT_OFFSET,
                              AVR32_FLASHC_FGPFR_BOOTPROT_SIZE,
                              (1 << AVR32_FLASHC_FGPFR_BOOTPROT_SIZE) - 1 -
                              ((bootprot_size) ?
                               32 - clz((((min(max(bootprot_size, AVR32_FLASHC_PAGE_SIZE << 1),
                                               AVR32_FLASHC_PAGE_SIZE <<
                                               ((1 << AVR32_FLASHC_FGPFR_BOOTPROT_SIZE) - 1)) +
                                           AVR32_FLASHC_PAGE_SIZE - 1) /
                                          AVR32_FLASHC_PAGE_SIZE) << 1) - 1) - 1 :
                               0));
  return flashc_get_bootloader_protected_size();
}


Bool flashc_is_external_privileged_fetch_locked(void)
{
  return (!flashc_read_gp_fuse_bit(AVR32_FLASHC_FGPFR_EPFL_OFFSET));
}


void flashc_lock_external_privileged_fetch(Bool lock)
{
  flashc_set_gp_fuse_bit(AVR32_FLASHC_FGPFR_EPFL_OFFSET, !lock);
}


Bool flashc_is_page_region_locked(int page_number)
{
  return flashc_is_region_locked(flashc_get_page_region(page_number));
}


Bool flashc_is_region_locked(unsigned int region)
{
  return ((AVR32_FLASHC.fsr & AVR32_FLASHC_FSR_LOCK0_MASK << (region & (AVR32_FLASHC_REGIONS - 1))) != 0);
}


void flashc_lock_page_region(int page_number, Bool lock)
{
  flashc_issue_command((lock) ? AVR32_FLASHC_FCMD_CMD_LP : AVR32_FLASHC_FCMD_CMD_UP, page_number);
}


void flashc_lock_region(unsigned int region, Bool lock)
{
  flashc_lock_page_region(flashc_get_region_first_page_number(region), lock);
}


void flashc_lock_all_regions(Bool lock)
{
  unsigned int error_status = 0;
  unsigned int region = AVR32_FLASHC_REGIONS;
  while (region)
  {
    flashc_lock_region(--region, lock);
    error_status |= flashc_error_status;
  }
  flashc_error_status = error_status;
}


//! @}


/*! \name Access to General-Purpose Fuses
 */
//! @{


Bool flashc_read_gp_fuse_bit(unsigned int gp_fuse_bit)
{
  return ((AVR32_FLASHC.fgpfr & AVR32_FLASHC_FGPFR_GPF00_MASK << (gp_fuse_bit & 0x1F)) != 0);
}


U32 flashc_read_gp_fuse_bitfield(unsigned int pos, unsigned int width)
{
  return AVR32_FLASHC.fgpfr >> (AVR32_FLASHC_FGPFR_GPF00_OFFSET + (pos & 0x1F)) &
         ((1 << min(width, 32)) - 1);
}


U8 flashc_read_gp_fuse_byte(unsigned int gp_fuse_byte)
{
  return AVR32_FLASHC.fgpfr >> (AVR32_FLASHC_FGPFR_GPF00_OFFSET + ((gp_fuse_byte & 0x03) << 3));
}


U32 flashc_read_all_gp_fuses(void)
{
  return AVR32_FLASHC.fgpfr;
}


Bool flashc_erase_gp_fuse_bit(unsigned int gp_fuse_bit, Bool check)
{
  flashc_issue_command(AVR32_FLASHC_FCMD_CMD_EGPB, gp_fuse_bit & 0x1F);
  return (check) ? flashc_read_gp_fuse_bit(gp_fuse_bit) : TRUE;
}


Bool flashc_erase_gp_fuse_bitfield(unsigned int pos, unsigned int width, Bool check)
{
  unsigned int error_status = 0;
  unsigned int gp_fuse_bit;
  pos &= 0x1F;
  width = min(width, 32);
  for (gp_fuse_bit = pos; gp_fuse_bit < pos + width; gp_fuse_bit++)
  {
    flashc_erase_gp_fuse_bit(gp_fuse_bit, FALSE);
    error_status |= flashc_error_status;
  }
  flashc_error_status = error_status;
  return (check) ? (flashc_read_gp_fuse_bitfield(pos, width) == (1 << width) - 1) : TRUE;
}


Bool flashc_erase_gp_fuse_byte(unsigned int gp_fuse_byte, Bool check)
{
  unsigned int error_status;
  unsigned int current_gp_fuse_byte;
  U32 value = flashc_read_all_gp_fuses();
  flashc_erase_all_gp_fuses(FALSE);
  error_status = flashc_error_status;
  for (current_gp_fuse_byte = 0; current_gp_fuse_byte < 4; current_gp_fuse_byte++, value >>= 8)
  {
    if (current_gp_fuse_byte != gp_fuse_byte)
    {
      flashc_write_gp_fuse_byte(current_gp_fuse_byte, value);
      error_status |= flashc_error_status;
    }
  }
  flashc_error_status = error_status;
  return (check) ? (flashc_read_gp_fuse_byte(gp_fuse_byte) == 0xFF) : TRUE;
}


Bool flashc_erase_all_gp_fuses(Bool check)
{
  flashc_issue_command(AVR32_FLASHC_FCMD_CMD_EAGPF, -1);
  return (check) ? (flashc_read_all_gp_fuses() == 0xFFFFFFFF) : TRUE;
}


void flashc_write_gp_fuse_bit(unsigned int gp_fuse_bit, Bool value)
{
  if (!value)
    flashc_issue_command(AVR32_FLASHC_FCMD_CMD_WGPB, gp_fuse_bit & 0x1F);
}


void flashc_write_gp_fuse_bitfield(unsigned int pos, unsigned int width, U32 value)
{
  unsigned int error_status = 0;
  unsigned int gp_fuse_bit;
  pos &= 0x1F;
  width = min(width, 32);
  for (gp_fuse_bit = pos; gp_fuse_bit < pos + width; gp_fuse_bit++, value >>= 1)
  {
    flashc_write_gp_fuse_bit(gp_fuse_bit, value & 0x01);
    error_status |= flashc_error_status;
  }
  flashc_error_status = error_status;
}


void flashc_write_gp_fuse_byte(unsigned int gp_fuse_byte, U8 value)
{
  flashc_issue_command(AVR32_FLASHC_FCMD_CMD_PGPFB, (gp_fuse_byte & 0x03) | value << 2);
}


void flashc_write_all_gp_fuses(U32 value)
{
  unsigned int error_status = 0;
  unsigned int gp_fuse_byte;
  for (gp_fuse_byte = 0; gp_fuse_byte < 4; gp_fuse_byte++, value >>= 8)
  {
    flashc_write_gp_fuse_byte(gp_fuse_byte, value);
    error_status |= flashc_error_status;
  }
  flashc_error_status = error_status;
}


void flashc_set_gp_fuse_bit(unsigned int gp_fuse_bit, Bool value)
{
  if (value)
    flashc_erase_gp_fuse_bit(gp_fuse_bit, FALSE);
  else
    flashc_write_gp_fuse_bit(gp_fuse_bit, FALSE);
}


void flashc_set_gp_fuse_bitfield(unsigned int pos, unsigned int width, U32 value)
{
  unsigned int error_status = 0;
  unsigned int gp_fuse_bit;
  pos &= 0x1F;
  width = min(width, 32);
  for (gp_fuse_bit = pos; gp_fuse_bit < pos + width; gp_fuse_bit++, value >>= 1)
  {
    flashc_set_gp_fuse_bit(gp_fuse_bit, value & 0x01);
    error_status |= flashc_error_status;
  }
  flashc_error_status = error_status;
}


void flashc_set_gp_fuse_byte(unsigned int gp_fuse_byte, U8 value)
{
  unsigned int error_status;
  switch (value)
  {
  case 0xFF:
    flashc_erase_gp_fuse_byte(gp_fuse_byte, FALSE);
    break;
  case 0x00:
    flashc_write_gp_fuse_byte(gp_fuse_byte, 0x00);
    break;
  default:
    flashc_erase_gp_fuse_byte(gp_fuse_byte, FALSE);
    error_status = flashc_error_status;
    flashc_write_gp_fuse_byte(gp_fuse_byte, value);
    flashc_error_status |= error_status;
  }
}


void flashc_set_all_gp_fuses(U32 value)
{
  unsigned int error_status;
  switch (value)
  {
  case 0xFFFFFFFF:
    flashc_erase_all_gp_fuses(FALSE);
    break;
  case 0x00000000:
    flashc_write_all_gp_fuses(0x00000000);
    break;
  default:
    flashc_erase_all_gp_fuses(FALSE);
    error_status = flashc_error_status;
    flashc_write_all_gp_fuses(value);
    flashc_error_status |= error_status;
  }
}


//! @}


/*! \name Access to Flash Pages
 */
//! @{


void flashc_clear_page_buffer(void)
{
  flashc_issue_command(AVR32_FLASHC_FCMD_CMD_CPB, -1);
}


Bool flashc_is_page_erased(void)
{
  return ((AVR32_FLASHC.fsr & AVR32_FLASHC_FSR_QPRR_MASK) != 0);
}


Bool flashc_quick_page_read(int page_number)
{
  flashc_issue_command(AVR32_FLASHC_FCMD_CMD_QPR, page_number);
  return flashc_is_page_erased();
}


Bool flashc_erase_page(int page_number, Bool check)
{
  Bool page_erased = TRUE;
  flashc_issue_command(AVR32_FLASHC_FCMD_CMD_EP, page_number);
  if (check)
  {
    unsigned int error_status = flashc_error_status;
    page_erased = flashc_quick_page_read(-1);
    flashc_error_status |= error_status;
  }
  return page_erased;
}


Bool flashc_erase_all_pages(Bool check)
{
  Bool all_pages_erased = TRUE;
  unsigned int error_status = 0;
  unsigned int page_number = flashc_get_page_count();
  while (page_number)
  {
    all_pages_erased &= flashc_erase_page(--page_number, check);
    error_status |= flashc_error_status;
  }
  flashc_error_status = error_status;
  return all_pages_erased;
}


void flashc_write_page(int page_number)
{
  flashc_issue_command(AVR32_FLASHC_FCMD_CMD_WP, page_number);
}


Bool flashc_check_user_page_erase(void)
{
  volatile U64 *user_page_ptr = (U64 *)AVR32_FLASHC_USER_PAGE;
  while (user_page_ptr < (U64 *)(AVR32_FLASHC_USER_PAGE + AVR32_FLASHC_USER_PAGE_SIZE))
  {
    if (*user_page_ptr++ != 0xFFFFFFFFFFFFFFFFULL)
      return FALSE;
  }
  return TRUE;
}


Bool flashc_erase_user_page(Bool check)
{
  flashc_issue_command(AVR32_FLASHC_FCMD_CMD_EUP, -1);
  return (check) ? flashc_check_user_page_erase() : TRUE;
}


void flashc_write_user_page(void)
{
  flashc_issue_command(AVR32_FLASHC_FCMD_CMD_WUP, -1);
}


volatile void *flashc_memset8(volatile void *dst, U8 src, size_t nbytes, Bool erase)
{
  return flashc_memset16(dst, src | (U16)src << 8, nbytes, erase);
}


volatile void *flashc_memset16(volatile void *dst, U16 src, size_t nbytes, Bool erase)
{
  return flashc_memset32(dst, src | (U32)src << 16, nbytes, erase);
}


volatile void *flashc_memset32(volatile void *dst, U32 src, size_t nbytes, Bool erase)
{
  return flashc_memset64(dst, src | (U64)src << 32, nbytes, erase);
}


volatile void *flashc_memset64(volatile void *dst, U64 src, size_t nbytes, Bool erase)
{
  // Use aggregated pointers to have several alignments available for a same address.
  UnionCVPtr flash_array_end;
  UnionVPtr dest;
  Union64 source = {0};
  StructCVPtr dest_end;
  UnionCVPtr flash_page_source_end;
  Bool incomplete_flash_page_end;
  Union64 flash_dword;
  UnionVPtr tmp;
  unsigned int error_status = 0;
  unsigned int i;

  // Reformat arguments.
  flash_array_end.u8ptr = AVR32_FLASH + flashc_get_flash_size();
  dest.u8ptr = dst;
  for (i = (Get_align((U32)dest.u8ptr, sizeof(U64)) - 1) & (sizeof(U64) - 1);
       src; i = (i - 1) & (sizeof(U64) - 1))
  {
    source.u8[i] = src;
    src >>= 8;
  }
  dest_end.u8ptr = dest.u8ptr + nbytes;

  // If destination is outside flash, go to next flash page if any.
  if (dest.u8ptr < AVR32_FLASH)
  {
    dest.u8ptr = AVR32_FLASH;
  }
  else if (flash_array_end.u8ptr <= dest.u8ptr && dest.u8ptr < AVR32_FLASHC_USER_PAGE)
  {
    dest.u8ptr = AVR32_FLASHC_USER_PAGE;
  }

  // If end of destination is outside flash, move it to the end of the previous flash page if any.
  if (dest_end.u8ptr > AVR32_FLASHC_USER_PAGE + AVR32_FLASHC_USER_PAGE_SIZE)
  {
    dest_end.u8ptr = AVR32_FLASHC_USER_PAGE + AVR32_FLASHC_USER_PAGE_SIZE;
  }
  else if (AVR32_FLASHC_USER_PAGE >= dest_end.u8ptr && dest_end.u8ptr > flash_array_end.u8ptr)
  {
    dest_end.u8ptr = flash_array_end.u8ptr;
  }

  // Align each end of destination pointer with its natural boundary.
  dest_end.u16ptr = (U16 *)Align_down((U32)dest_end.u8ptr, sizeof(U16));
  dest_end.u32ptr = (U32 *)Align_down((U32)dest_end.u16ptr, sizeof(U32));
  dest_end.u64ptr = (U64 *)Align_down((U32)dest_end.u32ptr, sizeof(U64));

  // While end of destination is not reached...
  while (dest.u8ptr < dest_end.u8ptr)
  {
    // Clear the page buffer in order to prepare data for a flash page write.
    flashc_clear_page_buffer();
    error_status |= flashc_error_status;

    // Determine where the source data will end in the current flash page.
    flash_page_source_end.u64ptr =
      (U64 *)min((U32)dest_end.u64ptr,
                 Align_down((U32)dest.u8ptr, AVR32_FLASHC_PAGE_SIZE) + AVR32_FLASHC_PAGE_SIZE);

    // Determine if the current destination page has an incomplete end.
    incomplete_flash_page_end = (Align_down((U32)dest.u8ptr, AVR32_FLASHC_PAGE_SIZE) >=
                                 Align_down((U32)dest_end.u8ptr, AVR32_FLASHC_PAGE_SIZE));

    // Use a flash double-word buffer to manage unaligned accesses.
    flash_dword.u64 = source.u64;

    // If destination does not point to the beginning of the current flash page...
    if (!Test_align((U32)dest.u8ptr, AVR32_FLASHC_PAGE_SIZE))
    {
      // If page erase is requested...
      if (erase)
      {
        // Fill the beginning of the page buffer with the current flash page data.
        for (tmp.u8ptr = (U8 *)Align_down((U32)dest.u8ptr, AVR32_FLASHC_PAGE_SIZE);
             tmp.u64ptr < (U64 *)Align_down((U32)dest.u8ptr, sizeof(U64));
             tmp.u64ptr++)
          *tmp.u64ptr = *tmp.u64ptr;
      }

      // If destination is not 64-bit aligned...
      if (!Test_align((U32)dest.u8ptr, sizeof(U64)))
      {
        // If page erase is requested...
        if (erase)
        {
          // Fill the beginning of the flash double-word buffer with the current flash page data.
          for (i = 0; i < Get_align((U32)dest.u8ptr, sizeof(U64)); i++)
            flash_dword.u8[i] = *tmp.u8ptr++;
        }
        // If page erase is not requested...
        else
        {
          // Erase the beginning of the flash double-word buffer.
          for (i = 0; i < Get_align((U32)dest.u8ptr, sizeof(U64)); i++)
            flash_dword.u8[i] = 0xFF;
        }

        // Align the destination pointer with its 64-bit boundary.
        dest.u64ptr = (U64 *)Align_down((U32)dest.u8ptr, sizeof(U64));

        // If the current destination double-word is not the last one...
        if (dest.u64ptr < dest_end.u64ptr)
        {
          // Write the flash double-word buffer to the page buffer and reinitialize it.
          *dest.u64ptr++ = flash_dword.u64;
          flash_dword.u64 = source.u64;
        }
      }
    }

    // Write the source data to the page buffer with 64-bit alignment.
    for (i = flash_page_source_end.u64ptr - dest.u64ptr; i; i--)
      *dest.u64ptr++ = source.u64;

    // If the current destination page has an incomplete end...
    if (incomplete_flash_page_end)
    {
      // If page erase is requested...
      if (erase)
      {
        tmp.u8ptr = (volatile U8 *)dest_end.u8ptr;

        // If end of destination is not 64-bit aligned...
        if (!Test_align((U32)dest_end.u8ptr, sizeof(U64)))
        {
          // Fill the end of the flash double-word buffer with the current flash page data.
          for (i = Get_align((U32)dest_end.u8ptr, sizeof(U64)); i < sizeof(U64); i++)
            flash_dword.u8[i] = *tmp.u8ptr++;

          // Write the flash double-word buffer to the page buffer.
          *dest.u64ptr++ = flash_dword.u64;
        }

        // Fill the end of the page buffer with the current flash page data.
        for (; !Test_align((U32)tmp.u64ptr, AVR32_FLASHC_PAGE_SIZE); tmp.u64ptr++)
          *tmp.u64ptr = *tmp.u64ptr;
      }
      // If page erase is not requested but end of destination is not 64-bit aligned...
      else if (!Test_align((U32)dest_end.u8ptr, sizeof(U64)))
      {
        // Erase the end of the flash double-word buffer.
        for (i = Get_align((U32)dest_end.u8ptr, sizeof(U64)); i < sizeof(U64); i++)
          flash_dword.u8[i] = 0xFF;

        // Write the flash double-word buffer to the page buffer.
        *dest.u64ptr++ = flash_dword.u64;
      }
    }

    // If the current flash page is in the flash array...
    if (dest.u8ptr <= AVR32_FLASHC_USER_PAGE)
    {
      // Erase the current page if requested and write it from the page buffer.
      if (erase)
      {
        flashc_erase_page(-1, FALSE);
        error_status |= flashc_error_status;
      }
      flashc_write_page(-1);
      error_status |= flashc_error_status;

      // If the end of the flash array is reached, go to the User page.
      if (dest.u8ptr >= flash_array_end.u8ptr)
        dest.u8ptr = AVR32_FLASHC_USER_PAGE;
    }
    // If the current flash page is the User page...
    else
    {
      // Erase the User page if requested and write it from the page buffer.
      if (erase)
      {
        flashc_erase_user_page(FALSE);
        error_status |= flashc_error_status;
      }
      flashc_write_user_page();
      error_status |= flashc_error_status;
    }
  }

  // Update the FLASHC error status.
  flashc_error_status = error_status;

  // Return the initial destination pointer as the standard memset function does.
  return dst;
}


volatile void *flashc_memcpy(volatile void *dst, const void *src, size_t nbytes, Bool erase)
{
  // Use aggregated pointers to have several alignments available for a same address.
  UnionCVPtr flash_array_end;
  UnionVPtr dest;
  UnionCPtr source;
  StructCVPtr dest_end;
  UnionCVPtr flash_page_source_end;
  Bool incomplete_flash_page_end;
  Union64 flash_dword;
  Bool flash_dword_pending = FALSE;
  UnionVPtr tmp;
  unsigned int error_status = 0;
  unsigned int i, j;

  // Reformat arguments.
  flash_array_end.u8ptr = AVR32_FLASH + flashc_get_flash_size();
  dest.u8ptr = dst;
  source.u8ptr = src;
  dest_end.u8ptr = dest.u8ptr + nbytes;

  // If destination is outside flash, go to next flash page if any.
  if (dest.u8ptr < AVR32_FLASH)
  {
    source.u8ptr += AVR32_FLASH - dest.u8ptr;
    dest.u8ptr = AVR32_FLASH;
  }
  else if (flash_array_end.u8ptr <= dest.u8ptr && dest.u8ptr < AVR32_FLASHC_USER_PAGE)
  {
    source.u8ptr += AVR32_FLASHC_USER_PAGE - dest.u8ptr;
    dest.u8ptr = AVR32_FLASHC_USER_PAGE;
  }

  // If end of destination is outside flash, move it to the end of the previous flash page if any.
  if (dest_end.u8ptr > AVR32_FLASHC_USER_PAGE + AVR32_FLASHC_USER_PAGE_SIZE)
  {
    dest_end.u8ptr = AVR32_FLASHC_USER_PAGE + AVR32_FLASHC_USER_PAGE_SIZE;
  }
  else if (AVR32_FLASHC_USER_PAGE >= dest_end.u8ptr && dest_end.u8ptr > flash_array_end.u8ptr)
  {
    dest_end.u8ptr = flash_array_end.u8ptr;
  }

  // Align each end of destination pointer with its natural boundary.
  dest_end.u16ptr = (U16 *)Align_down((U32)dest_end.u8ptr, sizeof(U16));
  dest_end.u32ptr = (U32 *)Align_down((U32)dest_end.u16ptr, sizeof(U32));
  dest_end.u64ptr = (U64 *)Align_down((U32)dest_end.u32ptr, sizeof(U64));

  // While end of destination is not reached...
  while (dest.u8ptr < dest_end.u8ptr)
  {
    // Clear the page buffer in order to prepare data for a flash page write.
    flashc_clear_page_buffer();
    error_status |= flashc_error_status;

    // Determine where the source data will end in the current flash page.
    flash_page_source_end.u64ptr =
      (U64 *)min((U32)dest_end.u64ptr,
                 Align_down((U32)dest.u8ptr, AVR32_FLASHC_PAGE_SIZE) + AVR32_FLASHC_PAGE_SIZE);

    // Determine if the current destination page has an incomplete end.
    incomplete_flash_page_end = (Align_down((U32)dest.u8ptr, AVR32_FLASHC_PAGE_SIZE) >=
                                 Align_down((U32)dest_end.u8ptr, AVR32_FLASHC_PAGE_SIZE));

    // If destination does not point to the beginning of the current flash page...
    if (!Test_align((U32)dest.u8ptr, AVR32_FLASHC_PAGE_SIZE))
    {
      // If page erase is requested...
      if (erase)
      {
        // Fill the beginning of the page buffer with the current flash page data.
        for (tmp.u8ptr = (U8 *)Align_down((U32)dest.u8ptr, AVR32_FLASHC_PAGE_SIZE);
             tmp.u64ptr < (U64 *)Align_down((U32)dest.u8ptr, sizeof(U64));
             tmp.u64ptr++)
          *tmp.u64ptr = *tmp.u64ptr;
      }

      // If destination is not 64-bit aligned...
      if (!Test_align((U32)dest.u8ptr, sizeof(U64)))
      {
        // If page erase is requested...
        if (erase)
        {
          // Fill the beginning of the flash double-word buffer with the current flash page data.
          for (i = 0; i < Get_align((U32)dest.u8ptr, sizeof(U64)); i++)
            flash_dword.u8[i] = *tmp.u8ptr++;
        }
        // If page erase is not requested...
        else
        {
          // Erase the beginning of the flash double-word buffer.
          for (i = 0; i < Get_align((U32)dest.u8ptr, sizeof(U64)); i++)
            flash_dword.u8[i] = 0xFF;
        }

        // Fill the end of the flash double-word buffer with the source data.
        for (; i < sizeof(U64); i++)
          flash_dword.u8[i] = *source.u8ptr++;

        // Align the destination pointer with its 64-bit boundary.
        dest.u64ptr = (U64 *)Align_down((U32)dest.u8ptr, sizeof(U64));

        // If the current destination double-word is not the last one...
        if (dest.u64ptr < dest_end.u64ptr)
        {
          // Write the flash double-word buffer to the page buffer.
          *dest.u64ptr++ = flash_dword.u64;
        }
        // If the current destination double-word is the last one, the flash
        // double-word buffer must be kept for later.
        else flash_dword_pending = TRUE;
      }
    }

    // Read the source data with the maximal possible alignment and write it to
    // the page buffer with 64-bit alignment.
    switch (Get_align((U32)source.u8ptr, sizeof(U32)))
    {
    case 0:
      for (i = flash_page_source_end.u64ptr - dest.u64ptr; i; i--)
        *dest.u64ptr++ = *source.u64ptr++;
      break;

    case sizeof(U16):
      for (i = flash_page_source_end.u64ptr - dest.u64ptr; i; i--)
      {
        for (j = 0; j < sizeof(U64) / sizeof(U16); j++) flash_dword.u16[j] = *source.u16ptr++;
        *dest.u64ptr++ = flash_dword.u64;
      }
      break;

    default:
      for (i = flash_page_source_end.u64ptr - dest.u64ptr; i; i--)
      {
        for (j = 0; j < sizeof(U64); j++) flash_dword.u8[j] = *source.u8ptr++;
        *dest.u64ptr++ = flash_dword.u64;
      }
    }

    // If the current destination page has an incomplete end...
    if (incomplete_flash_page_end)
    {
      // If the flash double-word buffer is in use, do not initialize it.
      if (flash_dword_pending) i = Get_align((U32)dest_end.u8ptr, sizeof(U64));
      // If the flash double-word buffer is free...
      else
      {
        // Fill the beginning of the flash double-word buffer with the source data.
        for (i = 0; i < Get_align((U32)dest_end.u8ptr, sizeof(U64)); i++)
          flash_dword.u8[i] = *source.u8ptr++;
      }

      // If page erase is requested...
      if (erase)
      {
        tmp.u8ptr = (volatile U8 *)dest_end.u8ptr;

        // If end of destination is not 64-bit aligned...
        if (!Test_align((U32)dest_end.u8ptr, sizeof(U64)))
        {
          // Fill the end of the flash double-word buffer with the current flash page data.
          for (; i < sizeof(U64); i++)
            flash_dword.u8[i] = *tmp.u8ptr++;

          // Write the flash double-word buffer to the page buffer.
          *dest.u64ptr++ = flash_dword.u64;
        }

        // Fill the end of the page buffer with the current flash page data.
        for (; !Test_align((U32)tmp.u64ptr, AVR32_FLASHC_PAGE_SIZE); tmp.u64ptr++)
          *tmp.u64ptr = *tmp.u64ptr;
      }
      // If page erase is not requested but end of destination is not 64-bit aligned...
      else if (!Test_align((U32)dest_end.u8ptr, sizeof(U64)))
      {
        // Erase the end of the flash double-word buffer.
        for (; i < sizeof(U64); i++)
          flash_dword.u8[i] = 0xFF;

        // Write the flash double-word buffer to the page buffer.
        *dest.u64ptr++ = flash_dword.u64;
      }
    }

    // If the current flash page is in the flash array...
    if (dest.u8ptr <= AVR32_FLASHC_USER_PAGE)
    {
      // Erase the current page if requested and write it from the page buffer.
      if (erase)
      {
        flashc_erase_page(-1, FALSE);
        error_status |= flashc_error_status;
      }
      flashc_write_page(-1);
      error_status |= flashc_error_status;

      // If the end of the flash array is reached, go to the User page.
      if (dest.u8ptr >= flash_array_end.u8ptr)
      {
        source.u8ptr += AVR32_FLASHC_USER_PAGE - dest.u8ptr;
        dest.u8ptr = AVR32_FLASHC_USER_PAGE;
      }
    }
    // If the current flash page is the User page...
    else
    {
      // Erase the User page if requested and write it from the page buffer.
      if (erase)
      {
        flashc_erase_user_page(FALSE);
        error_status |= flashc_error_status;
      }
      flashc_write_user_page();
      error_status |= flashc_error_status;
    }
  }

  // Update the FLASHC error status.
  flashc_error_status = error_status;

  // Return the initial destination pointer as the standard memcpy function does.
  return dst;
}


//! @}
