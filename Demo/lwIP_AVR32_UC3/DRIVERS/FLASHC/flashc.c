/* This source file is part of the ATMEL FREERTOS-0.9.0 Release */

/*This file has been prepared for Doxygen automatic documentation generation.*/
/*! \file *********************************************************************
 *
 * \brief Flash Controller driver.
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


#include "flashc.h"

/*! Flash command key*/
#define X_KEY 0xA5000000


/*! Get locke error.
 * \warning: Flash status register (FCR) is read, and Programmming error status may be automatically
 * cleared when reading FCR.
 */
#define Flashc_get_lockerror() ((AVR32_FLASHC.fsr & AVR32_FLASHC_FSR_LOCKE_MASK)>>AVR32_FLASHC_FSR_LOCKE_OFFSET)

/*! Get programming error.
 * \warning: Flash status register (FCR) is read, and locke error status may be automatically
 * cleared when reading FCR.
 */
#define Flashc_get_programming_error() ((AVR32_FLASHC.fsr & AVR32_FLASHC_FSR_PROGE_MASK)>>AVR32_FLASHC_FSR_PROGE_OFFSET)

/*! Check if page is erased (used with the quick page read command result)
 * \warning: Flash status register (FCR) is read, and error status may be automatically
 * cleared when reading FCR.
 */
#define Flashc_is_page_erased()  ((AVR32_FLASHC.fsr & AVR32_FLASHC_FSR_QPRR_MASK)>>AVR32_FLASHC_FSR_QPRR_OFFSET)

/*! Set: No erase is performed before programming. */
#define Flashc_set_no_erase_before_programming()  (AVR32_FLASHC.fcr |= AVR32_FLASHC_FCR_NEBP_MASK)

/*! Set: Page erase is performed before programming. */
#define Flashc_set_erase_before_programming()  (AVR32_FLASHC.fcr &= ~AVR32_FLASHC_FCR_NEBP_MASK)


/*!
 * Memcopy function
 * \param *s1 destination
 * \param *s2 source
 * \param n word numbers to copy
 */
U32 *flashc_memcpy(U32 *s1, const U32 *s2, const U32 n) {
  register U32 *u32pdst;
  register U32 i;
  u32pdst = s1;
  for (i = n; i > 0; i--) *u32pdst++ = *s2++;
  return s1;
}

/*!
 * Set number of wait state for flash controller.
 */
int flashc_set_wait_state(U16 ws)
{
  if (ws > 1 ) return FLASHC_INVALID_INPUT;
  if (ws == 0) AVR32_FLASHC.fcr &= ~AVR32_FLASHC_FWS_MASK; // update flash control register FCR
  if (ws == 1) AVR32_FLASHC.fcr |=  AVR32_FLASHC_FWS_MASK;
  return FLASHC_SUCCESS;
}


/*!
 * Page write n
 * \param n page number
 * \warning Assuming the page address is already loaded
 */
void flashc_page_write_n(U16 page_n) {
  register U32 u32Command;
  u32Command = X_KEY | AVR32_FLASHC_FCMD_CMD_WP; // key and command
  u32Command |= ((page_n<<AVR32_FLASHC_FCMD_PAGEN_OFFSET) & AVR32_FLASHC_FCMD_PAGEN_MASK);  // update page field
  flashc_busy_wait();
  AVR32_FLASHC.fcmd = u32Command;
}

/* Page write
 * Assuming the page address is already loaded
 */
void flashc_page_write(U16 page_n) {
  register U32 u32Command;
  u32Command = X_KEY | AVR32_FLASHC_FCMD_CMD_WP; // key and command
  u32Command |= ((page_n<<AVR32_FLASHC_FCMD_PAGEN_OFFSET) & AVR32_FLASHC_FCMD_PAGEN_MASK);  // update page field
  flashc_busy_wait();
  AVR32_FLASHC.fcmd = u32Command;
}

/* Clear page buffer */
void flashc_clear_page_buffer(void){
  register U32 u32Command;
  u32Command = X_KEY | AVR32_FLASHC_FCMD_CMD_CPB; // key and command clear page buffer
  flashc_busy_wait();
  AVR32_FLASHC.fcmd = u32Command;
}

/* Page erase
 * Assuming the page address is already loaded
 */
void flashc_erase_page(U16 page_n){
  register U32 u32Command;
  u32Command = X_KEY | AVR32_FLASHC_FCMD_CMD_EP; // key and command,
  u32Command |= ((page_n<<AVR32_FLASHC_FCMD_PAGEN_OFFSET) & AVR32_FLASHC_FCMD_PAGEN_MASK);  // update page field
  flashc_busy_wait();
  AVR32_FLASHC.fcmd = u32Command;
}

/* Erase all Pages */
void flashc_erase_all(void){
  register U32 u32Command;
  u32Command = X_KEY | AVR32_FLASHC_FCMD_CMD_EA; // key and command,
  //u32Command |= ((page_n<<AVR32_FLASHC_FCMD_PAGEN_OFFSET) & AVR32_FLASHC_FCMD_PAGEN_MASK);  // update page field
  flashc_busy_wait();
  AVR32_FLASHC.fcmd = u32Command;
  flashc_busy_wait();
}

/* Erase a page and check if OK with the quick page read command */
int flashc_erase_page_and_check(U16 page_n)
{
  flashc_erase_page(page_n); // erase page page_n first

  flashc_busy_wait();

  AVR32_FLASHC.fcmd = X_KEY | ((page_n<<AVR32_FLASHC_PAGEN_OFFSET)&AVR32_FLASHC_PAGEN_MASK) | AVR32_FLASHC_FCMD_CMD_QPR; // qpr on current page number
  while(!((AVR32_FLASHC.fsr & AVR32_FLASHC_FSR_FRDY_MASK)>>AVR32_FLASHC_FSR_FRDY_OFFSET));

  if (Flashc_is_page_erased() == 0) // check QPRR bit in FCR to have the result of the quick page read
    return FLASHC_FAILURE;
  return FLASHC_SUCCESS;
}

/*!
 * Page load and write
 * \warning Dest is a FLASH address at a page size boundary
 * (assuming the page is already erased)
 */
void flashc_page_copy_write(U32 *u32dest, const U32 *src) {
  register U32 u32command,pagen;
  flashc_memcpy(u32dest, src, AVR32_FLASHC_PAGE_SIZE / 4);  // copy Src to Dest (Dest is a FLASH address at a page boundary)
  pagen = (U32)(((U32)u32dest-AVR32_FLASH_ADDRESS)/AVR32_FLASHC_PAGE_SIZE); // memory page addr
  u32command = X_KEY | ((pagen<<AVR32_FLASHC_PAGEN_OFFSET)&AVR32_FLASHC_PAGEN_MASK)  |AVR32_FLASHC_FCMD_CMD_WP; // key and command
  flashc_busy_wait();
  AVR32_FLASHC.fcmd = u32command;
}

/* Copy data into page buffer */
#if __GNUC__
__attribute__((__always_inline__))
#endif
static __inline__ void flash_fill_temp_buffer(U32 u32Data, U32 u32Address)
{
  *((U32*)u32Address) = u32Data;
}

/* Read word from flash
 * addr should be 32-bit aligned.
 */
#if __GNUC__
__attribute__((__always_inline__))
#endif
static __inline__ U32 flash_rd_word(U32 const* addr)
{
  return *addr;
}

/**
 * This function allows to write up to 65535 bytes in the flash memory.
 * This function manages alignement issue (byte and page alignements).
 */
int flash_wr_block(U32 * src, U32 dst, U32 n)
{
   U32 u32NbWord=0;
   U32 u32Temp=0;
   U32 u32SavePageAddr=0;

   U32 u32Address = dst-(dst%AVR32_FLASHC_PAGE_SIZE); // Compute the start of the page to be modified

   while(n)  // While there is data to load from src buffer
   {
      //      u32Address = dst-((dst&0xFFFFffff)%AVR32_FLASHC_PAGE_SIZE); // Compute the start of the page to be modified
      u32SavePageAddr = (u32Address-AVR32_FLASH_ADDRESS)/AVR32_FLASHC_PAGE_SIZE;  //memorize page addr

      // For each word in this page
      for(u32NbWord=0 ; u32NbWord<AVR32_FLASHC_PAGE_SIZE/4 ; u32NbWord++)
      {
         if(n) //Still some data to load from src
         {
            if(u32Address >= dst) //current address is inside the target range adr
            {
              u32Temp = * ((U32*)src);  // load word from buffer src
              src++;
              n--;
            }
            else  //current word addr out of dst target
            {
              u32Temp = flash_rd_word((U32 const*)u32Address); // load word from existing flash
            }
         }
         else  //complete page with words from existing flash
         {
            u32Temp = flash_rd_word((U32 const*)u32Address);
         }
         flash_fill_temp_buffer(u32Temp, u32Address); // fill page buffer
         u32Address+=4; // one more word for u32Address
      }

      // u32Address = u32SavePageAddr*AVR32_FLASHC_PAGE_SIZE+AVR32_FLASH_ADDRESS;

      /*
      // Done with QPR
      for(u32NbWord=0 ; u32NbWord<AVR32_FLASHC_PAGE_SIZE/4 ; u32NbWord++)
      {
         if(flash_rd_word((U32 farcode*)u32Address)!=0xFFFFffff) // check if the page is erased
         {
            Flash_page_erase(u32SavePageAddr);
            break;
         }
         u32Address+=4;
      }
      */

    // Check if page is erased
    AVR32_FLASHC.fcmd = X_KEY | ((u32SavePageAddr<<AVR32_FLASHC_PAGEN_OFFSET)&AVR32_FLASHC_PAGEN_MASK) | AVR32_FLASHC_CMD_QPR; // qpr on current page number
    while(!((AVR32_FLASHC.fsr & AVR32_FLASHC_FSR_FRDY_MASK)>>AVR32_FLASHC_FSR_FRDY_OFFSET));

    if ( (AVR32_FLASHC.fsr & AVR32_FLASHC_FSR_QPRR_MASK)>> AVR32_FLASHC_FSR_QPRR_OFFSET == 0 ) // test QPR bit in FSR
    {  // erase page
       AVR32_FLASHC.fcmd = X_KEY | ((u32SavePageAddr<<AVR32_FLASHC_PAGEN_OFFSET)&AVR32_FLASHC_PAGEN_MASK) | AVR32_FLASHC_FCMD_CMD_EP; //page n erase cmd
       while(!((AVR32_FLASHC.fsr & AVR32_FLASHC_FSR_FRDY_MASK)>>AVR32_FLASHC_FSR_FRDY_OFFSET));
    }

    flashc_page_write_n(u32SavePageAddr); // write the corresponding page number
    flashc_clear_page_buffer();
   } // end while (n)
   return FLASHC_SUCCESS;
}

/* Erase all flash with pages access */
void flash_erase(void)
{
  U32 u32NbPage = flashc_get_page_count();
  while (u32NbPage) flashc_erase_page(--u32NbPage);
}
