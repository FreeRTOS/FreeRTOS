/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support
 * ----------------------------------------------------------------------------
 * Copyright (c) 2009, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/**
 * \file
 *
 * Interface for memories configuration on board.
 *
 */

#ifndef BOARD_MEMORIES_H
#define BOARD_MEMORIES_H

   // Micron MT47H128M16 ?16 Meg x 16 x 8 banks = 256 MBytes
   // => 2 chips used => 512 MBytes
   // data bus = 32 bits => 16 Meg x 32 x 8 Banks => 256 Meg * 16 available

#define DDR2_MEM8SIZE            0x20000000
#define DDR2_MEM16SIZE           0x10000000
#define DDR2_MEM32SIZE           0x8000000

#define EXT_32_LPDDR2_8BANK_16_32_SOD200_SIZE 0x20000000



//void  LPDDR2_AC_TIMING(LPDDR2 * st_ddr2, unsigned int f_base);
/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

extern void BOARD_RemapRom( void );
extern void BOARD_RemapRam( void );
extern void BOARD_ConfigureVddMemSel(uint8_t VddMemSel) ;
extern void BOARD_ConfigureDdram( uint8_t device );
extern void BOARD_ConfigureSdram( void );
extern void BOARD_ConfigureNandFlash( uint8_t busWidth ) ;
extern void BOARD_ConfigureNorFlash( uint8_t busWidth ) ;
extern void BOARD_ConfigureLpDdram(void);
#endif /* #ifndef BOARD_MEMORIES_H */

