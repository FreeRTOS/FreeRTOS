//*****************************************************************************
//
// hw_flash.h - Macros used when accessing the flash controller.
//
// Copyright (c) 2005,2006 Luminary Micro, Inc.  All rights reserved.
//
// Software License Agreement
//
// Luminary Micro, Inc. (LMI) is supplying this software for use solely and
// exclusively on LMI's Stellaris Family of microcontroller products.
//
// The software is owned by LMI and/or its suppliers, and is protected under
// applicable copyright laws.  All rights are reserved.  Any use in violation
// of the foregoing restrictions may subject the user to criminal sanctions
// under applicable laws, as well as to civil liability for the breach of the
// terms and conditions of this license.
//
// THIS SOFTWARE IS PROVIDED "AS IS".  NO WARRANTIES, WHETHER EXPRESS, IMPLIED
// OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE APPLY TO THIS SOFTWARE.
// LMI SHALL NOT, IN ANY CIRCUMSTANCES, BE LIABLE FOR SPECIAL, INCIDENTAL, OR
// CONSEQUENTIAL DAMAGES, FOR ANY REASON WHATSOEVER.
//
// This is part of revision 991 of the Stellaris Driver Library.
//
//*****************************************************************************

#ifndef __HW_FLASH_H__
#define __HW_FLASH_H__

//*****************************************************************************
//
// The following define the offsets of the FLASH registers.
//
//*****************************************************************************
#define FLASH_FMA               0x400FD000  // Memory address register
#define FLASH_FMD               0x400FD004  // Memory data register
#define FLASH_FMC               0x400FD008  // Memory control register
#define FLASH_FCRIS             0x400FD00c  // Raw interrupt status register
#define FLASH_FCIM              0x400FD010  // Interrupt mask register
#define FLASH_FCMISC            0x400FD014  // Interrupt status register
#define FLASH_FMPRE             0x400FE130  // FLASH read protect register
#define FLASH_FMPPE             0x400FE134  // FLASH program protect register
#define FLASH_USECRL            0x400FE140  // uSec reload register

//*****************************************************************************
//
// The following define the bit fields in the FLASH_FMC register.
//
//*****************************************************************************
#define FLASH_FMC_WRKEY_MASK    0xFFFF0000  // FLASH write key mask
#define FLASH_FMC_WRKEY         0xA4420000  // FLASH write key
#define FLASH_FMC_COMT          0x00000008  // Commit user register
#define FLASH_FMC_MERASE        0x00000004  // Mass erase FLASH
#define FLASH_FMC_ERASE         0x00000002  // Erase FLASH page
#define FLASH_FMC_WRITE         0x00000001  // Write FLASH word

//*****************************************************************************
//
// The following define the bit fields in the FLASH_FCRIS register.
//
//*****************************************************************************
#define FLASH_FCRIS_PROGRAM     0x00000002  // Programming status
#define FLASH_FCRIS_ACCESS      0x00000001  // Invalid access status

//*****************************************************************************
//
// The following define the bit fields in the FLASH_FCIM register.
//
//*****************************************************************************
#define FLASH_FCIM_PROGRAM      0x00000002  // Programming mask
#define FLASH_FCIM_ACCESS       0x00000001  // Invalid access mask

//*****************************************************************************
//
// The following define the bit fields in the FLASH_FMIS register.
//
//*****************************************************************************
#define FLASH_FCMISC_PROGRAM    0x00000002  // Programming status
#define FLASH_FCMISC_ACCESS     0x00000001  // Invalid access status

//*****************************************************************************
//
// The following define the bit fields in the FLASH_FMPRE and FLASH_FMPPE
// registers.
//
//*****************************************************************************
#define FLASH_FMP_BLOCK_31      0x80000000  // Enable for block 31
#define FLASH_FMP_BLOCK_30      0x40000000  // Enable for block 30
#define FLASH_FMP_BLOCK_29      0x20000000  // Enable for block 29
#define FLASH_FMP_BLOCK_28      0x10000000  // Enable for block 28
#define FLASH_FMP_BLOCK_27      0x08000000  // Enable for block 27
#define FLASH_FMP_BLOCK_26      0x04000000  // Enable for block 26
#define FLASH_FMP_BLOCK_25      0x02000000  // Enable for block 25
#define FLASH_FMP_BLOCK_24      0x01000000  // Enable for block 24
#define FLASH_FMP_BLOCK_23      0x00800000  // Enable for block 23
#define FLASH_FMP_BLOCK_22      0x00400000  // Enable for block 22
#define FLASH_FMP_BLOCK_21      0x00200000  // Enable for block 21
#define FLASH_FMP_BLOCK_20      0x00100000  // Enable for block 20
#define FLASH_FMP_BLOCK_19      0x00080000  // Enable for block 19
#define FLASH_FMP_BLOCK_18      0x00040000  // Enable for block 18
#define FLASH_FMP_BLOCK_17      0x00020000  // Enable for block 17
#define FLASH_FMP_BLOCK_16      0x00010000  // Enable for block 16
#define FLASH_FMP_BLOCK_15      0x00008000  // Enable for block 15
#define FLASH_FMP_BLOCK_14      0x00004000  // Enable for block 14
#define FLASH_FMP_BLOCK_13      0x00002000  // Enable for block 13
#define FLASH_FMP_BLOCK_12      0x00001000  // Enable for block 12
#define FLASH_FMP_BLOCK_11      0x00000800  // Enable for block 11
#define FLASH_FMP_BLOCK_10      0x00000400  // Enable for block 10
#define FLASH_FMP_BLOCK_9       0x00000200  // Enable for block 9
#define FLASH_FMP_BLOCK_8       0x00000100  // Enable for block 8
#define FLASH_FMP_BLOCK_7       0x00000080  // Enable for block 7
#define FLASH_FMP_BLOCK_6       0x00000040  // Enable for block 6
#define FLASH_FMP_BLOCK_5       0x00000020  // Enable for block 5
#define FLASH_FMP_BLOCK_4       0x00000010  // Enable for block 4
#define FLASH_FMP_BLOCK_3       0x00000008  // Enable for block 3
#define FLASH_FMP_BLOCK_2       0x00000004  // Enable for block 2
#define FLASH_FMP_BLOCK_1       0x00000002  // Enable for block 1
#define FLASH_FMP_BLOCK_0       0x00000001  // Enable for block 0

//*****************************************************************************
//
// The following define the bit fields in the FLASH_USECRL register.
//
//*****************************************************************************
#define FLASH_USECRL_MASK       0x000000FF  // Clock per uSec
#define FLASH_USECRL_SHIFT      0

//*****************************************************************************
//
// The erase size is the size of the FLASH block that is erased by an erase
// operation, and the protect size is the size of the FLASH block that is
// protected by each protection register.
//
//*****************************************************************************
#define FLASH_ERASE_SIZE        0x00000400
#define FLASH_PROTECT_SIZE      0x00000800

#endif // __HW_FLASH_H__
