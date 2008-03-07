//*****************************************************************************
//
// hw_types.h - Common types and macros.
//
// Copyright (c) 2005-2007 Luminary Micro, Inc.  All rights reserved.
// 
// Software License Agreement
// 
// Luminary Micro, Inc. (LMI) is supplying this software for use solely and
// exclusively on LMI's microcontroller products.
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
// This is part of revision 1582 of the Stellaris Peripheral Driver Library.
//
//*****************************************************************************

#ifndef __HW_TYPES_H__
#define __HW_TYPES_H__

//*****************************************************************************
//
// Define a boolean type, and values for true and false.
//
//*****************************************************************************
typedef unsigned char tBoolean;

#ifndef true
#define true 1
#endif

#ifndef false
#define false 0
#endif

//*****************************************************************************
//
// Macros for hardware access, both direct and via the bit-band region.
//
//*****************************************************************************
#define HWREG(x)                                                              \
        (*((volatile unsigned long *)(x)))
#define HWREGH(x)                                                             \
        (*((volatile unsigned short *)(x)))
#define HWREGB(x)                                                             \
        (*((volatile unsigned char *)(x)))
#define HWREGBITW(x, b)                                                       \
        HWREG(((unsigned long)(x) & 0xF0000000) | 0x02000000 |                \
              (((unsigned long)(x) & 0x000FFFFF) << 5) | ((b) << 2))
#define HWREGBITH(x, b)                                                       \
        HWREGH(((unsigned long)(x) & 0xF0000000) | 0x02000000 |               \
               (((unsigned long)(x) & 0x000FFFFF) << 5) | ((b) << 2))
#define HWREGBITB(x, b)                                                       \
        HWREGB(((unsigned long)(x) & 0xF0000000) | 0x02000000 |               \
               (((unsigned long)(x) & 0x000FFFFF) << 5) | ((b) << 2))

//*****************************************************************************
//
// Helper Macros for determining silicon revisions, etc.
//
// These macros will be used by Driverlib at "run-time" to create necessary
// conditional code blocks that will allow a single version of the Driverlib
// "binary" code to support multiple(all) Stellaris silicon revisions.
//
// It is expected that these macros will be used inside of a standard 'C' 
// conditional block of code, e.g.
//
//     if(DEVICE_IS_SANDSTORM())
//     {
//         do some Sandstorm specific code here.
//     }
//
// By default, these macros will be defined as run-time checks of the
// appropriate register(s) to allow creation of run-time conditional code
// blocks for a common DriverLib across the entire Stellaris family.
//
// However, if code-space optimization is required, these macros can be "hard-
// coded" for a specific version of Stellaris silicon.  Many compilers will
// then detect the "hard-coded" conditionals, and appropriately optimize the
// code blocks, eliminating any "unreachable" code.  This would result in 
// a smaller Driverlib, thus producing a smaller final application size, but
// at the cost of limiting the Driverlib binary to a specific Stellaris
// silicon revision.
//
//*****************************************************************************
#ifndef DEVICE_IS_SANDSTORM
#define DEVICE_IS_SANDSTORM                                                \
    (((HWREG(SYSCTL_DID0) & SYSCTL_DID0_VER_MASK) == SYSCTL_DID0_VER_0) || \
    (((HWREG(SYSCTL_DID0) & SYSCTL_DID0_VER_MASK) == SYSCTL_DID0_VER_1) && \
     ((HWREG(SYSCTL_DID0) & SYSCTL_DID0_CLASS_MASK) ==                     \
        SYSCTL_DID0_CLASS_SANDSTORM)))
#endif

#ifndef DEVICE_IS_FURY
#define DEVICE_IS_FURY                                                     \
    (((HWREG(SYSCTL_DID0) & SYSCTL_DID0_VER_MASK) == SYSCTL_DID0_VER_1) && \
     ((HWREG(SYSCTL_DID0) & SYSCTL_DID0_CLASS_MASK) ==                     \
        SYSCTL_DID0_CLASS_FURY))
#endif

#ifndef DEVICE_IS_REVA2
#define DEVICE_IS_REVA2                                                    \
    (((HWREG(SYSCTL_DID0) & SYSCTL_DID0_MAJ_MASK) == SYSCTL_DID0_MAJ_A) && \
     ((HWREG(SYSCTL_DID0) & SYSCTL_DID0_MIN_MASK) == SYSCTL_DID0_MIN_2))
#endif

#ifndef DEVICE_IS_REVC1
#define DEVICE_IS_REVC1                                                    \
    (((HWREG(SYSCTL_DID0) & SYSCTL_DID0_MAJ_MASK) == SYSCTL_DID0_MAJ_C) && \
     ((HWREG(SYSCTL_DID0) & SYSCTL_DID0_MIN_MASK) == SYSCTL_DID0_MIN_1))
#endif

#ifndef DEVICE_IS_REVC2
#define DEVICE_IS_REVC2                                                    \
    (((HWREG(SYSCTL_DID0) & SYSCTL_DID0_MAJ_MASK) == SYSCTL_DID0_MAJ_C) && \
     ((HWREG(SYSCTL_DID0) & SYSCTL_DID0_MIN_MASK) == SYSCTL_DID0_MIN_2))
#endif

#endif // __HW_TYPES_H__
