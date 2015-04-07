/*******************************************************************************
 * (c) Copyright 2009 Actel Corporation.  All rights reserved.
 * 
 * Assertion implementation.
 *
 * This file provides the implementation of the ASSERT macro. This file can be
 * modified to cater for project specific requirements regarding the way
 * assertions are handled.
 *
 * SVN $Revision: 1676 $
 * SVN $Date: 2009-12-02 16:47:03 +0000 (Wed, 02 Dec 2009) $
 */
#ifndef __MSS_ASSERT_H_
#define __MSS_ASSERT_H_

#include <assert.h>

#if defined ( __GNUC__   )

#if defined(NDEBUG)

#define ASSERT(CHECK)

#else   /* NDEBUG */
/*
 * SoftConsole assertion handling
 */
#define ASSERT(CHECK)  \
    do { \
        if (!(CHECK)) \
        { \
            __asm volatile ("BKPT\n\t"); \
        } \
    } while (0);
    
#endif  /* NDEBUG */

#else
/*
 * IAR Embedded Workbench or Keil assertion handling.
 * Call C library assert function which should result in error message
 * displayed in debugger.
 */
#define ASSERT(X)   assert(X)

#endif

#endif  /* __MSS_ASSERT_H_ */
